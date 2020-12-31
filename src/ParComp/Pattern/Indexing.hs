{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DerivingStrategies #-}

-- {-# LANGUAGE ScopedTypeVariables #-}
-- {-# LANGUAGE PartialTypeSignatures #-}

-- {-# LANGUAGE QuantifiedConstraints #-}


module ParComp.Pattern.Indexing
  (

  -- * Dummy matching
    dummyMatch

  -- * Indexing (locks and keys)
  , Template
  , Key
  , Lock (..)
  , KeyVal
  , mkLock
  , getLockKey
  , keyValFor
  , locksFor

  -- * Rule application
  , Index
  , applyDirRule

  -- * Index info
  , IndexInfo (..)
  , DirRule (..)
  , addIndexInfo
  -- , rmIndexInfo
  ) where


-- import           Prelude hiding (const, map, any)
-- 
-- import qualified System.Random as R
-- 
import           Control.Monad (guard, forM) --, void, forM)
-- import qualified Control.Monad.RWS.Strict as RWS
import           Control.Applicative ((<|>))

import qualified Pipes as P
import qualified Pipes.Prelude as P

-- import           Data.Lens.Light
-- 
-- import qualified Data.Primitive.Array as A
-- 
-- import           Data.Void (Void)
-- import           Data.String (IsString)
import qualified Data.Foldable as F
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import qualified ParComp.Pattern.Untyped as Un
import           ParComp.Pattern.Untyped
  ( Item(..), Var(..), Op(..)
  , Cond(..), Rigit(..), Pattern(..)
  , MatchT
  )
import qualified ParComp.Pattern.Rule as R

import           Debug.Trace (trace)


--------------------------------------------------
-- Global vars
--------------------------------------------------


-- | Retrieve the set of global variables bound in the pattern.
--
-- A variable is bound in the pattern if it gets bound during matching of the
-- pattern with an item.
--
-- Assumption: In case of the `Or` pattern, we assume that both branches
-- contain the same set of global variables.  This is non-trivial to check at
-- runtime (and hence is not enforced) due to `Rec` patterns.
globalVarsIn :: Pattern -> S.Set Var
globalVarsIn (P ip) = case ip of
--   Pair p1 p2 -> globalVarsIn p1 <> globalVarsIn p2
  Vec v -> foldMap globalVarsIn v
--   Union up -> case up of
--     Left p  -> globalVarsIn p
--     Right p -> globalVarsIn p
  Tag _ x -> globalVarsIn x
  _ -> S.empty
globalVarsIn (O op) = case op of
  Choice x y -> globalVarsIn x <> globalVarsIn y
--     let xs = globalVarsIn x
--         ys = globalVarsIn y
--      in if xs == ys
--            then xs
--            else error "globalVarsIn: different sets of variables in Or"
  Seq x y -> globalVarsIn x <> globalVarsIn y
  Via x y -> globalVarsIn x <> globalVarsIn y
  Label v -> S.singleton v
  Local _ -> error "globalVarsIn: encountered local variable!"
  Any -> S.empty
  Map _ p -> globalVarsIn p
  Map' f p ->
    let fs = globalVarsIn f
        ps = globalVarsIn p
     in if S.null fs
           then ps
           else error $ concat
              [ "globalVarsIn: functional pattern with global variables: "
              , show (S.toList fs)
              ]
  App _ -> S.empty
  -- Below, we don't inspect the condition, since it doesn't bind additional
  -- variables during matching
  With p _ -> globalVarsIn p
  -- Below, ignore `x` and `y`, which should contain local variables only
  Let x e y -> globalVarsIn e
  Fix p -> globalVarsIn p
  Rec -> S.empty


--------------------------------------------------
-- Dummy matching
--------------------------------------------------


-- | Dummy pattern matching
--
-- Match the pattern against a dummy value by assuming that they match
-- perfectly.  The motivation behind `dummyMatch` is to bind the (global)
-- variables in the pattern (to some dummy values), so that we can later learn
-- what variables the pattern actually uses (and e.g. use `mkLock`).
--
-- Internally, the function (a) retrieves the set of global variables in @p@
-- and (b) binds them to unit values.
dummyMatch :: (Monad m) => Pattern -> MatchT m ()
dummyMatch p = do
  mapM_
    (flip Un.bindVar Un.unit)
    (S.toList $ globalVarsIn p)


--------------------------------------------------
-- Indexing
--------------------------------------------------


-- | Index template: a pattern which determines which items can be stored in the
-- corresponding index structure.
type Template = Pattern


-- | Index key: a set of patterns which describe a particular search criterion.
type Key = S.Set Pattern


-- | Lock determines the indexing structure.
--
-- Each `Item` (`Pattern`) can be matched with the `Lock` to produce the
-- corresponding `Key`(s).  These keys then allow to find the item (pattern) in
-- the index corresponding to the lock.
data Lock = Lock
  { lockTemplate :: Template
    -- ^ Lock's template
  , lockKey :: Key
    -- ^ Relevant variables and patterns, whose values need to be specified in
    -- the corresponding key
  } deriving (Show, Eq, Ord)


-- | Key assigns values to the variables (and patterns) in the corresponding
-- lock (in `lockKey`, more precisely).
type KeyVal = M.Map Pattern Rigit


-- | Retrieve the index keys for a given index template.
getLockKey :: (P.MonadIO m) => Template -> MatchT m Key
getLockKey (P ip) = case ip of
  Unit -> pure S.empty
  Sym _ -> pure S.empty
  -- Vec v -> foldMap getLockKey v
  Vec v -> do
    -- TODO: perhaps possible to handle this case more efficiently?
    let f prev x = do
          next <- getLockKey x
          return (prev <> next)
    F.foldlM f S.empty v
  Tag _ x -> getLockKey x
getLockKey (O op) = case op of
  Label v ->
    Un.lookupVar v >>= \case
      Just it -> pure $ S.singleton (Un.labelP v)
      Nothing -> pure S.empty
  Local v -> error "getLockKey: encountered local variable!"
  Any -> pure S.empty
  Map fn p -> do
    Un.closeable p >>= \case
      True -> pure $ S.singleton (Un.mapP fn p)
      False -> pure S.empty
  Map' f p -> do
    Un.closeable p >>= \case
      True ->
        trace "getLockKey: doesn't handle Map' with a closeable pattern" $
          pure S.empty
      False -> pure S.empty
  App _ -> pure S.empty
  Choice x y -> do
    -- NB: Since we assume that both @x@ and @y@ contain the same global
    -- variables (see `globalVarsIn`), @getLockKey x@ and @getLockKey y@
    -- should yield the same result.
    s1 <- getLockKey x
    s2 <- getLockKey y
    -- NOTE: Perhaps the behavior below should be analoguous to how `Or` is
    -- handled in `getLockKeyC`?
    if s1 == s2
       then return s1
       else error "getLockKey Choice: different results for different branches"
  Seq x y -> (<>) <$> getLockKey x <*> getLockKey y
  -- TODO: Below, do we need to retrieve lock keys from `p`?
  Via p x -> (<>) <$> getLockKey p <*> getLockKey x
  With p c -> (<>) <$> getLockKey p <*> getLockKeyC c
  -- Below, ignore `x` and `y`, which should contain local variables only
  Let x e y -> getLockKey e
  Fix p -> getLockKey p
  Rec -> pure S.empty


-- | Retrieve the bound variables and patterns for the lock.
getLockKeyC :: (P.MonadIO m) => Cond Pattern -> MatchT m (S.Set Pattern)
getLockKeyC = \case
  Eq px py -> do
    cx <- Un.closeable px
    cy <- Un.closeable py
    case (cx, cy) of
      (True, False) -> pure $ S.singleton px
      (False, True) -> pure $ S.singleton py
      _ -> pure S.empty
  And c1 c2 -> (<>) <$> getLockKeyC c1 <*> getLockKeyC c2
  -- NB: `alt` not necessary below since `getLockVar` doesn't modify the state
--   Or c1 c2 -> getLockKeyC c1 <|> getLockKeyC c2
  Or c1 c2 -> do
    k1 <- getLockKeyC c1
    k2 <- getLockKeyC c2
    if k1 == k2
       then return k1
       else return k1 <|> return k2
  -- Neg c -> getLockKeyC c
--   TrueC -> pure S.empty
--   IsTrue p ->
--     Un.closeable p >>= \case
--       True  -> pure $ S.singleton p
--       False -> pure S.empty


-- | Retrieve the lock of the pattern.  The lock can be used to determine the
-- corresponding indexing structure.
mkLock :: (P.MonadIO m) => Template -> MatchT m Lock
mkLock p = Lock p <$> getLockKey p


-- | Generate all the locks for the given rule.
locksFor :: (P.MonadIO m) => R.DirRule -> P.ListT m Lock
locksFor rule =
  P.Select $ _locksFor rule P.yield


-- | Generate all the locks for the given rule.
_locksFor
  :: (P.MonadIO m)
  => R.DirRule
  -> (Lock -> m ())  -- ^ Monadic lock handler
  -> m ()
_locksFor rule handler = do
  Un.runMatchT $ do
    dummyMatch $ R.mainAnte rule
    case R.otherAntes rule of
      [other] -> do
        lock <- mkLock other
        Un.lift $ handler lock
      _ -> error "locksFor: doesn't handle non-binary rules"


-- | Retrieve the values of the global variables in the lock, thus creating the
-- key corresponding to the lock based on the current environment.
keyValFor :: (P.MonadIO m) => Key -> MatchT m KeyVal
keyValFor vars = do
  let ps = S.toList vars
  fmap M.fromList . forM ps $ \p -> do
--     P.liftIO $ do
--       putStr ">>> Closing "
--       print p
    it <- Un.close p
--     P.liftIO $ do
--       putStr ">>> Closed "
--       print p
--       putStr ">>> With "
--       print it
    return (p, it)


--------------------------------------------------
-- Directional rule with index information
--------------------------------------------------


-- | Index-related information
data IndexInfo = IndexInfo
  { indexTemp :: Template
    -- ^ Index template
  , indexKeys :: S.Set Key
    -- ^ Index keys
  } deriving (Show, Eq, Ord)


-- | Directional rule with index information assigned to other antecedents
data DirRule = DirRule
  { mainAnte :: Pattern
    -- ^ The main antecedent pattern
  , otherAntes :: [(Pattern, IndexInfo)]
    -- ^ The other antecedent patterns
  , dirConseq :: Pattern
    -- ^ The rule's consequent
  } deriving (Show, Eq, Ord)


-- | Add index information to a directional rule.
addIndexInfo :: (P.MonadIO m) => R.DirRule -> m DirRule
addIndexInfo rule = do
  -- TODO: locksFor also handles binary rules only
  locks <- P.toListM (P.enumerate $ locksFor rule)
  let temp = getGroupTemplate locks
      keys = S.fromList [lockKey lock | lock <- locks]
      info = IndexInfo temp keys
  return $ DirRule
    { mainAnte = R.mainAnte rule
    , otherAntes = case R.otherAntes rule of
        [other] -> [(other, info)]
        _ -> error "addIndexInfo: doesn't handle non-binary rules"
    , dirConseq = R.dirConseq rule
    }


-- | Retrieve the template from the group of locks with the same template.
getGroupTemplate :: [Lock] -> Template
getGroupTemplate xs =
  case S.toList (S.fromList $ map lockTemplate xs) of
    [temp] -> temp
    _ -> error "getGroupTemplate: unexpected number of templates"


-- -- | Add index information to a directional rule.
-- rmIndexInfo :: DirRule -> R.DirRule
-- rmIndexInfo DirRule{..} = R.DirRule
--   { R.mainAnte = mainAnte
--   , R.otherAntes = map fst otherAntes
--   , R.dirConseq = dirConseq
--   }


--------------------------------------------------
-- Directional rule with index information (BIS)
--------------------------------------------------


-- -- | Index-related information
-- data IndexInfo = IndexInfo
--   { indexTemp :: Template
--     -- ^ Index template
--   , indexKeys :: S.Set Key
--     -- ^ Index keys
--   } deriving (Show, Eq, Ord)


-- -- | Directional rule with index information assigned to other antecedents
-- data DirRule' = DirRule'
--   { mainAnte' :: Pattern
--     -- ^ The main antecedent pattern
--   , otherTemp :: Template
--     -- ^ Index template for the other pattern
--   , otherAnte :: M.Map Key Pattern
--     -- ^ The other antecedent pattern, one per index key
--   , dirConseq' :: Pattern
--     -- ^ The rule's consequent
--   } deriving (Show, Eq, Ord)


-- -- | Add index information to a directional rule.
-- addIndexInfo' :: (P.MonadIO m) => R.DirRule -> m DirRule'
-- addIndexInfo' rule = do
--   locks <- P.toListM (P.enumerate $ locksFor rule)
--   let keys = [lockKey lock | lock <- locks]
--   return $ DirRule'
--     { mainAnte' = R.mainAnte rule
--     , otherTemp = getGroupTemplate locks
--     , otherAnte = case R.otherAntes rule of
--         -- TODO: simplify the `other`!
--         [other] -> M.fromList [(key, other) | key <- keys]
--         _ -> error "addIndexInfo': doesn't handle non-binary rules"
--     , dirConseq' = R.dirConseq rule
--     }


--------------------------------------------------
-- Rule's application
--------------------------------------------------


-- | Index structure
type Index = M.Map Key (M.Map KeyVal (S.Set Un.Rigit))


-- | Apply directional rule.
applyDirRule
  :: (P.MonadIO m)
  => T.Text         -- ^ Rule's name
  -> (Template -> m Index)
                    -- ^ Function which retrieves the index
                    -- for a given template
  -> DirRule
  -> Un.Rigit
  -> Un.MatchT m Un.Rigit
applyDirRule ruleName getIndex rule mainItem = do
--   liftIO $ do
--     T.putStr "@@@ Matching: "
--     T.putStrLn ruleName
-- --     T.putStr "@@@ Other Ante: "
-- --     print $ Un.otherAntes rule !! 0
--     -- print $ Un.mainAnte rule
--     -- print mainItem
  Un.match Un.Strict (mainAnte rule) mainItem
  case otherAntes rule of
    [(otherPatt, otherInfo)] -> do
--       lock <- mkLock otherPatt
--       let template = lockTemplate lock
--           key = lockKey lock
      let template = indexTemp otherInfo
      key <- each . S.toList $ indexKeys otherInfo
--       liftIO $ do
--         T.putStr "@@@ Template: "
--         print template
--         T.putStr "@@@ Key: "
--         print key
      index <- Un.lift $ getIndex template
      -- index <- Un.lift $ retrieveIndex template
      let valItemMap = maybe M.empty id $ M.lookup key index
--       liftIO $ do
--         T.putStr "@@@ Index: "
--         print valItemMap
      keyVal <- keyValFor key
--       liftIO $ do
--         T.putStr "@@@ Val: "
--         print keyVal
      let otherItems = do
            maybe [] S.toList $ M.lookup keyVal valItemMap
      Un.forEach otherItems $ \otherItem -> do
--         liftIO $ do
--           T.putStr "@@@ Other: "
--           print otherItem
        Un.match Un.Strict otherPatt otherItem
--         liftIO $ do
--           T.putStr "@@@ Closing: "
--           print (Un.dirConseq rule)
        result <- Un.close (dirConseq rule)
        -- We managed to apply a rule!
--         liftIO $ do
--           T.putStr "@@@ "
--           T.putStr ruleName
--           T.putStr ": "
--           putStr $ show [mainItem, otherItem]
--           T.putStr " => "
--           print result
        -- Return the result
        return result
    _ -> error "applyRule: doesn't handle non-binary rules"

  where

    -- For each element in the list
    each = P.Select . P.each


-- -- | Apply directional rule.
-- applyDirRule'
--   :: (P.MonadIO m)
--   => T.Text         -- ^ Rule's name
--   -> (Template -> m Index)
--                     -- ^ Function which retrieves the index
--                     -- for a given template
--   -> DirRule'
--   -> Un.Rigit
--   -> Un.MatchT m Un.Rigit
-- applyDirRule' ruleName getIndex rule mainItem = do
-- --   liftIO $ do
-- --     T.putStr "@@@ Matching: "
-- --     T.putStrLn ruleName
-- -- --     T.putStr "@@@ Other Ante: "
-- -- --     print $ Un.otherAntes rule !! 0
-- --     -- print $ Un.mainAnte rule
-- --     -- print mainItem
--   Un.match Un.Strict (mainAnte' rule) mainItem
--   let template = otherTemp rule
-- --   liftIO $ do
-- --     T.putStr "@@@ Template: "
-- --     print template
-- --     T.putStr "@@@ Key: "
-- --     print key
--   index <- Un.lift $ getIndex template
--   (key, otherPatt) <- each . M.toList $ otherAnte rule
--   let valItemMap = maybe M.empty id $ M.lookup key index
-- --   liftIO $ do
-- --     T.putStr "@@@ Index: "
-- --     print valItemMap
--   keyVal <- keyValFor key
-- --   liftIO $ do
-- --     T.putStr "@@@ Val: "
-- --     print keyVal
--   let otherItems = do
--         maybe [] S.toList $ M.lookup keyVal valItemMap
--   Un.forEach otherItems $ \otherItem -> do
-- --     liftIO $ do
-- --       T.putStr "@@@ Other: "
-- --       print otherItem
--     Un.match Un.Strict otherPatt otherItem
-- --     liftIO $ do
-- --       T.putStr "@@@ Closing: "
-- --       print (Un.dirConseq rule)
--     result <- Un.close (dirConseq' rule)
--     -- We managed to apply a rule!
-- --     liftIO $ do
-- --       T.putStr "@@@ "
-- --       T.putStr ruleName
-- --       T.putStr ": "
-- --       putStr $ show [mainItem, otherItem]
-- --       T.putStr " => "
-- --       print result
--     -- Return the result
--     return result
--
--   where
--
--     -- For each element in the list
--     each = P.Select . P.each