{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}


-- | Parsing with deduction rules and indexing structures


module ParComp.Parser
  ( chartParse
  ) where


-- import qualified Prelude as P

import           Control.Monad (forM_, guard, unless)
import qualified Control.Monad.State.Strict as ST
import           Control.Monad.State.Strict (lift, liftIO)

import qualified Pipes as Pipes
import           Pipes (MonadIO)

import           Data.Lens.Light

import           Data.Maybe (maybeToList)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import qualified ParComp.ItemDev.Untyped as U
import qualified ParComp.ItemDev.Typed as Ty
import           ParComp.ItemDev.Typed (Pattern(..), Op(..))


--------------------------------------------------
-- State (chart, agenda, indexes)
--------------------------------------------------


-- | Index is a map from `Key`s to sets of items.  Each `Key` is defined within
-- the context of the corresponding `Lock` (see `_indexMap` below).
type Index = M.Map U.Key (S.Set U.Rigit)


-- | State of the parser
data State = State
  { _agenda :: S.Set U.Rigit
  , _chart :: S.Set U.Rigit
  , _indexMap :: M.Map U.Lock Index
  } deriving (Show, Eq, Ord)
$( makeLenses [''State] )


-- | Chart parsing monad transformer
type ChartT m = ST.StateT State m


-- | Empty state
--
-- TODO: The set of index locks should be established initially and fixed
-- throughout the entire parsing process.  Also, `registerIndex` should not be
-- available.
emptyState :: State
emptyState = State S.empty S.empty M.empty


-- | Remove an item from agenda
popFromAgenda :: (Monad m) => ChartT m (Maybe U.Rigit)
popFromAgenda = do
  st <- ST.get
  case S.minView (getL agenda st) of
    Nothing -> return Nothing
    Just (x, agenda') -> do
      ST.put $ setL agenda agenda' st
      return (Just x)


-- | Remove an item from agenda.
addToAgenda :: (Monad m) => U.Rigit -> ChartT m ()
addToAgenda x = do
  state <- ST.get
  let ag = getL agenda state
      ch = getL chart state
  unless (S.member x ag || S.member x ch) $ do
    ST.modify' $ setL agenda (S.insert x ag)


-- | Add an item to a chart (also put it in the corresponding indexing
-- structures).
addToChart :: (MonadIO m) => U.Rigit -> ChartT m ()
addToChart x = do
--   liftIO $ do
--     T.putStr ">>> Item: "
--     print x
  ST.modify' $ modL' chart (S.insert x)
  locks <- ST.gets $ M.keys . getL indexMap
  forM_ (U.groupByTemplate locks) $ \lockGroup -> do
--     liftIO $ do
--       T.putStr ">>> Template: "
--       print . U.lockTemplate $ head lockGroup
    Pipes.runListT $ do
      (lock, key) <- U.itemKeyFor x lockGroup
--       liftIO $ do
--         T.putStr ">>> Lock: "
--         print lock
--         T.putStr ">>> Key: "
--         print key
      lift $ saveKey lock key x


-- | Register an index with the given lock.
registerLock :: (Monad m) => U.Lock -> ChartT m ()
registerLock lock =
  ST.modify' $ modL' indexMap (M.insert lock M.empty)


-- | Save key for the given lock, together with the corresponding item.
saveKey :: (Monad m) => U.Lock -> U.Key -> U.Rigit -> ChartT m ()
saveKey lock key item = ST.modify'
  . modL' indexMap
  $ M.insertWith
      (M.unionWith S.union)
      lock
      (M.singleton key (S.singleton item))


-- | Retrieve the index with the given lock.
retrieveIndex :: (Monad m) => U.Lock -> ChartT m Index
retrieveIndex lock =
  ST.gets $ maybe M.empty id . M.lookup lock . getL indexMap


--------------------------------------------------
-- Indexing
--------------------------------------------------


-- | Apply directional rule.
applyDirRule
  :: (MonadIO m)
  => T.Text
  -> U.DirRule
  -> U.Rigit
  -> U.MatchT (ChartT m) U.Rigit
applyDirRule ruleName rule mainItem = do
--   liftIO $ do
--     T.putStrLn "@@@ Matching"
--     print $ U.mainAnte rule
--     print mainItem
  U.match U.Strict (U.mainAnte rule) mainItem
  case U.otherAntes rule of
    [otherPatt] -> do
      lock <- U.mkLock otherPatt
--       liftIO $ do
--         T.putStr "@@@ Lock: "
--         print lock
      index <- U.lift $ retrieveIndex lock
--       liftIO $ do
--         T.putStr "@@@ Index: "
--         print index
      key <- U.keyFor $ U.lockVars lock
--       liftIO $ do
--         T.putStr "@@@ Key: "
--         print key
      let otherItems =
            maybe [] S.toList $ M.lookup key index
      U.forEach otherItems $ \otherItem -> do
--         liftIO $ do
--           T.putStr "@@@ Other: "
--           print otherItem
        U.match U.Strict otherPatt otherItem
--         liftIO $ do
--           T.putStrLn "@@@ Matched with Other"
--           T.putStr "@@@ Closing: "
--           print (U.dirConseq rule)
        result <- U.close (U.dirConseq rule)
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


--------------------------------------------------
-- Parsing
--------------------------------------------------


-- | Perform chart parsing with the given grammar and deduction rules.
chartParse
  :: (U.IsPatt a)
  => [a]
    -- ^ Axiom-generated items
  -> M.Map T.Text (Ty.Rule a)
    -- ^ Named deduction rules
  -> Ty.Pattern a
    -- ^ Pattern the final item should match
  -> IO (Maybe a)
chartParse baseItems ruleMap finalPatt =

  flip ST.evalStateT emptyState $ do

    -- Register all the locks
    Pipes.runListT $ do
      rule <- each $ M.elems dirRuleMap
--       liftIO $ do
--         T.putStr "### Rule: "
--         print rule
      lock <- U.locksFor rule
--       liftIO $ do
--         T.putStr "### Lock: "
--         print lock
      lift $ registerLock lock

    -- Put all base items to agenda
    mapM_ addToAgenda (fmap U.encodeI baseItems)

    -- Process the agenda
    processAgenda

  where

    -- Map of untyped directional rules
    dirRuleMap = M.fromList $ do
      (name, typedRule) <- M.toList ruleMap
      let rule = Ty.compileRule typedRule
      (k, dirRule) <- zip [1..] $ U.directRule rule
      return (name `T.append` T.pack (show k), dirRule)

    -- Process agenda until final item found (or until empty)
    processAgenda = do
      popFromAgenda >>= \case
        Nothing -> return Nothing
        Just item -> do
          final <- liftIO $ case finalPatt of
            Ty.Patt p -> U.isMatch p item
            _ -> error "final item pattern invalid" 
          -- final <- liftIO $ isFinal item
          if final
             then do
               addToChart item
               return . Just $ U.decodeI item
             else do
               handleItem item
               addToChart item
               processAgenda

    -- Try to match the given item with other items already in the chart
    handleItem item = do
--       liftIO $ do
--         T.putStr "### Popped: "
--         print item
      -- For each deduction rule
      forM_ (M.toList dirRuleMap) $ \(ruleName, rule) -> do
        U.runMatchT $ do
          result <- applyDirRule ruleName rule item
          U.lift $ addToAgenda result

    -- For each element in the list
    each = Pipes.Select . Pipes.each
