{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}


-- | Parsing with deduction rules and indexing structures


module ParComp.Parser
  ( chartParse
  ) where


import           Prelude
import qualified Prelude as P

import           Control.Monad (forM_, guard, unless)
import qualified Control.Monad.State.Strict as ST
import           Control.Monad.State.Strict (lift, liftIO)

import qualified Pipes as Pipes
import           Pipes (MonadIO)

import           Data.Lens.Light

import           Data.Maybe (maybeToList, fromJust)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import qualified ParComp.Pattern.Untyped as U
import qualified ParComp.Pattern.Indexing as I
import qualified ParComp.Pattern.Rule as R
import qualified ParComp.Pattern.Typed as Ty
import           ParComp.Pattern.Typed (Pattern(..), Patt(..))


--------------------------------------------------
-- State (chart, agenda, indexes)
--------------------------------------------------


-- | State of the parser
data State = State
  { _agenda :: S.Set U.Rigit
  , _chart :: S.Set U.Rigit
  , _indexMap :: M.Map I.Template I.Index
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


-- | Add an item to a chart (also put it in the corresponding index
-- structures).
addToChart :: (MonadIO m) => U.Rigit -> ChartT m ()
addToChart x = do
--   liftIO $ do
--     T.putStr ">>> Item: "
--     print x
  ST.modify' $ modL' chart (S.insert x)
  -- For each index (template)
  tempIndex <- ST.gets $ getL indexMap
  forM_ (M.toList tempIndex) $ \(template, index) -> do
--     liftIO $ do
--       T.putStr ">>> Template: "
--       print template
    U.runMatchT $ do
      -- Match the item with the template
      U.match U.Lazy template x
      -- For each key
      U.forEach (M.keys index) $ \key -> do
        -- Determine the value of the key
        val <- I.keyValFor key
--         liftIO $ do
--           T.putStr ">>> Lock: "
--           print $ I.Lock template key
--           T.putStr ">>> KeyVal: "
--           print val
        -- Save the item in the index
        U.lift $ saveKeyVal template key val x


-- | Register an index with the given lock.
registerKeys :: (Monad m) => I.Template -> S.Set I.Key -> ChartT m ()
registerKeys temp keys = do
  let keyMap = M.fromAscList . fmap (, M.empty) $ S.toAscList keys
  ST.modify'
    . modL' indexMap
    $ M.insertWith
        -- M.union
        (M.unionWith (M.unionWith S.union))
        temp
        keyMap


-- | Save key for the given lock, together with the corresponding item.
saveKeyVal
  :: (Monad m)
  => I.Template
  -> I.Key
  -> I.KeyVal
  -> U.Rigit
  -> ChartT m ()
saveKeyVal temp key val item = ST.modify'
  . modL' indexMap
  $ M.insertWith merge temp
      (M.singleton key (M.singleton val (S.singleton item)))
  where
    merge x y = x `P.seq` y `P.seq` M.unionWith merge' x y
    merge' x y = x `P.seq` y `P.seq` M.unionWith S.union x y
    -- merge'' x y = x `P.seq` y `P.seq` S.union x y


-- | Retrieve the index with the given lock.
retrieveIndex :: (Monad m) => I.Template -> ChartT m I.Index
retrieveIndex template =
  ST.gets $ maybe M.empty id . M.lookup template . getL indexMap


--------------------------------------------------
-- Parsing
--------------------------------------------------


-- | Perform chart parsing with the given grammar and deduction rules.
chartParse
  :: (U.IsItem a)
  => [a]
    -- ^ Axiom-generated items
  -> M.Map T.Text (Ty.Rule a)
    -- ^ Named deduction rules
  -> Ty.Pattern a
    -- ^ Pattern the final item should match
  -> IO (Maybe a)
chartParse baseItems ruleMap finalPatt = do

  let addIndexInfo (n, r) = (n,) <$> I.addIndexInfo r
  dirRuleMap <- M.fromList <$>
    mapM addIndexInfo (M.toList dirRuleMapNoInfo)

  flip ST.evalStateT emptyState $ do

    -- Register all the locks
    Pipes.runListT $ do
      rule <- each $ M.elems dirRuleMap
--       liftIO $ do
--         T.putStr "### Rule: "
--         print rule
      (otherPatt, otherInfo) <- each $ I.otherAntes rule
      let temp = I.indexTemp otherInfo
          keys = I.indexKeys otherInfo
--       liftIO $ do
--         T.putStrLn "### Lock"
--         print temp
--         print keys
      lift $ registerKeys temp keys

    -- Retrieve the index map, otherwise benchmarks indicate a memory leak
    ixMap <- ST.gets $ getL indexMap

    -- Put all base items to agenda
    ixMap `P.seq` mapM_ addToAgenda (fmap U.encodeI baseItems)

    -- Process the agenda
    processAgenda dirRuleMap

  where

    -- Map of untyped directional rules with no index information
    dirRuleMapNoInfo = M.fromList $ do
      (name, typedRule) <- M.toList ruleMap
      let rule = Ty.compileRule typedRule
      (k, dirRule) <- zip [1..] $ R.directRule rule
      return (name `T.append` T.pack (show k), dirRule)

    -- Process agenda until final item found (or until empty)
    processAgenda dirRuleMap = do
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
               handleItem dirRuleMap item
               addToChart item
               processAgenda dirRuleMap

    -- Try to match the given item with other items already in the chart
    handleItem dirRuleMap item = do
--       liftIO $ do
--         T.putStr "### Popped: "
--         print item
      -- For each deduction rule
      forM_ (M.toList dirRuleMap) $ \(ruleName, rule) -> do
        U.runMatchT $ do
          result <- I.applyDirRule ruleName retrieveIndex rule item
          U.lift $ addToAgenda result

    -- For each element in the list
    each = Pipes.Select . Pipes.each
