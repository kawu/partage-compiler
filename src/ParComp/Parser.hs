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

import           Data.Maybe (maybeToList, fromJust)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Map.Strict as Map
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S

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
  { _agenda :: S.HashSet U.Rigit
  , _chart :: S.HashSet U.Rigit
  , _indexMap :: M.HashMap I.Template I.Index
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
--   case S.minView (getL agenda st) of
--     Nothing -> return Nothing
--     Just (x, agenda') -> do
--       ST.put $ setL agenda agenda' st
--       return (Just x)
  let agendaBefore = getL agenda st
  case S.toList agendaBefore of
    x : _ -> do
      let agendaAfter = S.delete x agendaBefore
      ST.put $ setL agenda agendaAfter st
      return (Just x)
    [] -> return Nothing


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
--       -- For each key
--       let onKey index' key = do
--             -- Determine the value of the key
--             val <- I.keyValFor key
-- --             liftIO $ do
-- --               T.putStr ">>> Lock: "
-- --               print $ I.Lock template key
-- --               T.putStr ">>> KeyVal: "
-- --               print val
--             return $ M.insertWith
--               (M.unionWith S.union)
--               key
--               (M.singleton val (S.singleton x))
--               index'
--       index' <- U.foldEach onKey index (M.keys index)
--       -- Update the index
--       U.lift $ updateIndex template index'


-- | Register an index with the given lock.
registerLock :: (Monad m) => I.Lock -> ChartT m ()
registerLock lock = do
  let temp = I.lockTemplate lock
      key = I.lockKey lock
  ST.modify'
    . modL' indexMap
    $ M.insertWith
        M.union
        -- (M.unionWith (M.unionWith S.union))
        temp
        (M.singleton key M.empty)


-- | Update the index.
updateIndex
  :: (Monad m)
  => I.Template
  -> I.Index    -- ^ New index fragment
  -> ChartT m ()
updateIndex temp index = ST.modify'
  . modL' indexMap
  $ M.insertWith
      (M.unionWith (M.unionWith S.union))
      temp
      index -- (M.singleton key (M.singleton val (S.singleton item)))


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
  $ M.insertWith
      (M.unionWith (M.unionWith S.union))
      temp
      (M.singleton key (M.singleton val (S.singleton item)))


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
  -> Map.Map T.Text (Ty.Rule a)
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
      lock <- I.locksFor rule
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
      (name, typedRule) <- Map.toList ruleMap
      let rule = Ty.compileRule typedRule
      (k, dirRule) <- zip [1..] $ R.directRule rule
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
          result <- I.applyDirRule ruleName retrieveIndex rule item
          U.lift $ addToAgenda result

    -- For each element in the list
    each = Pipes.Select . Pipes.each
