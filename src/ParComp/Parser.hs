{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}


-- | Parsing with deduction rules and indexing structures


module ParComp.Parser
  ( chartParse
  ) where


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

import qualified ParComp.Item as I
import qualified ParComp.Pattern as P
import           ParComp.Pattern (Pattern(..))


--------------------------------------------------
-- Utils
--------------------------------------------------


-- -- | All possible ways of injecting the given item among the list of items
-- inject :: a -> [a] -> [[a]]
-- inject x [] = [[x]]
-- inject x (x' : xs) =
--   here : there
--   where
--     here = x : x' : xs
--     there = do
--       xs' <- inject x xs
--       return $ x' : xs'


--------------------------------------------------
-- State (chart, agenda, indexes)
--------------------------------------------------


-- | Index is a map from `Key`s to sets of items.  Each `Key` is defined within
-- the context of the corresponding `Lock` (see `_indexMap` below).
type Index sym var lvar = M.Map
  (P.Key sym var lvar)
  (S.Set (I.Item sym))


-- | State of the parser
data State sym var lvar = State
  { _agenda :: S.Set (I.Item sym)
  , _chart :: S.Set (I.Item sym)
  , _indexMap :: M.Map (P.Lock sym var lvar) (Index sym var lvar)
  } deriving (Show, Eq, Ord)
$( makeLenses [''State] )


-- | Chart parsing monad transformer
type ChartT sym var lvar m = ST.StateT (State sym var lvar) m


-- | Empty state
--
-- TODO: The set of index locks should be established initially and fixed
-- throughout the entire parsing process.  Also, `registerIndex` should not be
-- available.
--
emptyState :: State sym var lvar
emptyState = State S.empty S.empty M.empty


-- | Remove an item from agenda
popFromAgenda :: (Monad m) => ChartT sym var lvar m (Maybe (I.Item sym))
popFromAgenda = do
  st <- ST.get
  case S.minView (getL agenda st) of
    Nothing -> return Nothing
    Just (x, agenda') -> do
      ST.put $ setL agenda agenda' st
      return (Just x)


-- | Remove an item from agenda.
addToAgenda :: (Monad m, Ord sym) => I.Item sym -> ChartT sym var lvar m ()
addToAgenda x = do
  state <- ST.get
  let ag = getL agenda state
      ch = getL chart state
  unless (S.member x ag || S.member x ch) $ do
    ST.modify' $ setL agenda (S.insert x ag)


-- | Add an item to a chart (also put it in the corresponding indexing
-- structures).
addToChart
  :: (MonadIO m, Show sym, Show var, Show lvar, Ord sym, Ord var, Ord lvar)
  => P.FunSet sym
    -- ^ Set of registered functions
  -> I.Item sym
  -> ChartT sym var lvar m ()
addToChart funSet x = do
--   liftIO $ do
--     T.putStr ">>> Item: "
--     print x
  ST.modify' $ modL' chart (S.insert x)
  locks <- ST.gets $ M.keys . getL indexMap
  forM_ locks $ \lock -> do
--     liftIO $ do
--       T.putStr ">>> Lock: "
--       print lock
    Pipes.runListT $ do
      key <- P.itemKeyFor funSet x lock
--       liftIO $ do
--         T.putStr ">>> Key: "
--         print key
      lift $ saveKey lock key x


-- | Register an index with the given lock.
registerLock
  :: (Monad m, Ord sym, Ord var, Ord lvar)
  => P.Lock sym var lvar
  -> ChartT sym var lvar m ()
registerLock lock =
  ST.modify' $ modL' indexMap (M.insert lock M.empty)


-- | Save key for the given lock, together with the corresponding item.
saveKey
  :: (Monad m, Ord sym, Ord var, Ord lvar)
  => P.Lock sym var lvar
  -> P.Key sym var lvar
  -> I.Item sym
  -> ChartT sym var lvar m ()
saveKey lock key item = ST.modify'
  . modL' indexMap
  $ M.insertWith
      (M.unionWith S.union)
      lock
      (M.singleton key (S.singleton item))


-- | Retrieve the index with the given lock.
retrieveIndex
  :: (Monad m, Ord sym, Ord var, Ord lvar)
  => P.Lock sym var lvar
  -> ChartT sym var lvar m (Index sym var lvar)
retrieveIndex lock =
  ST.gets $ maybe M.empty id . M.lookup lock . getL indexMap


--------------------------------------------------
-- Indexing
--------------------------------------------------


-- -- | Apply rule.
-- applyRule
--   :: (MonadIO m, Show sym, Show var, Show lvar, Ord sym, Ord var, Ord lvar)
--   => T.Text
--   -> P.Rule sym var lvar
--   -> I.Item sym
--   -> P.MatchT sym var lvar (ChartT sym var lvar m) (I.Item sym)
-- applyRule ruleName rule mainItem = do
--   -- For each split into the main pattern and the remaining patterns
--   P.forEach (P.pickOne $ P.antecedents rule) $ \(mainPatt, restPatt) -> do
--     P.match P.Strict mainPatt mainItem
--     case restPatt of
--       [otherPatt] -> do
--         lock <- P.mkLock otherPatt
--         liftIO $ do
--           T.putStr "@@@ Lock: "
--           print lock
--         index <- P.lift $ retrieveIndex lock
--         liftIO $ do
--           T.putStr "@@@ Index: "
--           print index
--         key <- P.keyFor lock
--         liftIO $ do
--           T.putStr "@@@ Key: "
--           print key
--         let otherItems =
--               maybe [] S.toList $ M.lookup key index
--         P.forEach otherItems $ \otherItem -> do
--           liftIO $ do
--             T.putStr "@@@ Other: "
--             print otherItem
--           P.match P.Strict otherPatt otherItem
--           liftIO $ do
--             T.putStrLn "@@@ Matched with Other"
--           P.check P.Strict (P.condition rule) >>= guard
--           liftIO $ do
--             T.putStrLn "@@@ Conditions checked"
--           result <- P.close (P.consequent rule)
--           -- We managed to apply a rule!
--           liftIO $ do
--             T.putStr "@@@ "
--             T.putStr ruleName
--             T.putStr ": "
--             putStr $ show [mainItem, otherItem]
--             T.putStr " => "
--             print result
--           -- Return the result
--           return result
--       _ -> error "applyRule: doesn't handle non-binary rules"
-- 
--     -- each = Pipes.Select . Pipes.each


-- | Apply directional rule.
applyDirRule
  :: (MonadIO m, Show sym, Show var, Show lvar, Ord sym, Ord var, Ord lvar)
  => T.Text
  -> P.DirRule sym var lvar
  -> I.Item sym
  -> P.MatchT sym var lvar (ChartT sym var lvar m) (I.Item sym)
applyDirRule ruleName rule mainItem = do
  P.match P.Strict (P.mainAnte rule) mainItem
  case P.otherAntes rule of
    [otherPatt] -> do
      lock <- P.mkLock otherPatt
--       liftIO $ do
--         T.putStr "@@@ Lock: "
--         print lock
      index <- P.lift $ retrieveIndex lock
--       liftIO $ do
--         T.putStr "@@@ Index: "
--         print index
      key <- P.keyFor lock
--       liftIO $ do
--         T.putStr "@@@ Key: "
--         print key
      let otherItems =
            maybe [] S.toList $ M.lookup key index
      P.forEach otherItems $ \otherItem -> do
--         liftIO $ do
--           T.putStr "@@@ Other: "
--           print otherItem
        P.match P.Strict otherPatt otherItem
--         liftIO $ do
--           T.putStrLn "@@@ Matched with Other"
        result <- P.close (P.dirConseq rule)
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
  :: (Show sym, Show var, Show lvar, Ord sym, Ord var, Ord lvar)
  => P.FunSet sym
    -- ^ Set of registered functions
  -> S.Set (I.Item sym)
    -- ^ Axiom-generated items
  -> M.Map T.Text (P.Rule sym var lvar)
    -- ^ Deduction rules (named)
  -> (I.Item sym -> Bool)
    -- ^ Is the item final?
  -> IO (Maybe (I.Item sym))
chartParse funSet baseItems ruleMap isFinal =

  flip ST.evalStateT emptyState $ do

    -- Register all the locks
    Pipes.runListT $ do
      rule <- each $ M.elems dirRuleMap
--       liftIO $ do
--         T.putStr "### Rule: "
--         print rule
      lock <- P.locksFor funSet rule
--       liftIO $ do
--         T.putStr "### Lock: "
--         print lock
      lift $ registerLock lock

    -- Put all base items to agenda
    mapM_ addToAgenda (S.toList baseItems)

    -- Process the agenda
    processAgenda

  where

    -- Map of directional rules
    dirRuleMap = M.fromList $ do
      (name, rule) <- M.toList ruleMap
      (k, dirRule) <- zip [1..] $ P.directRule rule
      return (name `T.append` T.pack (show k), dirRule)

    -- Process agenda until final item found (or until empty)
    processAgenda = do
      popFromAgenda >>= \case
        Nothing -> return Nothing
        Just item -> if isFinal item
          then do
            addToChart funSet item
            return $ Just item
          else do
            handleItem item
            addToChart funSet item
            processAgenda

    -- Try to match the given item with other items already in the chart
    handleItem item = do
--       liftIO $ do
--         T.putStr "### Popped: "
--         print item
      -- For each deduction rule
      forM_ (M.toList dirRuleMap) $ \(ruleName, rule) -> do
        P.runMatchT funSet $ do
          result <- applyDirRule ruleName rule item
          P.lift $ addToAgenda result

    -- For each element in the list
    each = Pipes.Select . Pipes.each
