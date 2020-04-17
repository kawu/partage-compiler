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
import           Control.Applicative (Alternative, (<|>), empty)

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


-- | @choice ps@ tries to apply the actions in the list @ps@ in order, until
-- one of them succeeds. Returns the value of the succeeding action.
choice :: Alternative f => [f a] -> f a
choice = foldr (<|>) empty


-- | Return subsets of the given size
subsets :: Int -> [a] -> [[a]]
subsets 0 _ = [[]]
subsets k xs = do
  (x, rest) <- pickOne xs
  subset <- subsets (k - 1) rest
  return $ x : subset


-- | All possible ways of picking one element from the (non-empty) list
pickOne :: [a] -> [(a, [a])]
-- pickOne [x] = [(x, [])]
pickOne [] = []
pickOne (x:xs) = 
  here : there
  where
    here = (x, xs)
    there = do
      (y, ys) <- pickOne xs
      return (y, x:ys)


-- | All possible ways of injecting the given item among the list of items
inject :: a -> [a] -> [[a]]
inject x [] = [[x]]
inject x (x' : xs) =
  here : there
  where
    here = x : x' : xs
    there = do
      xs' <- inject x xs
      return $ x' : xs'


--------------------------------------------------
-- State (chart, agenda, indexes)
--------------------------------------------------


-- | Index is a map from keys (see `P.bindAllTODO`) to sets of items.
type Index sym var = M.Map
  (P.Key sym var)
  (S.Set (I.Item sym))


-- | State of the parser
data State sym var = State
  { _agenda :: S.Set (I.Item sym)
  , _chart :: S.Set (I.Item sym)
  , _indexMap :: M.Map (P.Lock sym var) (Index sym var)
  } deriving (Show, Eq, Ord)
$( makeLenses [''State] )


-- | Chart parsing monad transformer
type ChartT sym var m = ST.StateT (State sym var) m


-- | Empty state
--
-- TODO: The set of index locks should be established initially and fixed
-- throughout the entire parsing process.  Also, `registerIndex` should not be
-- available.
--
emptyState :: State sym var
emptyState = State S.empty S.empty M.empty


-- | Remove an item from agenda
popFromAgenda :: (Monad m) => ChartT sym var m (Maybe (I.Item sym))
popFromAgenda = do
  st <- ST.get
  case S.minView (getL agenda st) of
    Nothing -> return Nothing
    Just (x, agenda') -> do
      ST.put $ setL agenda agenda' st
      return (Just x)


-- | Remove an item from agenda.
addToAgenda :: (Monad m, Ord sym) => I.Item sym -> ChartT sym var m ()
addToAgenda x = do
  state <- ST.get
  let ag = getL agenda state
      ch = getL chart state
  unless (S.member x ag || S.member x ch) $ do
    ST.modify' $ setL agenda (S.insert x ag)


-- | Add an item to a chart (also put it in the corresponding indexing
-- structures).
addToChart
  :: (MonadIO m, Ord sym, Ord var, Show sym, Show var)
  => P.FunSet sym
    -- ^ Set of registered functions
  -> I.Item sym
  -> ChartT sym var m ()
addToChart funSet x = do
--   ST.liftIO $ do
--     T.putStr ">>> Item: "
--     print x
  ST.modify' $ modL' chart (S.insert x)
  locks <- ST.gets $ M.keys . getL indexMap
  forM_ locks $ \lock -> do
--     ST.liftIO $ do
--       T.putStr ">>> Lock: "
--       print lock
    P.runMatchT funSet $ do
      key <- P.itemKeyFor x lock
--       ST.liftIO $ do
--         T.putStr ">>> Key: "
--         print key
      P.lift $ saveKey lock key x


-- | Retrieve the chart subsets of the given length
chartSubsets :: (Monad m) => Int -> ChartT sym var m [[I.Item sym]]
chartSubsets k = do
  ch <- ST.gets $ getL chart
  return $ subsets k (S.toList ch)


-- | Register an index with the given lock.
registerLock
  :: (Monad m, Ord sym, Ord var)
  => P.Lock sym var
  -> ChartT sym var m ()
registerLock lock =
  ST.modify' $ modL' indexMap (M.insert lock M.empty)


-- | Save key for the given lock, together with the corresponding item.
saveKey
  :: (Monad m, Ord sym, Ord var)
  => P.Lock sym var
  -> P.Key sym var
  -> I.Item sym
  -> ChartT sym var m ()
saveKey lock key item = ST.modify'
  . modL' indexMap
  $ M.insertWith
      (M.unionWith S.union)
      lock
      (M.singleton key (S.singleton item))


-- | Retrieve the index with the given lock.
retrieveIndex
  :: (Monad m, Ord sym, Ord var)
  => P.Lock sym var
  -> ChartT sym var m (Index sym var)
retrieveIndex lock =
  ST.gets $ maybe M.empty id . M.lookup lock . getL indexMap


--------------------------------------------------
-- Indexing
--------------------------------------------------


-- | Generate all the locks for the given rule.
--
-- TODO: Should be performed in a fresh environment?
--
locksFor
  :: (Monad m, Eq sym, Ord var)
  => P.Rule sym var
  -> P.MatchT sym var m (P.Lock sym var)
locksFor rule = P.withLocalEnv $ do
  (main, rest) <- each $ pickOne (P.antecedents rule)
  P.dummyMatch main
  case rest of
    [other] -> P.mkLock other
    _ -> error "locksFor: doesn't handle non-binary rules"
  where
    each = Pipes.Select . Pipes.each


-- | Perform the matching computation for each element in the list.  Start each
-- matching from a fresh state.
forEach
  :: (Monad m)
  => [a]
  -> (a -> P.MatchT sym var m b)
  -> P.MatchT sym var m b
forEach xs m = do
  state <- ST.get
  choice $ do
    x <- xs
    return $ do
      ST.put state
      m x


-- | Apply rule.
applyRule
  :: (MonadIO m, Show sym, Show var, Ord sym, Ord var)
  => T.Text
  -> P.Rule sym var
  -> I.Item sym
  -> P.MatchT sym var (ChartT sym var m) (I.Item sym)
applyRule ruleName rule mainItem = do
  -- For each split into the main pattern and the remaining patterns
  forEach (pickOne $ P.antecedents rule) $ \(mainPatt, restPatt) -> do
    P.match mainPatt mainItem
    case restPatt of
      [otherPatt] -> do
        lock <- P.mkLock otherPatt
--         ST.liftIO $ do
--           T.putStr "@@@ Lock: "
--           print lock
        index <- P.lift $ retrieveIndex lock
--         ST.liftIO $ do
--           T.putStr "@@@ Index: "
--           print index
        key <- P.keyFor lock
--         ST.liftIO $ do
--           T.putStr "@@@ Key: "
--           print key
        let otherItems =
              maybe [] S.toList $ M.lookup key index
        forEach otherItems $ \otherItem -> do
--           ST.liftIO $ do
--             T.putStr "@@@ Other: "
--             print otherItem
          P.match otherPatt otherItem
--           ST.liftIO $ do
--             T.putStrLn "@@@ Matched with Other"
          P.check (P.condition rule) >>= guard
--           ST.liftIO $ do
--             T.putStrLn "@@@ Conditions checked"
          result <- P.close (P.consequent rule)
          -- We managed to apply a rule!
--           ST.liftIO $ do
--             T.putStr "@@@ "
--             T.putStr ruleName
--             T.putStr ": "
--             putStr $ show [mainItem, otherItem]
--             T.putStr " => "
--             print result
          -- Return the result
          return result
      _ -> error "applyRule: doesn't handle non-binary rules"

    -- each = Pipes.Select . Pipes.each


--------------------------------------------------
-- Parsing
--------------------------------------------------


-- | Perform chart parsing with the given grammar and deduction rules.
chartParse
  :: (Show sym, Show var, Ord sym, Ord var)
  => P.FunSet sym
    -- ^ Set of registered functions
  -> S.Set (I.Item sym)
    -- ^ Axiom-generated items
  -> M.Map T.Text (P.Rule sym var)
    -- ^ Deduction rules (named)
  -> (I.Item sym -> Bool)
    -- ^ Is the item final?
  -> IO (Maybe (I.Item sym))
chartParse funSet baseItems ruleMap isFinal =

  flip ST.evalStateT emptyState $ do
    -- Register all the locks
    P.runMatchT funSet $ do
      rule <- each $ M.elems ruleMap
--       ST.liftIO $ do
--         T.putStr "# Rule: "
--         print rule
      lock <- locksFor rule
--       ST.liftIO $ do
--         T.putStr "# Lock: "
--         print lock
      P.lift $ registerLock lock

    -- Put all base items to agenda
    mapM_ addToAgenda (S.toList baseItems)

    -- Process the agenda
    processAgenda

  where

    each = Pipes.Select . Pipes.each

    -- Process agenda until empty, or until final item found
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
--       ST.liftIO $ do
--         T.putStr "### Popped: "
--         print item
      -- For each deduction rule
      forM_ (M.toList ruleMap) $ \(ruleName, rule) -> do
--         ST.liftIO $ do
--           T.putStr "# Rule: "
--           T.putStrLn ruleName
        P.runMatchT funSet $ do
          result <- applyRule ruleName rule item
          P.lift $ addToAgenda result
