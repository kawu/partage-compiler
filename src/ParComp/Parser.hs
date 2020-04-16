{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}


-- | Parsing with deduction rules and indexing structures


module ParComp.Parser
  ( chartParse
  ) where


import           Control.Monad (forM_)
import qualified Control.Monad.State.Strict as ST

import qualified Pipes as Pipes

import           Data.Lens.Light

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
addToAgenda x = ST.modify' $ modL' agenda (S.insert x)


-- | Add an item to a chart (also put it in the corresponding indexing
-- structures).
addToChart :: (Monad m, Ord sym) => I.Item sym -> ChartT sym var m ()
addToChart x = do
  ST.modify' $ modL' chart (S.insert x)
  -- TODO: put the item in the corresponding indexing structures


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


--------------------------------------------------
-- Indexing
--------------------------------------------------


-- | Generate all the locks for the given rule.
--
-- TODO: Should be performed in an empty environment?
--
locksFor
  -- TODO: trim down the list of class requirements
  :: (Monad m, Show sym, Show var, Eq sym, Ord var)
  => P.Rule sym var
  -> P.MatchT sym var m (P.Lock sym var)
locksFor rule = do
  (main, rest) <- each $ pickOne (P.antecedents rule)
  P.dummyMatch main
  case rest of
    [other] -> P.mkLock other
    _ -> error "locksFor: doesn't handle non-binary rules yet"
  where
    each = Pipes.Select . Pipes.each


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
      ST.liftIO $ do
        T.putStr "# Rule: "
        print rule
      lock <- locksFor rule
      ST.liftIO $ do
        T.putStr "# Lock: "
        print lock
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
            addToChart item
            return $ Just item
          else do
            handleItem item
            addToChart item
            processAgenda

    -- Try to match the given item with other items already in the chart
    handleItem item = do
--       ST.liftIO $ do
--         T.putStr "# Poped: "
--         print item
      -- For each deduction rule
      forM_ (M.toList ruleMap) $ \(ruleName, rule) -> do
--         ST.liftIO $ do
--           T.putStr "# Rule: "
--           T.putStrLn ruleName
        -- For each chart subset
        subs <- chartSubsets $ length (P.antecedents rule) - 1
--         ST.liftIO $ do
--           T.putStr "# Subset: "
--           print subs
        forM_ subs $ \items -> do
          -- For each possibly way of injecting the current item among
          -- the items in the subset
          forM_ (inject item items) $ \items' -> do
--             ST.liftIO $ do
--               T.putStr "# Matching: "
--               print items'
            P.runMatchT funSet $ do
              result <- P.apply rule items'
              P.lift $ addToAgenda result
              -- We managed to apply a rule!
--               ST.liftIO $ do
--                 T.putStr "# "
--                 T.putStr ruleName
--                 T.putStr ": "
--                 putStr $ show items'
--                 T.putStr " => "
--                 print result
