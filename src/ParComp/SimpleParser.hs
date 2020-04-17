{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}


-- | Simple, non-efficient parsing with deduction rules


module ParComp.SimpleParser
  ( chartParse
  ) where


import           Control.Monad (forM_)
import qualified Control.Monad.State.Strict as ST

import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import qualified ParComp.Item as I
import qualified ParComp.Pattern as P
import           ParComp.Pattern (Pattern(..))


-- | State of the parser
data State sym = State
  { agenda :: S.Set (I.Item sym)
  , chart :: S.Set (I.Item sym)
  } deriving (Show, Eq, Ord)


-- | Empty state
emptyState :: State sym
emptyState = State S.empty S.empty


-- | Remove an item from agenda
popFromAgenda :: (Monad m) => ST.StateT (State sym) m (Maybe (I.Item sym))
popFromAgenda = do
  st@State{..} <- ST.get
  case S.minView agenda of
    Nothing -> return Nothing
    Just (x, agenda') -> do
      ST.put $ st {agenda = agenda'}
      return (Just x)


-- | Remove an item from agenda
addToAgenda :: (Monad m, Ord sym) => I.Item sym -> ST.StateT (State sym) m ()
addToAgenda x = do
  ST.modify' $ \st -> st
    { agenda = S.insert x (agenda st) }


-- | Remove an item from agenda
addToChart :: (Monad m, Ord sym) => I.Item sym -> ST.StateT (State sym) m ()
addToChart x = do
  ST.modify' $ \st -> st
    { chart = S.insert x (chart st) }


-- | Retrieve the chart subsets of the given length
chartSubsets :: (Monad m) => Int -> ST.StateT (State sym) m [[I.Item sym]]
chartSubsets k = do
  ch <- ST.gets chart
  return $ subsets k (S.toList ch)


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
    mapM_ addToAgenda (S.toList baseItems)
    processAgenda

  where

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
              ST.lift . ST.lift $ addToAgenda result
              -- We managed to apply a rule!
--               ST.liftIO $ do
--                 T.putStr "# "
--                 T.putStr ruleName
--                 T.putStr ": "
--                 putStr $ show items'
--                 T.putStr " => "
--                 print result
