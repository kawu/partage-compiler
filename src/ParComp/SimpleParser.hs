{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}


-- | Simple, non-efficient parsing with deduction rules


module ParComp.SimpleParser
  ( chartParse
  ) where


import           Control.Monad (forM_)
import qualified Control.Monad.State.Strict as ST
import           Control.Monad.State.Strict (liftIO)

import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import qualified ParComp.ItemDev.Untyped as U
import qualified ParComp.ItemDev.Typed as Ty
import           ParComp.ItemDev.Typed (Pattern(..), Op(..))


-- | State of the parser
data State = State
  { agenda :: S.Set U.Rigit
  , chart :: S.Set U.Rigit
  } deriving (Show, Eq, Ord)


-- | Empty state
emptyState :: State
emptyState = State S.empty S.empty


-- | Remove an item from agenda
popFromAgenda :: (Monad m) => ST.StateT State m (Maybe U.Rigit)
popFromAgenda = do
  st@State{..} <- ST.get
  case S.minView agenda of
    Nothing -> return Nothing
    Just (x, agenda') -> do
      ST.put $ st {agenda = agenda'}
      return (Just x)


-- | Remove an item from agenda
addToAgenda :: (Monad m) => U.Rigit -> ST.StateT State m ()
addToAgenda x = do
  ST.modify' $ \st -> st
    { agenda = S.insert x (agenda st) }


-- | Remove an item from agenda
addToChart :: (Monad m) => U.Rigit -> ST.StateT State m ()
addToChart x = do
  ST.modify' $ \st -> st
    { chart = S.insert x (chart st) }


-- | Retrieve the chart subsets of the given length
chartSubsets :: (Monad m) => Int -> ST.StateT State m [[U.Rigit]]
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
  :: (U.IsPatt a)
  => [a]
    -- ^ Axiom-generated items
  -> M.Map T.Text (Ty.Rule a)
    -- ^ Named deduction rules
  -> Ty.Pattern a
    -- ^ Pattern the final item should match
  -> IO (Maybe a)
chartParse baseItems tyRuleMap finalPatt =

  flip ST.evalStateT emptyState $ do 
    mapM_ addToAgenda (fmap U.encodeI baseItems)
    processAgenda

  where

    -- Untyped rules
    ruleMap = M.fromList $ do
      (name, typedRule) <- M.toList tyRuleMap
      return (name, Ty.compileRule typedRule)

    -- Process agenda until empty, or until final item found
    processAgenda = do
      popFromAgenda >>= \case
        Nothing -> return Nothing
        Just item -> do
          final <- liftIO $ case finalPatt of
            Ty.Patt p -> U.isMatch p item
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
--       ST.liftIO $ do
--         T.putStr "# Poped: "
--         print item
      -- For each deduction rule
      forM_ (M.toList ruleMap) $ \(ruleName, rule) -> do
--         ST.liftIO $ do
--           T.putStr "# Rule: "
--           T.putStrLn ruleName
        -- For each chart subset
        subs <- chartSubsets $ length (U.antecedents rule) - 1
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
            U.runMatchT $ do
              result <- U.apply rule items'
              U.lift $ addToAgenda result
              -- We managed to apply a rule!
--               ST.liftIO $ do
--                 T.putStr "# "
--                 T.putStr ruleName
--                 T.putStr ": "
--                 putStr $ show items'
--                 T.putStr " => "
--                 print result
