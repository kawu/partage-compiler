{-# LANGUAGE RecordWildCards #-}


module ParComp.Pattern.Rule
  (
  -- * Rule
    Rule (..)
  , apply
  -- ** Directional rule
  , DirRule (..)
  , directRule
  ) where


import           Control.Monad (guard) -- , void, forM)

import qualified Pipes as P

import qualified ParComp.Pattern.Untyped as Un
import           ParComp.Pattern.Untyped
  ( Item(..), Var(..), Op(..)
  , Cond(..), Rigit(..)
  , MatchT
  , Pattern(..)
  )


--------------------------------------------------
-- Deduction rule
--------------------------------------------------


-- | Single deduction rule
data Rule = Rule
  { antecedents :: [Pattern]
    -- ^ The list of rule's antecedents
  , consequent :: Pattern
    -- ^ The rule's consequent
  , condition :: Cond Pattern
    -- ^ The rule's side condition
  } deriving (Show, Eq, Ord)


-- | Apply the deduction rule to the given items.  If the application succeeds,
-- the new chart item is returned.
--
-- The function treats the list of items as ordered and does not try other item
-- permutations when matching them with the `antecedents`.
apply :: (P.MonadIO m) => Rule -> [Rigit] -> MatchT m Rigit
apply Rule{..} items = do
  guard $ length antecedents == length items
  -- Match antecedents with the corresponding items
  mapM_
    (uncurry $ Un.match Un.Strict)
    (zip antecedents items)
  -- Make sure the side condition holds
  Un.checkStrict condition
  -- Convert the consequent to the resulting item
  Un.close consequent


--------------------------------------------------
-- Directional rule
--------------------------------------------------


-- | Directional rule
data DirRule = DirRule
  { mainAnte :: Pattern
    -- ^ The main antecedent pattern
  , otherAntes :: [Pattern]
    -- ^ The other antecedent patterns
  , dirConseq :: Pattern
    -- ^ The rule's consequent
  } deriving (Show, Eq, Ord)


-- | Compile the rule to the list of directional rules.
directRule :: Rule -> [DirRule]
directRule rule = do
  (main, rest) <- pickOne $ antecedents rule
  case rest of
    [other] -> return $ DirRule
      { mainAnte = main
      , otherAntes = [Un.withP other $ condition rule]
      , dirConseq = consequent rule
      }
    _ -> error "directRule: doesn't handle non-binary rules"


--------------------------------------------------
-- Utils
--------------------------------------------------


-- | All possible ways of picking one element from the (non-empty) list
pickOne :: [a] -> [(a, [a])]
pickOne [] = []
pickOne (x:xs) =
  here : there
  where
    here = (x, xs)
    there = do
      (y, ys) <- pickOne xs
      return (y, x:ys)
