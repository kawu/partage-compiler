{-# LANGUAGE RecordWildCards #-}


-- | Deduction rule


module ParComp.Pattern.RuleBis
  ( Rule (..)
  , apply
  ) where


import           Control.Monad (guard)

import qualified Pipes as P

import           ParComp.Item (Item (..))
import qualified ParComp.Pattern.UntypedBis as Un
import           ParComp.Pattern.UntypedBis (MatchT, Patt, Cond)


--------------------------------------------------
-- Deduction rule
--------------------------------------------------


-- | Single deduction rule
data Rule = Rule
  { antecedents :: [Patt]
    -- ^ The list of rule's antecedents
  , consequent :: Patt
    -- ^ The rule's consequent
  , condition :: Cond Patt
    -- ^ The rule's side condition
  } deriving (Show, Eq, Ord)


-- | Apply a deduction rule to a given list of items.  If the application
-- succeeds, the new chart item is returned.
--
-- The function treats the list of items as ordered and does not try other item
-- permutations when matching them with the `antecedents`.
apply :: (P.MonadIO m) => Rule -> [Item] -> MatchT m Item
apply Rule{..} items = do
  guard $ length antecedents == length items
  -- Match antecedents with the corresponding items
  mapM_
    (uncurry Un.match)
    (zip antecedents items)
  -- Make sure the side condition holds
  Un.check condition
  -- Convert the consequent to the resulting item
  Un.close consequent
