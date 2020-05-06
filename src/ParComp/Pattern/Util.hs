{-# LANGUAGE OverloadedStrings #-}


-- | General purpuse utility patterns


module ParComp.Pattern.Util
  (
  -- * General
    identity

  -- * Fun-based
  -- ** Lists
  , append
  , cons
  , splitOn
  ) where


import qualified ParComp.Pattern.Untyped as U
import           ParComp.Pattern.Untyped (IsItem(..), Fun(..), Pred(..))
import qualified ParComp.Pattern.Typed as Ty
import           ParComp.Pattern.Typed (Op(..))


--------------------------------------------------
-- General
--------------------------------------------------


-- | Identity function.
identity :: (Op repr) => repr (a -> a)
identity = letIn (local "x") (local "x") 


--------------------------------------------------
-- Fun-based
--------------------------------------------------


-- | Append two lists.
append :: (IsItem a, Op repr) => repr (([a], [a]) -> [a])
append = fun $ Fun "Util.append" $ \(xs, ys) -> pure (xs ++ ys)
{-# INLINE append #-}


-- | Cons an element at the beginning of a list.
cons :: (IsItem a, Op repr) => repr ((a, [a]) -> [a])
cons = fun $ Fun "Util.cons" $ \(x, xs) -> pure (x:xs)
{-# INLINE cons #-}


-- | Split a list at a at a given value.
splitOn :: (IsItem a, Eq a, Op repr) => repr ((a, [a]) -> ([a], [a]))
splitOn =
  fun (Fun "Util.splitOn" $ uncurry _split)
  where
    _split x0 = go
      where
        go list@(x:xs)
          | x == x0 = return ([], list)
          | otherwise = do
              (pref, suff) <- go xs
              return (x:pref, suff)
        go [] = mempty
