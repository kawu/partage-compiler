{-# LANGUAGE OverloadedStrings #-}


-- | General purpuse utility patterns


module ParComp.Pattern.Util
  (
  -- * Lists
    append
  , cons
  , splitOn
  ) where


import           Prelude
import qualified Prelude as P

import qualified ParComp.Pattern.Untyped as U
import           ParComp.Pattern.Untyped (IsItem(..), Fun(..))
import qualified ParComp.Pattern.Typed as Ty
import           ParComp.Pattern.Typed (Patt(..))


--------------------------------------------------
-- General
--------------------------------------------------


-- -- | Constant
-- constF :: (IsItem a, IsItem b, Patt repr) => a -> repr (b -> a)
-- constF x = fun $ Fun "Util.constF" $ P.const [x]


--------------------------------------------------
-- Lists
--------------------------------------------------


-- | Append two lists.
append :: (IsItem a, Patt repr) => repr (([a], [a]) -> [a])
append = fun $ Fun "Util.append" $ \(xs, ys) -> pure (xs ++ ys)
{-# INLINE append #-}


-- | Cons an element at the beginning of a list.
cons :: (IsItem a, Patt repr) => repr ((a, [a]) -> [a])
cons = fun $ Fun "Util.cons" $ \(x, xs) -> pure (x:xs)
{-# INLINE cons #-}


-- | Split a list at a at a given value.
splitOn :: (IsItem a, Eq a, Patt repr) => repr ((a, [a]) -> ([a], [a]))
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
