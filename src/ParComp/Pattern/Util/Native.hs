{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}


-- | Native general purpuse utility patterns


module ParComp.Pattern.Util.Native
  (
  -- * General
    identity

  -- * Lists
  , append
  , splitAt
  ) where


import           Prelude hiding
  (map, or, and, any, splitAt)

import qualified ParComp.Pattern.Untyped as U
import           ParComp.Pattern.Untyped (IsItem(..), Fun(..))
import qualified ParComp.Pattern.Typed as Ty
import           ParComp.Pattern.Typed
  ( Patt(..), pair, nothing, just, nil, cons
  , left, right, bimap, guard
  )


--------------------------------------------------
-- General
--------------------------------------------------


-- | Identity pattern
identity :: (Patt repr) => repr (a -> a)
identity = letIn (local "x") (local "x") 


--------------------------------------------------
-- Lists
--------------------------------------------------


-- | Append the first list at the end of the second list.
appendEnd :: (Patt repr) => repr [a] -> repr ([a] -> [a])
appendEnd ys =
  fix $ p1 `or` p2
  where
    p1 = letIn nil ys
    p2 = letIn
      (local "x" `cons` via rec (local "xs"))
      (local "x" `cons` local "xs")


-- | Append two lists.
append :: (Patt repr) => repr [a] -> repr [a] -> repr [a]
append xs ys = map (appendEnd ys) xs


-- | Split a list @xs@ into two parts @(ys, zs)@ w.r.t pattern @p@ so that:
--
-- * @ys = removeSuffix p xs@
-- * @zs = suffix p xs@
--
-- TODO: this is probably not a true description in case the pattern is not
-- satisfied nowhere?
--
splitAt :: forall repr a. (Patt repr) => repr a -> repr ([a] -> ([a], [a]))
splitAt p =
  fix $ p1 `or` p2
  where
    p1 = letIn
      ((p `cons` any) `and` local "suff")
      (pair nil (local "suff"))
    p2 = letIn
      (local "x" `cons` via
        splitRec
        (pair (local "xs") (local "ys"))
      )
      (pair (local "x" `cons` local "xs") (local "ys"))

    -- NB: defining and annotating `splitRec` is optional, but it allows to
    -- verify that the types (of `fix` and `rec`) match.
    splitRec :: repr ([a] -> ([a], [a]))
    splitRec = rec
