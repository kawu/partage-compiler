-- | Utility functions for the examples


module ParComp.Examples.Utils
  ( append
  , splitAt
  , suffix
  , (.:)
  ) where


import           Prelude hiding (splitAt)

import           ParComp.Patt


-- | Append two lists
append :: Ty PattFun ([a] -> [a] -> [a])
append = withVars $ \xs ys hd tl ->
  arg xs . arg ys . fun $
    (match xs nil `seqp` ys) `choice`
    (
      (cons hd tl `match` xs) `seqp`
      (cons hd (apply append tl ys))
    )


-- | Match a suffix of a given list.  Higher-order, recursive pattern.
suffix :: Ty Patt [a] -> Ty Patt [a]
suffix p = fix $ p `choice` cons anyp rec


-- | Split a list at a given element.
splitAt :: Ty PattFun (a -> [a] -> ([a], [a]))
splitAt = withVars $ \at xs hd tl ls rs ->
  arg at . arg xs . fun $
    ( match xs nil `seqp`
      pair nil nil
    ) `choice`
    ( match (hd .: tl) xs `seqp` (
      ( match hd at `seqp`
        pair nil xs
      ) `choice`
      ( match (pair ls rs) (apply splitAt at tl) `seqp`
        pair (hd .: ls) rs
      )
    ))


-- | Operator synonym to `cons`
(.:) :: Ty Patt a -> Ty Patt [a] -> Ty Patt [a]
(.:) = cons
infixr 5 .:
