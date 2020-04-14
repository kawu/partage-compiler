{-# LANGUAGE OverloadedStrings #-}


-- | Pattern matching for items and deduction rules


module ParComp.Pattern
  ( Pattern (..)
  , Env
  , match
  , evalMatch
  -- , evalMatch'
  ) where


-- import           Prelude hiding (Integer, either)
import           Control.Monad (guard)
import           Control.Applicative (empty)
import           Control.Monad.Trans.Maybe (MaybeT(..))
import           Control.Monad.State.Strict as S

import qualified Data.Text as T
import qualified Data.Map.Strict as M

import qualified ParComp.Item as I


-- | Pattern expression
data Pattern sym var
  -- | > Constant: match the given item expression only
  = Const (I.Item sym)
  -- | > Pair: recursively match item pair
  | Pair (Pattern sym var) (Pattern sym var)
  -- | > Union: recursively match item union
  | Union (Either (Pattern sym var) (Pattern sym var))
  -- | > Variable: match any item expression and bind it to the given variable
  | Var var
  -- | > Any: match any item expression (wildcard)
  | Any
  deriving (Show, Eq, Ord)


-- | Variable binding environment
type Env sym var = M.Map var (I.Item sym)


-- | Pattern matching monad
type PatternM sym var = MaybeT (S.State (Env sym var)) ()


-- | Bind the item to the given variable.  If the variable is already bound,
-- make sure that the new item is equal to the old one.
bind :: (Eq sym, Ord var) => var -> I.Item sym -> PatternM sym var
bind v it = do
  mayIt <- lift $ S.gets (M.lookup v)
  case mayIt of
    Nothing -> S.modify' $ M.insert v it
    Just it' -> guard $ it == it'


-- | Match the given pattern with the given item expression and bind item
-- subexpressions to pattern variables.
match :: (Eq sym, Ord var) => Pattern sym var -> I.Item sym -> PatternM sym var
match pt it =
  case (pt, it) of
    (Const it', it) -> do
      guard $ it' == it
      return ()
    (Pair p1 p2, I.Pair i1 i2) -> do
      match p1 i1
      match p2 i2
    (Union pu, I.Union iu) ->
      case (pu, iu) of
        (Left pl, Left il) ->
          match pl il
        (Right pr, Right ir) ->
          match pr ir
        -- Fail otherwise
        _ -> empty
    (Var x, _) ->
      bind x it
    (Any, _) ->
      return ()
    _ ->
      -- Fail otherwise
      empty


-- | Evaluate pattern matching.
evalMatch :: PatternM sym var -> Maybe (Env sym var)
evalMatch m =
  let (val, env) = S.runState (runMaybeT m) M.empty
   in case val of
        Nothing -> Nothing
        Just _  -> Just env


leftP :: Pattern sym T.Text
leftP = Pair
  (Pair (Var "A") (Pair (Var "B") (Var "beta")))
  (Pair (Var "i") (Var "j"))


rightP :: Pattern sym T.Text
rightP = Pair
  (Pair (Var "B") (Const I.Unit))
  (Pair (Var "j") (Var "k"))


main :: IO ()
main = do
  let triple x y z = I.Pair x (I.Pair y z)
      str = I.Sym . I.VStr
      int = I.Sym . I.VInt
      rule hd bd = I.Pair
        (str hd)
        (I.list $ map I.VStr bd)
      left = triple
        (rule "NP" ["DET", "N"])
        (int 1)
        (int 2)
      right = triple
        (rule "DET" [])
        (int 2)
        (int 3)
  print . evalMatch $ do
    match leftP left
    match rightP right


-- -- | Evaluate pattern matching.
-- evalMatch' :: PatternM T.Text T.Text -> Maybe (Env T.Text T.Text)
-- evalMatch' m =
--   let (val, env) = S.runState (runMaybeT m) M.empty
--    in case val of
--         Nothing -> Nothing
--         Just _  -> Just env
