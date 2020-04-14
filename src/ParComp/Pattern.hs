{-# LANGUAGE OverloadedStrings #-}


-- | Pattern matching for items and deduction rules


module ParComp.Pattern
  ( Pattern (..)
  , Env
--   , match
--   , evalMatch
  ) where


-- import           Prelude hiding (Integer, either)
import           Control.Monad (guard)
import           Control.Applicative (empty)
import           Control.Monad.Trans.Maybe (MaybeT(..))
-- import qualified Control.Monad.State.Strict as S
import qualified Control.Monad.RWS.Strict as RWS

import qualified Data.Text as T
import qualified Data.Map.Strict as M

import qualified ParComp.Item as I
import           ParComp.Item (Item)


--------------------------------------------------
-- Grammar
--------------------------------------------------


-- | Function name
newtype FunName = FunName {unFunName :: T.Text}
  deriving (Show, Eq, Ord)


-- | Predicate name
newtype PredName = PredName {unPredName :: T.Text}
  deriving (Show, Eq, Ord)



-- | The underlying grammar
data Grammar sym = Grammar
  { predMap :: M.Map PredName (Item sym -> Bool)
    -- ^ Named multi-argument predicate functions.
  , funMap :: M.Map FunName (Item sym -> Item sym)
    -- ^ Named multi-argument item expression functions
  }


-- | Empty grammar
emptyGram :: Grammar sym
emptyGram = Grammar M.empty M.empty


--------------------------------------------------
-- Pattern
--------------------------------------------------


-- | Pattern expression
data Pattern sym var
  -- | > Constant: match the given item expression
  = Const (Item sym)
  -- | > Pair: recursively match item pair
  | Pair (Pattern sym var) (Pattern sym var)
  -- | > Union: recursively match item union
  | Union (Either (Pattern sym var) (Pattern sym var))
  -- | > Variable: match any item expression and bind it to the given variable
  | Var var
  -- | > Any: match any item expression (wildcard)
  | Any
  -- | > App: apply function to the given argument pattern.  The pattern should
  -- contain no free variables, nor wildcards (i.e., it should be possible to
  -- `close` them)
  | App FunName (Pattern sym var)
  deriving (Show, Eq, Ord)


-- | Variable binding environment
type Env sym var = M.Map var (Item sym)


-- | Pattern matching monad
-- type MatchM sym var a = MaybeT (S.State (Env sym var)) a
type MatchM sym var a = MaybeT (RWS.RWS (Grammar sym) () (Env sym var)) a


-- | Evaluate pattern matching.
evalMatch :: Grammar sym -> MatchM sym var () -> Maybe (Env sym var)
evalMatch gram m =
  let (val, env, _) = RWS.runRWS (runMaybeT m) gram M.empty
   in case val of
        Nothing -> Nothing
        Just _  -> Just env


-- | Retrieve the item expression bound to the given variable.
retrieve :: Ord var => var -> MatchM sym var (Item sym)
retrieve v = do
  mayIt <- RWS.gets (M.lookup v)
  case mayIt of
    Nothing -> empty
    Just it -> return it


-- | Retrieve the predicate with the given name.  The function with the name
-- must exist, otherwise `retrievePred` thorws an error (alternatively, the
-- pattern match could simplify fail, but that could lead to hard to find
-- errors in deduction rules).
retrievePred :: PredName -> MatchM sym var (Item sym -> Bool)
retrievePred predName = do
  mayFun <- RWS.asks (M.lookup predName . predMap)
  case mayFun of
    Nothing -> error $ concat
      [ "retrievePred: function with name '"
      , T.unpack $ unPredName predName
      , "' does not exist"
      ]
    Just fun -> return fun


-- | Retrieve the symbol-level function with the given name.  The function with
-- the name must exist, otherwise `retrieveFun` thorws an error.
retrieveFun :: FunName -> MatchM sym var (Item sym -> Item sym)
retrieveFun funName = do
  mayFun <- RWS.asks (M.lookup funName . funMap)
  case mayFun of
    Nothing -> error $ concat
      [ "retrieveFun: function with name '"
      , T.unpack $ unFunName funName
      , "' does not exist"
      ]
    Just fun -> return fun


-- | Bind the item to the given variable.  If the variable is already bound,
-- make sure that the new item is equal to the old one.
bind :: (Eq sym, Ord var) => var -> Item sym -> MatchM sym var ()
bind v it = do
  mayIt <- RWS.lift $ RWS.gets (M.lookup v)
  case mayIt of
    Nothing -> RWS.modify' $ M.insert v it
    Just it' -> guard $ it == it'


-- | Match the given pattern with the given item expression and bind item
-- subexpressions to pattern variables.
match :: (Eq sym, Ord var) => Pattern sym var -> Item sym -> MatchM sym var ()
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
    (App fname p, it) -> do
      f <- retrieveFun fname
      it' <- f <$> close p
      guard $ it' == it
    _ ->
      -- Fail otherwise
      empty


-- | Convert the pattern (with no free variables nor wildcards) to the
-- corresponding item expression.
close :: (Ord var) => Pattern sym var -> MatchM sym var (Item sym)
close p =
  case p of
    Const it -> return it
    Pair p1 p2 -> I.Pair <$> close p1 <*> close p2
    Union up ->
      case up of
        Left lp  -> I.Union .  Left <$> close lp
        Right rp -> I.Union . Right <$> close rp
    -- this fails if variable x is not bound
    Var x -> retrieve x
    -- fail in case of a wildcard (`Any`) pattern
    Any -> empty
    App fname p -> do
      f <- retrieveFun fname
      f <$> close p


--------------------------------------------------
-- Side conditions
--------------------------------------------------


-- | Side condition expression
--
-- Note that a side condition must contain no free variables, nor wildcard
-- patterns.  This is because side conditions are not matched against items.
-- You should think of side conditions as additional checks verified once the
-- antecedent patterns are matched.
--
data Cond sym var
  -- | > Check the equality between the two patterns
  = Eq (Pattern sym var) (Pattern sym var)
  -- | > Check if the given predicate is satisfied
  | Pred PredName (Pattern sym var)
  -- | > Logical conjunction
  | And (Cond sym var) (Cond sym var)
  -- | > Logical disjunction
  | Or (Cond sym var) (Cond sym var)
  -- | > Logical negation
  | Neg (Cond sym var)
  deriving (Show, Eq, Ord)


-- | Side condition checking monad
-- type SideM sym var a = RWS.RWS (Grammar sym) () (Env sym var) a


-- | Check the side condition expression.  Note that `check` does not modify
-- the `Env`ironment, nor should it fail.  We keep it in the `MatchM` monad for
-- simplicity.
--
-- TODO: Consider putting `check` in its own monad, to enforce that it
-- satisfies the conditions described above.
--
check :: (Eq sym, Ord var) => Cond sym var -> MatchM sym var Bool
check cond =
  case cond of
    Eq px py  -> (==) <$> close px <*> close py
    Pred pname p -> retrievePred pname <*> close p
    And cx cy -> (&&) <$> check cx <*> check cy
    Or cx cy  -> (||) <$> check cx <*> check cy
    Neg c -> not <$> check c


--------------------------------------------------
-- TESTING
--------------------------------------------------


leftP :: Pattern sym T.Text
leftP = Pair
  (Pair (Var "A") (Pair (Var "B") (Var "beta")))
  (Pair (Var "i") (Var "j"))


rightP :: Pattern sym T.Text
rightP = Pair
  (Pair (Var "B") (Const I.Unit))
  (Pair (Var "j") (Var "k"))


-- | Primitive value
data Val
  -- | > Integer
  = VInt Int
  -- | > String
  | VStr T.Text
  deriving (Show, Eq, Ord)


main :: IO ()
main = do
  let triple x y z = I.Pair x (I.Pair y z)
      str = I.Sym . VStr
      int = I.Sym . VInt
      rule hd bd = I.Pair
        (str hd)
        (I.list $ map str bd)
      left = triple
        (rule "NP" ["DET", "N"])
        (int 1)
        (int 2)
      right = triple
        (rule "DET" [])
        (int 2)
        (int 3)
  print . evalMatch emptyGram $ do
    match leftP left
    match rightP right


-- -- | Evaluate pattern matching.
-- evalMatch' :: MatchM T.Text T.Text -> Maybe (Env T.Text T.Text)
-- evalMatch' m =
--   let (val, env) = RWS.runState (runMaybeT m) M.empty
--    in case val of
--         Nothing -> Nothing
--         Just _  -> Just env
