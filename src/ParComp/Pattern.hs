{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}


-- | Pattern matching for items and deduction rules


module ParComp.Pattern
  ( Pattern (..)
  , Cond (..)
  , Rule (..)
  , apply
  ) where


-- import           Prelude hiding (Integer, either)
import           Control.Monad (guard)
import           Control.Applicative (empty)
import           Control.Monad.Trans.Maybe (MaybeT(..))
import qualified Control.Monad.State.Strict as S
import qualified Control.Monad.RWS.Strict as RWS

import qualified Data.Text as T
import qualified Data.Set as Set
import qualified Data.Map.Strict as M

import qualified ParComp.Item as I
import           ParComp.Item (Item)

import           Debug.Trace (trace)


--------------------------------------------------
-- Grammar
--------------------------------------------------


-- -- | Function name
-- newtype FunName = FunName {unFunName :: T.Text}
--   deriving (Show, Eq, Ord)


-- -- | Predicate name
-- newtype PredName = PredName {unPredName :: T.Text}
--   deriving (Show, Eq, Ord)


-- -- | The underlying grammar
-- data Grammar sym = Grammar
--   { predMap :: M.Map PredName (Item sym -> Bool)
--     -- ^ Named multi-argument predicate functions.
--   , funMap :: M.Map FunName (Item sym -> Item sym)
--     -- ^ Named multi-argument item expression functions
--   }


-- -- | Empty grammar
-- emptyGram :: Grammar sym
-- emptyGram = Grammar M.empty M.empty


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
  -- | > Application: apply function to the given argument pattern.  The
  -- pattern must be possible to `close`
  | App (Item sym -> Item sym) (Pattern sym var)
  -- | > Disjunction: try to match the first pattern and, if this fails, move
  -- on to match the second pattern; in particular, the second patter is matched
  -- only if the first pattern matching fails
  | OrP (Pattern sym var) (Pattern sym var)
  -- | > Conjunction: match both patterns against the same item (provided for
  -- symmetry with `OrP`)
  | AndP (Pattern sym var) (Pattern sym var)
  -- | > Let: `Let x e y` should be read as ,,let x = e in y'', where:
  -- * `e` is matched with the underlying item
  -- * `x` is matched with the result to bind local variables
  -- * `y` is the result constructed based on the bound local variables
  | Let (Pattern sym var) (Pattern sym var) (Pattern sym var)
  -- | > Via: `Via p x` should be understood as matching `x` with the
  -- underlying item via `p`:
  -- * `p` is first matched with the underlying item
  -- * `x` is then matched with the result
  -- `Via` is different from `Let` in that variables in `x` are global (i.e.,
  -- with the scope of the rule).
  | Via (Pattern sym var) (Pattern sym var)


-- | Variable binding environment
type Env sym var = M.Map var (Item sym)


-- | Pattern matching monad
type MatchM sym var a = MaybeT (S.State (Env sym var)) a
-- type MatchM sym var a = MaybeT (RWS.RWS (Grammar sym) () (Env sym var)) a


-- | Evaluate pattern matching.
evalMatch :: MatchM sym var a -> Maybe (a, Env sym var)
evalMatch m =
  let (val, env) = S.runState (runMaybeT m) M.empty
   in case val of
        Nothing -> Nothing
        Just x  -> Just (x, env)
-- evalMatch :: Grammar sym -> MatchM sym var a -> Maybe (a, Env sym var)
-- evalMatch gram m =
--   let (val, env, _) = RWS.runRWS (runMaybeT m) gram M.empty
--    in case val of
--         Nothing -> Nothing
--         Just x  -> Just (x, env)


-- | Retrieve the item expression bound to the given variable.
retrieve :: Ord var => var -> MatchM sym var (Item sym)
retrieve v = do
  mayIt <- S.gets (M.lookup v)
  case mayIt of
    Nothing -> empty
    Just it -> return it


-- -- | Retrieve the predicate with the given name.  The function with the name
-- -- must exist, otherwise `retrievePred` thorws an error (alternatively, the
-- -- pattern match could simplify fail, but that could lead to hard to find
-- -- errors in deduction rules).
-- retrievePred :: PredName -> MatchM sym var (Item sym -> Bool)
-- retrievePred predName = do
--   mayFun <- RWS.asks (M.lookup predName . predMap)
--   case mayFun of
--     Nothing -> error $ concat
--       [ "retrievePred: function with name '"
--       , T.unpack $ unPredName predName
--       , "' does not exist"
--       ]
--     Just fun -> return fun


-- -- | Retrieve the symbol-level function with the given name.  The function with
-- -- the name must exist, otherwise `retrieveFun` thorws an error.
-- retrieveFun :: FunName -> MatchM sym var (Item sym -> Item sym)
-- retrieveFun funName = do
--   mayFun <- RWS.asks (M.lookup funName . funMap)
--   case mayFun of
--     Nothing -> error $ concat
--       [ "retrieveFun: function with name '"
--       , T.unpack $ unFunName funName
--       , "' does not exist"
--       ]
--     Just fun -> return fun


-- -- | Retrieve the set of local variables in the given pattern.
-- localVarsIn :: (Ord var) => Pattern sym var -> Set.Set var
-- localVarsIn p =
--   case p of
--     Const _ -> Set.empty
--     Pair p1 p2 -> localVarsIn p1 <> localVarsIn p2
--     Union up ->
--       case up of
--         Left p -> localVarsIn p
--         Right p -> localVarsIn p
--     Var v -> Set.singleton v
--     Any -> Set.empty
--     _ -> error "localVarsIn: unhandled pattern"


-- | Bind the item to the given variable.  If the variable is already bound,
-- make sure that the new item is equal to the old one.
bind :: (Eq sym, Ord var) => var -> Item sym -> MatchM sym var ()
bind v it = do
  mayIt <- S.lift $ S.gets (M.lookup v)
  case mayIt of
    Nothing -> S.modify' $ M.insert v it
    Just it' -> guard $ it == it'


-- | Perform matching with a local environment.
withLocalEnv :: MatchM sym var a -> MatchM sym var a
withLocalEnv m = do
  env <- S.get
  x <- m
  S.put env
  return x


-- | Match the given pattern with the given item expression and bind item
-- subexpressions to pattern variables.  The result of a match is an item
-- expression, which is not necessarily the same as the input item due to the
-- `Let` pattern construction, which allows to change the matching result.
match
  :: (Show sym, Show var, Eq sym, Ord var)
  => Pattern sym var
  -> Item sym
  -> MatchM sym var (Item sym)
match pt it =
  case (pt, it) of
    (Const it', it) -> do
      guard $ it' == it
      return it
    (Pair p1 p2, I.Pair i1 i2) ->
      I.Pair <$> match p1 i1 <*> match p2 i2
    (Union pu, I.Union iu) ->
      case (pu, iu) of
        (Left pl, Left il) ->
          I.Union . Left <$> match pl il
        (Right pr, Right ir) ->
          I.Union . Right <$> match pr ir
        -- Fail otherwise
        _ -> empty
    (Var x, _) -> do
      bind x it
      return it
    (Any, _) ->
      return it
    (App f p, it) -> do
      -- f <- retrieveFun fname
      it' <- f <$> close p
      guard $ it' == it
      return it
    (OrP p1 p2, it) -> do
      env <- S.get
      S.lift (runMaybeT $ match p1 it) >>= \case
        Just x -> return x
        Nothing -> do
          S.put env
          match p2 it
    (AndP p1 p2, it) -> do
      match p1 it
      match p2 it
    (Let x e y, it) -> do
      it' <- match e it
      withLocalEnv $ do
        match x it'
        close y
    (Via p x, it) -> do
      it' <- match p it
      match x it'
    _ ->
      -- Fail otherwise
      empty


-- | Convert the pattern to the corresponding item expression.  The pattern
-- should not have any free variables, nor wildcard patterns.
--
-- TODO: What about logical (conjunction/disjunction) patterns?  Let and Via?
--
close :: (Eq sym, Ord var) => Pattern sym var -> MatchM sym var (Item sym)
close p =
  case p of
    Const it -> return it
    Pair p1 p2 -> I.Pair <$> close p1 <*> close p2
    Union up ->
      case up of
        Left lp  -> I.Union .  Left <$> close lp
        Right rp -> I.Union . Right <$> close rp
    -- Fail if variable x not bound
    Var x -> retrieve x
    -- Fail in case of a wildcard (`Any`) pattern
    Any -> empty
    App f p -> do
      -- f <- retrieveFun fname
      f <$> close p
    -- Fail in case of logical patterns (TODO: ???)
    OrP p1 p2 -> error "close OrP"
    AndP p1 p2 -> error "close AndP"
    Let x e y -> error "close Let"
    Via p x -> error "close Via"
--     Let x e y -> do
--       match x =<< close e
--       close y


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
  -- | Pred PredName (Pattern sym var)
  | Pred (Item sym -> Bool) (Pattern sym var)
  -- | > Logical conjunction
  | And (Cond sym var) (Cond sym var)
  -- | > Logical disjunction
  | Or (Cond sym var) (Cond sym var)
  -- | > Logical negation
  | Neg (Cond sym var)
  -- | > Always True
  | CTrue
  -- deriving (Show, Eq, Ord)


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
    -- Pred pname p -> retrievePred pname <*> close p
    Pred pred p -> pred <$> close p
    And cx cy -> (&&) <$> check cx <*> check cy
    Or cx cy  -> (||) <$> check cx <*> check cy
    Neg c -> not <$> check c
    CTrue -> return True


--------------------------------------------------
-- Deduction rules
--------------------------------------------------


-- | Single deduction rule
data Rule sym var = Rule
  { antecedents :: [Pattern sym var]
    -- ^ The list of rule's antecedents
  , consequent :: Pattern sym var
    -- ^ The rule's consequent
  , condition :: Cond sym var
  }
  -- deriving (Show, Eq, Ord)


-- | Apply the deduction rule to the given items.  If the application succeeds,
-- the new chart item is returned.
--
-- The function treats the list of items as ordered and does not try other item
-- permutations when matching them with the `antecedents`.
--
apply
  :: (Show sym, Show var, Eq sym, Ord var)
  -- => Grammar sym
  => Rule sym var
  -> [Item sym]
  -> Maybe (Item sym)
apply Rule{..} items = do
  guard $ length antecedents == length items
  (res, _env) <- evalMatch $ do
    -- Match antecedents with the corresponding items
    mapM_
      (uncurry match)
      (zip antecedents items)
    -- Make sure the side condition holds
    check condition >>= guard
    -- Convert the consequent to the resulting item
    close consequent
  return res


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
  print . evalMatch $ do
    match leftP left
    match rightP right


-- -- | Evaluate pattern matching.
-- evalMatch' :: MatchM T.Text T.Text -> Maybe (Env T.Text T.Text)
-- evalMatch' m =
--   let (val, env) = RWS.runState (runMaybeT m) M.empty
--    in case val of
--         Nothing -> Nothing
--         Just _  -> Just env
