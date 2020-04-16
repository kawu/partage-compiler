{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}


-- | Pattern matching for items and deduction rules


module ParComp.Pattern
  (
  -- * Registered functions
    FunSet (..)
  , FunName (..)
  , emptyFunSet

  -- * Patterns and rules
  , Pattern (..)
  , Cond (..)
  , Rule (..)
  , apply
  , runMatchT
  ) where


-- import           Prelude hiding (Integer, either)
import           Control.Monad (guard, void)
import           Control.Applicative (empty, (<|>))
import           Control.Monad.Trans.Maybe (MaybeT(..))
import qualified Control.Monad.State.Strict as S
import qualified Control.Monad.RWS.Strict as RWS

import qualified Pipes as P

import           Data.Lens.Light

import qualified Data.Text as T
import qualified Data.Set as Set
import qualified Data.Map.Strict as M

import qualified ParComp.Item as I
import           ParComp.Item (Item)

import           Debug.Trace (trace)


--------------------------------------------------
-- Grammar
--------------------------------------------------


-- | Function name
newtype FunName = FunName {unFunName :: T.Text}
  deriving (Show, Eq, Ord)


-- | Predicate name
newtype PredName = PredName {unPredName :: T.Text}
  deriving (Show, Eq, Ord)


-- | Registered grammar functions
--
-- Note that the registered functions are can be in fact multi-argument, since
-- `Item` allows to encode tuples.
--
data FunSet sym = FunSet
  { predMap :: M.Map PredName (Item sym -> Bool)
    -- ^ Named predicate functions.
  , funMap :: M.Map FunName (Item sym -> Item sym)
    -- ^ Named item expression functions
  }


-- | Empty grammar
emptyFunSet :: FunSet sym
emptyFunSet = FunSet M.empty M.empty


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
  -- | > Application: apply function to the given argument pattern.
  -- The pattern must be possible to `close`.
  | App FunName (Pattern sym var)
  -- | > Disjunction: match items which match either of the two patterns.
  -- `OrP` provides non-determinism in pattern matching.
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
  -- | > Fix: `Fix p` defines a recursive pattern `p`, which can be referred to
  -- with `Rec` from within `p`
  | Fix (Pattern sym var)
  -- | > Rec: call recursive pattern `p` defined with `Fix p`
  | Rec
  deriving (Show, Eq, Ord)


-- | Variable binding environment
type Env sym var = M.Map var (Item sym)


-- | Pattern matching state
data PMState sym var = PMState
  { _env :: Env sym var
    -- ^ Variable binding environment
  , _fix :: Maybe (Pattern sym var)
    -- ^ Fixed recursive pattern
  } deriving (Show)
$( makeLenses [''PMState] )


-- | Pattern matching monad
type MatchT m sym var a = P.ListT (RWS.RWST (FunSet sym) () (PMState sym var) m) a
-- type MatchM sym var a = MaybeT (RWS.RWS (Grammar sym) () (Env sym var)) a


-- | Evaluate pattern matching.
-- evalMatch :: MatchM sym var a -> Maybe (a, Env sym var)
-- evalMatch m =
--   let (val, env) = S.runState (runMaybeT m) M.empty
--    in case val of
--         Nothing -> Nothing
--         Just x  -> Just (x, env)


-- | Evaluate pattern matching.
runMatchT :: (Monad m) => FunSet sym -> MatchT m sym var a -> m ()
-- runMatchT = flip S.evalStateT M.empty . P.runListT
runMatchT funSet m =
  void $ RWS.evalRWST (P.runListT m) funSet (PMState M.empty Nothing)


-- | Retrieve the item expression bound to the given variable.
retrieve :: (Monad m, Ord var) => var -> MatchT m sym var (Item sym)
retrieve v = do
  mayIt <- S.gets (M.lookup v . getL env)
  case mayIt of
    Nothing -> empty
    Just it -> return it


-- | Bind the item to the given variable.  If the variable is already bound,
-- make sure that the new item is equal to the old one.
bind :: (Monad m, Eq sym, Ord var) => var -> Item sym -> MatchT m sym var ()
bind v it = do
  mayIt <- S.lift $ S.gets (M.lookup v . getL env)
  case mayIt of
    Nothing -> S.modify' . modL env $ M.insert v it
    Just it' -> guard $ it == it'


-- | Perform matching in a local environment.
withLocalEnv :: (Monad m) => MatchT m sym var a -> MatchT m sym var a
withLocalEnv m = do
  env <- S.get
  x <- m
  S.put env
  return x


-- | Perform match with the recursive pattern.
withFix
  :: (Monad m)
  => Pattern sym var
  -> MatchT m sym var a
  -> MatchT m sym var a
withFix p m = do
  -- Retrieve the old fix
  oldFix <- S.lift . S.gets $ getL fix
  -- Register the new fix
  S.lift . S.modify' $ setL fix (Just p)
  x <- m
  -- Restore the old fix
  S.lift . S.modify' $ setL fix oldFix
  return x


-- | Retrieve the fixed recursive pattern.
fixed :: (Monad m) => MatchT m sym var (Pattern sym var)
fixed = do
  mayFix <- S.lift . S.gets $ getL fix
  case mayFix of
    Nothing -> empty
    Just p  -> return p


-- | Retrieve the predicate with the given name.  The function with the name
-- must exist, otherwise `retrievePred` thorws an error (alternatively, the
-- pattern match could simplify fail, but that could lead to hard to find
-- errors in deduction rules).
retrievePred :: (Monad m) => PredName -> MatchT m sym var (Item sym -> Bool)
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
retrieveFun :: (Monad m) => FunName -> MatchT m sym var (Item sym -> Item sym)
retrieveFun funName = do
  mayFun <- RWS.asks (M.lookup funName . funMap)
  case mayFun of
    Nothing -> error $ concat
      [ "retrieveFun: function with name '"
      , T.unpack $ unFunName funName
      , "' does not exist"
      ]
    Just fun -> return fun


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


-- | Match the given pattern with the given item expression and bind item
-- subexpressions to pattern variables.  The result of a match is an item
-- expression, which is not necessarily the same as the input item due to the
-- `Let` pattern construction, which allows to change the matching result.
match
  :: (Monad m, Show sym, Show var, Eq sym, Ord var)
  => Pattern sym var
  -> Item sym
  -> MatchT m sym var (Item sym)
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
    (App fname p, it) -> do
      f <- retrieveFun fname
      it' <- f <$> close p
      guard $ it' == it
      return it
    (OrP p1 p2, it) -> do
      env <- S.get
      match p1 it <|> do
        S.put env
        match p2 it
--     (OrP p1 p2, it) -> do
--       env <- S.get
--       S.lift (runMaybeT $ match p1 it) >>= \case
--         Just x -> return x
--         Nothing -> do
--           S.put env
--           match p2 it
    (AndP p1 p2, it) ->
      match p1 it >>= match p2
    (Let x e y, it) -> do
      it' <- match e it
      withLocalEnv $ do
        match x it'
        close y
    (Via p x, it) -> do
      it' <- match p it
      match x it'
    (Fix p, it) -> do
      withFix p $ do
        match p it
    (Rec, it) -> do
      p <- fixed
      match p it
    _ ->
      -- Fail otherwise
      empty


-- | Convert the pattern to the corresponding item expression.  The pattern
-- should not have any free variables, nor wildcard patterns.
--
-- TODO: What about logical (conjunction/disjunction) patterns?  Let and Via?
--
close
  :: (Monad m, Eq sym, Ord var)
  => Pattern sym var
  -> MatchT m sym var (Item sym)
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
    App fname p -> do
      f <- retrieveFun fname
      f <$> close p
    -- Fail in case of logical patterns, recursive patterns, etc.
    OrP p1 p2 -> error "close OrP"
    AndP p1 p2 -> error "close AndP"
    Let x e y -> error "close Let"
    Via p x -> error "close Via"
    Fix _ -> error "close Fix"
    Rec -> error "close Rec"
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
  | Pred PredName (Pattern sym var)
  -- | > Logical conjunction
  | And (Cond sym var) (Cond sym var)
  -- | > Logical disjunction
  | Or (Cond sym var) (Cond sym var)
  -- | > Logical negation
  | Neg (Cond sym var)
  -- | > Always True
  | CTrue
  deriving (Show, Eq, Ord)


-- | Side condition checking monad
-- type SideM sym var a = RWS.RWS (Grammar sym) () (Env sym var) a


-- | Check the side condition expression.  Note that `check` does not modify
-- the `Env`ironment, nor should it fail.  We keep it in the `MatchT` monad for
-- simplicity.
--
-- TODO: Consider putting `check` in its own monad, to enforce that it
-- satisfies the conditions described above.
--
check :: (Monad m, Eq sym, Ord var) => Cond sym var -> MatchT m sym var Bool
check cond =
  case cond of
    Eq px py  -> (==) <$> close px <*> close py
    Pred pname p -> retrievePred pname <*> close p
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
  deriving (Show, Eq, Ord)


-- | Apply the deduction rule to the given items.  If the application succeeds,
-- the new chart item is returned.
--
-- The function treats the list of items as ordered and does not try other item
-- permutations when matching them with the `antecedents`.
--
apply
  :: (Monad m, Show sym, Show var, Eq sym, Ord var)
  -- => Grammar sym
  => Rule sym var
  -> [Item sym]
  -- -> Maybe (Item sym)
  -> MatchT m sym var (Item sym)
apply Rule{..} items = do
  guard $ length antecedents == length items
  -- Match antecedents with the corresponding items
  mapM_
    (uncurry match)
    (zip antecedents items)
  -- Make sure the side condition holds
  check condition >>= guard
  -- Convert the consequent to the resulting item
  close consequent


--------------------------------------------------
-- TESTING
--------------------------------------------------


-- leftP :: Pattern sym T.Text
-- leftP = Pair
--   (Pair (Var "A") (Pair (Var "B") (Var "beta")))
--   (Pair (Var "i") (Var "j"))
--
--
-- rightP :: Pattern sym T.Text
-- rightP = Pair
--   (Pair (Var "B") (Const I.Unit))
--   (Pair (Var "j") (Var "k"))
--
--
-- -- | Primitive value
-- data Val
--   -- | > Integer
--   = VInt Int
--   -- | > String
--   | VStr T.Text
--   deriving (Show, Eq, Ord)
--
--
-- main :: IO ()
-- main = do
--   let triple x y z = I.Pair x (I.Pair y z)
--       str = I.Sym . VStr
--       int = I.Sym . VInt
--       rule hd bd = I.Pair
--         (str hd)
--         (I.list $ map str bd)
--       left = triple
--         (rule "NP" ["DET", "N"])
--         (int 1)
--         (int 2)
--       right = triple
--         (rule "DET" [])
--         (int 2)
--         (int 3)
--   print . evalMatch $ do
--     match leftP left
--     match rightP right
