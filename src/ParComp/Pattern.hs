{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}


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
  , MatchT
  , lift
  , apply
  , runMatchT
  , dummyMatch

  -- * Indexing
  , Lock
  , Key
  , mkLock
  ) where


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
import           Data.Maybe (isJust)

import qualified ParComp.Item as I
import           ParComp.Item (Item)

import           Debug.Trace (trace)


--------------------------------------------------
-- Function Set
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
  -- `Or` provides non-determinism in pattern matching.
  | Or (Pattern sym var) (Pattern sym var)
--   -- | > Conjunction: match both patterns against the same item (provided for
--   -- symmetry with `Or`)
--   | AndP (Pattern sym var) (Pattern sym var)
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
  -- with the scope of the rule).  `Via` can be also understood as conjunction.
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
type MatchT sym var m a =
  P.ListT (RWS.RWST (FunSet sym) () (PMState sym var) m) a
-- type MatchM sym var a = MaybeT (RWS.RWS (Grammar sym) () (Env sym var)) a


-- | Evaluate pattern matching.
-- evalMatch :: MatchM sym var a -> Maybe (a, Env sym var)
-- evalMatch m =
--   let (val, env) = S.runState (runMaybeT m) M.empty
--    in case val of
--         Nothing -> Nothing
--         Just x  -> Just (x, env)


-- | Lift computation to the inner monad.
lift :: (Monad m) => m a -> MatchT sym var m a
lift = S.lift . S.lift


-- | Evaluate pattern matching.
runMatchT :: (Monad m) => FunSet sym -> MatchT sym var m a -> m ()
-- runMatchT = flip S.evalStateT M.empty . P.runListT
runMatchT funSet m =
  void $ RWS.evalRWST (P.runListT m) funSet (PMState M.empty Nothing)


-- | Look up the value assigned to the given variable.
lookupVar :: (Monad m, Ord var) => var -> MatchT sym var m (Maybe (Item sym))
lookupVar v = S.gets $ M.lookup v . getL env


-- | Retrieve the item expression bound to the given variable.
retrieve :: (Monad m, Ord var) => var -> MatchT sym var m (Item sym)
retrieve v = 
  lookupVar v >>= \case
    Nothing -> empty
    Just it -> return it


-- | Bind the item to the given variable.  If the variable is already bound,
-- make sure that the new item is equal to the old one.
bind :: (Monad m, Eq sym, Ord var) => var -> Item sym -> MatchT sym var m ()
bind v it = do
  mayIt <- S.lift $ S.gets (M.lookup v . getL env)
  case mayIt of
    Nothing -> S.modify' . modL env $ M.insert v it
    Just it' -> guard $ it == it'


-- | Perform matching in a local environment.
withLocalEnv :: (Monad m) => MatchT sym var m a -> MatchT sym var m a
withLocalEnv m = do
  env <- S.get
  x <- m
  S.put env
  return x


-- | Perform match with the recursive pattern.
withFix
  :: (Monad m)
  => Pattern sym var
  -> MatchT sym var m a
  -> MatchT sym var m a
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
fixed :: (Monad m) => MatchT sym var m (Pattern sym var)
fixed = do
  mayFix <- S.lift . S.gets $ getL fix
  case mayFix of
    Nothing -> empty
    Just p  -> return p


-- | Retrieve the predicate with the given name.  The function with the name
-- must exist, otherwise `retrievePred` thorws an error (alternatively, the
-- pattern match could simplify fail, but that could lead to hard to find
-- errors in deduction rules).
retrievePred :: (Monad m) => PredName -> MatchT sym var m (Item sym -> Bool)
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
retrieveFun :: (Monad m) => FunName -> MatchT sym var m (Item sym -> Item sym)
retrieveFun funName = do
  mayFun <- RWS.asks (M.lookup funName . funMap)
  case mayFun of
    Nothing -> error $ concat
      [ "retrieveFun: function with name '"
      , T.unpack $ unFunName funName
      , "' does not exist"
      ]
    Just fun -> return fun


-- | Retrieve the set of global variables in the given pattern.
globalVarsIn :: (Ord var) => Pattern sym var -> Set.Set var
globalVarsIn = \case
  Const _ -> Set.empty
  Pair p1 p2 -> globalVarsIn p1 <> globalVarsIn p2
  Union up -> case up of
    Left p -> globalVarsIn p
    Right p -> globalVarsIn p
  Var v -> Set.singleton v
  Any -> Set.empty
  App _ p -> globalVarsIn p
  -- TODO: should we require that the sets of global variables in the two
  -- branches of the `Or` pattern are the same?  Otherwise, `keyFor` may not
  -- work (given that ultimately we match either the left or the right branch).
  Or x y -> globalVarsIn x <> globalVarsIn y
  -- Below, ignore `x` and `y`, which should contain local variables only
  Let x e y -> globalVarsIn e
  Via p x -> globalVarsIn p <> globalVarsIn x
  Fix p -> globalVarsIn p
  Rec -> Set.empty


-- | Match the given pattern with the given item expression and bind item
-- subexpressions to pattern variables.  The result of a match is an item
-- expression, which is not necessarily the same as the input item due to the
-- `Let` pattern construction, which allows to change the matching result.
match
  :: (Monad m, Show sym, Show var, Eq sym, Ord var)
  => Pattern sym var
  -> Item sym
  -> MatchT sym var m (Item sym)
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
    (Or p1 p2, it) -> do
      env <- S.get
      match p1 it <|> do
        S.put env
        match p2 it
--     (Or p1 p2, it) -> do
--       env <- S.get
--       S.lift (runMaybeT $ match p1 it) >>= \case
--         Just x -> return x
--         Nothing -> do
--           S.put env
--           match p2 it
--     (AndP p1 p2, it) ->
--       match p1 it >>= match p2
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


-- | Dummy pattern matching
--
-- Match the pattern against an invisible value by assuming that they match
-- perfectly.  The motivation behind `dummyMatch` is to bind the (global)
-- variables in the pattern (to some dummy values), so that we can later learn
-- what variables the pattern actually uses (and e.g. use `mkLock`).
--
-- TODO: This is not pretty...  Why don't just retrieve the set of global
-- variables in the pattern and work with this?
--
dummyMatch
  :: (Monad m, Show sym, Show var, Eq sym, Ord var)
  => Pattern sym var
  -> MatchT sym var m ()
dummyMatch p = do
  mapM_
    (flip bind I.Unit)
    (Set.toList $ globalVarsIn p)



-- | Convert the pattern to the corresponding item expression.  The pattern
-- should not have any free variables, nor wildcard patterns.
--
-- TODO: What about logical (conjunction/disjunction) patterns?  Let and Via?
--
close
  :: (Monad m, Eq sym, Ord var)
  => Pattern sym var
  -> MatchT sym var m (Item sym)
close p =
  case p of
    Const it -> pure it
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
    Or p1 p2 -> error "close Or"
    -- AndP p1 p2 -> error "close AndP"
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
  | OrC (Cond sym var) (Cond sym var)
  -- | > Logical negation
  | Neg (Cond sym var)
  -- | > Always True
  | TrueC
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
check :: (Monad m, Eq sym, Ord var) => Cond sym var -> MatchT sym var m Bool
check cond =
  case cond of
    Eq px py  -> (==) <$> close px <*> close py
    Pred pname p -> retrievePred pname <*> close p
    And cx cy -> (&&) <$> check cx <*> check cy
    OrC cx cy  -> (||) <$> check cx <*> check cy
    Neg c -> not <$> check c
    TrueC -> pure True


--------------------------------------------------
-- Indexing
--------------------------------------------------


-- | Lock determines the index, i.e., the set of pattern keys handled by a
-- given indexing structure.
type Lock sym var = Pattern sym var


-- | Key of a pattern assigns values to the individual variables in the
-- corresponding lock.  It is important to note that each key has its
-- corresponding lock (makes sense!).
type Key sym var = Env sym var


-- -- | Check if the given item fits the lock.
-- fitsIn :: I.Item sym -> Lock sym var -> Bool
-- fitsIn x = isJust . itemKey x


-- -- | Retrieve the key of the item for the given lock.
-- itemKey :: I.Item sym -> Lock sym var -> Maybe (Key sym var)
-- itemKey x lock = undefined


-- | Retrieve the lock of the pattern.  The lock can be used to determine the
-- corresponding indexing structure.
--
-- The function replaces free variables with wildcards, with the exception of
-- local variables, which are not handled.
--
-- TODO: In `Let x e y`, both `x` and `y` should contain no global variables.
-- However, this is currently not enforced in any way.
--
-- TODO: We should also rename bound variables, so that it's insensitive to
-- variable names.
--
mkLock
  :: (Monad m, Ord var)
  => Pattern sym var
  -> MatchT sym var m (Lock sym var)
mkLock = \case
  Const x -> pure $ Const x
  Pair x y -> Pair <$> mkLock x <*> mkLock y
  Union up -> case up of
    Left lp  -> Union .  Left <$> mkLock lp
    Right rp -> Union . Right <$> mkLock rp
  Var v ->
    lookupVar v >>= \case
      Just it -> pure $ Var v
      Nothing -> pure Any
  Any -> pure Any
  App fname p -> App fname <$> mkLock p
  Or x y -> Or <$> mkLock x <*> mkLock y
  Let x e y -> Let <$> pure x <*> mkLock e <*> pure y
  Via p x -> Via <$> mkLock p <*> mkLock x
  Fix p -> Fix <$> mkLock p
  Rec -> pure Rec


-- | Retrieve the key(s) of the item for the given lock.
--
-- TODO: the function must be evaluated in an empty environment, otherwise it
-- will return more than we want.
--
itemKeyFor
  :: (Monad m, Eq sym, Ord var, Show sym, Show var)
  => I.Item sym
  -> Lock sym var
  -> MatchT sym var m (Key sym var)
itemKeyFor x lock = do
  -- TODO: Since we ignore the item, it may be that we will generate several
  -- keys which are identical.  This might be a problem?  At least from the
  -- efficiency point of view.
  _ <- match lock x
  S.gets (getL env)


-- | Retrieve the values of the global variables in the lock, thus creating the
-- key corresponding to the lock based on the current environment.
--
-- TODO: in contrast with `itemKeyFor`, `keyFor` relies on the current
-- environment.
--
keyFor
  :: (Monad m, Ord var)
  => Lock sym var
  -> MatchT sym var m (Key sym var)
keyFor lock = do
  M.fromList <$> mapM
    (\v -> (v,) <$> retrieve v)
    (Set.toList $ globalVarsIn lock)


-- -- | Replace bound variables with their corresponding values and free variables
-- -- with wildcards (with the exception of local variables, which are not
-- -- handled).
-- bindAll = \case
--   Const x -> pure $ Const x
--   Pair x y -> Pair <$> bindAll x <*> bindAll y
--   Union up -> case up of
--     Left lp  -> Union .  Left <$> bindAll lp
--     Right rp -> Union . Right <$> bindAll rp
--   Var v ->
--     lookupVar v >>= \case
--       Just it -> pure $ Const it
--       Nothing -> pure Any
--   Any -> pure Any
--   App fname p -> App fname <$> bindAll p
--   Or x y -> Or <$> bindAll x <*> bindAll y
--   Let x e y -> Let <$> pure x <*> bindAll e <*> pure y
--   Via p x -> Via <$> bindAll p <*> bindAll x
--   Fix p -> Fix <$> bindAll p
--   Rec -> pure Rec


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
  -> MatchT sym var m (Item sym)
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
