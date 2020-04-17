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
  , match
  , check
  , close

  -- * Indexing
  , Lock
  , Key
  , mkLock
  , itemKeyFor
  , keyFor
  ) where


import qualified System.Random as R

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


--------------------------------------------------
-- Function register
--------------------------------------------------


-- | Function name
newtype FunName = FunName {unFunName :: T.Text}
  deriving (Show, Eq, Ord)


-- | Predicate name
newtype PredName = PredName {unPredName :: T.Text}
  deriving (Show, Eq, Ord)


-- | Record with registered grammar functions
--
-- Note that the registered functions can be multi-argument, since `Item`
-- allows to encode tuples.
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
data Pattern sym var lvar
  -- | > Constant: match the given item expression
  = Const (Item sym)
  -- | > Pair: recursively match item pair
  | Pair (Pattern sym var lvar) (Pattern sym var lvar)
  -- | > Union: recursively match item union
  | Union (Either (Pattern sym var lvar) (Pattern sym var lvar))
  -- | > Variable: match any item expression and bind it to the given variable
  | Var var
  -- | > Local variable: local variable used in the `Let` pattern
  | LVar lvar
  -- | > Any: match any item expression (wildcard)
  | Any
  -- | > Application: apply function to the given argument pattern.
  -- The pattern must be possible to `close`.
  | App FunName (Pattern sym var lvar)
  -- | > Disjunction: match items which match either of the two patterns.
  -- `Or` provides non-determinism in pattern matching.
  | Or (Pattern sym var lvar) (Pattern sym var lvar)
  -- | > Let: `Let x e y` should be read as ,,let x = e in y'', where:
  -- * `e` is matched with the underlying item
  -- * `x` is matched with the result to bind local variables
  -- * `y` is the result constructed based on the bound local variables
  | Let (Pattern sym var lvar) (Pattern sym var lvar) (Pattern sym var lvar)
  -- | > Via: `Via p x` should be understood as matching `x` with the
  -- underlying item via `p`:
  -- * `p` is first matched with the underlying item
  -- * `x` is then matched with the result
  -- `Via` is different from `Let` in that variables in `x` are global (i.e.,
  -- with the scope of the rule).  `Via` can be also understood as conjunction.
  | Via (Pattern sym var lvar) (Pattern sym var lvar)
  -- | > Fix: `Fix p` defines a recursive pattern `p`, which can be referred to
  -- with `Rec` from within `p`
  | Fix (Pattern sym var lvar)
  -- | > Rec: call recursive pattern `p` defined with `Fix p`
  | Rec
  deriving (Show, Eq, Ord)


-- | Retrieve the set of global variables in the given pattern.
globalVarsIn :: (Ord var) => Pattern sym var lvar -> Set.Set var
globalVarsIn = \case
  Const _ -> Set.empty
  Pair p1 p2 -> globalVarsIn p1 <> globalVarsIn p2
  Union up -> case up of
    Left p -> globalVarsIn p
    Right p -> globalVarsIn p
  Var v -> Set.singleton v
  LVar v -> error "globalVarsIn: encountered local variable!"
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


--------------------------------------------------
-- Pattern matching
--------------------------------------------------


-- | Variable binding environment
type Env sym var = M.Map var (Item sym)


-- | Pattern matching state
data PMState sym var lvar = PMState
  { _genv :: Env sym var
    -- ^ Global variable binding environment
  , _lenv :: Env sym lvar
    -- ^ Local variable binding environment
  , _fix :: Maybe (Pattern sym var lvar)
    -- ^ Fixed recursive pattern
  } deriving (Show)
$( makeLenses [''PMState] )


-- | Pattern matching monad transformer
type MatchT sym var lvar m a =
  P.ListT (RWS.RWST (FunSet sym) () (PMState sym var lvar) m) a


-- | Lift the computation in the inner monad to `MatchT`.
lift :: (Monad m) => m a -> MatchT sym var lvar m a
lift = S.lift . S.lift


-- | Run pattern matching computation with the underlying functions and
-- predicates.
runMatchT
  :: (Monad m)
  => FunSet sym
  -> MatchT sym var lvar m a
  -> m ()
runMatchT funSet m =
  void $ RWS.evalRWST (P.runListT m) funSet (PMState M.empty M.empty Nothing)


-- | Look up the value assigned to the global variable.
lookupVar
  :: (Monad m, Ord var)
  => var
  -> MatchT sym var lvar m (Maybe (Item sym))
lookupVar v = S.gets $ M.lookup v . getL genv


-- | Look up the value assigned to the local variable.
lookupLVar
  :: (Monad m, Ord lvar)
  => lvar
  -> MatchT sym var lvar m (Maybe (Item sym))
lookupLVar v = S.gets $ M.lookup v . getL lenv


-- | Retrieve the value bound to the given variable.
retrieveVar
  :: (Monad m, Ord var)
  => var
  -> MatchT sym var lvar m (Item sym)
retrieveVar v =
  lookupVar v >>= \case
    Nothing -> empty
    Just it -> return it


-- | Bind the item to the given variable.  If the variable is already bound,
-- make sure that the new item is equal to the old one.
bindVar
  :: (Monad m, Eq sym, Ord var)
  => var
  -> Item sym
  -> MatchT sym var lvar m ()
bindVar v it = do
  mayIt <- S.lift $ S.gets (M.lookup v . getL genv)
  case mayIt of
    Nothing -> S.modify' . modL genv $ M.insert v it
    Just it' -> guard $ it == it'


-- | Bind the item to the given local variable.
bindLVar
  :: (Monad m, Eq sym, Ord lvar)
  => lvar
  -> Item sym
  -> MatchT sym var lvar m ()
bindLVar v it = S.modify' . modL lenv $ M.insert v it


-- -- | Perform matching in a local global environment.  TODO: temporary function,
-- -- refactor and remove!
-- withLocalGlobalEnv :: (P.MonadIO m) => MatchT sym var lvar m a -> MatchT sym var lvar m a
-- withLocalGlobalEnv m = do
--   ge <- S.gets (getL genv)
--   le <- S.gets (getL lenv)
--   x <- m
--   S.modify' (setL genv ge)
--   S.modify' (setL lenv le)
--   return x


-- -- | Perform matching in a local environment.
-- withLocalEnv :: (P.MonadIO m) => MatchT sym var lvar m a -> MatchT sym var lvar m a
-- withLocalEnv m = do
--   -- TODO: Does this actually work in general?  What if `m` fails?  Then
--   -- environment is not restored.  This can be a serious problem, since we want
--   -- to allow disjunctive (`Or`) patterns.
--   e <- S.gets (getL lenv)
--   x <- m
--   S.modify' (setL lenv e)
--   return x


-- | Perform matching in a local environment.
withLocalEnv
  :: (P.MonadIO m)
  => MatchT sym var lvar m a
  -> MatchT sym var lvar m a
withLocalEnv m = do
  e <- S.gets (getL lenv)
  mark <- (`mod` 1000) <$> P.liftIO (R.randomIO :: IO Int)
  P.liftIO $ do
    putStr ">>> IN: "
    print mark
  m <|> do
    S.modify' (setL lenv e)
    P.liftIO $ do
      putStr "<<< OUT: "
      print mark
    empty


-- | Perform match with the recursive pattern.
withFix
  :: (Monad m)
  => Pattern sym var lvar
  -> MatchT sym var lvar m a
  -> MatchT sym var lvar m a
withFix p m = do
  -- Retrieve the old fix
  oldFix <- S.lift . S.gets $ getL fix
  -- Register the new fix
  S.lift . S.modify' $ setL fix (Just p)
  x <- m
  -- Restore the old fix
  -- TODO: similarly as with `withLocalEnv`, it's not clear if this is correct.
  -- It seems there's no guarantee that the original Fix will be restored,
  -- because `x <- m` above can fail.
  S.lift . S.modify' $ setL fix oldFix
  return x


-- | Retrieve the fixed recursive pattern.
fixed :: (Monad m) => MatchT sym var lvar m (Pattern sym var lvar)
fixed = do
  mayFix <- S.lift . S.gets $ getL fix
  case mayFix of
    Nothing -> empty
    Just p  -> return p


-- | Retrieve the predicate with the given name.  The function with the name
-- must exist, otherwise `retrievePred` thorws an error (alternatively, the
-- pattern match could simplify fail, but that could lead to hard-to-find
-- errors in deduction rules).
retrievePred
  :: (Monad m)
  => PredName
  -> MatchT sym var lvar m (Item sym -> Bool)
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
retrieveFun
  :: (Monad m)
  => FunName
  -> MatchT sym var lvar m (Item sym -> Item sym)
retrieveFun funName = do
  mayFun <- RWS.asks (M.lookup funName . funMap)
  case mayFun of
    Nothing -> error $ concat
      [ "retrieveFun: function with name '"
      , T.unpack $ unFunName funName
      , "' does not exist"
      ]
    Just fun -> return fun


-- | Match the given pattern with the given item expression and bind item
-- subexpressions to pattern variables.  The result of a match is an item
-- expression, which is not necessarily the same as the input item due to the
-- `Let` pattern construction, which allows to change the matching result.
match
  :: (P.MonadIO m, Show sym, Show var, Show lvar, Eq sym, Ord var, Ord lvar)
  => Pattern sym var lvar
  -> Item sym
  -> MatchT sym var lvar m (Item sym)
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
      bindVar x it
      return it
    (LVar x, _) -> do
      bindLVar x it
      return it
    (Any, _) ->
      return it
    (App fname p, it) -> do
      f <- retrieveFun fname
      it' <- f <$> close p
      guard $ it' == it
      return it
    (Or p1 p2, it) -> do
      -- NOTE: we retrieve and then restore the entire state, even though the
      -- fixed recursive pattern should never escape its syntactic scope so, in
      -- theory, it should not change between the first and the second branch
      -- of the `Or` pattern.  Perhaps this is something we could check
      -- dynamically, just in case?
      state <- S.get
      match p1 it <|> do
        S.put state
        match p2 it
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
-- Match the pattern against a dummy value by assuming that they match
-- perfectly.  The motivation behind `dummyMatch` is to bind the (global)
-- variables in the pattern (to some dummy values), so that we can later learn
-- what variables the pattern actually uses (and e.g. use `mkLock`).
--
-- Internally, the function (a) retrieves the set of global variables in @p@
-- and (b) binds them to unit values.
dummyMatch
  :: (Monad m, Eq sym, Ord var)
  => Pattern sym var lvar
  -> MatchT sym var lvar m ()
dummyMatch p = do
  mapM_
    (flip bindVar I.Unit)
    (Set.toList $ globalVarsIn p)



-- | Convert the pattern to the corresponding item expression.  This is only
-- possible if the pattern contains no free variables nor wildcard patterns.
-- Otherwise, `close` will silently fail.
--
-- Note that `close` should not modify the underlying state/environment.
--
-- The behavior of the function is undefined in case the pattern contains any
-- of the following:
-- * `Via` pattern
-- * recursive pattern (`Fix` / `Rec`)
close
  :: (P.MonadIO m, Eq sym, Ord var, Ord lvar, Show sym, Show var, Show lvar)
  => Pattern sym var lvar
  -> MatchT sym var lvar m (Item sym)
close = \case
  Const it -> pure it
  Pair p1 p2 -> I.Pair <$> close p1 <*> close p2
  Union up ->
    case up of
      Left lp  -> I.Union .  Left <$> close lp
      Right rp -> I.Union . Right <$> close rp
  -- Fail if variable x not bound
  Var v -> retrieveVar v
  LVar v ->
    lookupLVar v >>= \case
      Nothing -> empty
      Just it -> pure it
  -- Fail in case of a wildcard pattern
  Any -> empty
  App fname p -> do
    f <- retrieveFun fname
    f <$> close p
  Or p1 p2 ->
    close p1 <|> close p2
  Let x e y -> do
    it <- close e
    withLocalEnv $ do
      match x it
      close y
  -- Not sure what to do with the three patterns below.  The intuitive
  -- implementations are given below, but they would not necessarily provide
  -- the desired behavior (especially in case of Fix/Ref).
  Via _ _ -> error "close Via"
  Fix _ -> error "close Fix"
  Rec -> error "close Rec"
--   Via p x -> do
--     it <- close p
--     match x it
--   Fix p ->
--     withFix p $ do
--       close p
--   Rec -> do
--     p <- fixed
--     close p


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
data Cond sym var lvar
  -- | > Check the equality between the two patterns
  = Eq (Pattern sym var lvar) (Pattern sym var lvar)
  -- | > Check if the given predicate is satisfied
  -- | Pred PredName (Pattern sym var lvar)
  | Pred PredName (Pattern sym var lvar)
  -- | > Logical conjunction
  | And (Cond sym var lvar) (Cond sym var lvar)
  -- | > Logical disjunction
  | OrC (Cond sym var lvar) (Cond sym var lvar)
  -- | > Logical negation
  | Neg (Cond sym var lvar)
  -- | > Always True
  | TrueC
  deriving (Show, Eq, Ord)


-- | Check the side condition expression.  Note that `check` does not modify
-- the `Env`ironment.  We keep it in the `MatchT` monad for simplicity.
check
  :: (P.MonadIO m, Eq sym, Ord var, Ord lvar, Show sym, Show var, Show lvar)
  => Cond sym var lvar
  -> MatchT sym var lvar m Bool
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
type Lock sym var lvar = Pattern sym var lvar


-- | Key of a pattern assigns values to the individual variables in the
-- corresponding lock.  Each key has its corresponding lock (makes sense,
-- right?).
type Key sym var = Env sym var


-- | Retrieve the lock of the pattern.  The lock can be used to determine the
-- corresponding indexing structure.
--
-- The function replaces free variables with wildcards, with the exception of
-- local variables, which are not handled.
--
-- TODO: In `Let x e y`, both `x` and `y` should contain no global variables.
-- However, this is currently not enforced in any way.
--
-- TODO: We could also rename bound variables, so that the lock is insensitive
-- to variable names.  (UPDATE: this is not necessarily the best idea,
-- currently we rely on the fact that variables are not renamed).
--
mkLock
  :: (Monad m, Ord var)
  => Pattern sym var lvar
  -> MatchT sym var lvar m (Lock sym var lvar)
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
  LVar v -> error "mkLock LVar: not sure what to do here yet"
  Any -> pure Any
  App fname p -> App fname <$> mkLock p
  Or x y -> Or <$> mkLock x <*> mkLock y
  Let x e y -> Let <$> pure x <*> mkLock e <*> pure y
  Via p x -> Via <$> mkLock p <*> mkLock x
  Fix p -> Fix <$> mkLock p
  Rec -> pure Rec


-- -- | Retrieve the key(s) of the item for the given lock.
-- --
-- -- TODO: the function must be evaluated in a fresh environment.
-- -- TODO: `withLocalGlobalEnv` is not effective if the match fails!
-- --
-- itemKeyFor
--   :: (P.MonadIO m, Eq sym, Ord var, Ord lvar, Show sym, Show var, Show lvar)
--   => I.Item sym
--   -> Lock sym var lvar
--   -> MatchT sym var lvar m (Key sym var)
-- itemKeyFor x lock = withLocalGlobalEnv $ do
--   -- TODO: Since we ignore the item below (result of the match), it may be that
--   -- we will generate several keys which are identical.  This might be a
--   -- problem?  At least from the efficiency point of view.
--   _ <- match lock x
--   S.gets (getL genv)


-- | Retrieve the key(s) of the item for the given lock.
itemKeyFor
  :: (P.MonadIO m, Eq sym, Ord var, Ord lvar, Show sym, Show var, Show lvar)
  => FunSet sym
  -> I.Item sym
  -> Lock sym var lvar
  -> (Key sym var -> m ()) -- ^ Monadic key handler
  -> m ()
itemKeyFor funSet item lock handler = do
  runMatchT funSet $ do
    -- TODO: Since we ignore the item below (result of the match), it may be that
    -- we will generate several keys which are identical.  This might be a
    -- problem?  At least from the efficiency point of view.
    _ <- match lock item
    key <- S.gets (getL genv)
    lift $ handler key


-- | Retrieve the values of the global variables in the lock, thus creating the
-- key corresponding to the lock based on the current environment.
--
-- NOTE: in contrast with `itemKeyFor`, `keyFor` relies on the current
-- environment.
--
keyFor
  :: (Monad m, Ord var)
  => Lock sym var lvar
  -> MatchT sym var lvar m (Key sym var)
keyFor lock = do
  M.fromList <$> mapM
    (\v -> (v,) <$> retrieveVar v)
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
data Rule sym var lvar = Rule
  { antecedents :: [Pattern sym var lvar]
    -- ^ The list of rule's antecedents
  , consequent :: Pattern sym var lvar
    -- ^ The rule's consequent
  , condition :: Cond sym var lvar
  }
  deriving (Show, Eq, Ord)


-- | Apply the deduction rule to the given items.  If the application succeeds,
-- the new chart item is returned.
--
-- The function treats the list of items as ordered and does not try other item
-- permutations when matching them with the `antecedents`.
--
apply
  :: (P.MonadIO m, Eq sym, Ord var, Ord lvar, Show sym, Show var, Show lvar)
  -- => Grammar sym
  => Rule sym var lvar
  -> [Item sym]
  -> MatchT sym var lvar m (Item sym)
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