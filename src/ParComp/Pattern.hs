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

  -- * Pattern
  , Pattern (..)

  -- ** Matching
  , MatchT
  , lift
  , forEach
  , runMatchT
  , match
  , close

  -- * Condition
  , Cond (..)
  , check

  -- * Rule
  , Rule (..)
  , apply

  -- * Indexing (locks and keys)
  , Lock
  , Key
  , mkLock
  , itemKeyFor
  , keyFor
  , locksFor

  -- * Utils
  , pickOne
  ) where


-- import qualified System.Random as R

import           Control.Monad (guard, void, forM)
import           Control.Applicative (Alternative, (<|>), empty)
import           Control.Monad.Trans.Maybe (MaybeT(..))
import qualified Control.Monad.State.Strict as S
import qualified Control.Monad.RWS.Strict as RWS

import qualified Pipes as P

import           Data.Lens.Light

import qualified Data.Text as T
import qualified Data.Set as Set
import qualified Data.Map.Strict as M
import           Data.Maybe (isJust, catMaybes)

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
  -- | > With: pattern match and (then) check the condition
  | With (Pattern sym var lvar) (Cond sym var lvar)
  deriving (Show, Eq, Ord)


-- | Condition expression
--
-- Note that condition expression must contain no free variables, nor wildcard
-- patterns.  This is because side conditions are not matched against items.
data Cond sym var lvar
  -- | > Check the equality between two patterns
  = Eq (Pattern sym var lvar) (Pattern sym var lvar)
  -- | > Check if the given predicate is satisfied
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
  With p c -> globalVarsIn p <> globalVarsInC c


-- | Retrieve the set of global variables in the given pattern.
globalVarsInC :: (Ord var) => Cond sym var lvar -> Set.Set var
globalVarsInC = \case
  Eq p1 p2 -> globalVarsIn p1 <> globalVarsIn p2
  Pred _ p -> globalVarsIn p
  And c1 c2 -> globalVarsInC c1 <> globalVarsInC c2
  OrC c1 c2 -> globalVarsInC c1 <> globalVarsInC c2
  Neg c -> globalVarsInC c
  TrueC -> Set.empty


--------------------------------------------------
-- Pattern matching core
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


-- | Perform the matching computation for each element in the list.  Start each
-- matching from the current state (so that matching computations the
-- individual elements are independent).
forEach
  :: (Monad m)
  => [a]
  -> (a -> MatchT sym var lvar m b)
  -> MatchT sym var lvar m b
forEach xs m = do
  state <- S.get
  choice $ do
    x <- xs
    return $ do
      S.put state
      m x


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


-- | Perform the given patter matching in a local environment, restoring the
-- values of all the local variables at the end.
withLocalEnv
  :: (P.MonadIO m)
  => MatchT sym var lvar m a
  -> MatchT sym var lvar m a
withLocalEnv m = do
  e <- S.gets (getL lenv)
--   mark <- (`mod` 1000) <$> P.liftIO (R.randomIO :: IO Int)
--   P.liftIO $ do
--     putStr ">>> IN: "
--     print mark
  m <|> do
    -- Restore the local environment
    S.modify' (setL lenv e)
--     P.liftIO $ do
--       putStr "<<< OUT: "
--       print mark
    empty


-- | Perform match with the recursive pattern.
withFix
  :: (Monad m)
  => Pattern sym var lvar
  -> MatchT sym var lvar m a
  -> MatchT sym var lvar m a
withFix p m = do
  -- Retrieve the old fix
  oldFix <- S.gets $ getL fix
  -- Register the new fix
  S.modify' $ setL fix (Just p)
  m <|> do
    -- Restore the old fix
    S.modify' $ setL fix oldFix
    empty


-- | Retrieve the fixed recursive pattern.
fixed :: (Monad m) => MatchT sym var lvar m (Pattern sym var lvar)
fixed = do
  mayFix <- S.gets $ getL fix
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


--------------------------------------------------
-- Pattern matching
--------------------------------------------------


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
      -- of the `Or` pattern.  The same applies to local variables.  Perhaps
      -- this is something we could check dynamically, just in case?
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
    (With p c, it) -> do
      match p it
      check c >>= guard
      return it
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
--
-- Note that `close` should not modify the underlying state/environment.
--
-- The behavior of the function is undefined for patterns containing any of the
-- following:
-- * `Via` patterns
-- * recursive patterns (`Fix` / `Rec`)
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
      -- Since `x` should contain only local variables, we can (relatively)
      -- safely match it with `it`
      match x it
      close y
  With p c -> do
    it <- close p
    check c >>= guard
    return it
  -- Not sure what to do with the three patterns below.  The intuitive
  -- implementations are given below, but they would not necessarily provide
  -- the desired behavior (especially in case of Fix/Ref).  In case of `Via`,
  -- the intuitive implementation would require performing the match with
  -- possibly global variables.  We could alternatively perform the @close x@
  -- operation beforehand.
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


-- | Lock determines an indexing structure.
--
-- Each `I.Item` (`Pattern`) can be matched with the `Lock` to produce the
-- corresponding `Key`(s).  These keys then allow to find the item (pattern) in
-- the index corresponding to the lock.
data Lock sym var lvar = Lock
  { lockPatt :: Pattern sym var lvar
    -- ^ The pattern of the lock
  , lockVars :: Set.Set var
    -- ^ Variables pertinent to the lock
  } deriving (Show, Eq, Ord)


-- | Key assigns values to the (global) variables in the corresponding lock.
type Key sym var = Env sym var


-- -- | Retrieve the lock of the pattern.  The lock can be used to determine the
-- -- corresponding indexing structure.
-- --
-- -- The function replaces free variables with wildcards, with the exception of
-- -- local variables, which are not handled.
-- --
-- -- TODO: In `Let x e y`, both `x` and `y` should contain no global variables.
-- -- However, this is currently not enforced in any way.
-- --
-- -- TODO: We could also rename bound variables, so that the lock is insensitive
-- -- to variable names.  (UPDATE: this is not necessarily the best idea,
-- -- currently we rely on the fact that variables are not renamed).
-- --
-- mkLock
--   :: (Monad m, Ord var)
--   => Pattern sym var lvar
--   -> MatchT sym var lvar m (Lock sym var lvar)
-- mkLock = \case
--   Const x -> pure $ Const x
--   Pair x y -> Pair <$> mkLock x <*> mkLock y
--   Union up -> case up of
--     Left lp  -> Union .  Left <$> mkLock lp
--     Right rp -> Union . Right <$> mkLock rp
--   Var v ->
--     lookupVar v >>= \case
--       Just it -> pure $ Var v
--       Nothing -> pure Any
--   LVar v -> error "mkLock LVar"
--   Any -> pure Any
--   App fname p -> App fname <$> mkLock p
--   Or x y -> Or <$> mkLock x <*> mkLock y
--   Let x e y -> Let <$> pure x <*> mkLock e <*> pure y
--   Via p x -> Via <$> mkLock p <*> mkLock x
--   Fix p -> Fix <$> mkLock p
--   Rec -> pure Rec


-- | Variables bound in the given pattern
boundVars
  :: (Monad m, Ord var)
  => Pattern sym var lvar
  -> MatchT sym var lvar m (Set.Set var)
boundVars p =
  fmap (Set.fromList . catMaybes) $
    forM (Set.toList $ globalVarsIn p) $ \v ->
      lookupVar v >>= \case
        Just _  -> pure $ Just v
        Nothing -> pure Nothing


-- boundVars = \case
--   Const x -> pure Set.empty
--   Pair x y -> (<>) <$> boundVars x <*> boundVars y
--   Union up -> case up of
--     Left lp  -> boundVars lp
--     Right rp -> boundVars rp
--   Var v ->
--     lookupVar v >>= \case
--       Just it -> pure $ Set.singleton v
--       Nothing -> pure Set.empty
--   LVar v -> error "boundVars LVar"
--   Any -> pure Set.empty
--   App _ p -> boundVars p
--   Or x y -> (<>) <$> boundVars x <*> boundVars y
--   Let _ e _ -> boundVars e
--   Via p x -> (<>) <$> boundVars p <*> boundVars x
--   Fix p -> boundVars p
--   Rec -> pure Set.empty
--   -- NOTE: the condition should contain no separate variable?
--   With p _ -> error "boundVars With: not sure?"
--     -- boundVars p


-- | Retrieve the lock of the pattern.  The lock can be used to determine the
-- corresponding indexing structure.
mkLock
  :: (Monad m, Ord var)
  => Pattern sym var lvar
  -> MatchT sym var lvar m (Lock sym var lvar)
mkLock p = Lock p <$> boundVars p


-- | Generate all the locks for the given rule.
locksFor
  :: (P.MonadIO m, Eq sym, Ord var)
  => FunSet sym
    -- ^ Set of registered functions
  -> Rule sym var lvar
  -> P.ListT m (Lock sym var lvar)
locksFor funSet rule  =
  P.Select $ _locksFor funSet rule P.yield


-- | Generate all the locks for the given rule.
_locksFor
  :: (P.MonadIO m, Eq sym, Ord var)
  => FunSet sym
    -- ^ Set of registered functions
  -> Rule sym var lvar
  -> (Lock sym var lvar -> m ())  -- ^ Monadic lock handler
  -> m ()
_locksFor funSet rule handler = do
  runMatchT funSet $ do
    forEach (pickOne (antecedents rule)) $ \(main, rest) -> do
      dummyMatch main
      case rest of
        [other] -> do
          lock <- mkLock other
          lift $ handler lock
        _ -> error "locksFor: doesn't handle non-binary rules"


-- | Retrieve the key(s) of the item for the given lock.
itemKeyFor
  :: (P.MonadIO m, Eq sym, Ord var, Ord lvar, Show sym, Show var, Show lvar)
  => FunSet sym
  -> I.Item sym
  -> Lock sym var lvar
  -> P.ListT m (Key sym var)
itemKeyFor funSet item lock = do
  P.Select $ _itemKeyFor funSet item lock P.yield


-- | Retrieve the key(s) of the item for the given lock.
_itemKeyFor
  :: (P.MonadIO m, Eq sym, Ord var, Ord lvar, Show sym, Show var, Show lvar)
  => FunSet sym
  -> I.Item sym
  -> Lock sym var lvar
  -> (Key sym var -> m ()) -- ^ Monadic key handler
  -> m ()
_itemKeyFor funSet item lock handler = do
  runMatchT funSet $ do
    -- TODO: Since we ignore the item below (result of the match), it may be
    -- that we will generate several keys which are identical.  This may be a
    -- problem (or not) from the efficiency point of view.
    _ <- match (lockPatt lock) item
    key <- S.gets (getL genv)
    lift . handler $ M.restrictKeys key (lockVars lock)


-- -- | Retrieve the values of the global variables in the lock, thus creating the
-- -- key corresponding to the lock based on the current environment.
-- --
-- -- NOTE: in contrast with `itemKeyFor`, `keyFor` relies on the current
-- -- environment.
-- --
-- keyFor
--   :: (Monad m, Ord var)
--   => Lock sym var lvar
--   -> MatchT sym var lvar m (Key sym var)
-- keyFor lock = do
--   M.fromList <$> mapM
--     (\v -> (v,) <$> retrieveVar v)
--     (Set.toList $ globalVarsIn lock)


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
  M.fromList . catMaybes <$> mapM getVar
    (Set.toList $ lockVars lock)
  where
    getVar v = do
      lookupVar v >>= \case
        Nothing -> pure Nothing
        Just it -> pure (Just (v, it))


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
-- Utils
--------------------------------------------------


-- | Return subsets of the given size
subsets :: Int -> [a] -> [[a]]
subsets 0 _ = [[]]
subsets k xs = do
  (x, rest) <- pickOne xs
  subset <- subsets (k - 1) rest
  return $ x : subset


-- | All possible ways of picking one element from the (non-empty) list
pickOne :: [a] -> [(a, [a])]
pickOne [] = []
pickOne (x:xs) =
  here : there
  where
    here = (x, xs)
    there = do
      (y, ys) <- pickOne xs
      return (y, x:ys)


-- | @choice ps@ tries to apply the actions in the list @ps@ in order, until
-- one of them succeeds. Returns the value of the succeeding action.
choice :: Alternative f => [f a] -> f a
choice = foldr (<|>) empty


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
