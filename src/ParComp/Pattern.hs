{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}


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
  , MatchingStrategy (..)
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
  -- ** Directional rule
  , DirRule (..)
  , directRule

  -- * Indexing (locks and keys)
  , Lock (..)
  , Key
  , mkLock
  , groupByTemplate
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

import           Data.String (IsString)
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
  deriving (Show, Eq, Ord, IsString)


-- | Predicate name
newtype PredName = PredName {unPredName :: T.Text}
  deriving (Show, Eq, Ord, IsString)


-- | Record with registered grammar functions
--
-- Note that the registered functions can be multi-argument, since `Item`
-- allows to encode tuples.
--
data FunSet sym = FunSet
  { predMap :: M.Map PredName (Item sym -> Bool)
    -- ^ Named predicate functions.
  , funMap :: M.Map FunName (Item sym -> [Item sym])
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
  -- | > Mapping: match the pattern with the item and apply the function to the
  -- result.
  | Map FunName (Pattern sym var lvar)
  -- | > Application: apply the function to the item before pattern matching.
  | App FunName
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
-- Note that condition expression should not contain no free variables, nor
-- wildcard patterns.  This is because side conditions are not matched against
-- items.
data Cond sym var lvar
  -- | > Check the equality between two patterns
  = Eq (Pattern sym var lvar) (Pattern sym var lvar)
  -- | > Check if the given predicate is satisfied
  | Pred PredName (Pattern sym var lvar)
  -- | > Logical conjunction
  | And (Cond sym var lvar) (Cond sym var lvar)
  -- | > Logical disjunction
  | OrC (Cond sym var lvar) (Cond sym var lvar)
  -- | > Always True
  | TrueC
  -- NB: Logical negation would significantly complicate automatic indexing in
  -- general and lazy matching in particular.
  -- -- | > Logical negation
  -- | Neg (Cond sym var lvar)
  deriving (Show, Eq, Ord)


-- | Retrieve the set of global variables bound in the pattern.
--
-- A variable is bound in the pattern if it gets bound during matching of the
-- pattern with an item.
--
-- Assumption: In case of the `Or` pattern, we assume that both branches
-- contain the same set of global variables (this is currently checked at
-- runtime).
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
  Map _ p -> globalVarsIn p
  App _ -> Set.empty
  Or x y ->
    let xs = globalVarsIn x
        ys = globalVarsIn y
     in if xs == ys
           then xs
           else error "globalVarsIn: different sets of variables in Or"
  -- Below, ignore `x` and `y`, which should contain local variables only
  Let x e y -> globalVarsIn e
  Via p x -> globalVarsIn p <> globalVarsIn x
  Fix p -> globalVarsIn p
  Rec -> Set.empty
  -- Below, we don't inspect the condition, since it doesn't bind additional
  -- variables during matching
  With p _ -> globalVarsIn p


-- -- | Retrieve the set of global variables in the given pattern.
-- globalVarsInC :: (Ord var) => Cond sym var lvar -> Set.Set var
-- globalVarsInC = \case
--   Eq p1 p2 -> globalVarsIn p1 <> globalVarsIn p2
--   Pred _ p -> globalVarsIn p
--   And c1 c2 -> globalVarsInC c1 <> globalVarsInC c2
--   OrC c1 c2 -> globalVarsInC c1 <> globalVarsInC c2
--   Neg c -> globalVarsInC c
--   TrueC -> Set.empty


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
  , _penv :: Env sym (Pattern sym var lvar)
    -- ^ Pattern binding environment (only relevant for lazy matching)
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
runMatchT funSet m = void $
  RWS.evalRWST (P.runListT m) funSet
    (PMState M.empty M.empty Nothing M.empty)


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


-- | Look up the value bound to the given pattern.
lookupPatt
  :: (Monad m, Ord sym, Ord var, Ord lvar)
  => Pattern sym var lvar
  -> MatchT sym var lvar m (Maybe (Item sym))
lookupPatt p = S.gets $ M.lookup p . getL penv


-- | Bind the item value to the given pattern.
bindPatt
  :: (Monad m, Ord sym, Ord var, Ord lvar)
  => Pattern sym var lvar
  -> Item sym
  -> MatchT sym var lvar m ()
bindPatt p it = do
  mayIt <- S.lift $ S.gets (M.lookup p . getL penv)
  case mayIt of
    Nothing -> S.modify' . modL penv $ M.insert p it
    Just it' -> guard $ it == it'


-- | Perform two alternative matches.  The environment is restored to its
-- original state after the first match.
alt
  :: (P.MonadIO m)
  => MatchT sym var lvar m a
  -> MatchT sym var lvar m a
  -> MatchT sym var lvar m a
alt m1 m2 = do
  state <- S.get
  m1 <|> do
    S.put state
    m2


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
  -> MatchT sym var lvar m (Item sym -> [Item sym])
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


-- | Pattern matching strategy
data MatchingStrategy
  = Strict
  -- | Strict matching requires that, whenever a `Cond`ition is encountered, or
  -- a function `App`lication, all the variables necessary to their evaluation
  -- are already bound.  This should be considered as the default matching
  -- strategy.
  | Lazy
  -- | Lazy pattern matching can be performed in an environment where not all
  -- variables that are necessary to perform the evaluation are bound.  As a
  -- result of lazy matching, the pattern binding environment provides the
  -- values of selected patterns, which could not have been evaluated so far.
  deriving (Show, Eq, Ord)


-- | Match the pattern with the given item expression.  The resulting item is
-- not necessarily the same as the input item due to the `Let` pattern
-- construction, which allows to change the matching result.
match
  :: (P.MonadIO m, Show sym, Show var, Show lvar, Ord sym, Ord var, Ord lvar)
  => MatchingStrategy
  -> Pattern sym var lvar
  -> Item sym
  -> MatchT sym var lvar m (Item sym)
match ms pt it =
  case (pt, it) of
    (Const it', it) -> do
      guard $ it' == it
      return it
    (Pair p1 p2, I.Pair i1 i2) ->
      I.Pair <$> match ms p1 i1 <*> match ms p2 i2
    (Union pu, I.Union iu) ->
      case (pu, iu) of
        (Left pl, Left il) ->
          I.Union . Left <$> match ms pl il
        (Right pr, Right ir) ->
          I.Union . Right <$> match ms pr ir
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
    (Map fname p, it) -> do
      f <- retrieveFun fname
      let strict = do
            x <- close p
            it' <- each $ f x
            guard $ it' == it
            return it
      case ms of
        Strict -> strict
        Lazy -> do
          closeable p >>= \case
            True -> strict
            False -> do
              bindPatt p it
              return it
    (App fname, it) -> do
      f <- retrieveFun fname
      each $ f it
    (Or p1 p2, it) -> do
      -- NOTE: we retrieve and then restore the entire state, even though the
      -- fixed recursive pattern should never escape its syntactic scope so, in
      -- theory, it should not change between the first and the second branch
      -- of the `Or` pattern.  The same applies to local variables.  Perhaps
      -- this is something we could check dynamically, just in case?
      match ms p1 it `alt` match ms p2 it
--       state <- S.get
--       match ms p1 it <|> do
--         S.put state
--         match ms p2 it
    (Let x e y, it) -> do
      it' <- match ms e it
      withLocalEnv $ do
        match ms x it'
        close y
    (Via p x, it) -> do
      it' <- match ms p it
      match ms x it'
    (Fix p, it) -> do
      withFix p $ do
        match ms p it
    (Rec, it) -> do
      p <- fixed
      match ms p it
    (With p c, it) -> do
      match ms p it
      check ms c >>= guard
--       flag <- check ms c
--       e <- S.gets $ getL penv
--       P.liftIO $ do
--         putStr "!!! Lazy check: "
--         print c
--         putStr "!!! Pattern env: "
--         print e
--         putStr "!!! Result: "
--         print flag
--       guard flag
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
--
-- There is a subtle interaction between `close` and lazy matching.  It is
-- possible to `close` a pattern that actually contains free variables,
-- provided that the pattern binding environment provides the values of the
-- sub-patterns containing those variables (such variables are thus not truly
-- free, we don't know their value, but we know the values of certain patterns
-- that contain them).
close
  :: (P.MonadIO m, Ord sym, Ord var, Ord lvar, Show sym, Show var, Show lvar)
  => Pattern sym var lvar
  -> MatchT sym var lvar m (Item sym)
close p =
  lookupPatt p >>= \case
    Just it -> pure it
    Nothing -> byCase
  where
    byCase = case p of
      Const it -> pure it
      Pair p1 p2 -> I.Pair <$> close p1 <*> close p2
      Union up ->
        case up of
          Left lp  -> I.Union .  Left <$> close lp
          Right rp -> I.Union . Right <$> close rp
      -- Fail (silently) if variable x not bound
      Var v -> retrieveVar v
--         lookupVar v >>= \case
--           Just it -> pure it
--           Nothing -> error $ "close: Var not bound"
      LVar v ->
        lookupLVar v >>= \case
          Just it -> pure it
          -- Local variables have syntactic scope, so the following should
          -- never happen
          Nothing -> error $ "close: LVar not bound"
          -- Nothing -> empty
      -- Fail in case of a wildcard pattern
      Any -> empty
      Map fname p -> do
        f <- retrieveFun fname
        x <- close p
        y <- each $ f x
        return y
      App fname -> error "close App"
      Or p1 p2 ->
        -- NB: `alt` is not necessary, because `close` doesn't modify the state
        close p1 <|> close p2
      Let x e y -> do
        it <- close e
        withLocalEnv $ do
          -- Since `x` should contain only local variables, we can (relatively)
          -- safely match it with `it`
          match Strict x it
          close y
      With p c -> do
        it <- close p
        check Strict c >>= guard
        return it
      -- Not sure what to do with the three patterns below.  The intuitive
      -- implementations are given below, but they would not necessarily
      -- provide the desired behavior (especially in case of Fix/Ref).  In case
      -- of `Via`, the intuitive implementation would require performing the
      -- match with possibly global variables.  We could alternatively perform
      -- the @close x@ operation beforehand.  I guess we need some good
      -- examples showing what to do with those cases (if anything).
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


-- | Is the given pattern possible to close?
closeable
  :: (Monad m, Eq sym, Ord var, Ord lvar)
  => Pattern sym var lvar
  -> MatchT sym var lvar m Bool
closeable = \case
  Const it -> pure True
  Pair p1 p2 -> (&&) <$> closeable p1 <*> closeable p2
  Union up ->
    case up of
      Left lp  -> closeable lp
      Right rp -> closeable rp
  Var v ->
    lookupVar v >>= \case
      Just it -> pure True
      Nothing -> pure False
  LVar v ->
    lookupLVar v >>= \case
      Just it -> pure True
      Nothing -> pure False
  Any -> pure False
  Map _ p -> closeable p
  App _ -> pure False
  Or p1 p2 -> do
    c1 <- closeable p1
    c2 <- closeable p2
    -- NB: The notion of being `closeable` relies on the status of global
    -- variables (bound or not) in the pattern.  We assume that the set of
    -- global variables is the same in both `Or` branches.
    if c1 == c2
       then return c1
       else error "closeable Or: different results for different branches"
  Let x e y -> closeable e
  With p c -> (&&) <$> closeable p <*> closeableC c
  Via _ _ -> error "closeable Via"
  Fix _ -> error "closeable Fix"
  Rec -> error "closeable Rec"


-- | Is the given side condition possible to close?
closeableC
  :: (Monad m, Eq sym, Ord var, Ord lvar)
  => Cond sym var lvar
  -> MatchT sym var lvar m Bool
closeableC = \case
  Eq px py -> (&&) <$> closeable py <*> closeable py
  Pred _ p -> closeable p
  And cx cy -> (&&) <$> closeableC cx <*> closeableC cy
  -- TODO: what about the line below?
  OrC cx cy -> undefined
  -- OrC cx cy -> (&&) <$> closeableC cx <*> closeableC cy
  -- Neg c -> closeableC c
  TrueC -> pure True


--------------------------------------------------
-- Side conditions
--------------------------------------------------


-- | Check the side condition expression. 
--
-- NB: `check` does not modify the underlying state in case of `Strict`
-- matching.
check
  :: (P.MonadIO m, Ord sym, Ord var, Ord lvar, Show sym, Show var, Show lvar)
  => MatchingStrategy
  -> Cond sym var lvar
  -> MatchT sym var lvar m Bool
check Strict cond =
  case cond of
    Eq px py  -> (==) <$> close px <*> close py
    Pred pname p -> retrievePred pname <*> close p
    And cx cy -> (&&) <$> check Strict cx <*> check Strict cy
    OrC cx cy -> (||) <$> check Strict cx <*> check Strict cy
    -- Neg c -> not <$> check Strict c
    TrueC -> pure True
check Lazy cond =
  case cond of
    Eq px py -> do
      cx <- closeable px
      cy <- closeable py
      case (cx, cy) of
        (True, True) -> (==) <$> close px <*> close py
        (True, False) -> do
          bindPatt py =<< close px
          -- (*) See `Neg` below
          return True
        (False, True) -> do
          bindPatt px =<< close py
          -- (*) See `Neg` below
          return True
        (False, False) -> error "check Lazy: both patterns not closeable"
    Pred pname p -> do
      pred <- retrievePred pname
      closeable p >>= \case
        True  -> pred <$> close p
        -- False -> error "check Lazy: doesn't support not closeable Pred yet"
        False -> do
          -- NB: We bind the pattern (see also `getLockVarsC`) to the unit
          -- value to indicate that the value of the condition is True.
          bindPatt (With (Const I.Unit) (Pred pname p)) I.Unit
          -- (*) See `Neg` below
          return True
    And cx cy -> (&&) <$> check Lazy cx <*> check Lazy cy
    -- Similarly as in `getLockVarsC`, we take the alternative in case of `Or`
    OrC cx cy -> check Lazy cx `alt` check Lazy cy
    -- NB: The line below (commented out) is probably incorrect. In case of
    -- Lazy matching, some embedded check may succeed simply because we can't
    -- tell yet if it succeeds or not (see (*) above).  Hence, negating the
    -- embedded result doesn't make sense.
    -- Neg c -> not <$> check Lazy c
    TrueC -> pure True


--------------------------------------------------
-- Deduction rule
--------------------------------------------------


-- | Single deduction rule
data Rule sym var lvar = Rule
  { antecedents :: [Pattern sym var lvar]
    -- ^ The list of rule's antecedents
  , consequent :: Pattern sym var lvar
    -- ^ The rule's consequent
  , condition :: Cond sym var lvar
    -- ^ The rule's side condition
  } deriving (Show, Eq, Ord)


-- | Apply the deduction rule to the given items.  If the application succeeds,
-- the new chart item is returned.
--
-- The function treats the list of items as ordered and does not try other item
-- permutations when matching them with the `antecedents`.
--
apply
  :: (P.MonadIO m, Ord sym, Ord var, Ord lvar, Show sym, Show var, Show lvar)
  -- => Grammar sym
  => Rule sym var lvar
  -> [Item sym]
  -> MatchT sym var lvar m (Item sym)
apply Rule{..} items = do
  guard $ length antecedents == length items
  -- Match antecedents with the corresponding items
  mapM_
    (uncurry $ match Strict)
    (zip antecedents items)
  -- Make sure the side condition holds
  check Strict condition >>= guard
  -- Convert the consequent to the resulting item
  close consequent


--------------------------------------------------
-- Directional rule
--------------------------------------------------


-- | Directional rule
data DirRule sym var lvar = DirRule
  { mainAnte :: Pattern sym var lvar
    -- ^ The main antecedent pattern
  , otherAntes :: [Pattern sym var lvar]
    -- ^ The other antecedent patterns
  , dirConseq :: Pattern sym var lvar
    -- ^ The rule's consequent
  } deriving (Show, Eq, Ord)


-- | Compile the rule to the list of directional rules. 
directRule :: Rule sym var lvar -> [DirRule sym var lvar]
directRule rule = do
  (main, rest) <- pickOne $ antecedents rule
  case rest of
    [other] -> return $ DirRule
      { mainAnte = main
      , otherAntes = [With other $ condition rule]
      , dirConseq = consequent rule
      }
    _ -> error "directRule: doesn't handle non-binary rules"


-- -- | Apply the directional rule.
-- applyDir
--   :: (P.MonadIO m, Eq sym, Ord var, Ord lvar, Show sym, Show var, Show lvar)
--   => DirRule sym var lvar
--   -> Item sym
--   -> [Item sym]
--   -> MatchT sym var lvar m (Item sym)


--------------------------------------------------
-- Indexing
--------------------------------------------------


-- | Lock determines the indexing structure.
--
-- Each `I.Item` (`Pattern`) can be matched with the `Lock` to produce the
-- corresponding `Key`(s).  These keys then allow to find the item (pattern) in
-- the index corresponding to the lock.
data Lock sym var lvar = Lock
  { lockTemplate :: Pattern sym var lvar
    -- ^ Lock's template
  , lockVars :: Set.Set (Pattern sym var lvar)
    -- ^ Relevant variables and patterns, whose values need to be specified in
    -- the corresponding key
  -- , lockVars :: Set.Set var
  } deriving (Show, Eq, Ord)


-- | Key assigns values to the variables (and patterns) in the corresponding
-- lock (in `lockVars`, more precisely).
type Key sym var lvar = M.Map (Pattern sym var lvar) (I.Item sym)


-- | Retrieve the bound variables and patterns for the lock.
getLockVars
  :: (Monad m, Ord sym, Ord var, Ord lvar)
  => Pattern sym var lvar
  -> MatchT sym var lvar m (Set.Set (Pattern sym var lvar))
getLockVars = \case
  Const _ -> pure Set.empty
  Pair p1 p2 -> (<>) <$> getLockVars p1 <*> getLockVars p2
  Union up -> case up of
    Left p -> getLockVars p
    Right p -> getLockVars p
  Var v ->
    lookupVar v >>= \case
      Just it -> pure $ Set.singleton (Var v)
      Nothing -> pure Set.empty
  LVar v -> error "getLockVars: encountered local variable!"
  Any -> pure Set.empty
  Map fn p -> do
    closeable p >>= \case
      True -> pure $ Set.singleton (Map fn p)
      False -> pure Set.empty
  App _ -> pure Set.empty
  Or x y -> do
    -- NB: Since we assume that both @x@ and @y@ contain the same global
    -- variables (see `globalVarsIn`), @getLockVars x@ and @getLockVars y@
    -- should yield the same result.
    s1 <- getLockVars x
    s2 <- getLockVars y
    if s1 == s2
       then return s1
       else error "getLockVars Or: different results for different branches"
  -- Below, ignore `x` and `y`, which should contain local variables only
  Let x e y -> getLockVars e
  Via p x -> (<>) <$> getLockVars p <*> getLockVars x
  Fix p -> getLockVars p
  Rec -> pure Set.empty
  With p c -> (<>) <$> getLockVars p <*> getLockVarsC c


-- | Retrieve the bound variables and patterns for the lock.
getLockVarsC
  :: (Monad m, Ord sym, Ord var, Ord lvar)
  => Cond sym var lvar
  -> MatchT sym var lvar m (Set.Set (Pattern sym var lvar))
getLockVarsC = \case
  Eq px py -> do
    cx <- closeable px
    cy <- closeable py
    case (cx, cy) of
      (True, False) -> pure $ Set.singleton px
      (False, True) -> pure $ Set.singleton py
      _ -> pure Set.empty
  Pred pn p ->
    closeable p >>= \case
      -- NB: Below, we cast the predicate to a `With` pattern.  This is because
      -- currently the lock only supports patterns, and not conditions.
      True -> pure $ Set.singleton (With (Const I.Unit) (Pred pn p))
      False -> pure Set.empty
  And c1 c2 -> (<>) <$> getLockVarsC c1 <*> getLockVarsC c2
  -- NB: `alt` is not necessary since `getLockVar` doesn't modify the state
  OrC c1 c2 -> getLockVarsC c1 <|> getLockVarsC c2
  -- Neg c -> getLockVarsC c
  TrueC -> pure Set.empty


-- | Retrieve the lock of the pattern.  The lock can be used to determine the
-- corresponding indexing structure.
mkLock
  :: (Monad m, Ord sym, Ord var, Ord lvar)
  => Pattern sym var lvar
  -> MatchT sym var lvar m (Lock sym var lvar)
mkLock p =
  Lock p <$> getLockVars p


-- | Generate all the locks for the given rule.
locksFor
  :: (P.MonadIO m, Ord sym, Ord var, Ord lvar)
  => FunSet sym
    -- ^ Set of registered functions
  -> DirRule sym var lvar
  -> P.ListT m (Lock sym var lvar)
locksFor funSet rule  =
  P.Select $ _locksFor funSet rule P.yield


-- | Generate all the locks for the given rule.
_locksFor
  :: (P.MonadIO m, Ord sym, Ord var, Ord lvar)
  => FunSet sym
    -- ^ Set of registered functions
  -> DirRule sym var lvar
  -> (Lock sym var lvar -> m ())  -- ^ Monadic lock handler
  -> m ()
_locksFor funSet rule handler = do
  runMatchT funSet $ do
    -- forEach (pickOne (antecedents rule)) $ \(main, rest) -> do
    dummyMatch $ mainAnte rule
    case otherAntes rule of
      [other] -> do
        lock <- mkLock other
        lift $ handler lock
      _ -> error "locksFor: doesn't handle non-binary rules"


-- -- | Retrieve the key(s) of the item for the given lock.
-- itemKeyFor
--   :: (P.MonadIO m, Ord sym, Ord var, Ord lvar, Show sym, Show var, Show lvar)
--   => FunSet sym
--   -> I.Item sym
--   -> Lock sym var lvar
--   -> P.ListT m (Key sym var lvar)
-- itemKeyFor funSet item lock = do
--   P.Select $ _itemKeyFor funSet item lock P.yield
-- 
-- 
-- -- | Retrieve the key(s) of the item for the given lock.
-- _itemKeyFor
--   :: (P.MonadIO m, Ord sym, Ord var, Ord lvar, Show sym, Show var, Show lvar)
--   => FunSet sym
--   -> I.Item sym
--   -> Lock sym var lvar
--   -> (Key sym var lvar -> m ()) -- ^ Monadic key handler
--   -> m ()
-- _itemKeyFor funSet item lock handler = do
--   runMatchT funSet $ do
--     match Lazy (lockTemplate lock) item
--     key <- keyFor lock
--     lift $ handler key
-- 
-- 
-- -- | Retrieve the values of the global variables in the lock, thus creating the
-- -- key corresponding to the lock based on the current environment.
-- keyFor
--   :: (P.MonadIO m, Ord sym, Ord var, Ord lvar, Show sym, Show var, Show lvar)
--   => Lock sym var lvar
--   -> MatchT sym var lvar m (Key sym var lvar)
-- keyFor lock = do
--   let ps = Set.toList $ lockVars lock
--   fmap M.fromList . forM ps $ \p -> do
-- --     P.liftIO $ do
-- --       putStr "%%% KEY_FOR: "
-- --       print p
--     it <- close p
--     return (p, it)


-- | Group the set of locks by their templates.  Each group in the output list
-- will have the same `lockTemplate`.
groupByTemplate 
  :: (Ord sym, Ord var, Ord lvar)
  => [Lock sym var lvar]
  -> [[Lock sym var lvar]]
groupByTemplate locks = M.elems . M.fromListWith (<>) $ do
  lock <- locks
  return (lockTemplate lock, [lock])


-- | Retrieve the key(s) of the item for the given set of locks with the same
-- template.
itemKeyFor
  :: (P.MonadIO m, Ord sym, Ord var, Ord lvar, Show sym, Show var, Show lvar)
  => FunSet sym
  -> I.Item sym
  -> [Lock sym var lvar]
  -> P.ListT m (Lock sym var lvar, Key sym var lvar)
itemKeyFor funSet item lockGroup = do
  P.Select $
    _itemKeyFor funSet item lockGroup $
      \lock key -> P.yield (lock, key)


-- | Retrieve the key(s) of the item for the given lock.
_itemKeyFor
  :: (P.MonadIO m, Ord sym, Ord var, Ord lvar, Show sym, Show var, Show lvar)
  => FunSet sym
  -> I.Item sym
  -> [Lock sym var lvar]
  -> (Lock sym var lvar -> Key sym var lvar -> m ()) -- ^ Monadic key handler
  -> m ()
_itemKeyFor funSet item lockGroup handler = do
  runMatchT funSet $ do
    match Lazy groupTemplate item
    forEach lockGroup $ \lock -> do
      key <- keyFor $ lockVars lock
      lift $ handler lock key
  where
    groupTemplate =
      case Set.toList groupTemplates of
        [template] -> template
        xs -> error $
          "itemKeyFor: expected one lock template, got " ++ show (length xs)
    groupTemplates = Set.fromList $ do
      lock <- lockGroup
      return (lockTemplate lock)


-- | Retrieve the values of the global variables in the lock, thus creating the
-- key corresponding to the lock based on the current environment.
keyFor
  :: (P.MonadIO m, Ord sym, Ord var, Ord lvar, Show sym, Show var, Show lvar)
  => Set.Set (Pattern sym var lvar)
    -- ^ Lock variables
  -> MatchT sym var lvar m (Key sym var lvar)
keyFor vars = do
  let ps = Set.toList vars
  fmap M.fromList . forM ps $ \p -> do
    it <- close p
    return (p, it)


--------------------------------------------------
-- Utils
--------------------------------------------------


-- | TODO: add types
each :: (Monad m) => [a] -> P.ListT m a
each = P.Select . P.each


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
