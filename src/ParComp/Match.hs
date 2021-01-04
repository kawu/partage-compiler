{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}


-- | Pattern matching

-- TODO: Rename as `ParComp.Patt.Match`?


module ParComp.Match
  ( MatchT
  , runMatchT
  , lift
  , isMatch

  , match
  , eval
  , check

  -- * Provisional
  , fromItem
  , runCompile
  , runCompileTy
  , runCompileTy2
  ) where


import           Control.Monad (guard, void, forM_, forM)
import qualified Control.Monad.RWS.Strict as RWS
import           Control.Applicative (Alternative, (<|>), empty)

import qualified Pipes as P
import qualified Pipes.Prelude as P

import           Data.Lens.Light

import qualified Data.Text as T
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import qualified Data.Primitive.Array as A

import qualified ParComp.Patt.Core as C
import           ParComp.Patt.Core
  ( Term (..), Item (..), Var (..), Fun (..), PattFun(..)
  , Op (..), Cond (..), Patt (..)
  )
import           ParComp.Patt.Typed (Ty (..), IsItem (..))


--------------------------------------------------
-- Pattern matching core
--------------------------------------------------


-- | Variable binding environment
type Env v = M.Map v Item


-- | Pattern matching state
data PMState = PMState
  { _genv :: Env Var
    -- ^ Variable binding environment
  , _varGenIx :: Int
    -- ^ Variable index used for fresh variable generation
  }
$( makeLenses [''PMState] )


-- -- | The set of registered functions
-- newtype FunSet = FunSet
--   { funMap :: M.Map FunName (Item -> [Item])
--     -- ^ The set of registered item->item functions; the result type is [Item]
--     -- to allow for non-determinism
--   }


-- | Pattern matching monad transformer
type MatchT m a =
  P.ListT (RWS.RWST () () PMState m) a


-- | Empty state, with no variable bindings
emptyState :: PMState
emptyState = PMState M.empty 0


-- | Lift the computation in the inner monad to `MatchT`.
lift :: (Monad m) => m a -> MatchT m a
lift = RWS.lift . RWS.lift


-- | Perform the matching computation for each element in the list.  Start each
-- matching from the current state (so that matching computations the individual
-- elements are independent).
forEach
  :: (Monad m)
  => [a]
  -> (a -> MatchT m b)
  -> MatchT m b
forEach xs m = do
  state <- RWS.get
  choice $ do
    x <- xs
    return $ do
      RWS.put state
      m x


-- | Perform two alternative matches.  The environment is restored to its
-- original state after the first match.
alt
  :: (P.MonadIO m)
  => MatchT m a
  -> MatchT m a
  -> MatchT m a
alt m1 m2 = do
  state <- RWS.get
  m1 <|> do
    RWS.put state
    m2


-- -- | Perform pattern matching in a clear environment.
-- withClearEnv
--   :: (P.MonadIO m)
--   => MatchT m a
--   -> MatchT m a
-- withClearEnv m = do
--   e <- RWS.get
--   RWS.put emptyState
--   -- The second branch of the alternative makes sure to restore the environment
--   -- even if the first branch fails; not sure it's completely necessary, though
--   (m <* RWS.put e) <|> (RWS.put e >> empty)


-- | Run pattern matching computation with the underlying functions and
-- predicates.
runMatchT
  :: (Monad m)
  => MatchT m a
  -> m ()
runMatchT m = void $
  RWS.evalRWST (P.runListT m) ()
    emptyState


-- | Generate a fresh variable
freshVar :: (Monad m) => MatchT m Var
freshVar = do
  ix <- RWS.gets $ getL varGenIx
  let newVar = V $ T.pack (show ix)
      _MAXVAR = 10 ^ 9  -- NB: could use `maxBound` instead
  RWS.modify' $ modL varGenIx (\x -> (x `mod` _MAXVAR) + 1)
  lookupVar newVar >>= \case
    Nothing -> return newVar
    Just _  -> freshVar


-- | Look up the value assigned to the global variable.
lookupVar
  :: (Monad m)
  => Var
  -> MatchT m (Maybe Item)
lookupVar v = RWS.gets $ M.lookup v . getL genv


-- | Retrieve the value bound to the given variable.
retrieveVar
  :: (Monad m)
  => Var
  -> MatchT m Item
retrieveVar v =
  lookupVar v >>= \case
    Nothing -> empty
    Just it -> return it


-- | Bind the item to the given variable.  If the variable is already bound,
-- make sure that the new item is equal to the old one.
bindVar
  :: (Monad m)
  => Var
  -> Item
  -> MatchT m ()
bindVar v it = do
  mayIt <- RWS.gets (M.lookup v . getL genv)
  case mayIt of
    Nothing -> RWS.modify' . modL genv $ M.insert v it
    Just it' -> guard $ it == it'


-- | Discard (unbind) the variable.
ditchVar
  :: (Monad m)
  => Var
  -> MatchT m ()
ditchVar v = do
  RWS.modify' . modL genv $ M.delete v


--  -- | Retrieve the function with a given name.  The function with the name must
--  -- exist, otherwise `retrieveFun` thorws an error.
--  retrieveFun
--    :: (Monad m)
--    => FunName
--    -> MatchT m (Item -> [Item])
--  retrieveFun funName = do
--    mayFun <- RWS.gets (M.lookup funName . getL funMap)
--    case mayFun of
--      Nothing -> error $ concat
--        [ "retrieveFun: function with name '"
--        , T.unpack $ unFunName funName
--        , "' does not exist"
--        ]
--      Just fun -> return fun


--------------------------------------------------
-- High-level interface
--------------------------------------------------


-- | Convert `MatchT` to a regular list (non-idiomatic use).
toListM :: (P.MonadIO m) => MatchT (P.Producer a m) a -> m [a]
toListM = P.toListM . P.enumerate . toListT


-- | Convert `MatchT` to `P.ListT.
toListT :: (P.MonadIO m) => MatchT (P.Producer a m) a -> P.ListT m a
toListT m = do
  P.Select $
    _toListT m P.yield


-- | Lower-level handler-based `toListT`.
_toListT
  :: (P.MonadIO m)
  => MatchT m a
  -> (a -> m ()) -- ^ Monadic handler
  -> m ()
_toListT m h =
  runMatchT $ do
    x <- m
    lift $ h x


-- | Check if the pattern matches with the given item.
isMatch :: (P.MonadIO m) => Patt -> Item -> m Bool
isMatch p x =
  not <$> P.null (P.enumerate (doMatch p x))


-- | Perform pattern matching and generate the list of possible global variable
-- binding environments which satisfy the match.
doMatch :: (P.MonadIO m) => Patt -> Item -> P.ListT m ()
doMatch p x = do
  P.Select $
    _doMatch p x P.yield


-- | Lower-level handler-based `doMatch`.
_doMatch
  :: (P.MonadIO m)
  => Patt
  -> Item
  -> (() -> m ()) -- ^ Monadic handler
  -> m ()
_doMatch p x h = _toListT (match p x) h


--------------------------------------------------
-- Pattern matching
--------------------------------------------------


-- | Match a pattern with a given item.
match :: (P.MonadIO m) => Patt -> Item -> MatchT m ()
match (P ip) (I it) =
  case (ip, it) of
    (Unit, Unit) -> pure ()
    (Sym x, Sym y) -> guard $ x == y
    (Tag k x, Tag k' y) -> do
      guard $ k == k'
      match x y
    (Vec v1, Vec v2) -> do
      let n = A.sizeofArray v1
          m = A.sizeofArray v2
      if n /= m
         then error $ "match fail due to length mismatch: " ++ show (v1, v2)
         else return ()
      forM_ [0..n-1] $ \k -> do
        match (A.indexArray v1 k) (A.indexArray v2 k)
    _ -> error $ "match fail: " ++ show (ip, it)
match (O p) it =
  case p of
    Var x -> bindVar x it
    Any -> pure ()
    -- Const it' -> guard $ it' == it
    Select ix p' -> case it of
      I (Vec v) -> match p' (A.indexArray v ix)
      _ -> error "match Select with non-product item"
    Focus ix p' -> case it of
      I (Tag ix' it') -> do
        guard $ ix == ix'
        match p' it'
    Choice p1 p2 -> do
      match p1 it `alt` match p2 it
    Seq x y -> do
      match x it
      match y it
    Guard c -> check c
    Assign p q -> do
      x <- eval q
      match p x


-- | Check a condition expression.
check :: (P.MonadIO m) => Cond Patt -> MatchT m ()
check = \case
  Eq px py  -> do
    x <- eval px
    y <- eval py
    guard $ x == y
  And cx cy -> check cx >> check cy
  Or cx cy -> do
    -- This is somewhat low-level, but serves the purpose
    let cxProd = P.enumerate (check cx)
    P.lift (P.next cxProd) >>= \case
      Left _  -> check cy
      Right _ -> return ()
--     -- NOTE: We could use `P.head` instead of `P.next`
--     P.lift (P.head cxProd) >>= \case
--       Nothing -> check cy
--       Just () -> return ()
--   -- NB: The implementation below (commented out) may perform redundant checks
--   Or cx cy -> checkStrict cx <|> checkStrict cy


-- | Evaluate a pattern with no free variables nor wildcard patterns.
--
-- NOTE: The function should not modify the underlying state/environment.
--
eval :: (P.MonadIO m) => Patt -> MatchT m Item
eval (P p) =
  case p of
    Unit -> pure (I Unit)
    Sym x -> pure . I $ Sym x
    Vec v -> I . Vec <$> mapM eval v
    Tag k p' -> I . Tag k <$> eval p'
eval (O p) =
  case p of
    Var v -> retrieveVar v
    -- Const it -> pure it
    Seq p1 p2 -> eval p1 >> eval p2
    Choice p1 p2 ->
      -- NB: `alt` is not necessary, because `eval` doesn't modify the state
      eval p1 <|> eval p2
    -- Apply fname p' -> do
    Apply f p' -> do
      -- f <- retrieveFun fname
      x <- eval p'
      y <- each $ fbody f x
      return y
    ApplyP f xs -> do
      -- Replace all variables in function `f` with fresh variables
      let oldVars = C.varsInFun f
      varMap <- fmap M.fromList . forM (S.toList oldVars) $ \v -> do
        local <- freshVar
        return (v, local)
      let f' = C.replaceFunVars varMap f
      -- Evaluate the argument patterns
      args <- mapM eval xs
      -- Match the formal parameters of the functions with the arguments
      mapM_ (uncurry match) (zip (pfParams f') args)
      -- Evaluate the body of the function and discard the local variables
      eval (pfBody f') <|> do
        forM_ (M.toList varMap) $ \(_, local) -> do
          ditchVar local
        empty
    Assign p q -> do
      x <- eval q
      match p x >> pure (I Unit)
    Guard c -> check c >> pure (I Unit)

    -- Things that should not happen
    Any -> error "eval Any"


--------------------------------------------------
-- Provisional
--------------------------------------------------


fromItem_ :: Item -> Patt
fromItem_ x =
  case x of
    I Unit -> P Unit
    I (Sym x) -> P (Sym x)
    I (Tag k p) -> P (Tag k (fromItem_ p))
    I (Vec v) -> P (Vec $ fmap fromItem_ v)


fromItem :: Ty Item a -> Ty Patt a
fromItem = Ty . fromItem_ . unTy


compile_ :: P.MonadIO m => (Patt -> Patt) -> Item -> MatchT m Item
compile_ f x =
  eval (f (fromItem_ x))


compile :: P.MonadIO m => (Ty Patt a -> Ty Patt b) -> Ty Item a -> MatchT m (Ty Item b)
compile f x =
  Ty <$> eval (unTy $ f (fromItem x))


-- | Lower-level handler-based `doCompile`.
_doCompile
  :: (P.MonadIO m)
  => (Patt -> Patt)
  -> Item
  -> (Item -> m ()) -- ^ Monadic handler
  -> m ()
_doCompile f x h = _toListT (compile_ f x) h


-- | Perform compilation and generate the list of possible global variable
-- binding environments which satisfy the match.
doCompile :: (P.MonadIO m) => (Patt -> Patt) -> Item -> P.ListT m Item
doCompile f x = do
  P.Select $
    _doCompile f x P.yield


runCompile :: (P.MonadIO m) => (Patt -> Patt) -> Item -> m [Item]
runCompile f x = P.toListM . P.enumerate $ doCompile f x


runCompileTy_ :: (P.MonadIO m) => (Ty Patt a -> Ty Patt b) -> Ty Item a -> m [Ty Item b]
runCompileTy_ f x =
  map Ty <$> runCompile g (unTy x)
  where
    g :: Patt -> Patt
    g = unTy . f . Ty


runCompileTy
  :: (IsItem a, IsItem b, P.MonadIO m)
  => (Ty Patt a -> Ty Patt b)
  -> a
  -> m [b]
runCompileTy f x =
  map decode <$> runCompileTy_ f (encode I x)


-- -- | Check if the pattern matches with the given item.
-- isMatch :: (P.MonadIO m) => Patt -> Item -> m Bool
-- isMatch p x =
--   not <$> P.null (P.enumerate (doMatch p x))


_compile2 :: P.MonadIO m => (Patt -> Patt -> Patt) -> Item -> Item -> MatchT m Item
_compile2 f x y =
  eval (f (fromItem_ x) (fromItem_ y))


-- compile :: P.MonadIO m => (Ty Patt a -> Ty Patt b) -> Ty Item a -> MatchT m (Ty Item b)
-- compile f x =
--   Ty <$> eval (unTy $ f (fromItem x))


-- | Lower-level handler-based `doCompile`.
_doCompile2
  :: (P.MonadIO m)
  => (Patt -> Patt -> Patt)
  -> Item
  -> Item
  -> (Item -> m ()) -- ^ Monadic handler
  -> m ()
_doCompile2 f x y h = _toListT (_compile2 f x y) h


-- | Perform compilation and generate the list of possible global variable
-- binding environments which satisfy the match.
doCompile2 :: (P.MonadIO m) => (Patt -> Patt -> Patt) -> Item -> Item -> P.ListT m Item
doCompile2 f x y = do
  P.Select $
    _doCompile2 f x y P.yield


runCompile2 :: (P.MonadIO m) => (Patt -> Patt -> Patt) -> Item -> Item -> m [Item]
runCompile2 f x y = P.toListM . P.enumerate $ doCompile2 f x y


_runCompileTy2
  :: (P.MonadIO m)
  => (Ty Patt a -> Ty Patt b -> Ty Patt c)
  -> Ty Item a -> Ty Item b -> m [Ty Item c]
_runCompileTy2 f x y =
  map Ty <$> runCompile2 g (unTy x) (unTy y)
  where
    g :: Patt -> Patt -> Patt
    g x y = unTy $ f (Ty x) (Ty y)


runCompileTy2
  :: (IsItem a, IsItem b, IsItem c, P.MonadIO m)
  => (Ty Patt a -> Ty Patt b -> Ty Patt c)
  -> a -> b
  -> m [c]
runCompileTy2 f x y =
  map decode <$> _runCompileTy2 f (encode I x) (encode I y)


--------------------------------------------------
-- Utils
--------------------------------------------------


-- | Lift the list to `P.ListT`.
each :: (Monad m) => [a] -> P.ListT m a
each = P.Select . P.each


-- | @choice ps@ tries to apply the actions in the list @ps@ in order, until
-- one of them succeeds. Returns the value of the succeeding action.
choice :: Alternative f => [f a] -> f a
choice = foldr (<|>) empty
