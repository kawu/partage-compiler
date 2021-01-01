{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}


-- | Pattern matching


module ParComp.Match
  ( MatchT
  , runMatchT
  , lift
  , isMatch

  , match
  , close
  , check
  ) where


import           Control.Monad (guard, void, forM_)
import qualified Control.Monad.RWS.Strict as RWS
import           Control.Applicative (Alternative, (<|>), empty)

import qualified Pipes as P
import qualified Pipes.Prelude as P

import           Data.Lens.Light

import qualified Data.Map.Strict as M
import qualified Data.Primitive.Array as A

import           ParComp.ItemBis
  (Term (..), Item (..), Var, Fun (..), Op (..), Cond (..), Patt (..))


--------------------------------------------------
-- Pattern matching core
--------------------------------------------------


-- | Variable binding environment
type Env v = M.Map v Item


-- | Pattern matching state
data PMState = PMState
  { _genv :: Env Var
    -- ^ Variable binding environment
--    , _funMap :: M.Map FunName (Item -> [Item])
--      -- ^ Registered functions
--   , _lenv :: Env LVar
--     -- ^ Local variable binding environment
--   , _fix :: Maybe Pattern
--     -- ^ Fixed recursive pattern
--   , _penv :: Env Pattern
--     -- ^ Pattern binding environment (only relevant for lazy matching)
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


-- | Run pattern matching computation with the underlying functions and
-- predicates.
runMatchT
  :: (Monad m)
  => MatchT m a
  -> m ()
runMatchT m = void $
  RWS.evalRWST (P.runListT m) ()
    (PMState M.empty)


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
  mayIt <- RWS.lift $ RWS.gets (M.lookup v . getL genv)
  case mayIt of
    Nothing -> RWS.modify' . modL genv $ M.insert v it
    Just it' -> guard $ it == it'


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
      x <- close q
      match p x


-- | Check a condition expression.
check :: (P.MonadIO m) => Cond Patt -> MatchT m ()
check = \case
  Eq px py  -> do
    x <- close px
    y <- close py
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


-- | Convert the pattern to the corresponding item expression.  This is only
-- possible if the pattern contains no free variables nor wildcard patterns.
-- See also `strip`.
--
-- Note that `close` should not modify the underlying state/environment.
--
close :: (P.MonadIO m) => Patt -> MatchT m Item
close (P p) =
  case p of
    Unit -> pure (I Unit)
    Sym x -> pure . I $ Sym x
    Vec v -> I . Vec <$> mapM close v
    Tag k p' -> I . Tag k <$> close p'
close (O p) =
  case p of
    Var v -> retrieveVar v
    -- Const it -> pure it
    Seq p1 p2 -> close p1 >> close p2
    Choice p1 p2 ->
      -- NB: `alt` is not necessary, because `close` doesn't modify the state
      close p1 <|> close p2
    -- Apply fname p' -> do
    Apply f p' -> do
      -- f <- retrieveFun fname
      x <- close p'
      y <- each $ fbody f x
      return y


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
