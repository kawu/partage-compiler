{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DerivingStrategies #-}

-- {-# LANGUAGE ScopedTypeVariables #-}
-- {-# LANGUAGE PartialTypeSignatures #-}

-- {-# LANGUAGE QuantifiedConstraints #-}


module ParComp.Pattern.UntypedBis
  (
  -- * Functions
    Fun (..)
--   , Squeeze (..)
--   , Apply (..)

  -- * Patterns
  , Patt (..)
  , Cond (..)
--   , M
--   , C

  -- * Matching
  , MatchT
  , runMatchT
  , lift
  , isMatch

  , match
  , close
  , check
  ) where


import           Prelude hiding (const, map, any)

import qualified System.Random as R

import           Control.Monad (guard, void, forM_)
import qualified Control.Monad.RWS.Strict as RWS
import           Control.Applicative (Alternative, (<|>), empty)

import qualified Pipes as P
import qualified Pipes.Prelude as P

import           Data.Lens.Light

import qualified Data.Primitive.Array as A

import           Data.Void (Void)
import           Data.String (IsString)
import qualified Data.Foldable as F
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import qualified ParComp.Item as I
import           ParComp.Item (Term (..), Item (..))

import           Debug.Trace (trace)


--------------------------------------------------
-- Functions and predicates
--------------------------------------------------


-- | Function name
newtype FunName = FunName {unFunName :: T.Text}
  deriving (Eq, Ord, IsString)

instance Show FunName where
  show = T.unpack . unFunName

-- | Named function
--
-- We require that all function and predicate names are unique.
data Fun = Fun
  { fname :: FunName
    -- ^ The function's name
  , fbody :: Item -> [Item]
    -- ^ The function itself (non-deterministic)
  }

instance Show Fun where
  show Fun{..} = show fname

instance Eq Fun where
  x == y = fname x == fname y

instance Ord Fun where
  x `compare` y = fname x `compare` fname y


--  class Squeeze f where
--    squeeze :: f -> (Item -> [Item])
--
-- class Apply f where
--   apply :: f


-- instance Squeeze (Item -> [Item]) where
--   squeeze f = f
--
-- instance Apply (Fun -> Patt C -> Patt C) where
--   apply f = Apply f


-- instance Squeeze (Item -> Item -> [Item]) where
--   squeeze f = \x -> case x of
--     I.Vec v -> f (A.indexArray v 0) (A.indexArray v 1)
--     _ -> error "Squeeze 2-arg: arguments squeezed incorrectly"
--
-- instance Apply (Fun -> Patt C -> Patt C -> Patt C) where
--   -- TODO: use `pair x y` (once available in this module)
--   apply f x y = Apply f . Vec $ A.fromListN 2 [x, y]


-- instance MkFun (Item -> Item -> [Item]) where
--   squeeze f = \x -> case x of
--     I.Vec v -> f (A.indexArray v 0) (A.indexArray v 1)
--     _ -> error "MkFun 2-arg: argument squeezed incorrectly"
--   unsqueeze f x y = f . I.Vec $ A.fromListN 2 [x, y]
--
-- instance MkFun (Item -> Item -> Item -> [Item]) where
--   squeeze f = \x -> case x of
--     I.Vec v -> f (A.indexArray v 0) (A.indexArray v 1) (A.indexArray v 2)
--     _ -> error "MkFun 3-arg: argument squeezed incorrectly"
--   unsqueeze f x y z = f . I.Vec $ A.fromListN 3 [x, y, z]


-- -- | Named predicate
-- --
-- -- We require that all function and predicate names are unique.  (See the
-- -- `guard` function in the `Typed` module to understand why a predicate
-- -- should not have the same name as a function).
-- data Pred a = Pred
--   { pname :: T.Text
--     -- ^ The predicate's name
--   , pbody :: a -> Bool
--     -- ^ The predicate itself
--   }
--
-- instance Show (Pred a) where
--   show Pred{..} = T.unpack pname
--
-- instance Eq (Pred a) where
--   x == y = pname x == pname y
--
-- instance Ord (Pred a) where
--   x `compare` y = pname x `compare` pname y


--------------------------------------------------
-- Pattern
--------------------------------------------------


-- | Variable
newtype Var = Var {unVar :: T.Text}
   deriving (Show, Eq, Ord, IsString)


-- -- | Matching pattern
-- data M
--
-- -- | Constructing pattern
-- data C


-- | Pattern matching/constructing expression
data Op e where

  -- | Bind the current expression to a given variable
  Label   :: Var -> Op e
--   -- | Match a constant item expression
--   Const   :: Item -> Patt t
  -- | Match any item expression (wildcard pattern)
  Any     :: Op e

  -- | Select a given branch of a tagged expression
  Select  :: Int -> e -> Op e
  -- | Focus on a given branch of a product expression
  Focus   :: Int -> e -> Op e

  -- | Sequence: `Seq x y` first matches `x`, then `y`, with the item.  The
  -- result of the match with `y` is taken to be the result of the entire
  -- expression.
  Seq     :: e -> e -> Op e
  -- | Choice: `Choice x y` matches items which match either of the two
  -- patterns.  `Choice` provides non-determinism in pattern matching.
  Choice  :: e -> e -> Op e

  -- | Apply function to a pattern
  -- Apply   :: FunName -> Patt C -> Patt C
  Apply   :: Fun -> e -> Op e
  -- | Pattern assignment
  Assign  :: e -> e -> Op e

  -- NOTE: Pattern assignment can be seen as a uni-directional analog of
  -- equality constraint, in which the right-hand side is a constructing pattern
  -- and the left-hand side is a matching pattern.

  -- | Pattern guard
  Guard   :: Cond e -> Op e

  deriving (Show, Eq, Ord)

-- deriving instance Show (Patt t)
-- deriving instance Eq (Patt t)
-- deriving instance Ord (Patt t)


-- | Condition expression
--
-- Note that condition expression should contain no free variables, nor wildcard
-- patterns.  This is because side conditions are not matched against items.
data Cond e where
  -- | Equality check between two constructing pattern expressions
  Eq    :: e -> e -> Cond e
  -- | Logical conjunction
  And   :: Cond e -> Cond e -> Cond e
  -- | Logical disjunction
  Or    :: Cond e -> Cond e -> Cond e
  deriving (Show, Eq, Ord)

-- deriving instance Show Cond
-- deriving instance Eq Cond
-- deriving instance Ord Cond


-- | Pattern expression
data Patt
  = P (Term Patt)
  -- ^ Term pattern
  | O (Op Patt)
  -- ^ Operation pattern
  deriving (Show, Eq, Ord)


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
    Label x -> bindVar x it
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
    Label v -> retrieveVar v
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


-- -- | TODO
-- apply :: MkFun f => Fun -> (f -> Patt C)
-- apply Fun{..} = fbody
