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

  ) where


import           Prelude hiding (const, map, any)

import qualified System.Random as R

import           Control.Monad (guard, void, forM)
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

import           ParComp.Item (Item (..))

import           Debug.Trace (trace)


--------------------------------------------------
-- Functions and predicates
--------------------------------------------------


-- -- | Named function
-- --
-- -- We require that all function and predicate names are unique.
-- data Fun a b = Fun
--   { fname :: T.Text
--     -- ^ The function's name
--   , fbody :: a -> [b]
--     -- ^ The function itself (non-deterministic)
--   }
--
-- instance Show (Fun a b) where
--   show Fun{..} = T.unpack fname
--
-- instance Eq (Fun a b) where
--   x == y = fname x == fname y
--
-- instance Ord (Fun a b) where
--   x `compare` y = fname x `compare` fname y
--
--
-- -- -- | Named predicate
-- -- --
-- -- -- We require that all function and predicate names are unique.  (See the
-- -- -- `guard` function in the `Typed` module to understand why a predicate should
-- -- -- not have the same name as a function).
-- -- data Pred a = Pred
-- --   { pname :: T.Text
-- --     -- ^ The predicate's name
-- --   , pbody :: a -> Bool
-- --     -- ^ The predicate itself
-- --   }
-- --
-- -- instance Show (Pred a) where
-- --   show Pred{..} = T.unpack pname
-- --
-- -- instance Eq (Pred a) where
-- --   x == y = pname x == pname y
-- --
-- -- instance Ord (Pred a) where
-- --   x `compare` y = pname x `compare` pname y


--------------------------------------------------
-- Pattern
--------------------------------------------------


-- | Variable
newtype Var = Var {unVar :: T.Text}
   deriving (Show, Eq, Ord)


-- | Function name
newtype FunName = FunName {unFunName :: T.Text}
  deriving (Show, Eq, Ord)


-- | Matching pattern
data M

-- | Constructing pattern
data C


-- | Pattern matching/constructing expression
data Patt t where

  -- | Bind the current expression to a given variable
  Label   :: Var -> Patt t
  -- | Match a constant item expression
  Const   :: Item -> Patt t
  -- | Match any item expression (wildcard pattern)
  Any     :: Patt M

  -- | Select a given branch of a tagged expression
  Select  :: Int -> Patt M -> Patt M
  -- | Focus on a given branch of a product expression
  Focus   :: Int -> Patt M -> Patt M

  -- | Sequence: `Seq x y` first matches `x`, then `y`, with the item.  The
  -- result of the match with `y` is taken to be the result of the entire
  -- expression.
  Seq     :: Patt t -> Patt t -> Patt t
  -- | Choice: `Choice x y` matches items which match either of the two
  -- patterns.  `Choice` provides non-determinism in pattern matching.
  Choice  :: Patt t -> Patt t -> Patt t

  -- | Construct a product expression
  CoVec   :: A.Array (Patt C) -> Patt C
  -- | Construct a tagged expression
  CoTag   :: Int -> Patt C -> Patt C

  -- | Apply function to a patter
  Apply   :: FunName -> Patt C -> Patt C

  -- | Pattern guard
  Guard   :: Cond -> Patt M

deriving instance Show (Patt t)
deriving instance Eq (Patt t)
deriving instance Ord (Patt t)


-- | Condition expression
--
-- Note that condition expression should contain no free variables, nor wildcard
-- patterns.  This is because side conditions are not matched against items.
data Cond where
  -- | Equality check between two constructing pattern expressions
  Eq    :: Patt C -> Patt C -> Cond
  -- | Logical conjunction
  And   :: Cond -> Cond -> Cond
  -- | Logical disjunction
  Or    :: Cond -> Cond -> Cond

deriving instance Show Cond
deriving instance Eq Cond
deriving instance Ord Cond


--------------------------------------------------
-- Pattern matching core
--------------------------------------------------


-- | Variable binding environment
type Env v = M.Map v Item


-- | Pattern matching state
data PMState = PMState
  { _genv :: Env Var
    -- ^ Variable binding environment
  , _funMap :: M.Map FunName (Item -> [Item])
    -- ^ Registered functions
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
    (PMState M.empty M.empty)


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


-- | Retrieve the function with a given name.  The function with the name must
-- exist, otherwise `retrieveFun` thorws an error.
retrieveFun
  :: (Monad m)
  => FunName
  -> MatchT m (Item -> [Item])
retrieveFun funName = do
  mayFun <- RWS.gets (M.lookup funName . getL funMap)
  case mayFun of
    Nothing -> error $ concat
      [ "retrieveFun: function with name '"
      , T.unpack $ unFunName funName
      , "' does not exist"
      ]
    Just fun -> return fun


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


-- -- | Check if the pattern matches with the given item.
-- isMatch :: (P.MonadIO m) => Patt t -> Item -> m Bool
-- isMatch p x =
--   not <$> P.null (P.enumerate (doMatch p x))
--
--
-- -- | Perform pattern matching and generate the list of possible global variable
-- -- binding environments which satisfy the match.
-- --
-- -- TODO: This looks like a specialized version of toListT.  Should be
-- -- implemented in terms of it?
-- --
-- doMatch :: (P.MonadIO m) => Patt t -> Item -> P.ListT m Item
-- doMatch p x = do
--   P.Select $
--     _doMatch p x P.yield
--
--
-- -- | Lower-level handler-based `doMatch`.
-- _doMatch
--   :: (P.MonadIO m)
--   => Patt t
--   -> Item
--   -> (Item -> m ()) -- ^ Monadic handler
--   -> m ()
-- _doMatch p x h =
--   runMatchT $ do
--     y <- match p x
--     lift $ h y
--     -- e <- RWS.gets $ getL genv
--     -- lift $ h e


--------------------------------------------------
-- Pattern matching
--------------------------------------------------


-- | Match a pattern with a given item.
match :: (P.MonadIO m) => Patt M -> Item -> MatchT m ()
match p it =
  case p of
    Label x -> bindVar x it
    Any -> pure ()
    Const it' -> guard $ it' == it
    Select ix p' -> case it of
      Vec v -> match p' (A.indexArray v ix)
      _ -> error "match Select with non-product item"
    Focus ix p' -> case it of
      Tag ix' it' -> do
        guard $ ix == ix'
        match p' it'
    Choice p1 p2 -> do
      match p1 it `alt` match p2 it
    Seq x y -> do
      match x it
      match y it
    Guard c -> check c


-- | Check a condition expression.
check :: (P.MonadIO m) => Cond -> MatchT m ()
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
close :: (P.MonadIO m) => Patt C -> MatchT m Item
close p =
  case p of
    Label v -> retrieveVar v
    Const it -> pure it
    -- TODO: What's the point of closing the first pattern?
    Seq p1 p2 -> close p1 >> close p2
    Choice p1 p2 ->
      -- NB: `alt` is not necessary, because `close` doesn't modify the state
      close p1 <|> close p2
    CoVec v -> Vec <$> mapM close v
    CoTag k p' -> Tag k <$> close p'
    Apply fname p' -> do
      f <- retrieveFun fname
      x <- close p'
      y <- each $ f x
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
