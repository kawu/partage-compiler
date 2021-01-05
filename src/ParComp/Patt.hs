{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}


-- | Top-level pattern matching module


module ParComp.Patt
  (
  -- * Basic types from the core module
    Patt (..)
  , PattFun (..)

  -- * Type constructor
  , Ty (..)

  -- * Patterns for basic types
  -- ** Unit
  , unit
  -- ** Boolean
  , true
  , false
  -- ** Tuples
  , pair
  -- ** Maybe
  , nothing
  , just
  -- ** Either
  , left
  , right
  -- ** List
  , nil
  , cons

  -- * Smart pattern constructors
  , var
  , anyp
  , seqp
  , choice
  , assign
  , check
  , eq

  -- * Functions
  -- ** Native
  , Args (..)
  , Vars ()
  , withVars
  , Apply (..)
  , Compile (..)
  -- ** Foreign
  , foreign1arg
  , foreign2arg

  -- * Item encoding
  , IsItem (..)
  ) where


import           System.IO.Unsafe (unsafePerformIO)

import qualified Pipes as P
import qualified Pipes.Prelude as P

import           Data.String (fromString)

-- Core types and functions
import           ParComp.Patt.Core
import qualified ParComp.Match as X

-- Import non-qualified for re-export, qualified for local use
import           ParComp.Patt.Typed (Ty (..))
import qualified ParComp.Patt.Typed as Ty
import           ParComp.Patt.Item (IsItem (..))


--------------------------------------------------
-- Smart constructors
--------------------------------------------------


-- | Variable pattern
-- TODO: Make sure that special variable names ("arg@...") are not used.
var :: String -> Ty Patt a
var = Ty . O . Var . fromString


-- | Wildcard pattern
anyp :: Ty Patt a
anyp = Ty $ O Any


-- | Sequential pattern matching
seqp :: Ty Patt a -> Ty Patt b -> Ty Patt b
seqp (Ty p) (Ty q) = Ty . O $ Seq p q


-- | Choice pattern
choice :: Ty Patt a -> Ty Patt a -> Ty Patt a
choice (Ty p) (Ty q) = Ty . O $ Choice p q


-- | Assignment pattern
assign :: Ty Patt a -> Ty Patt a -> Ty Patt b
assign (Ty x) (Ty v) = Ty . O $ Assign x v


-- | Guard pattern
check :: Cond Patt -> Ty Patt ()
check = Ty . O . Guard


-- | Equality check (NB: `Eq` constraint is not required since all types of
-- items can be compared)
eq :: Ty Patt a -> Ty Patt a -> Cond Patt
eq (Ty p) (Ty q) = Eq p q


--------------------------------------------------
-- Types
--------------------------------------------------


-- | Unit
unit :: Ty Patt ()
unit = Ty.unit P


-- | True
true :: Ty Patt Bool
true = Ty.true P


-- | False
false :: Ty Patt Bool
false = Ty.false P


-- | Expression `pair x y` constructs a pair from `x` and `y`.
pair :: Ty Patt a -> Ty Patt b -> Ty Patt (a, b)
pair = Ty.pair P


-- | `Nothing`
nothing :: Ty Patt (Maybe a)
nothing = Ty.nothing P


-- | `Just`
just :: Ty Patt a -> Ty Patt (Maybe a)
just = Ty.just P


-- | `Left`
left :: Ty Patt a -> Ty Patt (Either a b)
left = Ty.left P


-- | `Right`
right :: Ty Patt b -> Ty Patt (Either a b)
right = Ty.right P


-- | `[]`
nil :: Ty Patt [a]
nil = Ty.nil P


-- | `x:xs`
cons :: Ty Patt a -> Ty Patt [a] -> Ty Patt [a]
cons = Ty.cons P


--------------------------------------------------
-- Native functions
--------------------------------------------------


-- | Type class to introduce free variables.
class Vars f a where
  -- | Generate free variables to produce a function.  The first argument
  -- represents the variable ID.
  genVars :: Int -> f -> Ty Patt a

instance (a ~ a') => Vars (Ty Patt a) a' where
  genVars _ = id

instance Vars f b => Vars (Ty Patt a -> f) b where
  genVars k f = genVars (k+1) $ f (var $ "var@" ++ show k)


-- | Generate free variables to produce a function.
withVars :: Vars f a => f -> Ty Patt a
withVars = genVars 1


-- | Type class to represent variadic pattern-level functions.
class Args a f where
  -- | Instantiate @a@ with as many arguments as needed to produce a function.
  withArgs :: a -> Ty PattFun f

instance f ~ a => Args (Ty Patt a) f where
  withArgs = Ty . PattFun [] . unTy

instance (f ~ (a -> b)) => Args (Ty Patt a -> Ty Patt b) f where
  withArgs f =
    -- TODO: Make sure function `f` does not already contain variable "arg@1"!
    Ty $ PattFun [unTy arg1] (unTy $ f arg1)
    where
      arg1 = var "arg@1"

instance (f ~ (a -> b -> c)) => Args
    (Ty Patt a -> Ty Patt b -> Ty Patt c)
    f
    where
  withArgs f =
    -- TODO: Make sure function `f` does not already contain variable "arg@1"!
    Ty $ PattFun [unTy arg1, unTy arg2] (unTy $ f arg1 arg2)
    where
      arg1 = var "arg@1"
      arg2 = var "arg@2"


-- | Type class to represent application of variadic pattern-level functions.
class Apply f a where
  -- | Match @b@ with as many arguments as needed to apply a function.
  apply :: Ty PattFun f -> a

instance (f ~ (a -> b)) => Apply f (Ty Patt a -> Ty Patt b) where
  apply (Ty f) (Ty x) = Ty . O $ ApplyP f [x]

instance (f ~ (a -> b -> c)) => Apply
    f
    (Ty Patt a -> Ty Patt b -> Ty Patt c)
    where
  apply (Ty f) (Ty x) (Ty y) = Ty . O $ ApplyP f [x, y]


--------------------------------------------------
-- Compilation
--------------------------------------------------


-- | Cast an item as a pattern
fromItem :: Item -> Patt
fromItem x =
  case x of
    I Unit -> P Unit
    I (Sym x) -> P (Sym x)
    I (Tag k p) -> P (Tag k (fromItem p))
    I (Vec v) -> P (Vec $ fmap fromItem v)


-- | Compile an untyped pattern-level function.
compileUn :: (P.MonadIO m) => PattFun -> [Item] -> m [Item]
compileUn f xs =
  -- TODO: non-idiomatic use, also probably inefficient!
  P.toListM . P.enumerate $ compileUn f xs
  where
    compileUn :: P.MonadIO m => PattFun -> [Item] -> P.ListT m Item
    compileUn f xs =
      P.Select . X.runMatchT $ do
        x <- X.eval . O . ApplyP f $ map fromItem xs
        X.lift $ P.yield x


-- | Type class to represent compilation of variadic pattern-level functions.
class Compile f g where
  -- | Compile pattern-level function of type @f@ to a function of type @g@.
  compile :: Ty PattFun f -> g

instance {-# OVERLAPS #-} (IsItem a, IsItem b, g ~ (a -> [b]))
    => Compile (a -> b) g where
  compile (Ty f) x =
    -- TODO: Won't need unsafePerformIO once the P.MonadIO constraint is ditched.
    unsafePerformIO $ do
      map (decode . Ty) <$> compileUn f [arg x]
    where
      arg = unTy . encode I

instance (IsItem a, IsItem b, IsItem c, g ~ (a -> b -> [c]))
    => Compile (a -> b -> c) g where
  compile (Ty f) x y =
    -- TODO: Won't need unsafePerformIO once the P.MonadIO constraint is ditched.
    unsafePerformIO $ do
      map (decode . Ty) <$> compileUn f [arg x, arg y]
    where
      arg = unTy . encode I


-- -- | Compile a 1-argument pattern-level function of type (a -> b) to an actual,
-- -- non-deterministic (a -> [b]) function.
-- compile1 :: (IsItem a, IsItem b) => Ty PattFun (a -> b) -> a -> [b]
-- compile1 (Ty f) x =
--   -- TODO: Won't need unsafePerformIO once the P.MonadIO constraint is ditched.
--   unsafePerformIO $ do
--     map (decode . Ty) <$> compileUn f [arg x]
--   where
--     arg = unTy . encode I
--
--
-- -- | Compile a 2-argument pattern-level function of type (a -> b -> c) to an
-- -- actual, non-deterministic (a -> b -> [c]) function.
-- compile2
--   :: (IsItem a, IsItem b, IsItem c)
--   => Ty PattFun (a -> b -> c)
--   -> a -> b -> [c]
-- compile2 (Ty f) x y =
--   -- TODO: Won't need unsafePerformIO once the P.MonadIO constraint is ditched.
--   unsafePerformIO $ do
--     map (decode . Ty) <$> compileUn f [arg x, arg y]
--   where
--     arg = unTy . encode I


--------------------------------------------------
-- Foreign functions
--------------------------------------------------


foreign1arg
  :: FunName
  -> (Ty Item a -> Ty Item b)
  -> Ty Patt a -> Ty Patt b
foreign1arg funName f =
  let named = ForeignFun funName $ \[x] -> [unTy $ f (Ty x)]
   in \x -> Ty . O $ Apply named [unTy x]


-- -- | Declare a named foreign function and lift it to a pattern-level function
-- foreign1arg :: FunName -> (Ty Item a -> Ty Item b) -> Ty Patt a -> Ty Patt b
-- foreign1arg funName f =
--   let named = ForeignFun funName $ \x -> [unTy $ f $ Ty x]
--    in Ty . O . Apply named . unTy


-- | 2-argument variant of `foreign1arg`
foreign2arg
  :: FunName
  -> (Ty Item a -> Ty Item b -> Ty Item c)
  -> Ty Patt a -> Ty Patt b -> Ty Patt c
foreign2arg funName f =
  let named = ForeignFun funName $ \[x, y] -> [unTy $ f (Ty x) (Ty y)]
   in \x y -> Ty . O $ Apply named [unTy x, unTy y]


-- -- | 2-argument variant of `foreign1arg`
-- foreign2arg
--   :: FunName
--   -> (Ty Item a -> Ty Item b -> Ty Item c)
--   -> Ty Patt a -> Ty Patt b -> Ty Patt c
-- foreign2arg funName f =
--   let named = ForeignFun funName $ \x -> [unTy $ I.pairI f $ Ty x]
--    in \x y -> Ty . O . Apply named . unTy $ pair x y
