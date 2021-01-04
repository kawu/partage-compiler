{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoMonomorphismRestriction #-}


-- | Top-level pattern matching module


module ParComp.Patt
  (
  -- * Basic types from the core module
    Patt (..)
  , PattFun (..)

  -- * Re-export the typed pattern-matching module
  , module ParComp.Patt.Typed

  -- * Smart constructors
  , var
  , anyp
  , seqp
  , choice
  , assign
  , check
  , eq

  -- * Functions
  , with1arg
  , with2arg
  , apply1
  , apply2
  , compile1
  , compile2
  ) where


import           System.IO.Unsafe (unsafePerformIO)

import qualified Pipes as P
import qualified Pipes.Prelude as P

import           Data.String (fromString)

-- Core types and functions
import           ParComp.Patt.Core
import qualified ParComp.Match as X

-- Import non-qualified for re-export, qualified for local use
import           ParComp.Patt.Typed


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
-- Native functions
--------------------------------------------------


-- TODO: Move with1arg etc. to Typed.hs?


-- | Make a typed pattern-level function from a given pattern-to-pattern
-- function.
with1arg :: (Ty Patt a -> Ty Patt b) -> Ty PattFun (a -> b)
with1arg f =
  -- TODO: Make sure function `f` does not already contain variable "arg@1"!
  Ty $ PattFun [unTy arg1] (unTy $ f arg1)
  where
    arg1 = var "arg@1"


-- | Make a typed pattern-level function from a given pattern-to-pattern
-- function.
with2arg :: (Ty Patt a -> Ty Patt b -> Ty Patt c) -> Ty PattFun (a -> b -> c)
with2arg f =
  -- TODO: Make sure function `f` does not already contain variable "arg@1"!
  Ty $ PattFun [unTy arg1, unTy arg2] (unTy $ f arg1 arg2)
  where
    arg1 = var "arg@1"
    arg2 = var "arg@2"


-- | Apply 1-argument pattern-level function to a pattern.
apply1 :: Ty PattFun (a -> b) -> Ty Patt a -> Ty Patt b
apply1 (Ty f) (Ty x) = Ty . O $ ApplyP f [x]


-- | Apply 1-argument pattern-level function to a pattern.
apply2 :: Ty PattFun (a -> b -> c) -> Ty Patt a -> Ty Patt b -> Ty Patt c
apply2 (Ty f) (Ty x) (Ty y) = Ty . O $ ApplyP f [x, y]


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


-- | Compile a 1-argument pattern-level function of type (a -> b) to an actual,
-- non-deterministic (a -> [b]) function.
compile1 :: (IsItem a, IsItem b) => Ty PattFun (a -> b) -> a -> [b]
compile1 (Ty f) x =
  -- TODO: Won't need unsafePerformIO once the P.MonadIO constraint is ditched.
  unsafePerformIO $ do
    map (decode . Ty) <$> compileUn f [arg x]
  where
    arg = unTy . encode I


-- | Compile a 2-argument pattern-level function of type (a -> b -> c) to an
-- actual, non-deterministic (a -> b -> [c]) function.
compile2
  :: (IsItem a, IsItem b, IsItem c)
  => Ty PattFun (a -> b -> c)
  -> a -> b -> [c]
compile2 (Ty f) x y =
  -- TODO: Won't need unsafePerformIO once the P.MonadIO constraint is ditched.
  unsafePerformIO $ do
    map (decode . Ty) <$> compileUn f [arg x, arg y]
  where
    arg = unTy . encode I
