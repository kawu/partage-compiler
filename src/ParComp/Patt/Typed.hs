{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}


-- | This module provides the encoding of common types (Booleans, tuples, lists,
-- Eithers, etc.) as terms, common for both the "ParComp.Patt" and
-- "ParComp.Item" modules.


module ParComp.Patt.Typed
  ( Ty (..)

  -- * Types
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
  ) where


import qualified Data.Text as T
import qualified Data.Primitive.Array as A

import           ParComp.Patt.Core (Term (..), Item (..))


--------------------------------------------------
-- Types
--------------------------------------------------


-- | Typed expression
newtype Ty expr a = Ty {unTy :: expr}
  deriving (Eq, Ord)
  deriving newtype (Show)


-- | Unit
unit :: (Term e -> e) -> Ty e ()
unit mk = Ty $ mk Unit


-- | True
true :: (Term e -> e) -> Ty e Bool
true mk = Ty $ mk . Tag 1 $ mk Unit


-- | False
false :: (Term e -> e) -> Ty e Bool
false mk = Ty $ mk . Tag 0 $ mk Unit


-- | Expression `pair x y` constructs a pair from `x` and `y`.
pair :: (Term e -> e) -> Ty e a -> Ty e b -> Ty e (a, b)
pair mk (Ty x) (Ty y) = Ty . mk . Vec $ A.fromListN 2 [x, y]


-- | `Nothing`
nothing :: (Term e -> e) -> Ty e (Maybe a)
nothing mk = Ty . mk . Tag 0 $ mk Unit


-- | `Just`
just :: (Term e -> e) -> Ty e a -> Ty e (Maybe a)
just mk = Ty . mk . Tag 1 . unTy


-- | `Left`
left :: (Term e -> e) -> Ty e a -> Ty e (Either a b)
left mk = Ty . mk . Tag 0 . unTy


-- | `Right`
right :: (Term e -> e) -> Ty e b -> Ty e (Either a b)
right mk = Ty . mk . Tag 1 . unTy


-- | `[]`
nil :: (Term e -> e) -> Ty e [a]
nil mk = Ty . mk . Tag 0 $ mk Unit


-- | `x:xs`
cons :: (Term e -> e) -> Ty e a -> Ty e [a] -> Ty e [a]
cons mk (Ty x) (Ty xs) = Ty . mk . Tag 1 . mk . Vec $ A.fromListN 2 [x, xs]
