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

import           ParComp.Item (Item)

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
type Var = T.Text

-- | Function name
type Name = T.Text

-- -- | Variable
-- newtype Var = Var T.Text
--   deriving (Show, Eq, Ord)
--
--
-- -- | Extract the variable.
-- unVar :: Var -> T.Text
-- unVar (Var x) = x


-- -- | Local variable name
-- newtype LVar = LVar T.Text
--   deriving (Show, Eq, Ord)
--
--
-- -- | Extract the variable.
-- unLVar :: LVar -> T.Text
-- unLVar (LVar x) = x



-- | Matching pattern
data M

-- | Constructing pattern
data C

-- | Pattern matching/constructing expression
data Patt t where

  -- | Select a given branch of a tagged expression
  Select  :: Int -> Patt M -> Patt M
  -- | Focus on a given branch of a product expression
  Focus   :: Int -> Patt M -> Patt M
  -- | Bind the current expression to a given variable
  Var     :: Var -> Patt t
  -- | Match any item expression (wildcard pattern)
  Any     :: Patt M
  -- | Match a constant item expression
  Const   :: Item -> Patt t

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

  -- | Apply function to a pattern
  Apply   :: Name -> Patt C -> Patt C

  -- | Pattern guard
  Guard   :: Cond -> Patt t

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
