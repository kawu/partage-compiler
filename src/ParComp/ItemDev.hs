{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
-- {-# LANGUAGE UndecidableInstances #-}


module ParComp.ItemDev
  ( testPatt
  -- ToItem (..)
  -- , testActive
  -- , testPatt
  ) where


import           Prelude hiding (span, any, or)

import qualified Data.Text as T

import qualified ParComp.ItemDev.Untyped as U
import           ParComp.ItemDev.Untyped (Op (..))


--------------------------------------------------
-- Concerete item
--------------------------------------------------


-- | Item expression categories
data Rule
data Span
data Sym


-- | Item expression
data Item expr cat where
  Item  :: expr Rule -> expr Span -> Item expr ()
  Rule  :: expr Sym -> expr [Sym] -> Item expr Rule
  Span  :: expr Int -> expr Int -> Item expr Span
  Pos   :: Int -> Item expr Int
  Head  :: T.Text -> Item expr Sym
  Body  :: [Maybe T.Text] -> Item expr [Sym]
--   Dot   :: Item expr Sym
--   Cons  :: expr Sym -> expr [Sym] -> Item expr [Sym]
--   Nil   :: Item expr [Sym]


-- deriving instance
--   (Show (expr [Sym]), Show (expr Sym), Show (expr Int), Show (expr Rule), Show (expr Span))
--     => (Show (Item expr cat))
-- deriving instance
--   (Eq (expr [Sym]), Eq (expr Sym), Eq (expr Int), Eq (expr Rule), Eq (expr Span))
--     => (Eq (Item expr cat))
-- deriving instance
--   (Ord (expr [Sym]), Ord (expr Sym), Ord (expr Int), Ord (expr Rule), Ord (expr Span))
--     => (Ord (Item expr cat))


-- -- | Concrete active item (tying the knot)
-- newtype ItemI cat = ItemI (Item ItemI cat)
--   deriving (Show, Eq, Ord)
-- 
-- instance ToItem (ItemI cat) where
--   encode (ItemI span) =
--     case span of
--       Item r s  -> pair (encode r) (encode s)
--       Rule      -> unit
--       Span i j  -> pair (encode i) (encode j)
--       Pos i     -> encode i
    

--------------------------------------------------
-- Concrete pattern
--------------------------------------------------


-- | Pattern expression
data Pattern cat where
  -- | Item pattern
  P :: Item Pattern cat -> Pattern cat
  -- | Operation pattern
  O :: U.Op (Pattern cat) -> Pattern cat
--   deriving (Show, Eq, Ord)


instance U.ToPattern (Pattern cat) where
  encodeP = \case
    P x ->
      case x of
        Item r s    -> U.pairP (U.encodeP r) (U.encodeP s)
        Rule hd bd  -> U.pairP (U.encodeP hd) (U.encodeP bd)
        Span i j    -> U.pairP (U.encodeP i) (U.encodeP j)
        Pos i       -> U.symP . T.pack . show $ i
        Head x      -> U.encodeP x
        Body xs     -> U.encodeP xs
    O op -> U.encodeP op


-- | Smart constructors
-- item r s    = P $ Item r s
-- rule hd bd  = P $ Rule hd bd
span i j    = P $ Span i j
pos i       = P $ Pos i
any         = O $ Any
or x y      = O $ Or x y


-- | Test pattern
testPatt =
  testSpan
  where
--     testRule = rule
--       ()
--       ()
    testSpan = 
      span (pos 0) (pos 1 `or` pos 2) 
      `or`
      span (pos 1) any


-- --------------------------------------------------
-- -- Pattern (OLD)
-- --------------------------------------------------
-- 
-- 
-- -- -- | Pattern expression
-- -- data Pattern where
-- --   P       :: Item Pattern -> Pattern
-- --   Const   :: Rigit -> Pattern
-- --   Or      :: Pattern -> Pattern -> Pattern
-- --   deriving (Show, Eq, Ord)
-- -- 
-- -- 
-- -- -- | Some (not particularly) smart constructors
-- -- unit'      = P $ Unit
-- -- sym' x     = P $ Sym x
-- -- pair' x y  = P $ Pair x y
-- -- left' x    = P . Union $ Left x
-- -- right' y   = P . Union $ Right y
-- -- 
-- -- 
-- -- -- | Example item expression
-- -- testPatt =
-- --   p1 `Or` p2
-- --     where
-- --       p1 = left' $ pair' (sym' "symbol") (Const unit)
-- --       p2 = pair' unit' (unit' `Or` sym' "other")
-- 
-- 
-- -- -- | Pattern expression
-- -- data Pattern sym
-- --   -- | > Constant: match the given item expression
-- --   = Const (Item sym)
-- --   -- | > Pair: recursively match item pair
-- --   | Pair (Pattern sym) (Pattern sym)
-- --   -- | > Union: recursively match item union
-- --   | Union (Either (Pattern sym) (Pattern sym))
-- --   -- | > Any: match any item expression (wildcard)
-- --   | Any
-- --   -- | > Disjunction: match items which match either of the two patterns.
-- --   -- `Or` provides non-determinism in pattern matching.
-- --   | Or (Pattern sym) (Pattern sym)
-- --   deriving (Show, Eq, Ord)
