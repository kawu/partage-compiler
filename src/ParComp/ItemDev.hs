{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}


module ParComp.ItemDev
  ( testPatt
  , Pattern (..)
  , Span
  , Rule
  , Sym
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


-- -- | Concrete active item (tying the knot)
-- newtype ItemI cat = ItemI (Item ItemI cat)
--   deriving (Show, Eq, Ord)
-- 
-- instance ToItem (ItemI cat) where
--   encodeI (ItemI span) =
--     case span of
--       Item r s  -> pair (encodeI r) (encodeI s)
--       Rule      -> unit
--       Span i j  -> pair (encodeI i) (encodeI j)
--       Pos i     -> encodeI i
    

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

deriving instance (Show (Item Pattern cat))
deriving instance (Show (Pattern cat))
deriving instance (Eq (Item Pattern cat))
deriving instance (Eq (Pattern cat))
deriving instance (Ord (Item Pattern cat))
deriving instance (Ord (Pattern cat))


-- | Smart constructors
item r s    = P $ Item r s
rule hd bd  = P $ Rule hd bd
hed x       = P $ Head x
body xs     = P $ Body xs
span i j    = P $ Span i j
pos i       = P $ Pos i
any         = O $ Any
or x y      = O $ Or x y


-- | TODO
encodeWith
  :: (U.ToPattern (Pattern cat))
  => (Item Pattern cat -> U.Pattern)
  -> Pattern cat
  -> U.Pattern
encodeWith enc = \case
  P pt -> enc pt
  O op -> U.encode op


-- | TODO
-- decodeWith
--   :: (U.ToPattern (Pattern cat))
--   => _ -- (U.Pattern -> Item Pattern cat)
--   -> U.Pattern
--   -> Pattern cat
decodeWith dec = \case
  U.P pt -> dec $ U.decode (U.P pt)
  U.O op -> O $ U.decode (U.O op)


-- Item
instance U.ToPattern (Pattern ()) where
  encode = encodeWith $ \case
    Item r s -> U.encode (r, s)
  decode = decodeWith $ uncurry item

-- Span
instance U.ToPattern (Pattern Span) where
  encode = encodeWith $ \case
    Span i j -> U.encode (i, j)
  decode = decodeWith $ uncurry span

-- Pos
instance U.ToPattern (Pattern Int) where
  encode = encodeWith $ \case
    Pos i -> U.encode i
  decode = decodeWith pos

-- Rule
instance U.ToPattern (Pattern Rule) where
  encode = encodeWith $ \case
    Rule hd bd -> U.encode (hd, bd)
  decode = decodeWith $ uncurry rule

-- Head
instance U.ToPattern (Pattern Sym) where
  encode = encodeWith $ \case
    Head x -> U.encode x
  decode = decodeWith hed

-- Body
instance U.ToPattern (Pattern [Sym]) where
  encode = encodeWith $ \case
    Body xs -> U.encode xs
  decode = decodeWith body


-- | Test pattern
testPatt :: Pattern Rule
testPatt =
  testRule
  where
    testRule = rule
      (hed "A")
      testBody
    testBody =
      -- body [Just "B"]
      (body [Nothing, Just "B"])
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
