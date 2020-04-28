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
  -- ToItem (..)
  -- , testActive
  -- , testPatt
  ) where


import           Prelude hiding (span, any, or, map, const)
import qualified Prelude as P

import qualified Data.Text as T

import qualified ParComp.ItemDev.Untyped as U
-- import           ParComp.ItemDev.Untyped
--   (Op(..), TyOr(..), TyVia(..), TyApp(..))
import qualified ParComp.ItemDev.Typed as Ty
import           ParComp.ItemDev.Typed (Pattern(..), Op(..))


--------------------------------------------------
-- Concerete item
--------------------------------------------------


-- | Item expression categories
data Active
data Rule
data Span
data Sym


-- -- | Item expression
-- data Item expr cat where
--   Item  :: expr Rule -> expr Span -> Item expr ()
--   Rule  :: expr Sym -> expr [Sym] -> Item expr Rule
--   Span  :: epxr Int -> expr Int -> Item expr Span
--   Pos   :: Int -> Item expr Int
--   Head  :: T.Text -> Item expr Sym
--   Body  :: [Maybe T.Text] -> Item expr [Sym]


class Item repr where
  item  :: repr Rule a -> repr Span b -> repr Active (a, b)
  span  :: repr Int a -> repr Int b -> repr Span (a, b)
  pos   :: Int -> repr Int Int
  rule  :: repr Sym a -> repr [Sym] b -> repr Rule (a, b)
  rhead :: T.Text -> repr Sym T.Text
  rbody :: [Maybe T.Text] -> repr [Sym] [Maybe T.Text]


instance Item Pattern where
  item (Patt r) (Patt s) = Patt (U.pairP r s)
  span (Patt x) (Patt y) = Patt (U.pairP x y)
  rule (Patt h) (Patt b) = Patt (U.pairP h b)
  pos i   = Patt $ U.encodeP i
  rhead x = Patt $ U.encodeP x
  rbody x = Patt $ U.encodeP x


-- testPatt :: (Item repr, Op repr) => repr Span ()
testPatt :: Pattern Active ()
testPatt =
  map constUnit testItem
  where
    testItem = item testRule testSpan
    testRule = rule
      (rhead "A")
      (rbody [Nothing, Just "B"] `or` rbody [Nothing])
    testSpan = span (pos 1 `or` pos 2) (pos 3)
    constUnit = U.Fun "constUnit" (P.const [()])


-- deriving instance (Show (Item down up))
-- 
-- -- Pos
-- instance U.IsPattern (Item Int Int) where
--   encode (Pos i) = U.encode i
--   decode = Pos . U.decode
-- 
-- -- Span
-- instance U.IsPattern (Item Span Span) where
--   encode (Span x y) = U.encode (x, y)
--   decode = uncurry Span . U.decode
-- 
-- 
-- -- -- | Concrete active item (tying the knot)
-- -- newtype ItemI cat = ItemI (Item ItemI cat)
-- --   deriving (Show, Eq, Ord)
-- -- 
-- -- instance ToItem (ItemI cat) where
-- --   encodeI (ItemI span) =
-- --     case span of
-- --       Item r s  -> pair (encodeI r) (encodeI s)
-- --       Rule      -> unit
-- --       Span i j  -> pair (encodeI i) (encodeI j)
-- --       Pos i     -> encodeI i
-- 
-- 
-- -- | Example item pattern
-- testPatt =
--   testSpan
--   where
-- --     testItem = item
-- --       testRule
-- --       testSpan
-- --     testRule = rule
-- --       (hed "A")
-- --       testBody
-- --     testBody =
-- --       (body [Nothing, Just "B"])
-- -- --     testBody =
-- -- --       (via (app "fun")
-- -- --         (body [Nothing, Just "B"])
-- -- --       )
--     testSpan =
--       Span (Pos 0) (Pos 1 `TyOr` Pos 2)
--       `TyOr`
--       -- Span (Pos 1) Any
--       Span (Pos 1) (Pos 3)
-- --    testPos = Pos 0 `TyOr` Pos 1


--------------------------------------------------
-- Concrete pattern
--------------------------------------------------


-- -- | Pattern expression
-- data Pattern cat where
--   -- | Item pattern
--   P :: Item Pattern cat -> Pattern cat
--   -- | Operation pattern
--   O :: U.Op (Pattern cat) -> Pattern cat
-- --   deriving (Show, Eq, Ord)
-- 
-- deriving instance (Show (Item Pattern cat))
-- deriving instance (Show (Pattern cat))
-- deriving instance (Eq (Item Pattern cat))
-- deriving instance (Eq (Pattern cat))
-- deriving instance (Ord (Item Pattern cat))
-- deriving instance (Ord (Pattern cat))
-- 
-- 
-- -- | Smart constructors
-- item r s    = P $ Item r s
-- rule hd bd  = P $ Rule hd bd
-- hed x       = P $ Head x
-- body xs     = P $ Body xs
-- span i j    = P $ Span i j
-- pos i       = P $ Pos i
-- any         = O $ Any
-- or x y      = O $ Or x y
-- via x y     = O $ Via x y
-- app fn      = O $ App fn
-- 
-- 
-- -- | TODO
-- encodeWith
--   :: (U.IsPattern (Pattern cat))
--   => (Item Pattern cat -> U.Pattern)
--   -> Pattern cat
--   -> U.Pattern
-- encodeWith enc = \case
--   P pt -> enc pt
--   O op -> U.encode op
-- 
-- 
-- -- | TODO
-- decodeWith
--   :: (U.IsPattern t, U.IsPattern (Pattern cat))
--   => (t -> Pattern cat)
--   -> U.Pattern
--   -> Pattern cat
-- decodeWith dec = \case
--   U.P pt -> dec $ U.decode (U.P pt)
--   U.O op -> O $ U.decode (U.O op)
-- 
-- 
-- -- Item
-- instance U.IsPattern (Pattern ()) where
--   encode = encodeWith $ \case
--     Item r s -> U.encode (r, s)
--   decode = decodeWith $ uncurry item
-- 
-- -- Span
-- instance U.IsPattern (Pattern Span) where
--   encode = encodeWith $ \case
--     Span i j -> U.encode (i, j)
--   decode = decodeWith $ uncurry span
-- 
-- -- Pos
-- instance U.IsPattern (Pattern Int) where
--   encode = encodeWith $ \case
--     Pos i -> U.encode i
--   decode = decodeWith pos
-- 
-- -- Rule
-- instance U.IsPattern (Pattern Rule) where
--   encode = encodeWith $ \case
--     Rule hd bd -> U.encode (hd, bd)
--   decode = decodeWith $ uncurry rule
-- 
-- -- Head
-- instance U.IsPattern (Pattern Sym) where
--   encode = encodeWith $ \case
--     Head x -> U.encode x
--   decode = decodeWith hed
-- 
-- -- Body
-- instance U.IsPattern (Pattern [Sym]) where
--   encode = encodeWith $ \case
--     Body xs -> U.encode xs
--   decode = decodeWith body
-- 
-- 
-- -- | Example item pattern
-- testPatt :: Pattern ()
-- testPatt =
--   testItem
--   where
--     testItem = item
--       testRule
--       testSpan
--     testRule = rule
--       (hed "A")
--       testBody
--     testBody =
--       (body [Nothing, Just "B"])
-- --     testBody =
-- --       (via (app "fun")
-- --         (body [Nothing, Just "B"])
-- --       )
--     testSpan =
--       span (pos 0) (pos 1 `or` pos 2) 
--       `or`
--       span (pos 1) any
