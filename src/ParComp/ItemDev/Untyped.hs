{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}


module ParComp.ItemDev.Untyped
  ( Item (..)
  , Pattern (..)
  , Op (..)
  , ToPattern (..)

  , unitP
  , symP
  , pairP
  , leftP
  , rightP
  ) where


import qualified Data.Text as T


--------------------------------------------------
-- Item
--------------------------------------------------


-- | Chart item expression
data Item expr where
  Unit  :: Item expr
  Sym   :: T.Text -> Item expr
  Pair  :: expr -> expr -> Item expr
  Union :: Either expr expr -> Item expr
  deriving (Show, Eq, Ord)


-- | Rigid item expression
newtype Rigit = I (Item Rigit)
  deriving (Show, Eq, Ord)


-- -- | Abstract constructors
-- unit      = Unit
-- sym x     = Sym x
-- pair x y  = Pair x y
-- left x    = Union $ Left x
-- right y   = Union $ Right y


-- -- | Rigit constructors
-- unit      = I Unit
-- sym x     = I $ Sym x
-- pair x y  = I $ Pair x y
-- left x    = I . Union $ Left x
-- right y   = I . Union $ Right y


--------------------------------------------------
-- Encoding items
--------------------------------------------------


-- class ToItem t where
--   -- | Encode a value as an item
--   encode :: t -> Rigit
-- 
-- 
-- instance ToItem () where
--   encode _ = unit
-- 
-- instance ToItem Bool where
--   encode True  = sym "T"
--   encode False = sym "F"
-- 
-- instance ToItem Int where
--   encode = sym . T.pack . show
-- 
-- instance ToItem T.Text where
--   encode = sym
-- 
-- instance (ToItem a, ToItem b) => ToItem (a, b) where
--   encode (x, y) = pair (encode x) (encode y)
-- 
-- instance (ToItem a, ToItem b, ToItem c) => ToItem (a, b, c) where
--   encode (x, y, z) = pair (encode x) (pair (encode y) (encode z))
-- 
-- instance (ToItem a, ToItem b) => ToItem (Either a b) where
--   encode (Left x)  = left  $ encode x
--   encode (right y) = right $ encode y


--------------------------------------------------
-- Pattern
--------------------------------------------------


-- | Pattern operation expression
data Op t where
  Or     :: t -> t -> Op t
  Any    :: Op t
  deriving (Show, Eq, Ord)


-- | Pattern expression
data Pattern where
  -- | Item pattern
  P :: Item Pattern -> Pattern
  -- | Operation pattern
  O :: Op Pattern -> Pattern
  deriving (Show, Eq, Ord)


-- data Pattern where
--   -- Const   :: Rigit -> Pattern
--   P       :: Item Pattern -> Pattern
--   Or      :: Pattern -> Pattern -> Pattern
--   Any     :: Pattern
--   deriving (Show, Eq, Ord)


-- | Pattern (item) constructors
unitP      = P Unit
symP x     = P $ Sym x
pairP x y  = P $ Pair x y
leftP x    = P . Union $ Left x
rightP y   = P . Union $ Right y


--------------------------------------------------
-- Encoding patterns
--------------------------------------------------


class ToPattern t where
  -- | Encode a value as a pattern
  encodeP :: t -> Pattern
  -- | Decode a value from a pattern
  decodeP :: Pattern -> t


instance ToPattern () where
  encodeP _ = unitP
  decodeP _ = ()

instance ToPattern Bool where
  encodeP = \case
    False -> leftP unitP
    True  -> rightP unitP
  decodeP (P (Union u)) =
    case u of
      Left  _ -> False
      Right _ -> True
  decodeP p =
    error $ "cannot decode " ++ show p ++ " to Bool"

instance ToPattern Int where
  encodeP = symP . T.pack . show
  decodeP (P (Sym x)) = read (T.unpack x)
  decodeP p =
    error $ "cannot decode " ++ show p ++ " to Int"

instance ToPattern T.Text where
  encodeP = symP
  decodeP (P (Sym x)) = x
  decodeP p =
    error $ "cannot decode " ++ show p ++ " to Text"

instance (ToPattern a, ToPattern b) => ToPattern (a, b) where
  encodeP (x, y) = pairP (encodeP x) (encodeP y)
  decodeP (P (Pair x y)) = (decodeP x, decodeP y)
  decodeP p =
    error $ "cannot decode " ++ show p ++ " to (,)"

instance (ToPattern a, ToPattern b, ToPattern c) => ToPattern (a, b, c) where
  encodeP (x, y, z) = pairP (encodeP x) (pairP (encodeP y) (encodeP z))
  decodeP (P (Pair x (P (Pair y z)))) = (decodeP x, decodeP y, decodeP z)
  decodeP p =
    error $ "cannot decode " ++ show p ++ " to (,,)"

instance (ToPattern a) => ToPattern (Maybe a) where
  encodeP = \case
    Nothing -> leftP unitP
    Just x -> rightP $ encodeP x
  decodeP (P (Union u)) =
    case u of
      Left _ -> Nothing
      Right x -> decodeP x
  decodeP p =
    error $ "cannot decode " ++ show p ++ " to Maybe"

instance (ToPattern a, ToPattern b) => ToPattern (Either a b) where
  encodeP = \case
    Left x  -> leftP  $ encodeP x
    Right y -> rightP $ encodeP y
  decodeP (P (Union u)) =
    case u of
      Left x  -> Left  $ decodeP x
      Right y -> Right $ decodeP y

instance (ToPattern a) => ToPattern [a] where
  encodeP = \case
    [] -> unitP
    x : xs -> pairP (encodeP x) (encodeP xs)

-- | Generic pattern operation encoding
instance (ToPattern t) => ToPattern (Op t) where
  encodeP = \case
    Or x y -> O $ Or (encodeP x) (encodeP y)
    Any -> O Any
