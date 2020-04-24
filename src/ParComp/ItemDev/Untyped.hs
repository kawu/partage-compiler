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
--   encodeI :: t -> Rigit
-- 
-- 
-- instance ToItem () where
--   encodeI _ = unit
-- 
-- instance ToItem Bool where
--   encodeI True  = sym "T"
--   encodeI False = sym "F"
-- 
-- instance ToItem Int where
--   encodeI = sym . T.pack . show
-- 
-- instance ToItem T.Text where
--   encodeI = sym
-- 
-- instance (ToItem a, ToItem b) => ToItem (a, b) where
--   encodeI (x, y) = pair (encodeI x) (encodeI y)
-- 
-- instance (ToItem a, ToItem b, ToItem c) => ToItem (a, b, c) where
--   encodeI (x, y, z) = pair (encodeI x) (pair (encodeI y) (encodeI z))
-- 
-- instance (ToItem a, ToItem b) => ToItem (Either a b) where
--   encodeI (Left x)  = left  $ encodeI x
--   encodeI (right y) = right $ encodeI y


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
  encode :: t -> Pattern
  -- | Decode a value from a pattern
  decode :: Pattern -> t


instance ToPattern () where
  encode _ = unitP
  decode _ = ()

instance ToPattern Bool where
  encode = \case
    False -> leftP unitP
    True  -> rightP unitP
  decode (P (Union u)) =
    case u of
      Left  _ -> False
      Right _ -> True
  decode p =
    error $ "cannot decode " ++ show p ++ " to Bool"

instance ToPattern Int where
  encode = symP . T.pack . show
  decode (P (Sym x)) = read (T.unpack x)
  decode p =
    error $ "cannot decode " ++ show p ++ " to Int"

instance ToPattern T.Text where
  encode = symP
  decode (P (Sym x)) = x
  decode p =
    error $ "cannot decode " ++ show p ++ " to Text"

instance (ToPattern a, ToPattern b) => ToPattern (a, b) where
  encode (x, y) = pairP (encode x) (encode y)
  decode (P (Pair x y)) = (decode x, decode y)
  decode p =
    error $ "cannot decode " ++ show p ++ " to (,)"

instance (ToPattern a, ToPattern b, ToPattern c) => ToPattern (a, b, c) where
  encode (x, y, z) = pairP (encode x) (pairP (encode y) (encode z))
  decode (P (Pair x (P (Pair y z)))) = (decode x, decode y, decode z)
  decode p =
    error $ "cannot decode " ++ show p ++ " to (,,)"

instance (ToPattern a) => ToPattern (Maybe a) where
  encode = \case
    Nothing -> leftP unitP
    Just x -> rightP $ encode x
  decode (P (Union u)) =
    case u of
      Left _ -> Nothing
      Right x -> Just (decode x)
  decode p =
    error $ "cannot decode " ++ show p ++ " to Maybe"

instance (ToPattern a, ToPattern b) => ToPattern (Either a b) where
  encode = \case
    Left x  -> leftP  $ encode x
    Right y -> rightP $ encode y
  decode (P (Union u)) =
    case u of
      Left x  -> Left  $ decode x
      Right y -> Right $ decode y
  decode p =
    error $ "cannot decode " ++ show p ++ " to Either"

instance (ToPattern a) => ToPattern [a] where
  encode = \case
    x : xs  -> leftP $ pairP (encode x) (encode xs)
    []      -> rightP unitP
  decode (P (Union u)) =
    case u of
      Left p ->
        let (x, xs) = decode p
         in x : xs
      Right _ -> []
  decode p =
    error $ "cannot decode " ++ show p ++ " to []"


-- | Generic pattern operation encoding
instance (ToPattern t) => ToPattern (Op t) where
  encode = \case
    Or x y -> O $ Or (encode x) (encode y)
    Any -> O Any
  decode (O op) =
    case op of
      Or x y -> Or (decode x) (decode y)
      Any -> Any
  decode p =
    error $ "cannot decode " ++ show p ++ " to Op"
