{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}


-- | Chart item representation


module ParComp.Item
  ( Item (..)
  , true
  , false
  ) where


import qualified Data.Text as T
import qualified Data.Primitive.Array as A


--------------------------------------------------
-- Item
--------------------------------------------------


-- | Chart item
data Item where
  Unit  :: Item
  Sym   :: {-# UNPACK #-} !T.Text -> Item
  -- | Non-empty vector of expressions (to represent product types)
  -- (TODO: or maybe we could/should use it to represent unit, too?)
  Vec   :: !(A.Array Item) -> Item
  -- | Tagged expression (to represent sum types)
  Tag   :: {-# UNPACK #-} !Int -> Item -> Item
--   Num   :: {-# UNPACK #-} !Int -> Item expr
--   -- ^ Integral number
  deriving (Show, Eq, Ord)


-- Special constructors for Booleans, since we treat them as special
-- (predicates)
false = Tag 0 Unit
true  = Tag 1 Unit


-- -- | Chart item expression
-- data Item expr where
--   Unit  :: Item expr
--   Sym   :: {-# UNPACK #-} !T.Text -> Item expr
--   -- | Non-empty vector of expressions (to represent product types)
--   -- (TODO: or maybe we could/should use it to represent unit, too?)
--   Vec   :: !(A.Array expr) -> Item expr
--   -- | Tagged expression (to represent sum types)
--   Tag   :: {-# UNPACK #-} !Int -> expr -> Item expr
-- --   Num   :: {-# UNPACK #-} !Int -> Item expr
-- --   -- ^ Integral number
--   deriving (Show, Eq, Ord)
--
--
-- -- | Rigid item expression
-- newtype Rigit = I (Item Rigit)
--   deriving (Eq, Ord)
--   deriving newtype (Show)
--
--
-- -- | Extract the rigit item.
-- unI :: Rigit -> Item Rigit
-- unI (I x) = x
--
--
-- -- | Rigit constructors
-- unit      = I Unit
-- sym x     = I $ Sym x
-- -- pair x y  = I $ Pair x y
-- -- left x    = I . Union $ Left x
-- -- right y   = I . Union $ Right y
--
--
-- -- | Construct a vector of `Rigit`s.
-- vec :: A.Array Rigit -> Rigit
-- vec = I . Vec
--   -- . A.fromList
--
--
-- -- | Construct a tagged `Rigit`.
-- tag :: Int -> Rigit -> Rigit
-- tag k = I . Tag k
--
--
-- -- -- | Construct a numeral `Rigit`.
-- -- num :: Int -> Rigit
-- -- num = I . Num
--
--
-- -- Special constructors for Booleans, since we treat them special (predicates)
-- false mkP = mkP . Tag 0 $ mkP Unit
-- true  mkP = mkP . Tag 1 $ mkP Unit


--------------------------------------------------
-- Item encoding
--------------------------------------------------


class IsItem t where
  -- | Encode a value as an item
  encode :: t -> Item
  -- | Decode a value from an item
  decode :: Item -> t


-- IMPORTANT NOTE: The implemented instances below must correspond with the
-- patterns provided in the Typed interface module.


instance IsItem () where
  encode _ = Unit
  decode _ = ()

-- TODO: re-implement based on Num?
instance IsItem Bool where
  encode = \case
    -- NB: we also use `true` below in `check`
    False -> false
    True  -> true
  decode x =
    case x of
      Tag k _ -> case k of
        0 -> False
        1 -> True
      _ -> error $ "cannot decode " ++ show x ++ " to Bool"

-- TODO: re-implement based on Num?
instance IsItem Int where
  encode = Sym . T.pack . show
  decode p = case p of
    Sym x -> read (T.unpack x)
    _ -> error $ "cannot decode " ++ show p ++ " to Int"

instance IsItem T.Text where
  encode = Sym
  decode p = case p of
    Sym x -> x
    _ -> error $ "cannot decode " ++ show p ++ " to Text"

instance (IsItem a, IsItem b) => IsItem (a, b) where
  encode (x, y) = Vec $
    A.fromListN 2 [encode x, encode y]
  decode p = case p of
    Vec v -> (decode (A.indexArray v 0), decode (A.indexArray v 1))
    _ -> error $ "cannot decode " ++ show p ++ " to (,)"

instance (IsItem a, IsItem b, IsItem c) => IsItem (a, b, c) where
  encode (x, y, z) = Vec $
    A.fromListN 3 [encode x, encode y, encode z]
  decode p = case p of
    Vec v ->
      ( decode (A.indexArray v 0)
      , decode (A.indexArray v 1)
      , decode (A.indexArray v 2)
      )
    _ -> error $ "cannot decode " ++ show p ++ " to (,,)"

instance (IsItem a) => IsItem (Maybe a) where
  encode = \case
    Nothing -> Tag 0 Unit
    Just x  -> Tag 1 $ encode x
  decode p = case p of
    Tag k x -> case k of
      0 -> Nothing
      1 -> Just (decode x)
    _ -> error $ "cannot decode " ++ show p ++ " to Maybe"

instance (IsItem a, IsItem b) => IsItem (Either a b) where
  encode = \case
    Left x  -> Tag 0 $ encode x
    Right y -> Tag 1 $ encode y
  decode p = case p of
    Tag k x -> case k of
      0 -> Left  $ decode x
      1 -> Right $ decode x
    _ -> error $ "cannot decode " ++ show p ++ " to Either"

instance (IsItem a) => IsItem [a] where
  encode = \case
    []      -> Tag 0 $ Unit
    x : xs  -> Tag 1 $ Vec $
      A.fromListN 2 [encode x, encode xs]
  decode p = case p of
    Tag k p' -> case k of
      0 -> []
      1 ->
        let (x, xs) = decode p'
         in x : xs
    _ -> error $ "cannot decode " ++ show p ++ " to []"
