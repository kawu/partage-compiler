{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}


-- | Chart item representation


module ParComp.Item
  (

  -- * Item
    Item (..)

  -- * Data types
  -- ** Boolean
  , true
  , false
  , unBool
  , bool'
  -- ** Tuple
  , pair
  , unPair
  , triple
  , unTriple
  -- ** Maybe
  , nothing
  , just
  , maybe'
  -- ** Either
  , left
  , right
  , either'
  , unEither
  -- ** List
  , nil
  , cons
  , list'
  , unList
  , append

  -- * Encoding
  , IsItem (..)
  ) where


-- import           Control.Arrow ((***))

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


--------------------------------------------------
-- Constructors and views
--------------------------------------------------


-- | True
true :: Item
true = Tag 1 Unit

-- | False
false :: Item
false = Tag 0 Unit

-- | Expression `bool' f t b` yields `t` if `b` is `True`, and `f` otherwise.
bool' :: a -> a -> Item -> a
bool' f t b =
  case b of
    Tag k _ -> case k of
      0 -> f
      1 -> t

-- | TODO
unBool :: Item -> Bool
unBool = bool' False True


-- | Expression `pair x y` constructs a pair from `x` and `y`.
pair :: Item -> Item -> Item
pair x y = Vec $ A.fromListN 2 [x, y]

-- | Deconstruct `pair x y` as `(x, y)`.
unPair :: Item -> (Item, Item)
unPair p = case p of
  Vec v -> (A.indexArray v 0, A.indexArray v 1)
  _ -> error "unPair: not a pair"


-- | Expression `pair x y` constructs a pair from `x` and `y`.
triple :: Item -> Item -> Item -> Item
triple x y z = Vec $ A.fromListN 3 [x, y, z]

-- | Deconstruct `pair x y` as `(x, y)`.
unTriple :: Item -> (Item, Item, Item)
unTriple p = case p of
  Vec v -> (A.indexArray v 0, A.indexArray v 1, A.indexArray v 2)
  _ -> error "unTriple: not a triple"


-- | `Nothing`
nothing :: Item
nothing = Tag 0 Unit

-- | `Just`
just :: Item -> Item
just = Tag 1

-- | Expression `maybe' n j m` yields `j x` if `m = just x`, and `n` otherwise.
maybe' :: a -> (Item -> a) -> Item -> a
maybe' n j m =
  case m of
    Tag 0 _ -> n
    Tag 1 x -> j x


-- | `Left`
left :: Item -> Item
left = Tag 0

-- | `Right`
right :: Item -> Item
right = Tag 1

-- | Expression `either' e l r` yields `l x` if `e = left x`, and `r y` if
-- `e = right y`.
either' :: (Item -> a) -> (Item -> a) -> Item -> a
either' l r e =
  case e of
    Tag 0 x -> l x
    Tag 1 y -> r y


-- | View of either
unEither :: Item -> Either Item Item
unEither = either' Left Right


-- | `[]`
nil :: Item
nil = Tag 0 Unit

-- | `x:xs`
cons :: Item -> Item -> Item
cons x xs = Tag 1 . Vec $ A.fromListN 2 [x, xs]

-- | TODO
list' :: a -> (Item -> Item -> a) -> Item -> a
list' n c lst =
  case lst of
    Tag 0 _ -> n
    Tag 1 (Vec v) -> c (A.indexArray v 0) (A.indexArray v 1)

-- | TODO
unList :: Item -> [Item]
unList = list' [] (\x xs -> x : unList xs)

-- | Append two lists
append :: Item -> Item -> Item
append =
  flip go
  where
    go ys = list' ys $ \x xs ->
      cons x (go ys xs)


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
    False -> false
    True  -> true
  decode = bool' False True
--     case x of
--       Tag k _ -> case k of
--         0 -> False
--         1 -> True
--       _ -> error $ "cannot decode " ++ show x ++ " to Bool"

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
  encode (x, y) = pair (encode x) (encode y)
  decode (unPair -> (x, y)) = (decode x, decode y)
--   encode (x, y) = Vec $
--     A.fromListN 2 [encode x, encode y]
--   decode p = case p of
--     Vec v -> (decode (A.indexArray v 0), decode (A.indexArray v 1))
--     _ -> error $ "cannot decode " ++ show p ++ " to (,)"

instance (IsItem a, IsItem b, IsItem c) => IsItem (a, b, c) where
  encode (x, y, z) = triple (encode x) (encode y) (encode z)
  decode (unTriple -> (x, y, z)) = (decode x, decode y, decode z)
--   encode (x, y, z) = Vec $
--     A.fromListN 3 [encode x, encode y, encode z]
--   decode p = case p of
--     Vec v ->
--       ( decode (A.indexArray v 0)
--       , decode (A.indexArray v 1)
--       , decode (A.indexArray v 2)
--       )
--     _ -> error $ "cannot decode " ++ show p ++ " to (,,)"

instance (IsItem a) => IsItem (Maybe a) where
  encode = \case
    Nothing -> nothing
    Just x -> just (encode x)
--   encode = \case
--     Nothing -> Tag 0 Unit
--     Just x  -> Tag 1 $ encode x
  decode = maybe' Nothing (Just . decode)
--   decode p = case p of
--     Tag k x -> case k of
--       0 -> Nothing
--       1 -> Just (decode x)
--     _ -> error $ "cannot decode " ++ show p ++ " to Maybe"

instance (IsItem a, IsItem b) => IsItem (Either a b) where
  encode = \case
    Left x -> left (encode x)
    Right x -> right (encode x)
--   encode = \case
--     Left x  -> Tag 0 $ encode x
--     Right y -> Tag 1 $ encode y
  decode = either' (Left . decode) (Right . decode)
--   decode p = case p of
--     Tag k x -> case k of
--       0 -> Left  $ decode x
--       1 -> Right $ decode x
--     _ -> error $ "cannot decode " ++ show p ++ " to Either"

instance (IsItem a) => IsItem [a] where
  encode = \case
    [] -> nil
    x:xs -> cons (encode x) (encode xs)
--   encode = \case
--     []      -> Tag 0 $ Unit
--     x : xs  -> Tag 1 $ Vec $
--       A.fromListN 2 [encode x, encode xs]
  decode = list' [] (\x xs -> decode x : decode xs)
--   decode p = case p of
--     Tag k p' -> case k of
--       0 -> []
--       1 ->
--         let (x, xs) = decode p'
--          in x : xs
--     _ -> error $ "cannot decode " ++ show p ++ " to []"
