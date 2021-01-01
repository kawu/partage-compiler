{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}


-- | Chart item representation


module ParComp.Item
  (

  -- * Item
    Term (..)
  , Item (..)

  -- * Data types
  -- ** Boolean
  , true
  , false
  , unBool
  , bool'
  -- ** Tuples
  , pair
  , pair'
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
  , suffix

  -- * Encoding
  , IsItem (..)
  , encodeI
  ) where


-- import           Control.Arrow ((***))

import qualified Data.Text as T
import qualified Data.Primitive.Array as A


--------------------------------------------------
-- Term
--------------------------------------------------


-- | Term expression
data Term expr where
  Unit  :: Term expr
  Sym   :: {-# UNPACK #-} !T.Text -> Term expr
  -- | Non-empty vector of expressions (to represent product types)
  -- (TODO: or maybe we could/should use it to represent unit, too?)
  Vec   :: !(A.Array expr) -> Term expr
  -- | Tagged expression (to represent sum types)
  Tag   :: {-# UNPACK #-} !Int -> expr -> Term expr
--   Num   :: {-# UNPACK #-} !Int -> Term expr
--   -- ^ Integral number
  deriving (Show, Eq, Ord)


--------------------------------------------------
-- Item
--------------------------------------------------


-- | Item expression
newtype Item = I {unI :: Term Item}
  deriving (Eq, Ord)
  deriving newtype (Show)


--------------------------------------------------
-- Constructors and views
--------------------------------------------------


-- | True
true :: (Term e -> e) -> e
true mk = mk . Tag 1 $ mk Unit

-- | False
false :: (Term e -> e) -> e
false mk = mk . Tag 0 $ mk Unit

-- | Expression `bool' f t b` yields `t` if `b` is `True`, and `f` otherwise.
bool' :: a -> a -> Item -> a
bool' f t b =
  case b of
    I (Tag k _) -> case k of
      0 -> f
      1 -> t

-- | TODO
unBool :: Item -> Bool
unBool = bool' False True


-- | Expression `pair x y` constructs a pair from `x` and `y`.
pair :: (Term e -> e) -> e -> e -> e
pair mk x y = mk . Vec $ A.fromListN 2 [x, y]

-- | TODO
pair' :: (Item -> Item -> a) -> Item -> a
pair' f p = case p of
  I (Vec v) -> f (A.indexArray v 0) (A.indexArray v 1)
  _ -> error "pair': not a pair"

-- | Deconstruct `pair x y` as `(x, y)`.
unPair :: Item -> (Item, Item)
unPair = pair' (,)


-- | Expression `pair x y` constructs a pair from `x` and `y`.
triple :: (Term e -> e) -> e -> e -> e -> e
triple mk x y z = mk . Vec $ A.fromListN 3 [x, y, z]

-- | Deconstruct `pair x y` as `(x, y)`.
unTriple :: Item -> (Item, Item, Item)
unTriple p = case p of
  I (Vec v) -> (A.indexArray v 0, A.indexArray v 1, A.indexArray v 2)
  _ -> error "unTriple: not a triple"


-- | `Nothing`
nothing :: (Term e -> e) -> e
nothing mk = mk . Tag 0 $ mk Unit

-- | `Just`
just :: (Term e -> e) -> e -> e
just mk = mk . Tag 1

-- | Expression `maybe' n j m` yields `j x` if `m = just x`, and `n` otherwise.
maybe' :: a -> (Item -> a) -> Item -> a
maybe' n j m =
  case m of
    I (Tag 0 _) -> n
    I (Tag 1 x) -> j x


-- | `Left`
left :: (Term e -> e) -> e -> e
left mk = mk . Tag 0

-- | `Right`
right :: (Term e -> e) -> e -> e
right mk = mk . Tag 1

-- | Expression `either' e l r` yields `l x` if `e = left x`, and `r y` if
-- `e = right y`.
either' :: (Item -> a) -> (Item -> a) -> Item -> a
either' l r e =
  case e of
    I (Tag 0 x) -> l x
    I (Tag 1 y) -> r y


-- | View of either
unEither :: Item -> Either Item Item
unEither = either' Left Right


-- | `[]`
nil :: (Term e -> e) -> e
nil mk = mk . Tag 0 $ mk Unit

-- | `x:xs`
cons :: (Term e -> e) -> e -> e -> e
cons mk x xs = mk . Tag 1 . mk . Vec $ A.fromListN 2 [x, xs]

-- | TODO
list' :: a -> (Item -> Item -> a) -> Item -> a
list' n c lst =
  case lst of
    I (Tag 0 _) -> n
    I (Tag 1 ( I (Vec v))) -> c (A.indexArray v 0) (A.indexArray v 1)

-- | TODO
unList :: Item -> [Item]
unList = list' [] (\x xs -> x : unList xs)

-- | Append two lists
append :: Item -> Item -> Item
append =
  flip go
  where
    go ys = list' ys $ \x xs ->
      cons I x (go ys xs)

-- | Is the first list a suffix of the second list?
-- TODO: Optimize
suffix :: Item -> Item -> Item
suffix xs ys =
  if xs == ys
  then true I
  else list'
          (false I)
          (\_hd tl -> suffix xs tl)
          ys


--------------------------------------------------
-- Item encoding
--------------------------------------------------


class IsItem t where
  -- | Encode a value as an item
  -- encode :: t -> Item
  encode :: (Term e -> e) -> t -> e
  -- | Decode a value from an item
  decode :: Item -> t
  -- decode :: (Show e) => (e -> Term e) -> e -> t


-- | Encode a value as a `Rigit`.
encodeI :: IsItem t => t -> Item
encodeI = encode I


-- IMPORTANT NOTE: The implemented instances below must correspond with the
-- patterns provided in the Typed interface module.


instance IsItem () where
  encode mk _ = mk Unit
  decode _ = ()

-- TODO: re-implement based on Num?
instance IsItem Bool where
  encode mk = \case
    False -> false mk
    True  -> true mk
  decode = bool' False True

-- TODO: re-implement based on Num?
instance IsItem Int where
  encode mk = mk . Sym . T.pack . show
  decode p = case p of
    I (Sym x) -> read (T.unpack x)
    _ -> error $ "cannot decode " ++ show p ++ " to Int"

instance IsItem T.Text where
  encode mk = mk . Sym
  decode p = case p of
    I (Sym x) -> x
    _ -> error $ "cannot decode " ++ show p ++ " to Text"

instance (IsItem a, IsItem b) => IsItem (a, b) where
  encode mk (x, y) = pair mk (encode mk x) (encode mk y)
  decode (unPair -> (x, y)) = (decode x, decode y)

instance (IsItem a, IsItem b, IsItem c) => IsItem (a, b, c) where
  encode mk (x, y, z) = triple mk (encode mk x) (encode mk y) (encode mk z)
  decode (unTriple -> (x, y, z)) = (decode x, decode y, decode z)

instance (IsItem a) => IsItem (Maybe a) where
  encode mk = \case
    Nothing -> nothing mk
    Just x -> just mk (encode mk x)
  decode = maybe' Nothing (Just . decode)

instance (IsItem a, IsItem b) => IsItem (Either a b) where
  encode mk = \case
    Left x -> left mk (encode mk x)
    Right x -> right mk (encode mk x)
  decode = either' (Left . decode) (Right . decode)

instance (IsItem a) => IsItem [a] where
  encode mk = \case
    [] -> nil mk
    x:xs -> cons mk (encode mk x) (encode mk xs)
  decode = list' [] (\x xs -> decode x : decode xs)
