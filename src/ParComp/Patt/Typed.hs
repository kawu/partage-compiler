{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}


-- | Typed interface for creating and manipulating patterns.  See `ParComp.Patt`
-- for the lower-level, untyped interface.


module ParComp.Patt.Typed
  ( Ty (..)

  -- * Types
  -- ** Unit
  , unit
  -- ** Boolean
  , true
  , false
  , unBool
  , bool'
  -- ** Tuples
  , pair
  , pair'
  , unPair
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
  ) where


import qualified Data.Text as T
import qualified Data.Primitive.Array as A

import           ParComp.Patt.Core
  (Term (..), Item (..), Patt (..), Op (..), Cond (..))


-- | Typed expression
newtype Ty expr a = Ty {unTy :: expr}
  deriving (Eq, Ord)
  deriving newtype (Show)


--------------------------------------------------
-- Smart constructors
--------------------------------------------------


--------------------------------------------------
-- Types
--------------------------------------------------


-- | Unit
unit :: (Term e -> e) -> Ty e ()
unit mk = Ty $ mk Unit


-- | True
true :: (Term e -> e) -> Ty e Bool
true mk = Ty $ mk . Tag 1 $ mk Unit


-- | False
false :: (Term e -> e) -> Ty e Bool
false mk = Ty $ mk . Tag 0 $ mk Unit


-- | Expression `bool' f t b` yields `t` if `b` is `True`, and `f` otherwise.
bool' :: a -> a -> Ty Item Bool -> a
bool' f t (Ty b) =
  case b of
    I (Tag k _) -> case k of
      0 -> f
      1 -> t


-- | TODO
unBool :: Ty Item Bool -> Bool
unBool = bool' False True


-- | Expression `pair x y` constructs a pair from `x` and `y`.
pair :: (Term e -> e) -> Ty e a -> Ty e b -> Ty e (a, b)
pair mk (Ty x) (Ty y) = Ty . mk . Vec $ A.fromListN 2 [x, y]


-- | TODO
pair' :: (Ty Item a -> Ty Item b -> c) -> Ty Item (a, b) -> c
pair' f (Ty p) = case p of
  I (Vec v) -> f (Ty $ A.indexArray v 0) (Ty $ A.indexArray v 1)
  _ -> error "pair': not a pair"


-- | Deconstruct `pair x y` as `(x, y)`.
unPair :: Ty Item (a, b) -> (Ty Item a, Ty Item b)
unPair = pair' (,)


-- | `Nothing`
nothing :: (Term e -> e) -> Ty e (Maybe a)
nothing mk = Ty . mk . Tag 0 $ mk Unit


-- | `Just`
just :: (Term e -> e) -> Ty e a -> Ty e (Maybe a)
just mk = Ty . mk . Tag 1 . unTy


-- | Expression `maybe' n j m` yields `j x` if `m = just x`, and `n` otherwise.
maybe' :: b -> (Ty Item a -> b) -> Ty Item (Maybe a) -> b
maybe' n j (Ty m) =
  case m of
    I (Tag 0 _) -> n
    I (Tag 1 x) -> j (Ty x)


-- | `Left`
left :: (Term e -> e) -> Ty e a -> Ty e (Either a b)
left mk = Ty . mk . Tag 0 . unTy


-- | `Right`
right :: (Term e -> e) -> Ty e b -> Ty e (Either a b)
right mk = Ty . mk . Tag 1 . unTy


-- | Expression `either' e l r` yields `l x` if `e = left x`, and `r y` if
-- `e = right y`.
either' :: (Ty Item a -> c) -> (Ty Item b -> c) -> Ty Item (Either a b) -> c
either' l r (Ty e) =
  case e of
    I (Tag 0 x) -> l (Ty x)
    I (Tag 1 y) -> r (Ty y)


-- | View of either
unEither :: Ty Item (Either a b) -> Either (Ty Item a) (Ty Item b)
unEither = either' Left Right


-- | `[]`
nil :: (Term e -> e) -> Ty e [a]
nil mk = Ty . mk . Tag 0 $ mk Unit


-- | `x:xs`
cons :: (Term e -> e) -> Ty e a -> Ty e [a] -> Ty e [a]
cons mk (Ty x) (Ty xs) = Ty . mk . Tag 1 . mk . Vec $ A.fromListN 2 [x, xs]


-- | TODO
list' :: b -> (Ty Item a -> Ty Item [a] -> b) -> Ty Item [a] -> b
list' n c (Ty lst) =
  case lst of
    I (Tag 0 _) -> n
    I (Tag 1 ( I (Vec v))) -> c (Ty $ A.indexArray v 0) (Ty $ A.indexArray v 1)


-- | TODO
unList :: Ty Item [a] -> [Ty Item a]
unList = list' [] (\x xs -> x : unList xs)


-- | Append two lists
append :: Ty Item [a] -> Ty Item [a] -> Ty Item [a]
append =
  flip go
  where
    go ys = list' ys $ \x xs ->
      cons I x (go ys xs)


-- | Is the first list a suffix of the second list?
-- TODO: Optimize
suffix :: Ty Item [a] -> Ty Item [a] -> Ty Item Bool
suffix xs ys =
  if xs == ys
  then true I
  else list'
          (false I)
          (\_hd tl -> suffix xs tl)
          ys


--------------------------------------------------
-- Encoding
--------------------------------------------------


class IsItem a where
  -- | Encode a value as an item
  encode :: (Term e -> e) -> a -> Ty e a
  -- | Decode a value from an item
  decode :: Ty Item a -> a


instance IsItem () where
  encode mk _ = Ty $ mk Unit
  decode _ = ()

-- TODO: re-implement based on Num?
instance IsItem Bool where
  encode mk = \case
    False -> false mk
    True  -> true mk
  decode = bool' False True

-- TODO: re-implement based on Num?
instance IsItem Int where
  encode mk = Ty . mk . Sym . T.pack . show
  decode (Ty p) = case p of
    I (Sym x) -> read (T.unpack x)
    _ -> error $ "cannot decode " ++ show p ++ " to Int"

instance IsItem T.Text where
  encode mk = Ty . mk . Sym
  decode (Ty p) = case p of
    I (Sym x) -> x
    _ -> error $ "cannot decode " ++ show p ++ " to Text"

instance (IsItem a, IsItem b) => IsItem (a, b) where
  encode mk (x, y) = pair mk (encode mk x) (encode mk y)
  decode (unPair -> (x, y)) = (decode x, decode y)

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
