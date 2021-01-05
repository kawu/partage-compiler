{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}


-- | Item-level functions


module ParComp.Patt.Item
  (
  -- * Item
    Item (..)

  -- * Types
  -- ** Unit
  , unit
  -- ** Boolean
  , true
  , false
  , unBool
  , boolI
  -- ** Tuples
  , pair
  , pairI
  , unPair
  -- ** Maybe
  , nothing
  , just
  , maybeI
  , unMaybe
  -- ** Either
  , left
  , right
  , eitherI
  , unEither
  -- ** List
  , nil
  , cons
  , listI
  , unList
  , append
  , suffix

  -- * Encoding
  , IsItem (..)
  ) where


import qualified Data.Text as T
import qualified Data.Primitive.Array as A

import           ParComp.Patt.Typed (Ty (..))
import qualified ParComp.Patt.Typed as Ty
import           ParComp.Patt.Core (Term (..), Item (..))


--------------------------------------------------
-- Functions from the "Typed.hs" module
-- specialized to items
--------------------------------------------------


-- | Unit
unit :: Ty Item ()
unit = Ty.unit I


-- | True
true :: Ty Item Bool
true = Ty.true I


-- | False
false :: Ty Item Bool
false = Ty.false I


-- | Expression `pair x y` constructs a pair from `x` and `y`.
pair :: Ty Item a -> Ty Item b -> Ty Item (a, b)
pair = Ty.pair I


-- | `Nothing`
nothing :: Ty Item (Maybe a)
nothing = Ty.nothing I


-- | `Just`
just :: Ty Item a -> Ty Item (Maybe a)
just = Ty.just I


-- | `Left`
left :: Ty Item a -> Ty Item (Either a b)
left = Ty.left I


-- | `Right`
right :: Ty Item b -> Ty Item (Either a b)
right = Ty.right I


-- | `[]`
nil :: Ty Item [a]
nil = Ty.nil I


-- | `x:xs`
cons :: Ty Item a -> Ty Item [a] -> Ty Item [a]
cons = Ty.cons I


--------------------------------------------------
-- Types
--------------------------------------------------


-- | Expression `bool f t b` yields `t` if `b` is `True`, and `f` otherwise.
boolI :: a -> a -> Ty Item Bool -> a
boolI f t (Ty b) =
  case b of
    I (Tag k _) -> case k of
      0 -> f
      1 -> t


-- | View of Boolean
unBool :: Ty Item Bool -> Bool
unBool = boolI False True


-- | TODO
pairI :: (Ty Item a -> Ty Item b -> c) -> Ty Item (a, b) -> c
pairI f (Ty p) = case p of
  I (Vec v) -> f (Ty $ A.indexArray v 0) (Ty $ A.indexArray v 1)
  _ -> error "pair': not a pair"


-- | Deconstruct `pair x y` as `(x, y)`.
unPair :: Ty Item (a, b) -> (Ty Item a, Ty Item b)
unPair = pairI (,)


-- | Expression `maybeI n j m` yields `j x` if `m = just x`, and `n` otherwise.
maybeI :: b -> (Ty Item a -> b) -> Ty Item (Maybe a) -> b
maybeI n j (Ty m) =
  case m of
    I (Tag 0 _) -> n
    I (Tag 1 x) -> j (Ty x)


-- | View of maybe
unMaybe :: Ty Item (Maybe a) -> Maybe (Ty Item a)
unMaybe = maybeI Nothing Just


-- | Expression `eitherI e l r` yields `l x` if `e = left x`, and `r y` if
-- `e = right y`.
eitherI :: (Ty Item a -> c) -> (Ty Item b -> c) -> Ty Item (Either a b) -> c
eitherI l r (Ty e) =
  case e of
    I (Tag 0 x) -> l (Ty x)
    I (Tag 1 y) -> r (Ty y)


-- | View of either
unEither :: Ty Item (Either a b) -> Either (Ty Item a) (Ty Item b)
unEither = eitherI Left Right


-- | TODO
listI :: b -> (Ty Item a -> Ty Item [a] -> b) -> Ty Item [a] -> b
listI n c (Ty lst) =
  case lst of
    I (Tag 0 _) -> n
    I (Tag 1 ( I (Vec v))) -> c (Ty $ A.indexArray v 0) (Ty $ A.indexArray v 1)


-- | TODO
unList :: Ty Item [a] -> [Ty Item a]
unList = listI [] (\x xs -> x : unList xs)


-- | Append two lists
append :: Ty Item [a] -> Ty Item [a] -> Ty Item [a]
append =
  flip go
  where
    go ys = listI ys $ \x xs ->
      cons x (go ys xs)


-- | Is the first list a suffix of the second list?
-- TODO: Optimize
suffix :: Ty Item [a] -> Ty Item [a] -> Ty Item Bool
suffix xs ys =
  if xs == ys
  then true
  else listI
          false
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
    False -> Ty.false mk
    True  -> Ty.true mk
  decode = boolI False True

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
  encode mk (x, y) = Ty.pair mk (encode mk x) (encode mk y)
  decode (unPair -> (x, y)) = (decode x, decode y)

instance (IsItem a) => IsItem (Maybe a) where
  encode mk = \case
    Nothing -> Ty.nothing mk
    Just x -> Ty.just mk (encode mk x)
  decode = maybeI Nothing (Just . decode)

instance (IsItem a, IsItem b) => IsItem (Either a b) where
  encode mk = \case
    Left x -> Ty.left mk (encode mk x)
    Right x -> Ty.right mk (encode mk x)
  decode = eitherI (Left . decode) (Right . decode)

instance (IsItem a) => IsItem [a] where
  encode mk = \case
    [] -> Ty.nil mk
    x:xs -> Ty.cons mk (encode mk x) (encode mk xs)
  decode = listI [] (\x xs -> decode x : decode xs)
