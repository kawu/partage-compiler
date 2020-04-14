{-# LANGUAGE OverloadedStrings #-}


module ParComp.Item
  ( Item(..)
  , Val(..)
  , list
  ) where


import qualified Data.Text as T


-- | Primitive value
data Val
  -- | > Integer
  = VInt Int
  -- | > String
  | VStr T.Text
  deriving (Show, Eq, Ord)


-- | Chart item expression
data Item sym
  -- | > Unit: ()
  = Unit
  -- | > Symbol: arbitrary symbol
  | Sym sym
  -- | > Pair: product of two items
  | Pair (Item sym) (Item sym)
  -- | > Union: sum of two items
  | Union (Either (Item sym) (Item sym))
  deriving (Show, Eq, Ord)


-- | List encoding
list :: [sym] -> Item sym
list xs =
  case xs of
    [] -> Unit
    (x : xs') -> Pair (Sym x) (list xs')
