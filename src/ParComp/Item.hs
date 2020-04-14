{-# LANGUAGE OverloadedStrings #-}


module ParComp.Item
  ( Item(..)
  , list
  ) where


import qualified Data.Text as T


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
list :: [Item sym] -> Item sym
list xs =
  case xs of
    (x : xs') -> Pair x (list xs')
    [] -> Unit
