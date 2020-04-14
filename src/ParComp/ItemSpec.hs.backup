{-# LANGUAGE OverloadedStrings #-}


-- | Item specification language.
--
-- There are two item-related languages we should be concerned about.
--
--
-- # Item *structure* specs
--
-- On the one hand, we need to be able to describe how the structure of an item
-- may look like.  For instance, that we have active and passive items, that
-- active items contain dotted rules on their first position, how these dotted
-- rules look like, etc.
--
-- 
-- # Item *pattern* specs
--
-- On the other hand, we need to describe item *patterns* in the actual
-- deduction rules / parsing schemata, which will be matched against existing
-- items (in the chart or agenda).
--
-- This is somewhat related to pattern matching in functional languages, but
-- there are also differences:
--
--  * In FP, we typically have a *single* item and a *sequence* of patterns,
--    and we want to match the item with the *first possible* pattern.
--  * In our case, we have a *bunch* of items (the chart) and *one or two*
--    patterns (premises/antecendents), and we want to find *all* item subsets
--    (singletons or pairs) which match the two patterns.  
--
-- Additionally, the two patterns will often have common sub-patterns, which
-- must be identical in the two matched items.  We could alternatively say that
-- the two patterns are independent, but that there are additional side
-- conditions which may enforce some similarities between the matched items.
--
--
-- Getting back to item and pattern specs: in this module, we are only
-- concerned with the former, i.e., how to describe the possible item
-- structures.  Algebraic data types should do the job.


module ParComp.ItemSpec
  (
  ) where


import           Prelude hiding (Integer, either)

import qualified Data.Text as T
import qualified Data.Map.Strict as M


-- | A record item is a mapping from attributes to their (item) values.
type RecordItem = M.Map T.Text Item


-- | A union item is a mapping from constructor names to their (item) values.
type UnionItem = M.Map T.Text Item


-- | Syntax tree for item specification
data Item
  -- | > Record (product type)
  = Record RecordItem
  -- | > Union (sum type)
  | Union UnionItem
  -- | > Integer
  | Integer
  -- | > Symbol
  | Sym
  -- | > Unit
  | Unit
  deriving (Show, Eq, Ord)


-- | Smart union constructor
union :: [(T.Text, Item)] -> Item
union = Union . M.fromList


-- | Smart record constructor
record :: [(T.Text, Item)] -> Item
record = Record . M.fromList


-- | Either (left/right) encoding
either :: Item -> Item -> Item
either left right = union
  [ ("Left", left)
  , ("Right", right)
  ]


-- | Pair encoding
pair :: Item -> Item -> Item
pair one two = record
  [ ("_1", one)
  , ("_2", two)
  ]


-- | List encoding
list :: Item -> Item
list ofx = either ofx (list ofx)
-- list (x:xs) = union
--   [ ("head", x)
--   , ("tail", list xs)
--   ]
-- -- list [] = Unit
-- list (x:xs) = union
--   [ ("nil", Unit)
--   ]



-- | CFG dotted rule
dottedRule = record
  [ ("head", Sym)
  , ("dot", Integer)
  , ("body", list Sym)
  ]


-- -- | A concrete CFG item
-- cfgItem :: Item
-- cfgItem =
