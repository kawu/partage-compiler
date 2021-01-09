{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}


-- | Tree-substitution grammar parsing


module ParComp.Examples.TSG
  (
  ) where


import           Prelude hiding (splitAt, span)

import qualified Data.Text as T
import qualified Data.Set as S

import           ParComp.Patt
import qualified ParComp.Patt.Item as I
import           ParComp.Examples.Utils


--------------------------------------------------
-- TSG item
--------------------------------------------------


-- | Item's span
type Span = (Int, Int)

-- | Non-terminal/terminal symbol
type Sym = T.Text

-- | Node identifier
type ID = T.Text

-- | Grammar node is either a non-terminal (label + identifier) node or a
-- terminal (only label) node.  In CFG there's no need to decorate nodes with
-- identifiers, we do that for the sake of example (such identifiers can be
-- useful in TSG/TAG parsing, for instance).
type Node = Either (Sym, ID) Sym

-- | Rule's head
type Head = Node

-- | Rule's body
type Body = [Maybe Node]

-- | Dotted rule
type DotRule = (Head, Body)

-- | Active item
type Active = (DotRule, Span)

-- | Top-level item
type Item = Either Active DotRule


item :: Ty Patt DotRule -> Ty Patt Span -> Ty Patt Item
item r s = left $ pair r s

top :: Ty Patt DotRule -> Ty Patt Item
top = right

rule :: Ty Patt Head -> Ty Patt Body -> Ty Patt DotRule
rule = pair

span :: Ty Patt Int -> Ty Patt Int -> Ty Patt Span
span = pair

pos :: Int -> Ty Patt Int
pos = encode P

head :: Node -> Ty Patt Head
head = encode P

-- | Dot in a dotted rule
dot :: Ty Patt (Maybe Node)
dot = nothing


--------------------------------------------------
-- Grammar
--------------------------------------------------


type Rule = (T.Text, [T.Text])


-- -- | Make the grammar from the set of CFG rules and the input sentence.
-- mkGram :: [T.Text] -> S.Set Rule -> Grammar
-- mkGram sent cfgRules = Grammar
--   { leafs = leafs
--   , roots = roots
--   , inter = internals
--   }
--   where
--     -- Heads, roots, and leafs
--     heads = S.fromList . (++) sent $ do
--       (hd, _bd) <- S.toList cfgRules
--       return hd
--     children = S.fromList $ do
--       (_hd, bd) <- S.toList cfgRules
--       bd
--     internals = S.intersection heads children
--     leafs = children `S.difference` internals
--     roots = heads `S.difference` internals


-- | Grammar
data Grammar = Grammar
  { leafs :: S.Set (Ty I.Item Node)
    -- ^ Set of grammar leaf nodes
  , roots :: S.Set (Ty I.Item Node)
    -- ^ Set of grammar root nodes
  , inter :: S.Set (Ty I.Item Node)
    -- ^ Set of grammar root nodes
--   { leafs :: S.Set Node
--     -- ^ Set of grammar leaf nodes
--   , roots :: S.Set Node
--     -- ^ Set of grammar root nodes
--   , inter  :: S.Set Node
--     -- ^ Set of grammar internal nodes
  }


--------------------------------------------------
-- Grammar functions / patterns
--------------------------------------------------


-- | Pattern to extract the non-terminal / terminal symbol of a node
label :: Ty Patt Node -> Ty Patt Sym
label =
  foreign1arg "label" extract
  where
    extract (I.unEither -> Left (I.unPair -> (x, _))) = x
    extract (I.unEither -> Right x) = x


-- -- | Determine the label of the node.
-- nodeLabel :: Node -> [Sym]
-- nodeLabel x = case T.splitOn "_" x of
--   [term] -> [term]
--   [nonTerm, _nodeId] -> [nonTerm]
--   _ -> error $ "nodeLabel: unhandled symbol (" ++ T.unpack x ++ ")"


-- | Leaf node predicate
leaf :: Grammar -> Ty Patt Node -> Ty Patt Bool
leaf gram =
  foreign1arg "leaf" isLeaf
  where
    isLeaf x
      | x `S.member` leafs gram = I.true
      | otherwise = I.false


-- | Root node predicate
root :: Grammar -> Ty Patt Node -> Ty Patt Bool
root gram =
  foreign1arg "leaf" isRoot
  where
    isRoot x
      | x `S.member` roots gram = I.true
      | otherwise = I.false


-- | Internal node predicate
internal :: Grammar -> Ty Patt Node -> Ty Patt Bool
internal gram =
  foreign1arg "leaf" isRoot
  where
    isRoot x
      | x `S.member` inter gram = I.true
      | otherwise = I.false


--------------------------------------------------
-- Deduction rules
--------------------------------------------------


-- -- | TSG complete rule
-- complete :: Grammar -> Ty.Rule Item
-- complete gram =
--
--   Ty.Rule [leftP, rightP] downP condP
--
--   where
--
--     -- Variables
--     v_A = var "A"         :: Pattern Node
--     v_B = var "B"         :: Pattern Node
--     v_C = var "C"         :: Pattern Node
--     v_alpha = var "alpha" :: Pattern Body
--     v_beta = var "beta"   :: Pattern Body
--     v_i = var "i"         :: Pattern Int
--     v_j = var "j"         :: Pattern Int
--     v_k = var "k"         :: Pattern Int
--
--     leftP = item
--       (rule v_A
--         (via splitAtDot
--           (pair v_alpha (dot .: just v_B .: v_beta))
--         )
--       )
--       (span v_i v_j)
--
--     rightP = item
--       (rule v_C
--         (guard endsWithDotP)
--         -- (suffix $ dot .: nil)
--       )
--       (span v_j v_k)
--
--     condP = or
--       ( and
--           ( eq (map label v_B)
--                (map label v_C)
--           )
--           ( and (leaf gram v_B)
--                 (root gram v_C)
--           )
--       )
--       ( and
--           ( eq v_B v_C )
--           ( and (internal gram v_B)
--                 (internal gram v_C)
--           )
--       )
--
--     downP = item
--       (rule v_A
--         ( bimap Util.append
--             v_alpha
--             (just v_B .: dot .: v_beta)
--         )
--       )
--       (span v_i v_k)


-- | TSG complete rule
complete :: Grammar -> Ty PattFun (Item -> Item -> Item)
complete gram =
  withVars $ \a b c as i j k alpha beta ->
    arg (item (rule a as) (span i j)) .
    arg (item
          (rule c (suffix $ dot .: nil))
          (span j k)) .
    fun $
      match
        (pair alpha (dot .: just b .: beta))
        (apply splitAt dot as)
        `seqp`
      choice
        ( match (label b) (label c) `seqp`
          match (leaf gram b) true `seqp`
          match (root gram c) true )
        ( match b c `seqp`
          match (internal gram b) true `seqp`
          match (internal gram c) true )
        `seqp`
      item
        (rule a (apply append alpha (just b .: dot .: beta)))
        (span i k)

--     condP = or
--       ( and
--           ( eq (map label v_B)
--                (map label v_C)
--           )
--           ( and (leaf gram v_B)
--                 (root gram v_C)
--           )
--       )
--       ( and
--           ( eq v_B v_C )
--           ( and (internal gram v_B)
--                 (internal gram v_C)
--           )
--       )
--
--     downP = item
--       (rule v_A
--         ( apply append
--             v_alpha
--             (just v_B .: dot .: v_beta)
--         )
--       )
--       (span v_i v_k)
