{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}


-- | Tree-substitution grammar parsing


module ParComp.Examples.TSG
  ( runTSG
  , testTSG
  ) where


import           Prelude hiding (splitAt, span)

import qualified Data.Text as T
import qualified Data.Set as S
import qualified Data.Map.Strict as M

import           ParComp.Patt
import qualified ParComp.Patt.Item as I
import           ParComp.Examples.Utils
import qualified ParComp.SimpleParser as SP


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


-- | Grammar rule
type Rule = (Node, [Node])


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

-- | Make the grammar from the set of CFG rules and the input sentence.
mkGram :: [T.Text] -> S.Set Rule -> Grammar
mkGram sent rules = Grammar
  { leafs = leafs
  , roots = roots
  , inter = internals
  }
  where
    -- Heads, roots, and leafs
    terms = map (encodeI . Right) sent
    heads = S.fromList . (++) terms $ do
      (hd, _bd) <- S.toList rules
      return $ encodeI hd
    children = S.fromList $ do
      (_hd, bd) <- S.toList rules
      map encodeI bd
    internals = S.intersection heads children
    leafs = children `S.difference` internals
    roots = heads `S.difference` internals
    encodeI = encode I.I


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


-- | TSG predict rule
predict :: Grammar -> Ty PattFun (Item -> Item -> Item)
predict gram =
  withVars $ \as b c i j rl ->
    arg (item (rule anyp as) (span i j)) .
    arg (top (rule c anyp `seqp` rl)) .
    fun $
      match
        (pair anyp (dot .: just b .: anyp))
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
      item rl (span j j)


-- | Compute the base items for the given sentence and grammar
tsgBaseItems
  :: [T.Text]
    -- ^ Input sentence
  -> S.Set Rule
    -- ^ TSG rules
  -> [Item]
tsgBaseItems inp cfgRules =
  base1 ++ base2 ++ baseRules
  where
    n = length inp
    base1 = do
      (hd, bd) <- S.toList cfgRules
      return $ Left (mkRule hd bd, (0, 0))
    base2 = do
      (i, term) <- zip [0..n-1] inp
      return $ Left (mkRule (Right term) [], (i, i + 1))
    baseRules = do
      (hd, bd) <- S.toList cfgRules
      return $ Right (mkRule hd bd)
    mkRule hd bd = (hd, Nothing : fmap Just bd)


--------------------------------------------------
-- Main
--------------------------------------------------


testRules :: S.Set Rule
testRules = S.fromList $ fmap prepareRule
   [ ("NP_1", ["N_2"])
   , ("NP_3", ["DET_4", "N_5"])
   -- NB: "NP_28" is an internal node (see below)
   , ("S_6", ["NP_28", "VP_8"])
   , ("VP_9", ["V_10"])
   , ("VP_11", ["V_12", "Adv_13"])
   , ("VP_14", ["Adv_15", "V_16"])
   , ("VP_17", ["Adv_18", "V_19", "NP_20"])
   , ("DET_21", ["a_1"])
   , ("DET_22", ["some_2"])
   , ("N_23", ["man_3"])
   , ("N_24", ["pizza_4"])
   , ("V_25", ["eats_5"])
   , ("V_26", ["runs_6"])
   , ("Adv_27", ["quickly_7"])
   , ("NP_28", ["DET_29", "N_30"])
   ]
--   [ ("NP_1", ["DET_2", "N_3"])
--   , ("DET_2", ["a_3"])
--   , ("N_4", ["man_5"])
--   ]
  where
    prepareRule (hd, bd) =
      ( prepareNode hd
      , fmap prepareNode bd
      )
    prepareNode x = case T.splitOn "_" x of
      [term] -> Right term
      [nonTerm, nodeId] -> Left (nonTerm, nodeId)
      _ -> error $ "testRules: unhandled symbol (" ++ T.unpack x ++ ")"


-- Input sentence
testSent :: [T.Text]
testSent = ["a", "man", "quickly", "eats", "some", "pizza"]
-- testSent = ["a", "man"]


-- Grammar
testGram :: Grammar
testGram = mkGram testSent testRules


-- | Run the parser on the test grammar and sentence.
runTSG :: IO (Maybe I.Item)
runTSG = do
  let baseItems = map (unTy . encode I.I) $ tsgBaseItems testSent testRules
      ruleMap = M.fromList
        [ ("CO", unTy $ complete testGram)
        , ("PR", unTy $ predict testGram)
        ]
      zero = pos 0
      slen = pos (length testSent)
      finalPatt = unTy $ item anyp (span zero slen)
  SP.chartParse baseItems ruleMap finalPatt


-- | Run the parser on the test grammar and sentence.
testTSG :: IO ()
testTSG = do
  runTSG >>= \case
    Nothing -> putStrLn "# No parse found"
    Just it -> print (decode (Ty it) :: Item)
