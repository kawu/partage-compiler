{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}


-- | Context-free grammar parsing


module ParComp.Examples.CFGBis
  ( -- runCFG
  , -- testCFG
  ) where


import           Prelude hiding
  (splitAt, span, map, or, and, any, const, head)

import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import qualified Data.Primitive.Array as A

import qualified ParComp.Item as I
import qualified ParComp.Pattern.UntypedBis as Un
import           ParComp.Pattern.UntypedBis
  (Patt (..), M, C, Cond (..))
import qualified ParComp.Pattern.RuleBis as R
import           ParComp.Pattern.RuleBis (Rule (..))

-- import           ParComp.Pattern.Untyped (Fun(..))
-- import           ParComp.Pattern.Typed
--   ( Pattern(..), Patt(..), Rule(..)
--   , pair, nothing, just, nil, cons, left, right, bimap
--   )
-- import qualified ParComp.Pattern.Util as Util

-- import qualified ParComp.Parser as P
import qualified ParComp.SimpleParserBis as SP


-------------------------------------------------------------------------------
-- Item types
-------------------------------------------------------------------------------


-- | Item's span
type Span = (Int, Int)


-- | Non-terminal/terminal symbol (label)
type Sym = T.Text


-- | Node identifier
type ID = T.Text


-- | Grammar node is either a non-terminal (label + identifier) node or a
-- terminal (only label) node.  In CFG there's no need to decorate nodes with
-- identifiers, we do that for the sake of example (such identifiers can be
-- useful in TSG/TAG parsing, for instance).
type Node = Either (Sym, ID) Sym


-- | Dotted rule's head
type Head = Node


-- | Dotted rule's body (`Nothing` represents the dot)
type Body = [Maybe Node]


-- | Dotted rule
type DotRule = (Head, Body)


-- | Active item
type Active = (DotRule, Span)


-- | Top-level item: either an actual active item or a grammar dotted rule.
-- Top-level rules are later used in the prediction deduction rule (because we
-- can).
type Item = Either Active DotRule


-------------------------------------------------------------------------------
-- Core item patterns
--
-- TODO: Move elsewhere!  Note also code duplication w.r.t. `IsItem` instances
-- in `Item.hs`.
-------------------------------------------------------------------------------


-- | Unit () pattern
unit :: Patt t
unit = Const I.Unit


-- | Pair pattern
pair :: Patt t -> Patt t -> Patt t
pair x y = Vec $ A.fromListN 2 [x, y]


-- | Cons (list) pattern
nil :: Patt t
nil = Tag 0 unit


-- | Cons (list) pattern
cons :: Patt t -> Patt t -> Patt t
-- cons x xs = Tag 1 $ Vec $ A.fromListN 2 [x, xs]
cons x xs = Tag 1 $ pair x xs


-- | Left pattern (`Either`)
left :: Patt t -> Patt t
left = Tag 0


-- | Right pattern (`Either`)
right :: Patt t -> Patt t
right = Tag 1


-- | Pair pattern
nothing :: Patt t
nothing = Tag 0 unit


-- | Pair pattern
just :: Patt t -> Patt t
just = Tag 1


-------------------------------------------------------------------------------
-- Item patterns (Untyped)
--
-- TODO: Type!
--
-- Note that it should not be necessary to define the item patterns manually.
-- The plan is to automatically generated such patterns for custom data types
-- using Template Haskell.
-------------------------------------------------------------------------------


-- | Top-level active item pattern
-- item :: Patt repr => repr DotRule -> repr Span -> repr Item
item :: Patt t -> Patt t -> Patt t
item r s = left $ pair r s


-- | Dotted rule as a top-level item
-- top :: Patt repr => repr DotRule -> repr Item
top :: Patt t -> Patt t
top = right


-- | Dotted rule
-- rule :: Patt repr => repr Head -> repr Body -> repr DotRule
rule :: Patt t -> Patt t -> Patt t
rule = pair


-- | Item's span
-- span :: Patt repr => repr Int -> repr Int -> repr Span
span :: Patt t -> Patt t -> Patt t
span = pair


-- | Position in a sentence
-- pos :: Patt repr => Int -> repr Int
pos :: Int -> Patt t
pos = Const . I.encode


-- | Dotted rule's head
-- head :: Patt repr => Node -> repr Head
head :: Node -> Patt t
head = Const . I.encode


-- | Dot in a dotted rule
-- dot :: Patt repr => repr (Maybe Node)
dot :: Patt t
dot = nothing


-------------------------------------------------------------------------------
-- Grammar representation
-------------------------------------------------------------------------------


-- | Pattern to extract the non-terminal / terminal symbol of a node
-- TODO: Need to register the function first!
label :: Patt C -> Patt C
label = Apply "label"
-- label =
--   fun (Fun "label" nodeLabel)
--   where
--     nodeLabel (Left (nonTerm, _nodeId)) = [nonTerm]
--     nodeLabel (Right term) = [term]


-------------------------------------------------------------------------------
-- CFG deduction rules
-------------------------------------------------------------------------------


-- | CFG complete rule
complete :: Rule
complete =

  Rule
  { antecedents  = [leftP, rightP]
  , consequent = downP
  , condition = condP
  }

  where

    -- Variables (declaring them with type annotations provides additional type
    -- safety, but is not obligatory; see the prediction rule below, where type
    -- annotations are not used, for comparison)
    v_A = Label "A"         :: Patt t
    v_As = Label "As"       :: Patt t
    v_B = Label "B"         :: Patt t
    v_C = Label "C"         :: Patt t
    -- v_Cs = Label "Cs"       :: Patt t
    v_alpha = Label "alpha" :: Patt t
    v_beta = Label "beta"   :: Patt t
    v_i = Label "i"         :: Patt t
    v_j = Label "j"         :: Patt t
    v_k = Label "k"         :: Patt t

    leftP = item (rule v_A v_As) (span v_i v_j)
      `Seq` Assign
                (pair v_alpha (dot .: just v_B .: v_beta))
                (splitAtDot v_As)

--     -- First antecendent
--     leftP = item
--       (rule v_A
--         (via splitAtDot
--           (pair v_alpha (dot .: just v_B .: v_beta))
--         )
--       )
--       (span v_i v_j)

    -- Second antecendent
    rightP = item
      (rule v_C (suffix (dot .: nil)))
      (span v_j v_k)

--     -- Second antecendent
--     rightP = item
--       (rule v_C (suffix (dot .: nil)))
--       (span v_j v_k)

    -- Side condition
    condP = Eq (label v_B) (label v_C)

--
--     -- Side condition
--     condP = eq
--       (map label v_B)
--       (map label v_C)

    -- Consequent
    downP = item
      (rule v_A
        (append
          v_alpha
          (just v_B .: dot .: v_beta)
        )
      )
      (span v_i v_k)

--
--     -- Consequent
--     downP = item
--       (rule v_A
--         (bimap Util.append
--           v_alpha
--           (just v_B .: dot .: v_beta)
--         )
--       )
--       (span v_i v_k)
--
--
--
-- -- | CFG predict rule
-- predict :: Rule Item
-- predict =
--   Rule [leftP, rightP] downP condP
--   where
--     leftP = item
--       (rule any
--         (suffix $ dot .: just (var "B") .: any)
--       )
--       (span (var "i") (var "j"))
--     rightP = top $
--       rule (var "C") (var "alpha")
--     condP = eq
--       (map label (var "B"))
--       (map label (var "C"))
--     downP = item
--       (rule (var "C") (var "alpha"))
--       (span (var "j") (var "j"))
--
--
-- -------------------------------------------------------------------------------
-- -- Axioms
-- -------------------------------------------------------------------------------
--
--
-- -- | Enumerate base items for the given sentence and grammar.
-- cfgBaseItems
--   :: [T.Text]                   -- ^ Input sentence
--   -> S.Set (Node, [Node])       -- ^ CFG rules: set of (head, body) pairs
--   -> [Item]
-- cfgBaseItems inp cfgRules =
--   base1 ++ base2 ++ baseRules
--   where
--     n = length inp
--     base1 = do
--       (hd, bd) <- S.toList cfgRules
--       return $ Left (mkRule hd bd, (0, 0))
--     base2 = do
--       (i, term) <- zip [0..n-1] inp
--       return $ Left (mkRule (Right term) [], (i, i + 1))
--     baseRules = do
--       (hd, bd) <- S.toList cfgRules
--       return $ Right (mkRule hd bd)
--     mkRule hd bd = (hd, Nothing : fmap Just bd)
--
--
-- -------------------------------------------------------------------------------
-- -- Main
-- -------------------------------------------------------------------------------
--
--
-- -- | Test CFG-like grammar (instead of non-terminals, nodes are used)
-- testRules :: S.Set (Node, [Node])
-- testRules = S.fromList $ fmap prepareRule
--   [ ("NP_1", ["N_2"])
--   , ("NP_3", ["DET_4", "N_5"])
--   , ("S_6", ["NP_7", "VP_8"])
--   , ("VP_9", ["V_10"])
--   , ("VP_11", ["V_12", "Adv_13"])
--   , ("VP_14", ["Adv_15", "V_16"])
--   , ("VP_17", ["Adv_18", "V_19", "NP_20"])
--   , ("DET_21", ["a"])
--   , ("DET_22", ["some"])
--   , ("N_23", ["man"])
--   , ("N_24", ["pizza"])
--   , ("V_25", ["eats"])
--   , ("V_26", ["runs"])
--   , ("Adv_27", ["quickly"])
--   ]
--   where
--     prepareRule (hd, bd) =
--       ( prepareNode hd
--       , fmap prepareNode bd
--       )
--     prepareNode x = case T.splitOn "_" x of
--       [term] -> Right term
--       [nonTerm, nodeId] -> Left (nonTerm, nodeId)
--       _ -> error $ "testRules: unhandled symbol (" ++ T.unpack x ++ ")"
--
--
-- -- | Test sentence to parse
-- testSent :: [T.Text]
-- testSent = ["a", "man", "quickly", "eats", "some", "pizza"]
--
--
-- -- | Run the parser on the test grammar and sentence.
-- runCFG :: Bool -> IO (Maybe Item)
-- runCFG simpleParser = do
--   let baseItems = cfgBaseItems testSent testRules
--       ruleMap = M.fromList
--         [ ("CO", complete)
--         , ("PR", predict)
--         ]
--       zero = pos 0
--       slen = pos (length testSent)
--       finalPatt = item any (span zero slen)
--   if simpleParser
--      then SP.chartParse baseItems ruleMap finalPatt
--      else P.chartParse  baseItems ruleMap finalPatt
--
--
-- -- | Run the parser on the test grammar and sentence.
-- testCFG :: IO ()
-- testCFG = do
--   runCFG False >>= \case
--     Nothing -> putStrLn "# No parse found"
--     Just it -> print it


--------------------------------------------------
-- Utility patterns
--------------------------------------------------


-- | Operator synonym to `cons`
-- (.:) :: (Patt repr) => repr a -> repr [a] -> repr [a]
(.:) :: Patt t -> Patt t -> Patt t
(.:) = cons
infixr 5 .:



-- | Split a rule's body at the dot
-- TODO: Need to register the function first!
-- splitAtDot :: Patt repr => repr (Body -> (Body, Body))
splitAtDot :: Patt C -> Patt C
splitAtDot = Apply "splitAtDot"


-- | Append two lists
append :: Patt C -> Patt C -> Patt C
append = undefined


-- -- | Split a rule's body at the dot.
-- splitAtDot :: Patt repr => repr (Body -> (Body, Body))
-- splitAtDot =
--   fun (Fun "splitAtDot" ((:[]) . go))
--   where
--     go list@(x:xs)
--       -- dot is represented by Nothing
--       | x == Nothing = ([], list)
--       | otherwise =
--           let (pref, suff) = go xs
--            in (x:pref, suff)
--     go [] = ([], [])
--
--
-- -- | Match any suffix that satisfies the given suffix pattern.
-- suffix :: (Patt repr) => repr [a] -> repr [a]
-- suffix p = fix $ choice p (any .: rec)


-- | Check if the item contains a given suffix.
-- TODO: Need to register the function first!
-- suffix :: (Patt repr) => repr [a] -> repr [a]
suffix :: Patt C -> Patt M
suffix p = undefined
