{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
-- {-# LANGUAGE ScopedTypeVariables #-}


-- | Context-free grammar parsing


module ParComp.Examples.CFGBis
  ( runCFGBis
  , testCFGBis
  ) where


import           Prelude hiding (splitAt, span)  -- , map, or, and, any, const, head)

import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import           Data.String (fromString)

import qualified ParComp.Patt.Core as C
import           ParComp.Patt.Core
  (Item (..), Fun (..), FunName (..), Op (..))

import           ParComp.Patt
import qualified ParComp.Patt.Item as I
import qualified ParComp.Patt.Typed as Ty
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
type TopItem = Either Active DotRule


-------------------------------------------------------------------------------
-- Item patterns
--
-- Note that it should not be necessary to define the item patterns manually.
-- The plan is to automatically generated such patterns for custom data types
-- using Template Haskell.
-------------------------------------------------------------------------------


-- | Top-level active item pattern
item :: Ty Patt DotRule -> Ty Patt Span -> Ty Patt TopItem
item r s = left $ pair r s


-- | Dotted rule as a top-level item
top :: Ty Patt DotRule -> Ty Patt TopItem
top = right


-- | Dotted rule
rule :: Ty Patt Head -> Ty Patt Body -> Ty Patt DotRule
rule = pair


-- | Item's span
span :: Ty Patt Int -> Ty Patt Int -> Ty Patt Span
span = pair


-- | Position in a sentence
pos :: Int -> Ty Patt Int
pos = encode P


-- | Dotted rule's head
head :: Node -> Ty Patt Head
head = encode P


-- | Dot in a dotted rule
dot :: Ty Patt (Maybe Node)
dot = nothing


-------------------------------------------------------------------------------
-- Grammar representation
-------------------------------------------------------------------------------


-- TODO: Move `foreignFun` etc. to a different module


-- | Name a function and lift it to a pattern-level function
foreignFun :: FunName -> (Ty Item a -> Ty Item b) -> Ty Patt a -> Ty Patt b
foreignFun funName f =
  let named = Fun funName $ \x -> [unTy $ f $ Ty x]
   in Ty . O . Apply named . unTy


-- | 2-argument variant of `name`
foreignFun2
  :: FunName
  -> (Ty Item a -> Ty Item b -> Ty Item c)
  -> Ty Patt a -> Ty Patt b -> Ty Patt c
foreignFun2 funName f =
  let named = Fun funName $ \x -> [unTy $ I.pairI f $ Ty x]
   in \x y -> Ty . O . Apply named . unTy $ pair x y


-- | Pattern to extract the non-terminal / terminal symbol of a node
label :: Ty Patt Node -> Ty Patt Sym
label =
  foreignFun "label" extract
  where
    extract (I.unEither -> Left (I.unPair -> (x, _))) = x
    extract (I.unEither -> Right x) = x
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
  { antecedents  = [unTy leftP, unTy rightP]
  , consequent = unTy downP
  , condition = condP
  }

  where

    -- Variables (declaring them with type annotations provides additional type
    -- safety, but is not obligatory; see the prediction rule below, where type
    -- annotations are not used, for comparison)
    v_A = var "A"         :: Ty Patt Node
    v_As = var "As"       :: Ty Patt Body
    v_B = var "B"         :: Ty Patt Node
    v_C = var "C"         :: Ty Patt Node
    v_alpha = var "alpha" :: Ty Patt Body
    v_beta = var "beta"   :: Ty Patt Body
    v_i = var "i"         :: Ty Patt Int
    v_j = var "j"         :: Ty Patt Int
    v_k = var "k"         :: Ty Patt Int

    leftP = item (rule v_A v_As) (span v_i v_j) `seqp`
            assign
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
    -- TODO: not safe!
    condP = eq (label v_B) (label v_C)

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
--     downP = item
--       (rule v_A
--         (bimap Util.append
--           v_alpha
--           (just v_B .: dot .: v_beta)
--         )
--       )
--       (span v_i v_k)



-- | CFG predict rule
predict :: Rule
predict =
  Rule [unTy leftP, unTy rightP] (unTy downP) condP
  where
--     -- TODO: This does not work due to the `suffix`, which should not
--     -- take a matching pattern as its first argument!
--     leftP = item
--       (rule anyp
--         (suffix $ dot .: just (var "B") .: anyp)
--       )
--       (span (var "i") (var "j"))
    leftP = item
      (rule anyp (var "body"))
      (span (var "i") (var "j"))
      `seqp`
      assign
        (pair anyp (dot .: just (var "B") .: anyp))
        (splitAtDot (var "body"))
    rightP = top $
      rule (var "C") (var "alpha")
    condP = eq
      (label (var "B"))
      (label (var "C"))
    downP = item
      (rule (var "C") (var "alpha"))
      (span (var "j") (var "j"))


-------------------------------------------------------------------------------
-- Axioms
-------------------------------------------------------------------------------


-- | Enumerate base items for the given sentence and grammar.
cfgBaseItems
  :: [T.Text]                   -- ^ Input sentence
  -> S.Set (Node, [Node])       -- ^ CFG rules: set of (head, body) pairs
  -> [TopItem]
cfgBaseItems inp cfgRules =
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


-------------------------------------------------------------------------------
-- Main
-------------------------------------------------------------------------------


-- | Test CFG-like grammar (instead of non-terminals, nodes are used)
testRules :: S.Set (Node, [Node])
testRules = S.fromList $ fmap prepareRule
  [ ("NP_1", ["N_2"])
  , ("NP_3", ["DET_4", "N_5"])
  , ("S_6", ["NP_7", "VP_8"])
  , ("VP_9", ["V_10"])
  , ("VP_11", ["V_12", "Adv_13"])
  , ("VP_14", ["Adv_15", "V_16"])
  , ("VP_17", ["Adv_18", "V_19", "NP_20"])
  , ("DET_21", ["a"])
  , ("DET_22", ["some"])
  , ("N_23", ["man"])
  , ("N_24", ["pizza"])
  , ("V_25", ["eats"])
  , ("V_26", ["runs"])
  , ("Adv_27", ["quickly"])
  ]
  where
    prepareRule (hd, bd) =
      ( prepareNode hd
      , fmap prepareNode bd
      )
    prepareNode x = case T.splitOn "_" x of
      [term] -> Right term
      [nonTerm, nodeId] -> Left (nonTerm, nodeId)
      _ -> error $ "testRules: unhandled symbol (" ++ T.unpack x ++ ")"


-- | Test sentence to parse
testSent :: [T.Text]
testSent = ["a", "man", "quickly", "eats", "some", "pizza"]


-- | Run the parser on the test grammar and sentence.
runCFGBis :: IO (Maybe Item)
runCFGBis = do
  let baseItems = map (unTy . encode I) $ cfgBaseItems testSent testRules
      ruleMap = M.fromList
        [ ("CO", complete)
        , ("PR", predict)
        ]
      zero = pos 0
      slen = pos (length testSent)
      finalPatt = unTy $ item anyp (span zero slen)
  SP.chartParse baseItems ruleMap finalPatt


-- | Run the parser on the test grammar and sentence.
testCFGBis :: IO ()
testCFGBis = do
  runCFGBis >>= \case
    Nothing -> putStrLn "# No parse found"
    Just it -> print $ (decode (Ty it) :: TopItem)


--------------------------------------------------
-- Utility patterns
--------------------------------------------------


-- | Operator synonym to `cons`
-- (.:) :: (Patt repr) => repr a -> repr [a] -> repr [a]
(.:) :: Ty Patt a -> Ty Patt [a] -> Ty Patt [a]
(.:) = cons
infixr 5 .:


splitAtDot :: Ty Patt Body -> Ty Patt (Body, Body)
splitAtDot =
  splitAt dot


-- | Split a list at a given element
splitAt :: Ty Patt a -> Ty Patt [a] -> Ty Patt ([a], [a])
splitAt =

  foreignFun2 "splitAt" doit

  where

    doit :: Ty Item a -> Ty Item [a] -> Ty Item ([a], [a])
    doit at xs =
      let (ls, rs) = go at xs
       in Ty.pair I ls rs

    go :: Ty Item a -> Ty Item [a] -> (Ty Item [a], Ty Item [a])
    go at list = I.listI
      (Ty.nil I, Ty.nil I)
      (\x xs ->
         if x == at
         then (Ty.nil I, list)
         else
           let (pref, suff) = go at xs
            in (Ty.cons I x pref, suff)
      ) list


-- | Append two lists
append :: Ty Patt [a] -> Ty Patt [a] -> Ty Patt [a]
append =
  foreignFun2 "append" I.append
--   O . Apply app $ pair p q
--   where
--     app = Fun "append" $ I.pair' (\xs ys -> [I.append xs ys])


-- | Check if the list contains a given suffix.
-- TODO: This is somewhat ugly, also the argument pattern cannot contain free
-- variables...
suffix :: Ty Patt [a] -> Ty Patt [a]
suffix p =
  xs `seqp` check cond `seqp` xs
  where
    xs = var "xs"
    cond = eq (hasSuffix p xs) true
    hasSuffix = foreignFun2 "suffix" I.suffix
