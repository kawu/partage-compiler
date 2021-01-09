{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
-- {-# LANGUAGE ScopedTypeVariables #-}


-- | Context-free grammar parsing


module ParComp.Examples.CFG
  ( runCFG
  , testCFG
  ) where


import           Prelude hiding (splitAt, span)

import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import           ParComp.Patt.Core (Item (..))

import           ParComp.Patt
import qualified ParComp.Patt.Item as I

import qualified ParComp.SimpleParser as SP
import           ParComp.Examples.Utils


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


-- | Dot in a dotted rule
dot :: Ty Patt (Maybe Node)
dot = nothing


-------------------------------------------------------------------------------
-- Grammar representation
-------------------------------------------------------------------------------


-- | Pattern to extract the non-terminal / terminal symbol of a node
label :: Ty Patt Node -> Ty Patt Sym
label =
  foreign1arg "label" extract
  where
    extract (I.unEither -> Left (I.unPair -> (x, _))) = x
    extract (I.unEither -> Right x) = x


-------------------------------------------------------------------------------
-- CFG deduction rules
-------------------------------------------------------------------------------


-- | CFG complete rule
complete :: Ty PattFun (TopItem -> TopItem -> TopItem)
complete =
  withVars $ \a as b c alpha beta i j k ->
    arg (item (rule a as) (span i j)) .
    arg (item (rule c (suffix (dot .: nil))) (span j k)) .
    fun $
      match
        (pair alpha (dot .: just b .: beta))
        (apply splitAt dot as) `seqp`
      check (label b `eq` label c) `seqp`
      item
        (rule a (apply append alpha (just b .: dot .: beta)))
        (span i k)


-- | CFG predict rule
predict :: Ty PattFun (TopItem -> TopItem -> TopItem)
predict =
  withVars $ \i j b c alpha ->
    arg (item (rule anyp (suffix (dot .: just b .: anyp))) (span i j)) .
    arg (top (rule c alpha)) .
    fun $
      match (label b) (label c) `seqp`
      item (rule c alpha) (span j j)


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
runCFG :: IO (Maybe Item)
runCFG = do
  let baseItems = map (unTy . encode I) $ cfgBaseItems testSent testRules
      ruleMap = M.fromList
        [ ("CO", unTy complete)
        , ("PR", unTy predict)
        ]
      zero = pos 0
      slen = pos (length testSent)
      finalPatt = unTy $ item anyp (span zero slen)
  SP.chartParse baseItems ruleMap finalPatt


-- | Run the parser on the test grammar and sentence.
testCFG :: IO ()
testCFG = do
  runCFG >>= \case
    Nothing -> putStrLn "# No parse found"
    Just it -> print $ (decode (Ty it) :: TopItem)


-------------------------------------------------------------------------------
-- Alternative foreign functions, for the record
-------------------------------------------------------------------------------


-- -- | Append two lists
-- append :: Ty Patt [a] -> Ty Patt [a] -> Ty Patt [a]
-- append =
--   foreign2arg "append" I.append


-- -- | Check if the item contains a given suffix.
-- suffix p =
--   xs `seqp` check cond `seqp` xs
--   where
--     xs = var "xs"
--     cond = eq (hasSuffix p xs) true
--     hasSuffix = foreign2arg "suffix" I.suffix


-- splitAtDot :: Ty Patt Body -> Ty Patt (Body, Body)
-- splitAtDot =
--   splitAt dot
--
--
-- -- | Split a list at a given element
-- splitAt :: Ty Patt a -> Ty Patt [a] -> Ty Patt ([a], [a])
-- splitAt =
--
--   foreign2arg "splitAt" doit
--
--   where
--
--     doit :: Ty Item a -> Ty Item [a] -> Ty Item ([a], [a])
--     doit at xs =
--       let (ls, rs) = go at xs
--        in I.pair ls rs
--
--     go at list = I.listI
--       (I.nil, I.nil)
--       (\x xs ->
--          if x == at
--          then (I.nil, list)
--          else
--            let (pref, suff) = go at xs
--             in (I.cons x pref, suff)
--       ) list
