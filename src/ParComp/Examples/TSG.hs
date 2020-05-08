{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}


-- | TSG parsing example


module ParComp.Examples.TSG
  ( testTSG
  ) where


import           Prelude hiding
  (splitAt, span, map, or, and, any, const, head)
import qualified Prelude as P

import           Control.Monad (forM_)
import qualified Control.Monad as P

import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import           Data.Maybe (fromJust)

import           ParComp.Pattern.Untyped (Fun(..))
import qualified ParComp.Pattern.Typed as Ty
import           ParComp.Pattern.Typed
  ( Pattern, Patt(..), Cond
  , pair, nothing, just, nil, cons
  , left, right, bimap, guard
  )
import qualified ParComp.Pattern.Util as U

import           ParComp.Parser (chartParse)

import           Debug.Trace (trace)


--------------------------------------------------
-- TSG item
--------------------------------------------------


-- | Item's span
type Span = (Int, Int)

-- | Grammar node
type Node = T.Text

-- | Non-terminal/terminal symbol
type Sym = T.Text

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


item :: Pattern DotRule -> Pattern Span -> Pattern Item
item r s = left $ pair r s

top :: Pattern DotRule -> Pattern Item
top = right

rule :: Pattern Head -> Pattern Body -> Pattern DotRule
rule = pair

span :: Pattern Int -> Pattern Int -> Pattern Span
span = pair

pos :: Int -> Pattern Int
pos = const

head :: Node -> Pattern Head
head = const

-- | Dot in a dotted rule
dot :: Pattern (Maybe Node)
dot = nothing


--------------------------------------------------
-- Utility functions / patterns
--------------------------------------------------


-- | Synonym to `cons`
(.:) :: Pattern a -> Pattern [a] -> Pattern [a]
(.:) = cons
infixr 5 .:


-- | Split at dot.
splitAtDot :: Pattern (Body -> (Body, Body))
splitAtDot = fun $ _splitAt "splitAtDot" Nothing


-- | Split a list at a given value.
_splitAt :: (Eq a) => T.Text -> a -> Fun [a] ([a], [a])
_splitAt txt y =
  Fun txt ((:[]) . go)
  where
    go list@(x:xs)
      | x == y = ([], list)
      | otherwise =
          let (pref, suff) = go xs
           in (x:pref, suff)
    go [] = ([], [])


-- | Safe version of `last`
lastMaybe :: [a] -> Maybe a
lastMaybe = \case
  [] -> Nothing
  [x] -> Just x
  _ : xs -> lastMaybe xs


-- -- | Does the body of the dotted rule ends with the dot?
-- endsWithDotP :: Pred Body
-- endsWithDotP = endsWithP "endsWithDotP" Nothing
--
--
-- -- | Check if the list ends with dot.  If so, return it as is.
-- endsWithP :: (Eq a) => T.Text -> a -> Pred [a]
-- endsWithP txt y = Pred txt $ \xs ->
--   lastMaybe xs == Just y


-- | Does the body of the dotted rule ends with the dot?
endsWithDotP :: Fun Body Bool
endsWithDotP = endsWithP "endsWithDotP" Nothing


-- | Check if the list ends with dot.  If so, return it as is.
endsWithP :: (Eq a) => T.Text -> a -> Fun [a] Bool
endsWithP txt y = Fun txt $ \xs -> do
  return (lastMaybe xs == Just y)


--------------------------------------------------
-- Grammar
--------------------------------------------------


type Rule = (T.Text, [T.Text])


-- | Make the grammar from the set of CFG rules and the input sentence.
mkGram :: [T.Text] -> S.Set Rule -> Grammar
mkGram sent cfgRules = Grammar
  { leafs = leafs
  , roots = roots
  , inter = internals
  }
  where
    -- Heads, roots, and leafs
    heads = S.fromList . (++) sent $ do
      (hd, _bd) <- S.toList cfgRules
      return hd
    children = S.fromList $ do
      (_hd, bd) <- S.toList cfgRules
      bd
    internals = S.intersection heads children
    leafs = children `S.difference` internals
    roots = heads `S.difference` internals


-- | Grammar
data Grammar = Grammar
  { leafs :: S.Set Node
    -- ^ Set of grammar leaf nodes
  , roots :: S.Set Node
    -- ^ Set of grammar root nodes
  , inter  :: S.Set Node
    -- ^ Set of grammar internal nodes
  }


--------------------------------------------------
-- Grammar functions / patterns
--------------------------------------------------

-- | Node label
label :: Pattern (Node -> Sym)
label = fun $ Fun "label" nodeLabel


-- | Determine the label of the node.
nodeLabel :: Node -> [Sym]
nodeLabel x = case T.splitOn "_" x of
  [term] -> [term]
  [nonTerm, _nodeId] -> [nonTerm]
  _ -> error $ "nodeLabel: unhandled symbol (" ++ T.unpack x ++ ")"


-- | Leaf node predicate
leaf :: Grammar -> Pattern Node -> Pattern Cond
-- leaf gram = check $ Pred "leaf" $ \x -> x `S.member` leafs gram
leaf gram =
  let namedFun = Fun "leaf" $ \x -> pure (x `S.member` leafs gram)
   in isTrue . map (fun namedFun)


-- | Root node predicate
root :: Grammar -> Pattern Node -> Pattern Cond
-- root gram = check $ Pred "root" $ \x -> x `S.member` roots gram
root gram =
  let namedFun = Fun "root" $ \x -> pure (x `S.member` roots gram)
   in isTrue . map (fun namedFun)


-- | Internal node predicate
internal :: Grammar -> Pattern Node -> Pattern Cond
-- internal gram = check $ Pred "internal" $ \x -> x `S.member` inter gram
internal gram =
  let namedFun = Fun "internal" $ \x -> pure (x `S.member` inter gram)
   in isTrue . map (fun namedFun)


--------------------------------------------------
-- Rules
--------------------------------------------------


-- | TSG complete rule
complete :: Grammar -> Ty.Rule Item
complete gram =

  Ty.Rule [leftP, rightP] downP condP

  where

    -- Variables
    v_A = var "A"         :: Pattern Node
    v_B = var "B"         :: Pattern Node
    v_C = var "C"         :: Pattern Node
    v_alpha = var "alpha" :: Pattern Body
    v_beta = var "beta"   :: Pattern Body
    v_i = var "i"         :: Pattern Int
    v_j = var "j"         :: Pattern Int
    v_k = var "k"         :: Pattern Int

    leftP = item
      (rule v_A
        (via splitAtDot
          (pair v_alpha (dot .: just v_B .: v_beta))
        )
      )
      (span v_i v_j)

    rightP = item
      (rule v_C
        (guard endsWithDotP)
        -- (suffix $ dot .: nil)
      )
      (span v_j v_k)

    condP = or
      ( and
          ( eq (map label v_B)
               (map label v_C)
          )
          ( and (leaf gram v_B)
                (root gram v_C)
          )
      )
      ( and
          ( eq v_B v_C )
          ( and (internal gram v_B)
                (internal gram v_C)
          )
      )

    downP = item
      (rule v_A
        ( bimap U.append
            v_alpha
            (just v_B .: dot .: v_beta)
        )
      )
      (span v_i v_k)


-- | TSG predict rule
predict :: Grammar -> Ty.Rule Item
predict gram =

  Ty.Rule [leftP, rightP] downP condP

  where

    -- Variables
    v_B = var "B"         :: Pattern Node
    v_C = var "C"         :: Pattern Node
    v_i = var "i"         :: Pattern Int
    v_j = var "j"         :: Pattern Int
    v_rule = var "rule"   :: Pattern DotRule

    leftP = item
      (rule any
        ( via splitAtDot
            (pair any (dot .: just v_B .: any))
        )
      )
      (span v_i v_j)

    rightP = top $ rule v_C any `and` v_rule

    condP = or
      ( and
          ( eq (map label v_B)
               (map label v_C)
          )
          ( and (leaf gram v_B)
                (root gram v_C)
          )
      )
      ( and
          ( eq v_B v_C
          )
          ( and (internal gram v_B)
                (internal gram v_C)
          )
      )

    downP = item v_rule (span v_j v_j)


-- | Compute the base items for the given sentence and grammar
cfgBaseItems 
  :: [T.Text]
    -- ^ Input sentence
  -> S.Set (T.Text, [T.Text])
    -- ^ TSG rules
  -> [Item]
cfgBaseItems inp cfgRules =
  base1 ++ base2 ++ baseRules
  where
    n = length inp
    base1 = do
      (hd, bd) <- S.toList cfgRules
      return $ Left (mkRule hd bd, (0, 0))
    base2 = do
      (i, term) <- zip [0..n-1] inp
      return $ Left (mkRule term [], (i, i + 1))
    baseRules = do
      (hd, bd) <- S.toList cfgRules
      return $ Right (mkRule hd bd)
    mkRule hd bd = (hd, Nothing : fmap Just bd)


--------------------------------------------------
-- Main
--------------------------------------------------


testTSG :: IO ()
testTSG = do
  let cfgRules = S.fromList
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
--         [ ("NP_1", ["DET_2", "N_3"])
--         , ("DET_2", ["a_3"])
--         , ("N_4", ["man_5"])
--         ]

      -- Input sentence
      -- sent = ["a", "man"]
      sent = ["a", "man", "quickly", "eats", "some", "pizza"]

      gram = mkGram sent cfgRules
      baseItems = cfgBaseItems sent cfgRules
      ruleMap = M.fromList
        [ ("CO", complete gram)
        , ("PR", predict gram)
        ]
      finalPatt = item any
        (span (pos 0) (pos $ length sent))
--   forM_ baseItems print
--   putStr "roots: " >> print roots
--   putStr "leafs: " >> print leafs
--   putStr "internals: " >> print internals
  chartParse baseItems ruleMap finalPatt >>= \case
    Nothing -> putStrLn "# No parse found"
    Just it -> print it 
