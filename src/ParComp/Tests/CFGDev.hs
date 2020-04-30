{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}

{-# LANGUAGE ScopedTypeVariables #-}


-- | Context-free grammar parsing


module ParComp.Tests.CFGDev
  ( testCFGDev
  , suffix
  , testAppEnd
  , testX
  , testMatch
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

import qualified ParComp.ItemDev.Untyped as U
import           ParComp.ItemDev.Untyped (Fun(..), Pred(..), IsPatt(..))
import qualified ParComp.ItemDev.Typed as Ty
import           ParComp.ItemDev.Typed
  (Pattern(..), Op(..), bimap, guard)
import           ParComp.ParserDev (chartParse)

import           Debug.Trace (trace)


--------------------------------------------------
-- CFG item
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
type Top = Either Active DotRule


-- | Item tagless-final representation
class Item repr where
  topItem :: repr Active -> repr Top
  topRule :: repr DotRule -> repr Top
  active  :: repr DotRule -> repr Span -> repr Active
  span    :: repr Int -> repr Int -> repr Span
  pos     :: Int -> repr Int
  rule    :: repr Head -> repr Body -> repr DotRule
  head    :: Node -> repr Head
  body    :: Body -> repr Body

-- NB: The implementation of the individual functions must be consistent with
-- the `IsPatt` class.
instance Item Pattern where
  topItem (Patt it) = Patt (U.leftP it)
  topRule (Patt r)  = Patt (U.rightP r)
  active (Patt r) (Patt s) = Patt (U.pairP r s)
  span (Patt x) (Patt y) = Patt (U.pairP x y)
  rule (Patt h) (Patt b) = Patt (U.pairP h b)
  pos i   = Patt $ U.encodeP i
  head x  = Patt $ U.encodeP x
  body x  = Patt $ U.encodeP x


-- | Dot in a dotted rule
dot :: Maybe Node
dot = Nothing


--------------------------------------------------
-- Utility functions
--------------------------------------------------


-- | Replace any value by unit.
constF :: b -> Fun a b
constF x = Fun "constF" $ P.const [x]


-- | Append two lists.
append :: Fun ([a], [a]) [a]
append = Fun "append" $ \(xs, ys) -> do
  return (xs ++ ys)


-- | Construct a list from a head and a tail.
consList :: Fun (a, [a]) [a]
consList = Fun "consList" $ \(x, xs) -> do
  return (x : xs)


-- | Split at dot.
splitAtDot :: Fun Body (Body, Body)
splitAtDot = _splitAt "splitAtDot" dot


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


-- | Check if the list ends with dot.  If so, return it as is.
endsWith :: (Eq a) => T.Text -> a -> Fun [a] [a]
endsWith txt y = Fun txt $ \xs -> do
  P.guard $ lastMaybe xs == Just y
  return xs


-- | Make sure that the body of the dotted rule ends with the dot.
endsWithDot :: Fun Body Body
endsWithDot = endsWith "endsWithDot" dot


-- | Check if the list ends with dot.  If so, return it as is.
endsWithP :: (Eq a) => T.Text -> a -> Pred [a]
endsWithP txt y = Pred txt $ \xs ->
  lastMaybe xs == Just y


-- | Does the body of the dotted rule ends with the dot?
endsWithDotP :: Pred Body
endsWithDotP = endsWithP "endsWithDotP" dot


-- | Safe version of `last`
lastMaybe :: [a] -> Maybe a
lastMaybe = \case
  [] -> Nothing
  [x] -> Just x
  _ : xs -> lastMaybe xs


-- | Head label
labelH :: Fun Node Sym
labelH = Fun "labelH" nodeLabel


-- | Body element label
labelB :: Fun (Maybe Node) Sym
labelB = Fun "labelB" $ \case
  Nothing -> error "labelB: encountered Nothing"
  Just x -> nodeLabel x


-- | Determine the label of the node.
nodeLabel :: Node -> [Sym]
nodeLabel x = case T.splitOn "_" x of
  [term] -> [term]
  [nonTerm, _nodeId] -> [nonTerm]
  _ -> error $ "nodeLabel: unhandled symbol (" ++ T.unpack x ++ ")"


--------------------------------------------------
-- Utility patterns
--------------------------------------------------


-- | Operator synonym to `cons`
(<:) :: (Op repr) => repr a -> repr [a] -> repr [a]
(<:) = cons
infixr 5 <:


-- | Match any suffix that satisfies the given suffix pattern.
suffix :: (Op repr) => repr [a] -> repr [a]
suffix p = fix $ or p (any <: rec)


-- -- | Remove suffix starting with the given element.
-- removeSuffixCont
--   :: forall repr a. (Op repr)
--   => repr a       -- ^ First element of the suffix
--   -> repr [a]     -- ^ Suffix matching continuation
--   -> repr [a]     -- ^ The entire list
-- removeSuffixCont p cont =
--   fix $ p1 `or` (p2 `or` p3)
--   where
--     p1 = letIn any (p <: any) (nil `and` cont)
--     p2 = any <: rec
--     p3 = nil `and` cont


-- -- | Remove suffix starting with the given element.
-- removeSuffix :: forall repr a. (Op repr) => repr a -> repr ([a] -> [a])
-- removeSuffix p =
--   fix $ p1 `or` (p2 `or` p3)
--   where
--     p1 = letIn (p <: any) nil
--     p2 = expand (any <: rec)
--     p3 = expand nil


-- | Split a list @xs@ into two parts @(ys, zs)@ w.r.t pattern @p@ so that:
--
-- * @ys = removeSuffix p xs@
-- * @zs = suffix p xs@
--
splitAt :: forall repr a. (Op repr) => repr a -> repr ([a] -> ([a], [a]))
splitAt p =
  fix $ p1 `or` (p2 `or` p3)
  where
    p1 = letIn
      ((p <: any) `and` local "suff")
      (pair nil (local "suff"))
    p2 = letIn
      (local "x" <: via
        splitRec
        (pair (local "xs") (local "ys"))
      )
      (pair (local "x" <: local "xs") (local "ys"))
    p3 = letIn nil (pair nil nil)

    -- NB: defining and annotating `splitRec` is optional, but it allows to
    -- verify that the types (of `fix` and `rec`) match.
    splitRec :: repr ([a] -> ([a], [a]))
    splitRec = rec


-- | Append the first list at the end of the second list.
appendEnd :: forall repr a. (Op repr) => repr [a] -> repr ([a] -> [a])
appendEnd ys =
  fix $ p1 `or` p2
  where
    p1 = letIn nil ys
    p2 = letIn
      (local "x" <: via rec (local "xs"))
      (local "x" <: local "xs")


-- | Append two lists.
append' :: forall repr a. (Op repr) => repr [a] -> repr [a] -> repr [a]
append' xs ys = map (appendEnd ys) xs


--------------------------------------------------
-- Tests
--------------------------------------------------


testAppEnd :: Pattern (Body -> Body)
testAppEnd = appendEnd nil


testX :: Body
testX = [Nothing, Just "a"]


testMatch :: IO ()
testMatch = U.runMatchT $ do
  let f = unPatt testAppEnd
      x = U.encodeI testX
  it' <- U.match U.Strict f x
  U.lift $ do
    putStr "f   : " >> print f
    putStr "x   : " >> print testX
    putStr "it' : " >> print (U.decodeI it' :: Body)


-- testApp :: Pattern [Int]
-- testApp = append'
--   (const 1 <: const 2 <: nil)
--   (const 3 <: const 4 <: nil)


--------------------------------------------------
-- Rules
--------------------------------------------------


-- | Typed deduction rule
data Rule repr = Rule
  { antecedents :: [repr Top]
  , consequent  :: repr Top
  , sideCond    :: repr Bool
  }


-- | Compile the rule to its untyped counterpart.
compileRule :: Rule Pattern -> U.Rule
compileRule Rule{..} = U.Rule
  { U.antecedents = P.map Ty.unPatt antecedents
  , U.consequent  = Ty.unPatt consequent
  , U.condition   = Ty.unCond sideCond
  }


-- | CFG complete rule
complete :: U.Rule
complete =

  compileRule $
    Rule [leftP, rightP] downP condP

  where

    leftP = topItem $ active
      (rule v_A
        -- (via (fun splitAtDot)
        (via (splitAt (const dot))
          (pair v_alpha (const dot <: v_B <: v_beta))
        )
      )
      (span v_i v_j)

    rightP = topItem $ active
      (rule v_C
        -- (guard endsWithDotP)
        (suffix $ const dot <: nil)
        -- (removeSuffix (const dot) any)
      )
      (span v_j v_k)

    condP = eq
      (map (fun labelB) v_B)
      (map (fun labelH) v_C)

    downP = topItem $ active
      (rule v_A
        (append'
        -- (bimap append
          v_alpha
          (v_B <: const dot <: v_beta)
        )
      )
      (span v_i v_k)

    -- Variables and their types
    v_A = var "A"         :: Pattern Node
    v_B = var "B"         :: Pattern (Maybe Node)
    v_C = var "C"         :: Pattern Node
    v_alpha = var "alpha" :: Pattern Body
    v_beta = var "beta"   :: Pattern Body
    v_i = var "i"         :: Pattern Int
    v_j = var "j"         :: Pattern Int
    v_k = var "k"         :: Pattern Int


-- | CFG predict rule
predict :: U.Rule
predict =
  compileRule $
    Rule [leftP, rightP] downP condP
  where
    leftP = topItem $ active
      (rule any
        (suffix $ const dot <: var "B" <: any)
      )
      (span (var "i") (var "j"))
    rightP = topRule $
      rule (var "C")
        ( (var "alpha" :: Pattern Body)
--           `and` append' (var "alpha" :: Pattern Body) (nil :: Pattern Body)
        )
    condP = eq
      (map (fun labelB) $ var "B")
      (map (fun labelH) $ var "C")
    downP = topItem $ active
      (rule (var "C") (var "alpha"))
      (span (var "j") (var "j"))


--------------------------------------------------
-- Axioms 
--------------------------------------------------


-- | Compute the base items for the given sentence and grammar
cfgBaseItems 
  :: [T.Text]
    -- ^ Input sentence
  -> S.Set (T.Text, [T.Text])
    -- ^ CFG rules
  -> S.Set U.Rigit
cfgBaseItems inp cfgRules =
  S.fromList $ base1 ++ base2 ++ baseRules
  where
    n = length inp
    base1 = do
      -- Note that we use prediction
      i <- [0]
      (ruleHead, ruleBody) <- S.toList cfgRules
      let theRule = mkRule ruleHead ruleBody
          theSpan = span (pos i) (pos i)
          theItem = active theRule theSpan
          theTop  = topItem theItem
      return . U.strip $ Ty.unPatt theTop
    base2 = do
      (i, term) <- zip [0..n-1] inp
      let theRule = mkRule term []
          theSpan = span (pos i) (pos $ i + 1)
          theItem = active theRule theSpan
          theTop  = topItem theItem
      return . U.strip $ Ty.unPatt theTop
    baseRules = do
      (ruleHead, ruleBody) <- S.toList cfgRules
      let theRule = mkRule ruleHead ruleBody
          theTop  = topRule theRule
      return . U.strip $ Ty.unPatt theTop
    mkRule hd bd = rule
      (head hd)
      (body $ Nothing : P.map Just bd)


--------------------------------------------------
-- Main 
--------------------------------------------------


testCFGDev :: IO ()
testCFGDev = do
  let cfgRules = S.fromList
        [ ("NP_1", ["N_2"])
        , ("NP_3", ["DET_4", "N_5"])
        , ("S_6", ["NP_7", "VP_8"])
        , ("VP_9", ["V_10"])
        , ("VP_11", ["V_12", "Adv_13"])
        , ("VP_14", ["Adv_15", "V_16"])
        , ("VP_17", ["Adv_18", "V_19", "NP_20"])
        , ("DET_21", ["a"])
        , ("DET_22", ["some"])
        , ("N_23", ["dog"])
        , ("N_24", ["pizza"])
        , ("V_25", ["eats"])
        , ("V_26", ["runs"])
        , ("Adv_27", ["quickly"])
        ]
--         [ ("NP_3", ["DET_4", "N_5"])
--         , ("DET_21", ["a"])
--         , ("N_23", ["dog"])
--         ]
      sent = ["a", "dog", "quickly", "eats", "some", "pizza"]
--       sent = ["a", "dog"]
      baseItems = cfgBaseItems sent cfgRules
      ruleMap = M.fromList
        [ ("CO", complete)
        , ("PR", predict)
        ]
      pos = U.I . U.Sym . T.pack . show
      zero = pos 0
      slen = pos (length sent)
      isFinal = \case
        U.I (U.Union (Left (U.I (U.Pair _ (U.I (U.Pair i j))))))
          | i == zero && j == slen -> True
        _ -> False
--   forM_ (S.toList baseItems) print
  chartParse baseItems ruleMap isFinal >>= \case
    Nothing -> putStrLn "# No parse found"
    Just it -> print it
