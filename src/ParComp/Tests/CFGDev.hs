{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}


-- | Context-free grammar parsing


module ParComp.Tests.CFGDev
  ( testCFGDev
  ) where


import           Prelude hiding (splitAt, span, map, or, and, any, const)
import qualified Prelude as P

import           Control.Monad (guard, forM_)

import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import           Data.Maybe (fromJust)

import qualified ParComp.ItemDev.Untyped as U
import           ParComp.ItemDev.Untyped (Fun(..))
import qualified ParComp.ItemDev.Typed as Ty
import           ParComp.ItemDev.Typed (Pattern(..), Op(..))
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
type Rule = (Head, Body)

-- | Active item
type Active = (Rule, Span)

-- | Top-level item
type Top = Either Active Rule


-- | Item tagless-final representation
class Item repr where
  top   :: Either (repr Active) (repr Rule) -> repr Top
  item  :: repr Rule -> repr Span -> repr Active
  span  :: repr Int -> repr Int -> repr Span
  pos   :: Int -> repr Int
  rule  :: repr Head -> repr Body -> repr Rule
  rhead :: Node -> repr Head
  rbody :: Body -> repr Body

instance Item Pattern where
  top = \case
    Left  (Patt it) -> Patt (U.leftP it)
    Right (Patt r)  -> Patt (U.rightP r)
  item (Patt r) (Patt s) = Patt (U.pairP r s)
  span (Patt x) (Patt y) = Patt (U.pairP x y)
  rule (Patt h) (Patt b) = Patt (U.pairP h b)
  pos i   = Patt $ U.encodeP i
  rhead x = Patt $ U.encodeP x
  rbody x = Patt $ U.encodeP x


--------------------------------------------------
-- Utils
--------------------------------------------------


-- -- | Replace any value by unit.
-- constF :: b -> Fun a b
-- constF x = Fun "constF" $ P.const [x]


-- | Append two lists.
append :: Fun ([a], [a]) [a]
append = Fun "append" $ \(xs, ys) -> do
  return (xs ++ ys)


-- | Operator version of `cons`
(<:) :: (Op repr) => repr a -> repr [a] -> repr [a]
(<:) = cons
infixr 5 <:


-- | Construct a list from a head and a tail.
consList :: Fun (a, [a]) [a]
consList = Fun "consList" $ \(x, xs) -> do
  return (x : xs)


-- | Split a list at a given value.
-- TODO: The name should be different for different arguments!
splitAt :: (Eq a) => a -> Fun [a] ([a], [a])
splitAt y =
  Fun "splitAt" ((:[]) . go)
  where
    -- showIt x = trace ("### splitAt: " ++ show x) x
    go list@(x:xs)
      | x == y = ([], list)
      | otherwise =
          let (pref, suff) = go xs
           in (x:pref, suff)
    go [] = ([], [])


-- | Check if the list ends with dot.  If so, return it as is.
-- TODO: The name should be different for different arguments!
endsWith :: (Eq a) => a -> Fun [a] [a]
endsWith y = Fun "endsWith" $ \xs -> do
  guard $ lastMaybe xs == Just y
  return xs


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
-- Rules
--------------------------------------------------


-- | CFG complete rule with dots
-- complete :: Rule
complete :: U.Rule
complete =
  U.Rule [leftP, rightP] downP condP
  where
    leftP = Ty.unPatt . top . Left $ item
      (rule (var "A")
        (via (fun $ splitAt dot)
          (pair (var "alpha") (const dot <: var "B" <: var "beta"))
        )
      )
      (span (var "i") (var "j"))
    rightP = Ty.unPatt . top . Left $ item
      (rule (var "C")
        (app . fun $ endsWith dot)
      )
      (span (var "j") (var "k"))
    condP = Ty.unCond $ eq
      (map labelB $ var "B")
      (map labelH $ var "C")
    downP = Ty.unPatt . top . Left $ item
      (rule (var "A")
        -- (append
        -- (map' append
          -- (pair
        (bimap append
          (var "alpha")
          (cons
            (var "B")
            (cons (const dot) (var "beta"))
          )
          -- )
        )
      )
      (span (var "i") (var "k"))
    dot = Nothing


-- | CFG predict rule
predict :: U.Rule
predict =
  U.Rule [leftP, rightP] downP condP
  where
    leftP = Ty.unPatt . top . Left $ item
      (rule any
        (via (fun $ splitAt dot)
          (pair any (const dot <: var "B" <: any))
        )
      )
      (span (var "i") (var "j"))
    rightP = Ty.unPatt . top . Right $
      and (rule (var "C") any) (var "rule")
    condP = Ty.unCond $ eq
      (map labelB $ var "B")
      (map labelH $ var "C")
    downP = Ty.unPatt . top . Left $ item
      (var "rule")
      (span (var "j") (var "j"))
    dot = Nothing


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
          theItem = item theRule theSpan
          theTop  = top (Left theItem)
      return . U.strip $ Ty.unPatt theTop
    base2 = do
      (i, term) <- zip [0..n-1] inp
      let theRule = mkRule term []
          theSpan = span (pos i) (pos $ i + 1)
          theItem = item theRule theSpan
          theTop  = top (Left theItem)
      return . U.strip $ Ty.unPatt theTop
    baseRules = do
      (ruleHead, ruleBody) <- S.toList cfgRules
      let theRule = mkRule ruleHead ruleBody
          theTop  = top (Right theRule)
      return . U.strip $ Ty.unPatt theTop
    mkRule hd bd = rule
      (rhead hd)
      (rbody $ Nothing : P.map Just bd)


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
