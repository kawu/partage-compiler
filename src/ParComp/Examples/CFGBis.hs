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

import qualified ParComp.ItemBis as I
import           ParComp.ItemBis
  (Ty (..), Item (..), Op (..), Patt (..), Cond (..), Fun (..), FunName (..))
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
-- Core item patterns
--
-- TODO: Move elsewhere!
-------------------------------------------------------------------------------


-- | Unit () pattern
unit :: Ty Patt ()
unit = I.unit P


-- | Pair pattern
pair :: Ty Patt a -> Ty Patt b -> Ty Patt (a, b)
pair = I.pair P


-- | Cons (list) pattern
nil :: Ty Patt [a]
nil = I.nil P


-- | Cons (list) pattern
cons :: Ty Patt a -> Ty Patt [a] -> Ty Patt [a]
cons = I.cons P


-- | Left pattern (`Either`)
left :: Ty Patt a -> Ty Patt (Either a b)
left = I.left P


-- | Right pattern (`Either`)
right :: Ty Patt b -> Ty Patt (Either a b)
right = I.right P


-- | TODO
nothing :: Ty Patt (Maybe a)
nothing = I.nothing P


-- | TODO
just :: Ty Patt a -> Ty Patt (Maybe a)
just = I.just P


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
pos = I.encode P


-- | Dotted rule's head
head :: Node -> Ty Patt Head
head = I.encode P


-- | Dot in a dotted rule
dot :: Ty Patt (Maybe Node)
dot = nothing


-------------------------------------------------------------------------------
-- Grammar representation
-------------------------------------------------------------------------------


-- | Name a function and lift it to a pattern-level function
name :: FunName -> (Ty Item a -> Ty Item b) -> Ty Patt a -> Ty Patt b
name funName f =
  let named = Fun funName $ \x -> [unTy $ f $ Ty x]
   in Ty . O . Apply named . unTy


-- | 2-argument variant of `name`
name2
  :: FunName
  -> (Ty Item a -> Ty Item b -> Ty Item c)
  -> Ty Patt a -> Ty Patt b -> Ty Patt c
name2 funName f =
  let named = Fun funName $ \x -> [unTy $ I.pair' f $ Ty x]
   in \x y -> Ty . O . Apply named . unTy $ pair x y


-- | Pattern to extract the non-terminal / terminal symbol of a node
label :: Ty Patt Node -> Ty Patt Sym
label =
  name "label" extract
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


-- | Variable (TODO: Move)
var :: String -> Ty Patt a
var = Ty . O . Var . fromString


-- | Wildcard pattern (TODO: Move)
anyp :: Ty Patt a
anyp = Ty $ O Any


-- TODO: Maybe the resulting type should be `Ty Patt Void`?
-- TODO: Move
assign :: Ty Patt a -> Ty Patt a -> Ty Patt b
assign (Ty x) (Ty v) = Ty . O $ Assign x v


-- TODO: Move
(&) :: Ty Patt a -> Ty Patt a -> Ty Patt a
(&) (Ty p) (Ty q) = Ty . O $ Seq p q
infixr 5 &


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
    v_A = var "A"         :: Ty Patt a
    v_As = var "As"       :: Ty Patt a
    v_B = var "B"         :: Ty Patt a
    v_C = var "C"         :: Ty Patt a
    v_alpha = var "alpha" :: Ty Patt a
    v_beta = var "beta"   :: Ty Patt a
    v_i = var "i"         :: Ty Patt a
    v_j = var "j"         :: Ty Patt a
    v_k = var "k"         :: Ty Patt a

    leftP = item (rule v_A v_As) (span v_i v_j) &
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
    condP = Eq (unTy $ label v_B) (unTy $ label v_C)

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
      & assign
          (pair anyp (dot .: just (var "B") .: anyp))
          (splitAtDot (var "body"))
    rightP = top $
      rule (var "C") (var "alpha")
    -- TODO: Eq -> eq
    condP = Eq
      (unTy $ label (var "B"))
      (unTy $ label (var "C"))
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
  let baseItems = map (unTy . I.encode I) $ cfgBaseItems testSent testRules
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
    Just it -> print $ (I.decode (Ty it) :: TopItem)


--------------------------------------------------
-- Utility patterns
--------------------------------------------------


-- | Operator synonym to `cons`
-- (.:) :: (Patt repr) => repr a -> repr [a] -> repr [a]
(.:) :: Ty Patt a -> Ty Patt [a] -> Ty Patt [a]
(.:) = I.cons P
infixr 5 .:


splitAtDot :: Ty Patt Body -> Ty Patt (Body, Body)
splitAtDot =
  -- O . Apply splitAt . pair dot
  splitAt dot


-- | Split a list at a given element
splitAt :: Ty Patt a -> Ty Patt [a] -> Ty Patt ([a], [a])
splitAt =

  name2 "splitAt" doit

  where

    doit :: Ty Item a -> Ty Item [a] -> Ty Item ([a], [a])
    doit at xs =
      let (ls, rs) = go at xs
       in I.pair I ls rs

    go at list = I.list'
      (I.nil I, I.nil I)
      (\x xs ->
         if x == at
         then (I.nil I, list)
         else
           let (pref, suff) = go at xs
            in (I.cons I x pref, suff)
      ) list


-- | Append two lists
append :: Ty Patt [a] -> Ty Patt [a] -> Ty Patt [a]
append =
  name2 "append" I.append
--   O . Apply app $ pair p q
--   where
--     app = Fun "append" $ I.pair' (\xs ys -> [I.append xs ys])


-- -- -- -- | Match any suffix that satisfies the given suffix pattern.
-- -- -- suffix :: (Patt repr) => repr [a] -> repr [a]
-- -- -- suffix p = fix $ choice p (any .: rec)
-- --
-- --
-- -- -- | Check if the item contains a given suffix.
-- -- -- suffix :: (Patt repr) => repr [a] -> repr [a]
-- -- suffixP :: Patt C -> Patt M
-- -- suffixP p =
-- --   xs `Seq` Guard cond
-- --   where
-- --     xs = Label "xs"
-- --     cond = Eq (apply suffix p (xs :: Patt C)) (Const I.true)


-- | Check if the list contains a given suffix.
suffix :: Ty Patt [a] -> Ty Patt [a]
suffix p =

  xs & check cond

  where

    xs = var "xs"
    -- TODO: Define `eq` with appropriate type safeness properties?
    cond = Eq (unTy $ hasSuffix p xs) (unTy $ I.true P)

    -- fun = Fun "suffix" $ I.pair' (\xs ys -> [I.suffix xs ys])
    hasSuffix = name2 "suffix" I.suffix

    check = Ty . O . Guard
