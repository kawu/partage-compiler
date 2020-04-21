{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}


-- | Context-free grammar parsing


module ParComp.Tests.CFG
  ( testCFG
  ) where


import           Prelude hiding (splitAt)

-- import           Control.Monad (forM_)
-- 
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import           Data.Maybe (fromJust)

import qualified ParComp.Item as I
import qualified ParComp.Pattern as P
import           ParComp.Pattern (Pattern(..), Cond(..), FunName(..))
import           ParComp.Parser (chartParse)

import           Debug.Trace (trace)


-- -- | CFG complete rule
-- complete :: P.Rule T.Text T.Text
-- complete =
--   P.Rule [leftP, rightP] consP P.TrueC
--   where
--     leftP = Pair
--       (Pair (Var "A") (Pair (Var "B") (Var "beta")))
--       (Pair (Var "i") (Var "j"))
--     rightP = Pair
--       (Pair (Var "B") (Const I.Unit))
--       (Pair (Var "j") (Var "k"))
--     consP = Pair
--       (Pair (Var "A") (Var "beta"))
--       (Pair (Var "i") (Var "k"))


-- | Append two (item) lists.
append :: I.Item sym -> [I.Item sym]
append (I.Pair xs ys) =
  [go xs]
  where
    go xs =
      case xs of
        I.Unit -> ys
        I.Pair x xs' -> I.Pair x (go xs')
        _ -> error "append: argument xs not a list"
append _ = error "append: argument not a pair of lists"


-- | Split the list at the given item.
splitAt :: (Eq sym) => I.Item sym -> I.Item sym -> [I.Item sym]
splitAt item =
  (:[]) . uncurry I.Pair . go
  where
    go list@(I.Pair x xs)
      | x == item = (I.Unit, list)
      | otherwise =
         let (pref, suff) = go xs
          in (I.Pair x pref, suff)
    go I.Unit = (I.Unit, I.Unit)
    go _ = error "splitAt: argument not a list"


-- | Local pattern and rule type synonyms
type Patt = Pattern T.Text T.Text T.Text
type Rule = P.Rule T.Text T.Text T.Text


-- | Match suffix which satisfies the given predicate.
suffix' :: (I.Item sym -> Bool) -> I.Item sym -> [I.Item sym]
suffix' p xs
  | p xs = xs : rest
  | otherwise = rest
  where
    rest =
      case xs of
        I.Pair x xs' -> suffix' p xs'
        I.Unit -> []
        _ -> error "suffix: argument not a list"


-- | Does the list end with dot?
endsWithDot :: (Eq sym) => I.Item sym -> [I.Item sym]
endsWithDot = suffix' $ \case
  I.Pair I.Unit I.Unit -> True
  _ -> False


-- | Match suffix.
suffix :: Patt -> Patt
-- suffix p = Or p (Pair Any $ suffix p)
suffix p = Fix $ Or p (Pair Any Rec)


-- | Remove suffix starting from the first element which satisfies the given
-- pattern.
removeSuffix :: Patt -> Patt
removeSuffix p =
  Fix $ Or p1 (Or p2 p3)
  where
    p1 = Let Any (Pair p Any) nil
    -- p2 = Pair Any (removeSuffix p)
    p2 = Pair Any Rec
    p3 = nil
    nil = Const I.Unit


-- -- | Split a list xs into two parts (ys, zs) w.r.t pattern p so that:
-- --
-- -- * ys = removeSuffix p xs
-- -- * zs = suffix p xs
-- --
-- splitAt :: Patt -> Patt
-- splitAt p =
--   Fix $ Or p1 (Or p2 p3)
--   where
--     p1 = Let
--       (LVar "suff")
--       (cons p Any)
--       (pair nil (LVar "suff"))
--     p2 = Let
--       (pair (LVar "x") (pair (LVar "pref") (LVar "suff")))
--       -- NOTE: we could simply write:
--       --   `(cons Any (splitAt p))`
--       -- However, we don't want recursion in our patterns, since this would
--       -- prevent us from comparing them and storing them in dictionaries.
--       -- Explicit recursion with `Fix` and `Rec` solves this problem.
--       (cons Any Rec)
--       (pair (cons (LVar "x") (LVar "pref")) (LVar "suff"))
--     p3 = pair nil nil
--     -- Helper functions
--     nil = Const I.Unit
--     cons = Pair
--     pair = Pair


-- -- | A version of `splitAt` which works by manually renaming variables.
-- -- This should not be necessar, though!
-- splitAt' :: Patt -> Patt
-- splitAt' p =
--   go 0
--   where
--     go k = 
--       Or p1 (Or p2 p3)
--       where
--         p1 = Let
--           (var "suffix")
--           (cons p Any)
--           (pair nil (var "suffix"))
--         p2 = Let
--           (pair (var "x") (pair (var "pref") (var "suff")))
--           (cons Any (go (k + 1)))
--           (pair (cons (var "x") (var "pref")) (var "suff"))
--         p3 = pair nil nil
--         -- Helper functions
--         nil = Const I.Unit
--         cons = Pair
--         pair = Pair
--         var str = Var $ str `T.append` T.pack (show k)


-- | CFG complete rule with dots
complete :: Rule
complete =
  P.Rule [leftP, rightP] downP condP
  where
    leftP = item
      (rule (Var "A")
        -- ( Via (splitAt dot)
        ( Via (App "splitAtDot")
            (Pair (Var "alpha") (Pair dot (Pair (Var "B") (Var "beta"))))
        )
      )
      (span "i" "j")
    rightP = item
      (rule (Var "C")
        -- (suffix $ Pair dot nil)
        (App "endsWithDot")
      )
      (span "j" "k")
    condP = Eq
      (Map "label" (Var "B"))
      (Map "label" (Var "C"))
    downP = item
      (rule (Var "A")
        ( Map "append" $ Pair
            (Var "alpha")
            (Pair (Var "B") (Pair dot (Var "beta")))
        )
      )
      (span "i" "k")
    -- Some helper functions, to make the code more readable
    item r s = Union . Left $ Pair r s
    rule x y = Pair x y
    cons x y = Pair x y
    span i j = (Pair (Var i) (Var j))
    -- The dot is represented just as nil (empty list)
    dot = unit
    nil = unit
    unit = Const I.Unit


-- | CFG predict rule
predict :: Rule
predict =
  P.Rule [leftP, rightP] downP condP
  where
    leftP = item
      (rule Any
        -- ( Via (splitAt dot)
        ( Via (App "splitAtDot")
            (Pair Any (Pair dot (Pair (Var "B") Any)))
        )
      )
      (span "i" "j")
    rightP = Union . Right $ Via (rule (Var "C") Any) (Var "rule")
    condP = Eq
      (Map "label" (Var "B"))
      (Map "label" (Var "C"))
    downP = item
      (Var "rule")
      (span "j" "j")
    -- Some helper functions, to make the code more readable
    item r s = Union . Left $ Pair r s
    rule x y = Pair x y
    cons x y = Pair x y
    span i j = (Pair (Var i) (Var j))
    -- The dot is represented just as nil (empty list)
    dot = unit
    unit = Const I.Unit


-- | Compute the base items for the given sentence and grammar
cfgBaseItems 
  :: [T.Text]
    -- ^ Input sentence
  -> S.Set (T.Text, [T.Text])
    -- ^ CFG rules
  -> S.Set (I.Item T.Text)
cfgBaseItems inp cfgRules =
  S.fromList $ base1 ++ base2 ++ baseRules
  where
    n = length inp
    base1 = do
      -- Note that we use prediction
      -- i <- [0..n-1]
      i <- [0]
      (ruleHead, ruleBody) <- S.toList cfgRules
      let rule = mkRule ruleHead ruleBody
          span = mkSpan i i
      return $ mkItem rule span
    base2 = do
      (i, term) <- zip [0..n-1] inp
      let rule = mkRule term []
          span = mkSpan i (i + 1)
      return $ mkItem rule span
    baseRules = do
      (ruleHead, ruleBody) <- S.toList cfgRules
      let rule = mkRule ruleHead ruleBody
      return . I.Union $ Right rule
    mkItem rl sp = I.Union . Left $ I.Pair rl sp
    mkRule hd bd = I.Pair (I.Sym hd) (I.list $ dot : map I.Sym bd)
    mkSpan i j = I.Pair (pos i) (pos j)
    pos = I.Sym . T.pack . show
    -- The dot is represented just as nil (empty list)
    dot = I.Unit


testCFG :: IO ()
testCFG = do
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
      label = \case
        I.Sym x ->
          case T.splitOn "_" x of
            [term] -> [I.Sym term]
            [nonTerm, _nodeId] -> [I.Sym nonTerm]
            _ -> error $ "label: unhandled symbol (" ++ T.unpack x ++ ")"
        x -> error $ "label: unhandled item (" ++ show x ++ ")"
      cfgFunSet = P.emptyFunSet
        { P.funMap = M.fromList
            [ ("append", append)
            , ("label", label)
            , ("splitAtDot", splitAt I.Unit)  -- I.Unit represents dot
            , ("endsWithDot", endsWithDot)
            ]
        }
      sent = ["a", "dog", "quickly", "eats", "some", "pizza"]
      baseItems = cfgBaseItems sent cfgRules
      ruleMap = M.fromList
        [ ("CO", complete)
        , ("PR", predict)
        ]
      pos = I.Sym . T.pack . show
      zero = pos 0
      slen = pos (length sent)
      isFinal = \case
        I.Union (Left (I.Pair _ (I.Pair i j)))
          | i == zero && j == slen -> True
        _ -> False
  -- forM_ (S.toList baseItems) print
  chartParse cfgFunSet baseItems ruleMap isFinal >>= \case
    Nothing -> putStrLn "# No parse found"
    Just it -> print it 
