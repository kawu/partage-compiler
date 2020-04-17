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
import           ParComp.Pattern (Pattern(..))
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


-- Append two (item) lists
append :: I.Item sym -> I.Item sym
append (I.Pair xs ys) =
  go xs
  where
    go xs =
      case xs of
        I.Unit -> ys
        I.Pair x xs' -> I.Pair x (go xs')
        _ -> error "append: argument xs not a list"
append _ = error "append: argument not a pair of lists"


-- | Local pattern and rule type synonyms
type Patt = Pattern T.Text T.Text T.Text
type Rule = P.Rule T.Text T.Text T.Text


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


-- | Split a list xs into two parts (ys, zs) w.r.t pattern p so that:
--
-- * ys = removeSuffix p xs
-- * zs = suffix p xs
--
splitAt :: Patt -> Patt
splitAt p =
  Fix $ Or p1 (Or p2 p3)
  where
    p1 = Let
      (LVar "suff")
      (cons p Any)
      (pair nil (LVar "suff"))
    p2 = Let
      (pair (LVar "x") (pair (LVar "pref") (LVar "suff")))
      -- NOTE: we could simply write:
      --   `(cons Any (splitAt p))`
      -- However, we don't want recursion in our patterns, since this would
      -- prevent us from comparing them and storing them in dictionaries.
      -- Explicit recursion with `Fix` and `Rec` solves this problem.
      (cons Any Rec)
      (pair (cons (LVar "x") (LVar "pref")) (LVar "suff"))
    p3 = pair nil nil
    -- Helper functions
    nil = Const I.Unit
    cons = Pair
    pair = Pair


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
  P.Rule [leftP, rightP] downP P.TrueC
  where
    leftP = item
      (rule (Var "A")
        ( Via (splitAt dot)
            (Pair (Var "alpha") (Pair dot (Pair (Var "B") (Var "beta"))))
        )
      )
      (span "i" "j")
    rightP = item
      (rule (Var "B")
        (suffix $ Pair dot nil)
      )
      (span "j" "k")
    downP = item
      (rule (Var "A")
        ( App (P.FunName "append") $ Pair
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
  P.Rule [leftP, rightP] downP P.TrueC
  where
    leftP = item
      (rule Any
        ( Via (splitAt dot)
            (Pair Any (Pair dot (Pair (Var "B") Any)))
        )
      )
      (span "i" "j")
    rightP = Union . Right $ Via (rule (Var "B") Any) (Var "rule")
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


-- | CFG grammar functions
cfgFunSet :: P.FunSet T.Text
cfgFunSet = P.emptyFunSet
  { P.funMap = M.singleton (P.FunName "append") append
  }


testCFG :: IO ()
testCFG = do
  let cfgRules = S.fromList
        [ ("NP", ["N"])
        , ("NP", ["DET", "N"])
        , ("S", ["NP", "VP"])
        , ("VP", ["V"])
        , ("VP", ["V", "Adv"])
        , ("VP", ["Adv", "V"])
        , ("VP", ["Adv", "V", "NP"])
        , ("DET", ["a"])
        , ("DET", ["some"])
        , ("N", ["dog"])
        , ("N", ["pizza"])
        , ("V", ["eats"])
        , ("V", ["runs"])
        , ("Adv", ["quickly"])
        ]
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
