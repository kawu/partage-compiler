{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}


-- | Context-free grammar parsing


module ParComp.Tests.CFG
  ( testCFG
  ) where


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
--   P.Rule [leftP, rightP] consP P.CTrue
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
        _ -> error "appendI: argument xs not a list"
append _ = error "appendI: argument not a pair of lists"


-- | Local pattern type synonym
type Patt = Pattern T.Text T.Text


-- | Match suffix.
suffix :: Patt -> Patt
suffix p = OrP p (Pair Any $ suffix p)


-- | Remove suffix starting from the first element which satisfies the given
-- pattern.
removeSuffix :: Patt -> Patt
removeSuffix p =
  OrP p1 (OrP p2 p3)
  where
    p1 = Let Any (Pair p Any) nil
    p2 = Pair Any (removeSuffix p)
    p3 = nil
    nil = Const I.Unit


-- | Split a list xs into two parts (ys, zs) w.r.t pattern p so that:
--
-- * ys = removeSuffix p xs
-- * zs = suffix p xs
--
split :: Patt -> Patt
split p =
  OrP p1 (OrP p2 p3)
  where
    p1 = Let
      (Var "suff")
      (cons p Any)
      (pair nil (Var "suff"))
    p2 = Let
      (pair (Var "x") (pair (Var "pref") (Var "suff")))
      (cons Any (split p))
      (pair (cons (Var "x") (Var "pref")) (Var "suff"))
    p3 = pair nil nil
    -- Helper functions
    nil = Const I.Unit
    cons = Pair
    pair = Pair


-- -- | A version of `split` which works by manually renaming variables.
-- -- This should not be necessar, though!
-- split' :: Patt -> Patt
-- split' p =
--   go 0
--   where
--     go k = 
--       OrP p1 (OrP p2 p3)
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
complete :: P.Rule T.Text T.Text
complete =
  P.Rule [leftP, rightP] downP P.CTrue
  where
    leftP = item
      (rule (Var "A")
        ( Via (split dot)
            (Pair (Var "alpha") (Pair dot (Pair (Var "B") (Var "beta"))))
        )
--         (AndP
--           (suffix $ Pair dot (Pair (Var "B") (Var "beta")))
--           (Let (Var "alpha") (removeSuffix dot) unit)
--         )
      )
      (span "i" "j")
    rightP = item
      (rule (Var "B")
        (suffix $ Pair dot nil)
      )
      (span "j" "k")
    downP = item
      (rule (Var "A")
        ( App append $ Pair
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
predict :: P.Rule T.Text T.Text
predict =
  P.Rule [leftP, rightP] downP P.CTrue
  where
    leftP = item
      (rule Any
        ( Via (split dot)
            (Pair Any (Pair dot (Pair (Var "B") Any)))
        )
--         (AndP
--           (suffix $ Pair dot (Pair (Var "B") (Var "beta")))
--           (Let (Var "alpha") (removeSuffix dot) unit)
--         )
      )
      (span "i" "j")
    rightP = Union . Right $ rule (Var "B") (Var "beta")
    downP = item
      -- (rule (Var "B") (Pair dot (Var "beta")))
      (rule (Var "B") (Var "beta"))
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


-- -- | CFG grammar functions
-- cfgFuns :: P.Grammar T.Text
-- cfgFuns = P.emptyGram
--   { P.funMap = M.singleton (P.FunName "append") appendI
--   }


testCFG :: IO ()
testCFG = do
  let cfgRules = S.fromList
        [ ("NP", ["DET", "N"])
        , ("S", ["NP", "VP"])
        , ("VP", ["V"])
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
  chartParse baseItems ruleMap isFinal >>= \case
    Nothing -> putStrLn "# No parse found"
    Just it -> print it 
