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

import qualified ParComp.Item as I
import qualified ParComp.Pattern as P
import           ParComp.Pattern (Pattern(..))
import           ParComp.Parser (chartParse)


-- | CFG complete rule
complete :: P.Rule T.Text T.Text
complete =
  P.Rule [leftP, rightP] consP P.CTrue
  where
    leftP = Pair
      (Pair (Var "A") (Pair (Var "B") (Var "beta")))
      (Pair (Var "i") (Var "j"))
    rightP = Pair
      (Pair (Var "B") (Const I.Unit))
      (Pair (Var "j") (Var "k"))
    consP = Pair
      (Pair (Var "A") (Var "beta"))
      (Pair (Var "i") (Var "k"))


-- | Compute the base items for the given sentence and grammar
cfgBaseItems 
  :: [T.Text]
    -- ^ Input sentence
  -> S.Set (T.Text, [T.Text])
    -- ^ CFG rules
  -> S.Set (I.Item T.Text)
cfgBaseItems inp cfgRules =
  S.fromList $ base1 ++ base2
  where
    n = length inp
    base1 = do
      i <- [0..n-1]
      (ruleHead, ruleBody) <- S.toList cfgRules
      let rule = mkRule ruleHead ruleBody
          span = mkSpan i i
      return $ I.Pair rule span
    base2 = do
      (i, term) <- zip [0..n-1] inp
      let rule = mkRule term []
          span = mkSpan i (i + 1)
      return $ I.Pair rule span
    mkRule hd bd = I.Pair (I.Sym hd) (I.list $ map I.Sym bd)
    mkSpan i j = I.Pair (pos i) (pos j)
    pos = I.Sym . T.pack . show


testCFG :: IO ()
testCFG = do
  let cfgGram = S.fromList
        [ ("NP", ["DET", "N"])
        , ("S", ["NP", "VP"])
        , ("VP", ["V"])
        , ("VP", ["V", "Adv"])
        , ("DET", ["a"])
        , ("N", ["dog"])
        , ("V", ["runs"])
        , ("Adv", ["quickly"])
        ]
      sent = ["a", "dog", "runs", "quickly"]
      baseItems = cfgBaseItems sent cfgGram
      ruleMap = M.fromList [("CO", complete)]
      pos = I.Sym . T.pack . show
      zero = pos 0
      slen = pos (length sent)
      isFinal = \case
        I.Pair _ (I.Pair i j)
          | i == zero && j == slen -> True
        _ -> False
  -- forM_ (S.toList baseItems) print
  chartParse P.emptyGram baseItems ruleMap isFinal >>= \case
    Nothing -> putStrLn "# No parse found"
    Just it -> print it 
