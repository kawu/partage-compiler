{-# LANGUAGE OverloadedStrings #-}


import           Prelude hiding (any, const, and)

import           Test.Tasty
import           Test.Tasty.SmallCheck as SC
import           Test.Tasty.QuickCheck as QC
import           Test.Tasty.HUnit

import           Data.List (sort)
import           Data.Ord

import qualified ParComp.Pattern.Typed as Ty
import           ParComp.Pattern.Typed
  (Patt (..), pair)
import qualified ParComp.Pattern.Util as U


main :: IO ()
main = defaultMain tests


tests :: TestTree
tests = testGroup "Tests" [properties, unitTests]


properties :: TestTree
properties = testGroup "Properties" [scProps, qcProps]


scProps = testGroup "(checked by SmallCheck)"
  [ SC.testProperty "Fermat's little theorem" $
      \x -> ((x :: Integer)^7 - x) `mod` 7 == 0
--   -- the following property does not hold
--   , SC.testProperty "Fermat's last theorem" $
--       \x y z n ->
--         (n :: Integer) >= 3 SC.==> x^n + y^n /= (z^n :: Integer)
  ]


qcProps = testGroup "(checked by QuickCheck)"
  [ QC.testProperty "Util.append (xs, ys) == xs ++ ys" $
      \xs ys -> Ty.apply U.append (xs :: [Int], ys) == [xs ++ ys]
  , QC.testProperty "sort == sort . reverse" $
      \list -> sort (list :: [Int]) == sort (reverse list)
  , QC.testProperty "Fermat's little theorem" $
      \x -> ((x :: Integer)^7 - x) `mod` 7 == 0
--   -- the following property does not hold
--   , QC.testProperty "Fermat's last theorem" $
--       \x y z n ->
--         (n :: Integer) >= 3 QC.==> x^n + y^n /= (z^n :: Integer)
  ]


unitTests = testGroup "Unit tests"
  [ testCase "List comparison (different length)" $
      [1, 2, 3] `compare` [1,2] @?= GT

--   -- the following test does not hold
--   , testCase "List comparison (same length)" $
--       [1, 2, 3] `compare` [1,2,2] @?= LT

  , testCase "Util.append" $ do
      Ty.apply U.append ([1, 2], [3]) @?= [[1, 2, 3 :: Int]]

  -- Check if we can still match the original item after applying via
  , testCase "via ... `and` ..." $ do
      let f = letIn any (const ())
          p = via f any `and` pair (const 1) (const 2)
          x = (1 :: Int, 2 :: Int)
      Ty.match p x @?= True

  ]


---------------------------------------------------------------------
-- Utils
---------------------------------------------------------------------


(@@?=) :: (Show a, Eq a) => IO a -> a -> Assertion
mx @@?= y = do
    x <- mx
    x @?= y
