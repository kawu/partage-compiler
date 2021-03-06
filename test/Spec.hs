{-# LANGUAGE OverloadedStrings #-}
-- {-# LANGUAGE NoMonomorphismRestriction #-}


import           Prelude hiding (any, const, and, or, seq)

import           Test.Tasty
import           Test.Tasty.SmallCheck as SC
import           Test.Tasty.QuickCheck as QC
import           Test.Tasty.HUnit

import qualified Data.Set as S
import qualified Data.Text as T
import           Data.List (sort)
import           Data.Ord

import qualified ParComp.Patt.Item as I
import           ParComp.Patt.Item (Item(..), IsItem(..))

-- import qualified ParComp.Pattern.UntypedBis as Un
-- import qualified ParComp.Pattern.Indexing as Ix
-- import qualified ParComp.Pattern.Typed as Ty
-- import           ParComp.Pattern.Typed
--   ( Patt (..), match, match'
--   , pair, unit, false, true, nil, cons, left, right, nothing, just
--   )
-- import qualified ParComp.Pattern.Util as Util


main :: IO ()
main = defaultMain tests


tests :: TestTree
tests = testGroup "Tests" [properties]  --, unitTests]


properties :: TestTree
properties = testGroup "Properties" [qcProps]  --, scProps]


-- scProps = testGroup "(checked by SmallCheck)"
--   [ SC.testProperty "Fermat's little theorem" $
--       \x -> ((x :: Integer)^7 - x) `mod` 7 == 0
--   -- the following property does not hold
--   , SC.testProperty "Fermat's last theorem" $
--       \x y z n ->
--         (n :: Integer) >= 3 SC.==> x^n + y^n /= (z^n :: Integer)
--   ]


qcProps = testGroup "(checked by QuickCheck)"
  [ QC.testProperty "decode (encode [x1, ..., xn]) == [x1, ..., xn]" $
      \xs -> (decode . encode I) xs == (xs :: [Int])
  , QC.testProperty "decode (encode (Just x)) == Just x" $
      \x -> (decode . encode I) (Just x) == Just (x :: T.Text)
  , QC.testProperty "append xs ys == xs ++ ys" $
      \xs ys -> decode (I.append (encode I xs) (encode I ys)) == (xs ++ ys :: [Int])

  , QC.testProperty "suffix xs xs == True" $
      \xs ->
        let xsI = encode I (xs :: [Int])
         in decode (I.suffix xsI xsI) == True
  , QC.testProperty "suffix ys (xs ++ ys) == True" $
      \xs ys ->
        let xsI = encode I (xs :: [T.Text])
            ysI = encode I (ys :: [T.Text])
            zsI = I.append xsI ysI
         in decode (I.suffix ysI zsI) == True
  , QC.testProperty "suffix xs (x:xs) == True" $
      \x xs ->
        let xI = encode I (x :: Int)
            xsI = encode I (xs :: [Int])
            xxsI = I.cons xI xsI
         in decode (I.suffix xsI xxsI) == True
  , QC.testProperty "suffix (x:xs) xs == False" $
      \x xs ->
        let xI = encode I (x :: Int)
            xsI = encode I (xs :: [Int])
            xxsI = I.cons xI xsI
         in decode (I.suffix xxsI xsI) == False
  ]

-- unitTests = testGroup "Unit tests"
--   [ patternUnitTests
--   , indexUnitTests
--   , otherUnitTests
--   ]
-- 
-- 
-- patternUnitTests = testGroup "(patterns)"
--   [ testCase "Util.append" $ do
--       Ty.apply Util.append ([1, 2], [3]) @?= [[1, 2, 3 :: Int]]
-- 
--   -- Check if we can still match the original item after applying via
--   , testCase "via ... `and` ..." $ do
--       let f = letIn any (const ())
--           p = via f any `seq` pair (const 1) (const 2)
--           x = (1 :: Int, 2 :: Int)
--       match p x @?= True
-- 
--   -- Check if we can interpret Boolean functions as conditions
--   , testCase "const True" $ do
--       match (any `with` const True) () @?= True
--   , testCase "const False" $ do
--       match (any `with` const False) () @?= False
--   , testCase "const False `and` const True" $ do
--       let c = const False `and` const True
--       match (any `with` c) () @?= False
--   , testCase "const False `or` const True" $ do
--       let c = const False `or` const True
--       match (any `with` c) () @?= True
-- 
-- --   -- Check if we can interpret conditions as Boolean functions
-- --   -- (this does not type check, and it shoudn't)
-- --   , testCase "condition -> Boolean function" $ do
-- --       let p = const (1 :: Int) `eq` const 2
-- --       match p True @?= True
-- 
--   -- Check if IsItem instances correspond with patterns for several basic types
--   , testCase "match unit ()" $ do
--       match unit () @?= True
-- 
--   , testCase "match false False" $ do
--       match false False @?= True
--   , testCase "match true True" $ do
--       match true True @?= True
--   , testCase "match false True" $ do
--       match false True @?= False
--   , testCase "match true False" $ do
--       match true False @?= False
-- 
--   , testCase "match nil []" $ do
--       match nil ([] :: [()]) @?= True
--   , testCase "match (1 `cons` nil) [1]" $ do
--       match (const (1 :: Int) `cons` nil) [1::Int] @?= True
--   , testCase "match (1 `cons` nil) []" $ do
--       match (const (1 :: Int) `cons` nil) [] @?= False
-- 
--   , testCase "match nothing Nothing" $ do
--       match nothing (Nothing :: Maybe Int) @?= True
--   , testCase "match (just 1) (Just 1)" $ do
--       match (just $ const 1) (Just 1 :: Maybe Int) @?= True
--   , testCase "match nothing (Just 1)" $ do
--       match nothing (Just 1 :: Maybe Int) @?= False
--   , testCase "match (just 1) Nothing" $ do
--       match (just $ const 1) (Nothing :: Maybe Int) @?= False
-- 
--   , testCase "match (left 1) (Left 1)" $ do
--       match (left $ const 1) (Left 1 :: Either Int ()) @?= True
--   , testCase "match (left 1) (Right ())" $ do
--       match (left $ const 1) (Right () :: Either Int ()) @?= False
--   , testCase "match (right unit) (Left 1)" $ do
--       match (right unit) (Left 1 :: Either Int ()) @?= False
-- 
--   -- Check match'
--   , testCase "match' unit ()" $ do
--       match' unit () @?= [()]
--   , testCase "match' false False" $ do
--       match' false False @?= [False]
--   , testCase "match' false True" $ do
--       match' false True @?= []
--   , testCase "with const True `or` const True" $ do
--       let c = const True `or` const True
--       match' (any `with` c) () @?= [()]
--   ]
-- 
-- 
-- indexUnitTests = testGroup "(indexing)"
--   [ testCase "with nothing" $ do
--       let main  = pair (var "i") (var "j")
--           other = pair (var "j") (var "k")
--       keys <- Un.toListM $ do
--         Ix.dummyMatch (Ty.unPatt main)
--         Ix.getLockKey (Ty.unPatt other)
--       keys @?= [S.singleton . Un.labelP $ Un.Var "j"]
--   , testCase "with const True `or` const True" $ do
--       let main  = pair (var "i") (var "j")
--           cond  = const True `or` const True
--           other = pair (var "j") (var "k") `with` cond
--       keys <- Un.toListM $ do
--         Ix.dummyMatch (Ty.unPatt main)
--         Ix.getLockKey (Ty.unPatt other)
--       keys @?= [S.singleton . Un.labelP $ Un.Var "j"]
--   ]
-- 
-- 
-- otherUnitTests = testGroup "(other)"
--   [ testCase "var \"b\" `with` var \"b\"" $ do
--       match (var "b" `with` var "b") True @=? True
--       match (var "b" `with` var "b") False @=? False
-- 
-- --   , testCase "with function" $ do
-- --       let app = Util.append :: Ty.Pattern (([Int], [Int]) -> [Int])
-- --       match (any `with` eq app app) True @=? True
-- 
-- --   -- Check if illegal patterns can be used as conditions (e.g. local, var, any)
-- --   , testCase "illegal patterns as conditions" $ do
-- --       match (any `with` any) True @?= True
-- 
--   ]


---------------------------------------------------------------------
-- Utils
---------------------------------------------------------------------


(@@?=) :: (Show a, Eq a) => IO a -> a -> Assertion
mx @@?= y = do
    x <- mx
    x @?= y


---------------------------------------------------------------------
-- QuickCheck instances
---------------------------------------------------------------------


instance QC.Arbitrary T.Text where 
  arbitrary = fmap T.pack arbitrary
  shrink x  = map T.pack (shrink $ T.unpack x)
