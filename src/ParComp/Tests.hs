{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}


-- | Provisional module for testing


module ParComp.Tests where


import           ParComp.Patt
import qualified ParComp.Patt.Item as I


-- | List length
lengthF :: Ty PattFun ([a] -> Int)
lengthF =
  withArgs $ \xs ->
    withVars $ \tl ->
      ((xs `assign` nil) `seqp` zero) `choice`
      (
        (cons anyp tl `assign` xs) `seqp`
        (plus1 (apply lengthF tl))
      )
  where
    zero = encode P (0 :: Int)
    plus1 = foreign1arg "plus1" $ \x ->
      I.encode I.I (I.decode x + 1)


-- | A strange variation on `cons`
consF :: Ty PattFun ([Int] -> [Int])
consF = withArgs $ \xs ->
  (assign (cons one anyp) xs `seqp` cons one xs) `choice`
  (assign (cons two anyp) xs `seqp` cons two xs) `choice`
  xs
  where
    one = encode P (1 :: Int)
    two = encode P 2


-- | Append (see `appendF'` for another variant)
appendF :: Ty PattFun ([a] -> [a] -> [a])
appendF =
  withArgs $ \xs ys ->
    withVars $ \hd tl ->
      (check (xs `eq` nil) `seqp` ys) `choice`
      (
        (cons hd tl `assign` xs) `seqp`
        (cons hd (apply appendF tl ys))
      )


appendF' :: Ty PattFun ([a] -> [a] -> [a])
appendF' =
  withArgs $ \xs ys ->
    withVars $ \hd tl ->
      ((xs `assign` nil) `seqp` ys) `choice`
      (
        (cons hd tl `assign` xs) `seqp`
        (cons hd (apply appendF' tl ys))
      )
