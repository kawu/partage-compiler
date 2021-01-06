{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}


-- | Provisional module for testing


module ParComp.Tests where


import           ParComp.Patt
import qualified ParComp.Patt.Item as I


-- | List length
lengthF :: Ty PattFun ([a] -> Int)
lengthF =
  withVars $ \xs tl ->
    arg xs $
    fun $
      ((xs `match` nil) `seqp` zero) `choice`
      (
        (cons anyp tl `match` xs) `seqp`
        (plus1 (apply lengthF tl))
      )
  where
    zero = encode P (0 :: Int)
    plus1 = foreign1arg "plus1" $ \x ->
      I.encode I.I (I.decode x + 1)


-- | A strange variation on `cons`
consF :: Ty PattFun ([Int] -> [Int])
consF = withVars $ \xs -> arg xs $ fun $
  (match (cons one anyp) xs `seqp` cons one xs) `choice`
  (match (cons two anyp) xs `seqp` cons two xs) `choice`
  xs
  where
    one = encode P (1 :: Int)
    two = encode P 2


-- | Append (see `appendF'` for another variant)
appendF :: Ty PattFun ([a] -> [a] -> [a])
appendF = withVars $ \xs ys hd tl ->
  arg xs . arg ys . fun $
    (check (xs `eq` nil) `seqp` ys) `choice`
    (
      (cons hd tl `match` xs) `seqp`
      (cons hd (apply appendF tl ys))
    )

appendF' :: Ty PattFun ([a] -> [a] -> [a])
appendF' = withVars $ \xs ys hd tl ->
  arg xs . arg ys . fun $
    ((xs `match` nil) `seqp` ys) `choice`
    (
      (cons hd tl `match` xs) `seqp`
      (cons hd (apply appendF' tl ys))
    )
