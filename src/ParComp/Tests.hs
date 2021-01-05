{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}


-- | Provisional module for testing


module ParComp.Tests where


import           ParComp.Patt


-- | A strange variation on `cons`
consF :: Ty PattFun ([Int] -> [Int])
consF = with1arg $ \xs ->
  (assign (cons one anyp) xs `seqp` cons one xs) `choice`
  (assign (cons two anyp) xs `seqp` cons two xs) `choice`
  xs
  where
    one = encode P 1
    two = encode P 2


-- | Append (see `appendF'` for another variant)
appendF :: Ty PattFun ([a] -> [a] -> [a])
appendF = with2arg $ \xs ys ->
  (check (xs `eq` nil) `seqp` ys) `choice`
  (
    (cons hd tl `assign` xs) `seqp`
    (cons hd (apply2 appendF tl ys))
  )
  where
    hd = var "hd"
    tl = var "tl"


-- | Append
appendF' :: forall a. Ty PattFun ([a] -> [a] -> [a])
appendF' = with2arg $ \xs ys ->
  ((xs `assign` nil) `seqp` ys) `choice`
  (
    (cons hd tl `assign` xs) `seqp`
    (cons hd (apply2 appendF' tl ys))
  )
  where
    hd = var "hd" :: Ty Patt a
    tl = var "tl" :: Ty Patt [a]
