{-# LANGUAGE OverloadedStrings #-}


-- | Provisional module for testing


module ParComp.Tests where


import           ParComp.Patt


-- | A strange variation on `cons`
consF :: Ty PattFun ([Int] -> [Int])
consF = with1arg $ \xs ->
  (assign (cons P one anyp) xs `seqp` cons P one xs) `choice`
  (assign (cons P two anyp) xs `seqp` cons P two xs) `choice`
  xs
  where
    one = encode P 1
    two = encode P 2


-- | Append (see `appendF'` for another variant)
appendF :: Ty PattFun ([a] -> [a] -> [a])
appendF = with2arg $ \xs ys ->
  (check (xs `eq` nil P) `seqp` ys) `choice`
  (
    (cons P hd tl `assign` xs) `seqp`
    (cons P hd (apply2 appendF tl ys))
  )
  where
    hd = var "hd"
    tl = var "tl"


-- | Append
appendF' :: Ty PattFun ([a] -> [a] -> [a])
appendF' = with2arg $ \xs ys ->
  ((xs `assign` nil P) `seqp` ys) `choice`
  (
    (cons P hd tl `assign` xs) `seqp`
    (cons P hd (apply2 appendF' tl ys))
  )
  where
    hd = var "hd"
    tl = var "tl"
