{-# LANGUAGE OverloadedStrings #-}


-- | Provisional module for testing


module ParComp.Tests where


import           ParComp.Patt.Core
  (Var, PattFun(..), Op(..), Cond(..), Patt(..))
import qualified ParComp.Patt.Typed as P
import           ParComp.Patt.Typed (Ty (..))
import qualified ParComp.Match as X


runCons2Test :: [Int] -> IO ()
runCons2Test xs = do
  xs <- X.runCompileTy cons2 xs
  mapM_ print xs


runAppendTest :: [Int] -> [Int] -> IO ()
runAppendTest xs ys = do
  xs <- X.runCompileTy2 append xs ys
  mapM_ print xs


-- withArg :: (Ty Patt a -> Ty Patt b) -> Ty Patt a -> Ty Patt b
-- withArg name f =
--   \x -> Ty . O $ ApplyP fn (unTy x)
--   where
--     fn = PattFun name (unTy . f . Ty)


withArg :: (Ty Patt a -> Ty Patt b) -> Ty Patt a -> Ty Patt b
withArg f = \x ->
  Ty . O $ ApplyP fun [unTy x]
  where
    -- TODO: Make sure function `f` does not already contain variable "x"!
    xarg = var "xarg"
    fun = PattFun [unTy xarg] (unTy $ f xarg)


withArgs2
  :: (Ty Patt a -> Ty Patt b -> Ty Patt c)
  -> Ty Patt a -> Ty Patt b -> Ty Patt c
withArgs2 f = \x y ->
  Ty . O $ ApplyP fun [unTy x, unTy y]
  where
    -- TODO: Make sure function `f` does not already contain variable "x"!
    xarg1 = var "xarg1"
    xarg2 = var "xarg2"
    fun = PattFun [unTy xarg1, unTy xarg2] (unTy $ f xarg1 xarg2)


cons2 :: Ty Patt [Int] -> Ty Patt [Int]
cons2 = withArg $ \xs ->
  (assign (cons one anyp) xs & cons one xs) |||
  (assign (cons two anyp) xs & cons two xs) |||
  xs
  where
    one = P.encode P 1
    two = P.encode P 2


append :: Ty Patt [a] -> Ty Patt [a] -> Ty Patt [a]
append = withArgs2 $ \xs ys ->
  (check (xs === nil) & ys) |||
  (
    cons hd tl =:= xs &
    cons hd (append tl ys)
  )
  where
    hd = var "hd"
    tl = var "tl"


assign :: Ty Patt a -> Ty Patt a -> Ty Patt b
assign (Ty x) (Ty v) = Ty . O $ Assign x v


-- | Pair pattern
pair :: Ty Patt a -> Ty Patt b -> Ty Patt (a, b)
pair = P.pair P


-- | Cons (list) pattern
cons :: Ty Patt a -> Ty Patt [a] -> Ty Patt [a]
cons = P.cons P


-- | Empty list
nil :: Ty Patt [a]
nil = P.nil P


-- | Wildcard pattern
anyp :: Ty Patt a
anyp = Ty $ O Any


-- | Wildcard pattern
var :: Var -> Ty Patt a
var = Ty . O . Var


-- | Guard pattern
check :: Cond Patt -> Ty Patt ()
check = Ty . O . Guard


-- Sequence
(&) :: Ty Patt a -> Ty Patt b -> Ty Patt b
(&) (Ty p) (Ty q) = Ty . O $ Seq p q
infixr 5 &


-- Choice
(|||) :: Ty Patt a -> Ty Patt a -> Ty Patt a
(|||) (Ty p) (Ty q) = Ty . O $ Choice p q
infixr 5 |||


-- | Equality check
(===) :: Ty Patt a -> Ty Patt a -> Cond Patt
(===) (Ty p) (Ty q) = Eq p q
infixr 6 ===


-- | Assignment
(=:=) :: Ty Patt a -> Ty Patt a -> Ty Patt ()
(=:=) (Ty p) (Ty q) = Ty . O $ Assign p q
infixr 6 =:=
