{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RecordWildCards #-}

-- {-# LANGUAGE ScopedTypeVariables #-}


-- | This module provides the operations that can be used to construct (typed)
-- item patterns in the tagless final stile (see e.g.
-- http://okmij.org/ftp/tagless-final/).


module ParComp.Pattern.Typed
  ( Pattern (..)
  , Patt (..)
  -- , Cond

  -- * Matching
  , match
  , apply

  -- * Non-core patterns
  -- ** Patterns for basic types
  , unit
  , pair
  , false
  , true
  , nothing
  , just
  , left
  , right
  , nil
  , cons
  -- ** Other patterns
  , bimap
  , guard
  -- , isTrue

  -- * Deduction rule
  , Rule (..)
  , compileRule
  ) where


import           Prelude hiding (const, map, any)
import qualified Prelude as P

import           System.IO.Unsafe (unsafePerformIO)

import qualified Control.Monad as P
import           Control.Monad.IO.Class (MonadIO)

import qualified Pipes as Pi
import qualified Pipes.Prelude as Pi

import qualified Data.Text as T

import qualified ParComp.Pattern.Untyped as U
import           ParComp.Pattern.Untyped (IsItem)


--------------------------------------------------
-- Pattern
--------------------------------------------------


-- | Typed representation of a pattern.
data Pattern a
  = Patt {unPatt  :: U.Pattern}
  | Cond {unCond  :: U.Cond U.Pattern}
  | FunP {unFun   :: U.Fun U.Rigit U.Rigit}
  | Vect {unVect  :: [U.Pattern]}
    -- ^ Vect serves to build vector patterns
  deriving (Show, Eq, Ord)


-- -- | Condition marker
-- data Cond


-- | Tagless-final encoding of typed patterns.
class Patt (repr :: * -> *) where

  ------------------------------------------
  -- Data structure building patterns
  ------------------------------------------

  nix     :: repr (a, a)
  add     :: repr a -> repr (b, c) -> repr (a -> b, c)
  build   :: a -> repr (a, b) -> repr b
  tag     :: Int -> repr a -> repr a

  ------------------------------------------
  -- Core matching patterns
  ------------------------------------------

  any     :: repr a
  var     :: T.Text -> repr a
  const   :: (IsItem a) => a -> repr a

  ------------------------------------------
  -- Control patterns
  ------------------------------------------

  seq     :: repr a -> repr a -> repr a
  choice  :: repr a -> repr a -> repr a

  ------------------------------------------
  -- Functional patterns
  ------------------------------------------

  fun     :: (IsItem a, IsItem b) => U.Fun a b -> repr (a -> b)
  app     :: repr (a -> b) -> repr b
  map     :: repr (a -> b) -> repr a -> repr b
  via     :: repr (a -> b) -> repr b -> repr a

  ------------------------------------------
  -- Condition patterns
  ------------------------------------------

  with    :: repr a -> repr Bool -> repr a

  -- | Cast a predicate pattern as a condition
  -- isTrue  :: repr Bool -> repr Cond
  eq      :: repr a -> repr a -> repr Bool
  and     :: repr Bool -> repr Bool -> repr Bool
  or      :: repr Bool -> repr Bool -> repr Bool


  ------------------------------------------
  -- Defining functions
  ------------------------------------------
 
  letIn   :: repr a -> repr b -> repr (a -> b)
  local   :: T.Text -> repr a
  fix     :: repr a -> repr a
  rec     :: repr a


-- NB: The implementation of the individual functions must be consistent with
-- the `IsItem` class.
instance Patt Pattern where

  nix                       = Vect []
  add  (Patt x) (Vect xs)   = Vect (x:xs)
  build _ (Vect xs)
    | len == 0              = Patt U.unitP
    | len == 1              = Patt (xs !! 0)
    | otherwise             = Patt (U.vecP xs)
    where len = length xs
  tag k (Patt x)            = Patt (U.tagP k x)

  any                       = Patt U.anyP
  var v                     = Patt (U.labelP $ U.Var v)
  const x                   = Patt (U.encodeP x)

  seq (Patt x) (Patt y)     = Patt (U.seqP x y)
  choice (Patt x) (Patt y)  = Patt (U.choiceP x y)
  -- and (Patt x) (Patt y)     = Patt (U.viaP x y)
  -- or  (Patt x) (Patt y)     = Patt (U.choiceP x y)

  fun f                     = FunP (encodeFun f)
  app (FunP f)              = Patt (U.appP f)

  map (FunP f) (Patt x)     = Patt (U.mapP f x)
  map (Patt f) (Patt x)     = Patt (U.map'P f x)
  via (Patt f) (Patt x)     = Patt (U.viaP f x)

  -- NEW 05.04.2020 (TODO: make sure this is correct)
  via (FunP f) (Patt x)     = Patt (U.viaP (U.appP f) x)

  with (Patt x) y           = Patt (U.withP x (asCond y))
  eq (Patt x) (Patt y)      = Cond (U.Eq x y)
  and x y                   = Cond (U.And (asCond x) (asCond y))
  or  x y                   = Cond (U.Or  (asCond x) (asCond y))

  -- isTrue (Patt x)           = Cond (U.IsTrue x)
--   with (Patt x) (Cond y)    = Patt (U.withP x y)
--   eq (Patt x) (Patt y)      = Cond (U.Eq x y)
--   and (Cond x) (Cond y)     = Cond (U.And x y)
--   or  (Cond x) (Cond y)     = Cond (U.Or x y)

  letIn (Patt x) (Patt y)   = Patt (U.letP x U.anyP y)

  local v                   = Patt (U.localP $ U.LVar v)
  fix (Patt x)              = Patt (U.fixP x)
  rec                       = Patt (U.recP)


-- | Cast a Boolean pattern as a condition.
asCond :: Pattern Bool -> U.Cond U.Pattern
asCond (Cond c) = c
asCond (Patt x) = U.Eq x (U.true U.P)
asCond _ = error "asCond: cannot handle pattern"


-- | Encode function as a function on untyped items.
encodeFun
  :: (IsItem a, IsItem b)
  => U.Fun a b
  -> U.Fun U.Rigit U.Rigit
encodeFun f =
  U.Fun {U.fname = U.fname f, U.fbody = fbody'}
  where
    fbody' x0 = do
      let x1 = U.decodeI x0
      x2 <- U.fbody f x1
      return $ U.encodeI x2


-- -- | Strip the predicate from types.
-- encodePred :: (IsItem a) => U.Pred a -> U.Pred U.Rigit
-- encodePred p =
--   U.Pred {U.pname = U.pname p, U.pbody = pbody'}
--   where
--     pbody' x0 =
--       let x1 = U.decodeI x0
--        in U.pbody p x1


--------------------------------------------------
-- Patterns for standard types
--------------------------------------------------


-- | Match `()` of `().
unit :: Patt repr => repr ()
unit = build () nix


-- | Match a pair of patterns.
pair :: Patt repr => repr a -> repr b -> repr (a, b)
pair x y = build (,) $ add x (add y nix)


-- | Match `False` of `Bool`.
false :: Patt repr => repr Bool
false = tag 0 $ build False nix


-- | Match `True` of `Bool`.
true :: Patt repr => repr Bool
true = tag 1 $ build True nix


-- | Match `Nothing` of `Maybe`.
nothing :: Patt repr => repr (Maybe a)
nothing = tag 0 $ build Nothing nix


-- | Match `Just` of `Maybe`.
just :: Patt repr => repr a -> repr (Maybe a)
just x = tag 1 . build Just $ add x nix


-- | Match `Left` of `Either`.
left :: Patt repr => repr a -> repr (Either a b)
left x = tag 0 . build Left $ add x nix


-- | Match `Right` of `Either`.
right :: Patt repr => repr b -> repr (Either a b)
right x = tag 1 . build Right $ add x nix


-- | Match empty list.
nil :: Patt repr => repr [a]
nil = tag 0 $ build [] nix


-- | Match non-empty list.
cons :: Patt repr => repr a -> repr [a] -> repr [a]
cons x xs = tag 1 . build (:) $ add x (add xs nix)


--------------------------------------------------
-- Other patterns
--------------------------------------------------


-- | Curry the function and apply it to the given arguments.
bimap :: (Patt repr, IsItem b, IsItem c, IsItem d)
      => repr ((b, c) -> d) -> repr b -> repr c -> repr d
bimap f x y = map f (pair x y)


-- -- | Check if the predicate is satisfied on the current item.
-- guard :: (Patt repr, IsItem a) => U.Pred a -> repr a
-- guard p =
--   app $ fun f
--   where
--     f = U.Fun {U.fname = U.pname p, U.fbody = body}
--     body x = do
--       P.guard (U.pbody p x)
--       return x


-- | Check if the predicate is satisfied on the current item.
guard :: (Patt repr, IsItem a) => U.Fun a Bool -> repr a
guard p =
  app $ fun f
  where
    f = U.Fun {U.fname = U.fname p, U.fbody = body}
    body x = do
      P.guard =<< U.fbody p x
      return x


-- -- | Cast a predicate pattern as a condition.
-- isTrue :: (Patt repr) => repr Bool -> repr Cond
-- isTrue = eq (const True)


--------------------------------------------------
-- Typed rule
--------------------------------------------------


-- | Typed deduction rule for items of type @a@.
data Rule a = Rule
  { antecedents :: [Pattern a]
  , consequent  :: Pattern a
  , condition   :: Pattern Bool
  }


-- | Compile the rule to its untyped counterpart.
compileRule :: Rule a -> U.Rule
compileRule Rule{..} = U.Rule
  { U.antecedents = P.map unPatt antecedents
  , U.consequent  = unPatt consequent
  , U.condition   = unCond condition
  }


--------------------------------------------------
-- Typed matching
--------------------------------------------------


-- | Verify if the pattern matches with the given value.
--
-- Warning: the function (provisionally) relies on `unsafePerformIO`.
match :: (IsItem a) => Pattern a -> a -> Bool
match (Patt p) x = unsafePerformIO $ U.isMatch p (U.encodeI x)
match (FunP _) _ = error "cannot match function"
match (Cond _) _ = error "cannot match condition"
match (Vect _) _ = error "cannot match vector (forgot to use `build`?)"


-- | Apply functional pattern to a value.
--
-- Warning: the function (provisionally) relies on `unsafePerformIO`.
apply :: (IsItem a, IsItem b) => Pattern (a -> b) -> a -> [b]
apply patt x = unsafePerformIO $ case patt of
  Patt p -> decodeAll $ U.doMatch p (U.encodeI x)
  FunP f -> decodeAll $ U.doMatch (U.appP f) (U.encodeI x)
  Cond _ -> error "cannot apply condition"
  Vect _ -> error "cannot apply vector (forgot to use `build`?)"
  where
    decodeAll
      = fmap (P.map U.decodeI)
      . Pi.toListM
      . Pi.enumerate
