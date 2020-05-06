{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RecordWildCards #-}

-- {-# LANGUAGE ScopedTypeVariables #-}


-- | This module provides the operations that can be used to construct (typed)
-- item patterns in the tagless final stile (see e.g.
-- http://okmij.org/ftp/tagless-final/).


module ParComp.Pattern.Typed
  ( Pattern (..)
  , Op (..)

  -- * Matching
  , match
  , apply

  -- * Non-core patterns
  -- ** Patterns for basic types
  , pair
  , nothing
  , just
  , left
  , right
  , nil
  , cons
  -- ** Other patterns
  , bimap
  , guard

  -- * Deduction rule
  , Rule (..)
  , compileRule
  ) where


import           Prelude hiding (const, map, any)

import qualified Prelude as P
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


-- | Tagless-final encoding of operations supported by patterns.
class Op (repr :: * -> *) where

--   pair    :: repr a -> repr b -> repr (a, b)
--   cons    :: repr a -> repr [a] -> repr [a]
--   nil     :: repr [a]

--   -- TODO: Do we really need this?  Besides, the type is not very nice...
--   unit    :: repr a

  nix     :: repr (a, a)
  add     :: repr a -> repr (b, c) -> repr (a -> b, c)
  build   :: a -> repr (a, b) -> repr b
  tag     :: Int -> repr a -> repr a

  any     :: repr a
  var     :: T.Text -> repr a
  const   :: (IsItem a) => a -> repr a

  and     :: repr a -> repr a -> repr a
  or      :: repr a -> repr a -> repr a

  fun     :: (IsItem a, IsItem b) => U.Fun a b -> repr (a -> b)
  app     :: repr (a -> b) -> repr b
  map     :: repr (a -> b) -> repr a -> repr b
  via     :: repr (a -> b) -> repr b -> repr a
  -- expand  :: repr a -> repr (a -> a)

  -- app     :: (IsItem a) => U.Fun a a -> repr a
  -- via     :: (IsItem a, IsItem b) => U.Fun a b -> repr b -> repr a

  with    :: repr a -> repr Bool -> repr a
  eq      :: repr a -> repr a -> repr Bool
  andC    :: repr Bool -> repr Bool -> repr Bool
  orC     :: repr Bool -> repr Bool -> repr Bool
  check   :: (IsItem a) => U.Pred a -> repr a -> repr Bool

  -- In @letIn x y@:
  -- * @x@ is matched with the underlying item of type @a@
  -- * @y@ is constructed to provide new type @b@
  -- The expression thus has the type @a -> b@.
  letIn   :: repr a -> repr b -> repr (a -> b)
  local   :: T.Text -> repr a
  fix     :: repr a -> repr a
  rec     :: repr a

--   letIn'  :: repr a -> repr a -> repr b -> repr b -> repr a
--   fix'    :: (repr a -> repr b) -> repr a -> repr b


-- NB: The implementation of the individual functions must be consistent with
-- the `IsItem` class.
instance Op Pattern where

--   pair   (Patt x) (Patt y)  = Patt (U.pairP x y)
--   cons   (Patt x) (Patt y)  = Patt (U.rightP $ U.pairP x y)
--   nil                       = Patt (U.leftP U.unitP)

--   unit                      = Patt U.unitP

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

  and (Patt x) (Patt y)     = Patt (U.viaP x y)
  or  (Patt x) (Patt y)     = Patt (U.orP x y)

  fun f                     = FunP (encodeFun f)
  app (FunP f)              = Patt (U.appP f)

  map (FunP f) (Patt x)     = Patt (U.mapP f x)
  map (Patt f) (Patt x)     = Patt (U.map'P f x)
  via (Patt f) (Patt x)     = Patt (U.viaP f x)

  -- NEW 05.04.2020 (TODO: make sure this is correct)
  via (FunP f) (Patt x)     = Patt (U.viaP (U.appP f) x)

--   app (Patt f)              = Patt f

--   fun f                     = Patt . U.appP $ encodeFun f
--   map f (Patt p)            = Patt $ U.mapP (encodeFun f) p
--   via (Patt f) (Patt x)     = Patt $ U.viaP f x
--   -- via f (Patt x)            = Patt $ U.viaP (U.appP (encodeFun f)) x
-- 
--   app (Patt f)              = Patt f
--   -- expand (Patt f)           = Patt f

  with (Patt x) (Cond c)    = Patt (U.withP x c)
  eq (Patt x) (Patt y)      = Cond (U.Eq x y)
  orC  (Cond x) (Cond y)    = Cond (U.OrC x y)
  andC (Cond x) (Cond y)    = Cond (U.And x y)
  check p (Patt x)          = Cond (U.Check (encodePred p) x)

  letIn (Patt x) (Patt y)   = Patt (U.letP x U.anyP y)

  local v                   = Patt (U.localP $ U.LVar v)
  fix (Patt x)              = Patt (U.fixP x)
  rec                       = Patt (U.recP)


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


-- | Strip the predicate from types.
encodePred :: (IsItem a) => U.Pred a -> U.Pred U.Rigit
encodePred p =
  U.Pred {U.pname = U.pname p, U.pbody = pbody'}
  where
    pbody' x0 =
      let x1 = U.decodeI x0
       in U.pbody p x1


--------------------------------------------------
-- Patterns for standard types
--------------------------------------------------


-- | Match a pair of patterns.
pair :: Op repr => repr a -> repr b -> repr (a, b)
pair x y = build (,) $ add x (add y nix)


-- | Match `Nothing` of `Maybe`.
nothing :: Op repr => repr (Maybe a)
nothing = tag 0 $ build Nothing nix


-- | Match `Just` of `Maybe`.
just :: Op repr => repr a -> repr (Maybe a)
just x = tag 1 . build Just $ add x nix


-- | Match `Left` of `Either`.
left :: Op repr => repr a -> repr (Either a b)
left x = tag 0 . build Left $ add x nix


-- | Match `Right` of `Either`.
right :: Op repr => repr b -> repr (Either a b)
right x = tag 1 . build Right $ add x nix


-- | Match empty list.
nil :: Op repr => repr [a]
nil = tag 0 $ build [] nix
-- nil = tag 0 unit


-- | Match non-empty list.
cons :: Op repr => repr a -> repr [a] -> repr [a]
cons x xs = tag 1 . build (:) $ add x (add xs nix)


--------------------------------------------------
-- Other patterns
--------------------------------------------------


-- | Curry the function and apply it to the given arguments.
bimap :: (Op repr, IsItem b, IsItem c, IsItem d)
      => U.Fun (b, c) d -> repr b -> repr c -> repr d
bimap f x y = map (fun f) (pair x y)


-- | Check if the predicates is satisfied on the current item.
guard :: (Op repr, IsItem a) => U.Pred a -> repr a
guard p =
  app $ fun f
  where
    f = U.Fun {U.fname = U.pname p, U.fbody = body}
    body x = do
      P.guard (U.pbody p x)
      return x


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
match :: (MonadIO m, IsItem a) => Pattern a -> a -> m Bool
match (Patt p) x = U.isMatch p (U.encodeI x)
match (FunP _) _ = error "cannot match function"
match (Cond _) _ = error "cannot match condition"
match (Vect _) _ = error "cannot match vector (forgot to use `build`?)"


-- | Apply functional pattern to a value.
--
-- Note: `apply` is not an idiomatic use of the typed interface.  On the other
-- hand, `MonadIO` constraint is provisional, so the type of this function will
-- later change and it will most likely become idiomatic...
apply :: (MonadIO m, IsItem a, IsItem b) => Pattern (a -> b) -> a -> m [b]
apply patt x = case patt of
  Patt p -> decodeAll $ U.doMatch p (U.encodeI x)
  FunP f -> decodeAll $ U.doMatch (U.appP f) (U.encodeI x)
  Cond _ -> error "cannot apply condition"
  Vect _ -> error "cannot apply vector (forgot to use `build`?)"
  where
    decodeAll
      = fmap (P.map U.decodeI)
      . Pi.toListM
      . Pi.enumerate
