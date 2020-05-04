{-# LANGUAGE KindSignatures #-}

-- {-# LANGUAGE ScopedTypeVariables #-}


-- | This module provides the operations that can be used to construct (typed)
-- item patterns in the tagless final stile (see e.g.
-- http://okmij.org/ftp/tagless-final/).


module ParComp.ItemDev.Typed
  ( Pattern (..)
  , Op (..)

  -- * Utils
  -- , bimap
  , guard
  ) where


import           Prelude hiding (map, any)
import qualified Control.Monad as P

import qualified Data.Text as T

import qualified ParComp.ItemDev.Untyped as U
import           ParComp.ItemDev.Untyped (IsPatt)


-- | Typed representation of a pattern.
data Pattern a
  = Patt {unPatt  :: U.Pattern}
  | Cond {unCond  :: U.Cond U.Pattern}
  | FunP {unFun   :: U.Fun U.Rigit U.Rigit}
  | Vect {unVect  :: [U.Pattern]}
    -- ^ Vect serves to build vector patterns
  deriving (Show, Eq, Ord)



-- -- | An existential type encapsulating types that are representable.
-- data Repr repr = forall a . MkRepr (repr a)


-- -- | An existential builder for representable objects.
-- pack :: repr a -> Repr repr
-- pack = MkRepr


-- | Encoding of operations for building data structures.
class Build repr where
  nil     :: repr (a, a)
  cons    :: repr a -> repr (b, c) -> repr (a -> b, c)
  vec     :: a -> repr (a, b) -> repr b

instance Build Pattern where
  nil                       = Vect [] 
  cons (Patt x) (Vect xs)   = Vect (x:xs)
  vec _ (Vect xs)           = Patt (U.vecP xs)


data S a = S a

single :: Build repr => repr a -> repr (S a)
single x = vec S $ cons x nil

pair' :: Build repr => repr a -> repr b -> repr (a, b)
pair' x y = vec (,) $ cons x (cons y nil)


-- | Tagless-final encoding of operations supported by patterns.
class Op (repr :: * -> *) where

--   pair    :: repr a -> repr b -> repr (a, b)
--   cons    :: repr a -> repr [a] -> repr [a]
--   nil     :: repr [a]

  any     :: repr a
  var     :: T.Text -> repr a
  const   :: (IsPatt a) => a -> repr a

  and     :: repr a -> repr a -> repr a
  or      :: repr a -> repr a -> repr a

  fun     :: (IsPatt a, IsPatt b) => U.Fun a b -> repr (a -> b)
  app     :: repr (a -> b) -> repr b
  map     :: repr (a -> b) -> repr a -> repr b
  via     :: repr (a -> b) -> repr b -> repr a
  -- expand  :: repr a -> repr (a -> a)

  -- app     :: (IsPatt a) => U.Fun a a -> repr a
  -- via     :: (IsPatt a, IsPatt b) => U.Fun a b -> repr b -> repr a

  with    :: repr a -> repr Bool -> repr a
  eq      :: repr a -> repr a -> repr Bool
  check   :: (IsPatt a) => U.Pred a -> repr a -> repr Bool

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
-- the `IsPatt` class.
instance Op Pattern where

--   pair   (Patt x) (Patt y)  = Patt (U.pairP x y)
--   cons   (Patt x) (Patt y)  = Patt (U.rightP $ U.pairP x y)
--   nil                       = Patt (U.leftP U.unitP)

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
  check p (Patt x)          = Cond (U.Check (encodePred p) x)

  letIn (Patt x) (Patt y)   = Patt (U.letP x U.anyP y)

  local v                   = Patt (U.localP $ U.LVar v)
  fix (Patt x)              = Patt (U.fixP x)
  rec                       = Patt (U.recP)


-- | Encode function as a function on untyped items.
encodeFun
  :: (IsPatt a, IsPatt b)
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
encodePred :: (IsPatt a) => U.Pred a -> U.Pred U.Rigit
encodePred p =
  U.Pred {U.pname = U.pname p, U.pbody = pbody'}
  where
    pbody' x0 =
      let x1 = U.decodeI x0
       in U.pbody p x1


--------------------------------------------------
-- Utils
--------------------------------------------------


-- -- | Curry the function and apply it to the given arguments.
-- bimap :: (Op repr, IsPatt b, IsPatt c, IsPatt d)
--       => U.Fun (b, c) d -> repr b -> repr c -> repr d
-- bimap f x y = map (fun f) (pair x y)


-- | Check if the predicates is satisfied on the current item.
guard :: (Op repr, IsPatt a) => U.Pred a -> repr a
guard p =
  app $ fun f
  where
    f = U.Fun {U.fname = U.pname p, U.fbody = body}
    body x = do
      P.guard (U.pbody p x)
      return x
