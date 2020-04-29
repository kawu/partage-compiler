-- | This module provides the operations that can be used to construct (typed)
-- item patterns in the tagless final stile (see e.g.
-- http://okmij.org/ftp/tagless-final/).


module ParComp.ItemDev.Typed
  ( Pattern (..)
  , Op (..)
  ) where


import           Prelude hiding (map, any)

import qualified Data.Text as T

import qualified ParComp.ItemDev.Untyped as U
import           ParComp.ItemDev.Untyped (IsPatt)


-- | Typed representation of a pattern.
data Pattern a
  = Patt {unPatt :: U.Pattern}
  | Cond {unCond :: U.Cond U.Pattern}
  deriving (Show, Eq, Ord)


-- | Tagless-final encoding of (one-parameter) operations supported on
-- patterns.
class Op repr where

  pair    :: repr a -> repr b -> repr (a, b)
  cons    :: repr a -> repr [a] -> repr [a]

  any     :: repr a
  var     :: T.Text -> repr a
  const   :: (IsPatt a) => a -> repr a

  map     :: (IsPatt a, IsPatt b) => U.Fun a b -> repr a -> repr b
  via     :: (IsPatt a, IsPatt b) => U.Fun a b -> repr b -> repr a
  app     :: (IsPatt a) => U.Fun a a -> repr a

  eq      :: repr a -> repr a -> repr Bool
  with    :: repr a -> repr Bool -> repr a

  and     :: repr a -> repr a -> repr a
  or      :: repr a -> repr a -> repr a
  

-- NB: The implementation of the individual functions must be consistent with
-- the `IsPatt` class.
instance Op Pattern where

  pair   (Patt x) (Patt y)  = Patt (U.pairP x y)
  cons   (Patt x) (Patt y)  = Patt (U.rightP $ U.pairP x y)

  var v                     = Patt (U.labelP $ U.Var v)
  const x                   = Patt (U.encodeP x)

  map f (Patt p)            = Patt $ U.mapP (encodeFun f) p

  via f (Patt x)            = Patt $ U.viaP (U.appP (encodeFun f)) x
  app f                     = Patt . U.appP $ encodeFun f

  with (Patt x) (Cond c)    = Patt (U.withP x c)
  eq (Patt x) (Patt y)      = Cond (U.Eq x y)

  and (Patt x) (Patt y)     = Patt (U.viaP x y)
  or (Patt x) (Patt y)      = Patt (U.orP x y)
  any                       = Patt U.anyP


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
