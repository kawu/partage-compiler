-- | This module provides the operations that can be used to construct (typed)
-- item patterns in the tagless final stile (see e.g.
-- http://okmij.org/ftp/tagless-final/).


module ParComp.ItemDev.Typed
  ( Pattern (..)
  , Op (..)
  ) where


import           Prelude hiding (map, any)

-- import           Data.Void (Void)
import qualified Data.Text as T

import qualified ParComp.ItemDev.Untyped as U
import           ParComp.ItemDev.Untyped (IsPatt)

import Debug.Trace (trace)


-- | Typed pattern @Pattern a b@ matches objects of type @a@ and computes
-- objects of type @b@.
data Pattern a
  = Patt {unPatt :: U.Pattern}
  | Cond {unCond :: U.Cond U.Pattern}
  deriving (Show, Eq, Ord)


-- | Tagless-final encoding of (one-parameter) operations supported on
-- patterns.
class Op repr where

  pair    :: repr a -> repr b -> repr (a, b)
  cons    :: repr a -> repr [a] -> repr [a]

  var     :: T.Text -> repr a
  const   :: (IsPatt a) => a -> repr a

  map     :: (IsPatt a, IsPatt b) => U.Fun a b -> repr a -> repr b
  bimap   :: (IsPatt b, IsPatt c, IsPatt d)
          => U.Fun (b, c) d -> repr b -> repr c -> repr d

  -- TODO: Below, you could replace:
  -- * `app` with `fun`
  -- * `merge` with `app`
  fun     :: (IsPatt a, IsPatt b) => U.Fun a b -> repr (a -> b)
  via     :: repr (a -> b) -> repr b -> repr a
  app     :: repr (a -> a) -> repr a

  eq      :: repr a -> repr a -> repr Bool
  with    :: repr a -> repr Bool -> repr a

  and     :: repr a -> repr a -> repr a
  or      :: repr a -> repr a -> repr a
  any     :: repr a
  
--   pair    :: repr a b -> repr c d -> repr (a, c) (b, d)
--   cons    :: repr a b -> repr [a] [b] -> repr [a] [b]
-- 
--   -- append  :: repr [a] [b] -> repr [a] [b] -> repr [a] [b]
-- 
--   via     :: repr a b -> repr b c -> repr a c
--   var     :: T.Text -> repr a a
--   any     :: repr a a
--   const   :: (IsPatt a) => a -> repr a a
--   app     :: (Show a, IsPatt a, Show b, IsPatt b) => U.Fun a b -> repr a b
--   map     :: (Show b, IsPatt b, Show c, IsPatt c) => U.Fun b c -> repr a b -> repr a c
--   map2    :: (IsPatt b, IsPatt c, IsPatt d)
--           => U.Fun (b, c) d -> repr a b -> repr a c -> repr a d
-- 
--   with    :: repr a b -> repr () Bool -> repr a b 
--   eq      :: repr a b -> repr a' b -> repr () Bool


instance Op Pattern where

  pair   (Patt x) (Patt y) = Patt (U.pairP x y)
  cons   (Patt x) (Patt y) = Patt (U.rightP $ U.pairP x y)

  var v                      = Patt (U.labelP $ U.Var v)
  const x                    = Patt (U.encodeP x)

  map f (Patt p) = Patt $
    let fun' x0 = do
--           let x1 = trace ("%%% x0: " ++ show x0) (U.decodeI x0)
--           x2 <- trace ("%%% x1: " ++ show x1) (U.fbody f x1)
--           let x3 = trace ("%%% x2: " ++ show x2) (U.encodeI x2)
--           return $ trace ("%%% x3: " ++ show x3) x3
          let x1 = U.decodeI x0
          x2 <- U.fbody f x1
          return $ U.encodeI x2
        g = U.Fun {U.fname = U.fname f, U.fbody = fun'}
     in U.mapP g p

  bimap f (Patt x) (Patt y) = Patt $
    let fun' x0 = do
          let x1 = U.decodeI x0
          x2 <- U.fbody f x1
          return $ U.encodeI x2
          -- (:[]) . U.encodeI . U.fbody f . U.decodeI
        g = U.Fun {U.fname = U.fname f, U.fbody = fun'}
     in U.mapP g (U.pairP x y)

  fun f = Patt $
    let fun' x0 = do
          let x1 = U.decodeI x0
          x2 <- U.fbody f x1
          return $ U.encodeI x2
--               msg = unlines
--                 [ "%%% x1: " ++ show x1
--                 , "%%% x2: " ++ show x2
--                 , "%%% x3: " ++ show x3
--                 ]
--           return $ trace msg x3
        g = U.Fun {U.fname = U.fname f, U.fbody = fun'}
     in U.appP g
  
  via (Patt x) (Patt y)     = Patt (U.viaP x y)
  app (Patt x)              = Patt x

  with (Patt x) (Cond c)    = Patt (U.withP x c)
  eq (Patt x) (Patt y)      = Cond (U.Eq x y)

  and (Patt x) (Patt y)     = Patt (U.viaP x y)
  or (Patt x) (Patt y)      = Patt (U.orP x y)
  any                       = Patt U.anyP


-- -- | Typed pattern @Pattern a b@ matches objects of type @a@ and computes
-- -- objects of type @b@.
-- data Pattern a b
--   = Patt {unPatt :: U.Pattern}
--   | Cond {unCond :: U.Cond U.Pattern}
--   deriving (Show, Eq, Ord)
-- 
-- 
-- -- | Tagless-final encoding of generic operations supported on patterns.
-- class Op repr where
--   
--   pair    :: repr a b -> repr c d -> repr (a, c) (b, d)
--   cons    :: repr a b -> repr [a] [b] -> repr [a] [b]
-- 
--   -- append  :: repr [a] [b] -> repr [a] [b] -> repr [a] [b]
-- 
--   or      :: repr a b -> repr a b -> repr a b
--   via     :: repr a b -> repr b c -> repr a c
--   var     :: T.Text -> repr a a
--   any     :: repr a a
--   const   :: (IsPatt a) => a -> repr a a
--   app     :: (Show a, IsPatt a, Show b, IsPatt b) => U.Fun a b -> repr a b
--   map     :: (Show b, IsPatt b, Show c, IsPatt c) => U.Fun b c -> repr a b -> repr a c
--   map2    :: (IsPatt b, IsPatt c, IsPatt d)
--           => U.Fun (b, c) d -> repr a b -> repr a c -> repr a d
-- 
--   with    :: repr a b -> repr () Bool -> repr a b 
--   eq      :: repr a b -> repr a' b -> repr () Bool
-- 
-- --   map'    :: (IsPatt a, IsPatt b) => U.Fun a b -> repr a a -> repr b b
-- 
-- 
-- -- append' :: (Op repr) => repr [a] [b] -> repr [a] [b] -> repr [a] [b]
-- -- append' = undefined
-- 
-- 
-- instance Op Pattern where
-- 
--   pair  (Patt x) (Patt y) = Patt (U.pairP x y)
--   cons  (Patt x) (Patt y) = Patt (U.rightP $ U.pairP x y)
-- 
--   or    (Patt x) (Patt y) = Patt (U.orP x y)
--   via   (Patt x) (Patt y) = Patt (U.viaP x y)
--   var v                   = Patt (U.labelP $ U.Var v)
--   any                     = Patt U.anyP
--   const x                 = Patt (U.encodeP x)
-- 
--   app f = Patt $
--     let fun' x0 = do
--           let x1 = U.decodeI x0
--           x2 <- U.fun f x1
--           return $ U.encodeI x2
-- --               msg = unlines
-- --                 [ "%%% x1: " ++ show x1
-- --                 , "%%% x2: " ++ show x2
-- --                 , "%%% x3: " ++ show x3
-- --                 ]
-- --           return $ trace msg x3
--         g = U.Fun {U.fname = U.fname f, U.fun = fun'}
--      in U.appP g
-- 
--   map f (Patt p) = Patt $
--     -- let fun' = (:[]) . U.encodeI . U.fun f . U.decodeI
--     let fun' x0 = do
-- --           let x1 = trace ("%%% x0: " ++ show x0) (U.decodeI x0)
-- --           x2 <- trace ("%%% x1: " ++ show x1) (U.fun f x1)
-- --           let x3 = trace ("%%% x2: " ++ show x2) (U.encodeI x2)
-- --           return $ trace ("%%% x3: " ++ show x3) x3
--           let x1 = U.decodeI x0
--           x2 <- U.fun f x1
--           return $ U.encodeI x2
--         g = U.Fun {U.fname = U.fname f, U.fun = fun'}
--      in U.mapP g p
-- 
--   map2 f (Patt x) (Patt y) = Patt $
--     let fun' x0 = do
--           let x1 = U.decodeI x0
--           x2 <- U.fun f x1
--           return $ U.encodeI x2
--           -- (:[]) . U.encodeI . U.fun f . U.decodeI
--         g = U.Fun {U.fname = U.fname f, U.fun = fun'}
--      in U.mapP g (U.pairP x y)
-- 
--   with (Patt x) (Cond c)  = Patt (U.withP x c)
--   eq (Patt x) (Patt y)    = Cond (U.Eq x y)
