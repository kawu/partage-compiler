{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DerivingStrategies #-}

-- {-# LANGUAGE QuantifiedConstraints #-}


module ParComp.Pattern.Untyped
  (

  -- * Core types
    Fun (..)
--   , Pred (..)
  , Var (..)
  , LVar (..)

--   -- * Registered functions
--     FunSet (..)
--   , FunName (..)
--   , emptyFunSet

  -- * Items and patterns
  , Item (..)
  , Rigit (..)
  , Pattern (..)
  , Op (..)
  , Cond (..)

  , strip

  -- ** IsItem class
  , IsItem (..)
  , encodeI
  , decodeI
  , encodeP
  , decodeP

  -- ** Smart constructors
  , unitP
  , symP
  , vecP
  , tagP
--   , pairP
--   , leftP
--   , rightP

  , orP
  , viaP
  , appP
  , mapP
  , map'P
  , labelP
  , anyP
  , withP

  , localP
  , letP
  , fixP
  , recP

  -- * Matching
  , MatchT
  , MatchingStrategy (..)
  , isMatch
  , doMatch
  , lift
  , forEach
  , runMatchT
  , match
  , close
  , check

  -- * Rule
  , Rule (..)
  , apply
  -- ** Directional rule
  , DirRule (..)
  , directRule

  -- * Indexing (locks and keys)
  , Lock (..)
  , Key
  , mkLock
  , groupByTemplate
  , itemKeyFor
  , keyFor
  , locksFor

  -- * Utils
  , pickOne
  ) where


import           Prelude hiding (const, map, any)

import qualified System.Random as R

import           Control.Monad (guard, void, forM)
import qualified Control.Monad.RWS.Strict as RWS
import           Control.Applicative (Alternative, (<|>), empty)

import qualified Pipes as P
import qualified Pipes.Prelude as P

import           Data.Lens.Light

import qualified Data.Primitive.Array as A

import           Data.Void (Void)
import           Data.String (IsString)
import qualified Data.Foldable as F
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import           Debug.Trace (trace)


--------------------------------------------------
-- Item
--------------------------------------------------


-- | Chart item expression
data Item expr where
  Unit  :: Item expr
  Sym   :: {-# UNPACK #-} !T.Text -> Item expr

--   Pair  :: expr -> expr -> Item expr
--   Union :: Either expr expr -> Item expr

  -- New primitives below

  Vec   :: A.Array expr -> Item expr
  -- ^ Non-empty vector of expressions (to represent product types)
  -- (TODO: or maybe we could/should use it to represent unit, too?)

  Tag   :: {-# UNPACK #-} !Int -> expr -> Item expr
  -- ^ Tagged expression (to represent sum types)

--   Num   :: {-# UNPACK #-} !Int -> Item expr
--   -- ^ Integral number

  deriving (Show, Eq, Ord)


-- instance (Show expr) => Show (Item expr) where
--   show Unit = "()"
--   show (Sym x) = "\"" ++ T.unpack x ++ "\""
--   show (Vec v) = show (F.toList v)
--   show (Tag k x) = show k ++ ":" ++ show x


-- | Rigid item expression
newtype Rigit = I (Item Rigit)
  deriving (Eq, Ord)
  deriving newtype (Show)


-- | Extract the rigit item.
unI :: Rigit -> Item Rigit
unI (I x) = x


-- | Rigit constructors
unit      = I Unit
sym x     = I $ Sym x
-- pair x y  = I $ Pair x y
-- left x    = I . Union $ Left x
-- right y   = I . Union $ Right y


-- | Construct a vector of `Rigit`s.
vec :: A.Array Rigit -> Rigit
vec = I . Vec
  -- . A.fromList


-- | Construct a tagged `Rigit`.
tag :: Int -> Rigit -> Rigit
tag k = I . Tag k


-- -- | Construct a numeral `Rigit`.
-- num :: Int -> Rigit
-- num = I . Num


-- Special constructors for Booleans, since we treat them special (predicates)
false mkP = mkP . Tag 0 $ mkP Unit
true  mkP = mkP . Tag 1 $ mkP Unit


--------------------------------------------------
-- Functions and predicates
--------------------------------------------------


-- | Named function
--
-- We require that all function and predicate names are unique.
data Fun a b = Fun
  { fname :: T.Text
    -- ^ The function's name
  , fbody :: a -> [b]
    -- ^ The function itself (non-deterministic)
  }

instance Show (Fun a b) where
  show Fun{..} = T.unpack fname

instance Eq (Fun a b) where
  x == y = fname x == fname y

instance Ord (Fun a b) where
  x `compare` y = fname x `compare` fname y


-- -- | Named predicate
-- --
-- -- We require that all function and predicate names are unique.  (See the
-- -- `guard` function in the `Typed` module to understand why a predicate should
-- -- not have the same name as a function).
-- data Pred a = Pred
--   { pname :: T.Text
--     -- ^ The predicate's name
--   , pbody :: a -> Bool
--     -- ^ The predicate itself
--   }
-- 
-- instance Show (Pred a) where
--   show Pred{..} = T.unpack pname
-- 
-- instance Eq (Pred a) where
--   x == y = pname x == pname y
-- 
-- instance Ord (Pred a) where
--   x `compare` y = pname x `compare` pname y


--------------------------------------------------
-- Pattern
--------------------------------------------------


-- | Variable
newtype Var = Var T.Text
  deriving (Show, Eq, Ord)


-- | Extract the variable.
unVar :: Var -> T.Text
unVar (Var x) = x


-- | Local variable name
newtype LVar = LVar T.Text
  deriving (Show, Eq, Ord)


-- | Extract the variable.
unLVar :: LVar -> T.Text
unLVar (LVar x) = x


-- | Pattern operation expression
data Op t
  = Or t t
  -- ^ Or (disjunction): match items which match either of the two patterns.
  -- `Or` provides non-determinism in pattern matching.
  | Via t t
  -- ^ Via: `Via p x` should be understood as matching `x` with the underlying
  -- item via `p`:
  -- * `p` is first matched with the underlying item
  -- * `x` is then matched with the result
  -- `Via` can be seen as conjunction.
  | Label Var
  -- ^ Label: match any item expression and bind it to the given variable
  | Local LVar
  -- ^ Local variable: local variable used in the `Let` pattern
  | Any
  -- ^ Any: match any item expression (wildcard pattern)
  | Map (Fun Rigit Rigit) t
  -- ^ Mapping: match the pattern with the item and apply the function to the
  -- result.
  | Map' t t
  -- ^ Mapping: match the (second) pattern with the item and apply the first,
  -- functional pattern to the result.
  | App (Fun Rigit Rigit)
  -- ^ Application: apply the function to the item before pattern matching.
  | With t (Cond t)
  -- ^ With: pattern match and (then) check the condition
  | Let t t t
  -- ^ Let: `Let x e y` should be read as ,,let x = e in y'', where:
  -- * `e` is matched with the underlying item
  -- * `x` is matched with the result to bind local variables
  -- * `y` is the result constructed based on the bound local variables
  | Fix t
  -- ^ Fix: `Fix p` defines a recursive pattern `p`, which can be referred to
  -- with `Rec` from within `p`
  | Rec
  -- ^ Rec: call recursive pattern `p` defined with `Fix p`
  deriving (Show, Eq, Ord)


-- | Condition expression
--
-- Note that condition expression should contain no free variables, nor
-- wildcard patterns.  This is because side conditions are not matched against
-- items.
data Cond t
  = Eq t t
  -- ^ Check the equality between two patterns
--   | Check (Pred Rigit) t
--   -- ^ Check if the given predicate is satisfied
  | And (Cond t) (Cond t)
  -- ^ Logical conjunction
  | OrC (Cond t) (Cond t)
  -- ^ Logical disjunction
--   | TrueC
--   -- ^ Always True
  | IsTrue t
  -- ^ Check if the given Boolean (predicate) pattern is satisfied
  deriving (Show, Eq, Ord)


-- | Pattern expression
data Pattern
  = P (Item Pattern)
  -- ^ Item pattern
  | O (Op Pattern)
  -- ^ Operation pattern
  deriving (Show, Eq, Ord)

-- instance Show Pattern where
--   show (P x) = show x
--   show (O x) = show x


-- | Pattern constructors
unitP       = P $ Unit
symP x      = P $ Sym x
-- pairP x y   = P $ Pair x y
-- leftP x     = P . Union $ Left x
-- rightP y    = P . Union $ Right y

viaP x y    = O $ Via x y
orP x y     = O $ Or x y
appP f      = O $ App f
mapP f x    = O $ Map f x
map'P f x   = O $ Map' f x
labelP v    = O $ Label v
localP v    = O $ Local v
anyP        = O $ Any
withP p c   = O $ With p c
letP x e y  = O $ Let x e y
fixP p      = O $ Fix p
recP        = O $ Rec


-- | Construct a vector of `Pattern`s.
vecP :: [Pattern] -> Pattern
-- vecP :: A.Array Pattern -> Pattern
vecP = P . Vec . A.fromList


-- | Construct a tagged `Pattern`.
tagP :: Int -> Pattern -> Pattern
tagP k = P . Tag k


-- | Convert the pattern to the corresponding item expression, in case it does
-- not use any `Op`s (pattern specific operations/constructions).
strip :: Pattern -> Rigit
strip = \case
  P ip -> case ip of
    Unit  -> unit
    Sym x -> sym x
--     Pair x y -> pair (strip x) (strip y)
    Vec v -> vec (fmap strip v)
--     Union u -> case u of
--       Left x  -> left  $ strip x
--       Right y -> right $ strip y
    Tag k x -> tag k (strip x)
  O op -> error $ "cannot strip pattern with Op: " ++ show (O op)


-- -- | The inverse of `strip`.
-- clothe :: Rigit -> Pattern
-- clothe = undefined


--------------------------------------------------
-- Item/pattern encoding
--------------------------------------------------


class IsItem t where
  -- | Encode a value as an item
  encode :: (Item p -> p) -> t -> p
  -- | Decode a value from an item
  decode :: (Show p) => (p -> Item p) -> p -> t


-- | Encode a value as a `Rigit`. 
encodeI :: IsItem t => t -> Rigit
encodeI = encode I


-- | Decode a value from a `Rigit`.
decodeI :: IsItem t => Rigit -> t
decodeI = decode unI


-- | Encode a value as a `Pattern`. 
encodeP :: IsItem t => t -> Pattern
encodeP = encode P


-- | Decode a value from a `Pattern`.
decodeP :: IsItem t => Pattern -> t
decodeP = decode $ \case
  P x -> x
  O _ -> error "decodeP: cannot decode O"


-- IMPORTANT NOTE: The implemented instances below must correspond with the
-- patterns provided in the Typed interface module.


instance IsItem () where
  encode mkP _ = mkP Unit
  decode unP _ = ()

-- TODO: re-implement based on Num?
instance IsItem Bool where
  encode mkP = \case
    -- NB: we alsu use `true` below in `check`
    False -> false mkP  -- mkP . Tag 0 $ mkP Unit
    True  -> true mkP   -- mkP . Tag 1 $ mkP Unit
  decode unP x =
    case unP x of
      Tag k _ -> case k of
        0 -> False
        1 -> True
      _ -> error $ "cannot decode " ++ show x ++ " to Bool"

-- instance IsItem Bool where
--   encode mkP = \case
--     False -> mkP . Union . Left  $ mkP Unit
--     True  -> mkP . Union . Right $ mkP Unit
--   decode unP x =
--     case unP x of
--       Union u -> case u of
--         Left  _ -> False
--         Right _ -> True
--       _ -> error $ "cannot decode " ++ show x ++ " to Bool"

-- TODO: re-implement based on Num?
instance IsItem Int where
  encode mkP = mkP . Sym . T.pack . show
  decode unP p = case unP p of
    Sym x -> read (T.unpack x)
    _ -> error $ "cannot decode " ++ show p ++ " to Int"

instance IsItem T.Text where
  encode mkP = mkP . Sym
  decode unP p = case unP p of
    Sym x -> x
    _ -> error $ "cannot decode " ++ show p ++ " to Text"

instance (IsItem a, IsItem b) => IsItem (a, b) where
  encode mkP (x, y) = mkP . Vec $
    A.fromListN 2 [encode mkP x, encode mkP y]
  decode unP p = case unP p of
    Vec v -> (decode unP (A.indexArray v 0), decode unP (A.indexArray v 1))
    _ -> error $ "cannot decode " ++ show p ++ " to (,)"

-- instance (IsItem a, IsItem b) => IsItem (a, b) where
--   encode mkP (x, y) = mkP $ Pair (encode mkP x) (encode mkP y)
--   decode unP p = case unP p of
--     Pair x y -> (decode unP x, decode unP y)
--     _ -> error $ "cannot decode " ++ show p ++ " to (,)"

instance (IsItem a, IsItem b, IsItem c) => IsItem (a, b, c) where
  encode mkP (x, y, z) = mkP . Vec $
    A.fromListN 3 [encode mkP x, encode mkP y, encode mkP z]
  decode unP p = case unP p of
    Vec v -> 
      ( decode unP (A.indexArray v 0)
      , decode unP (A.indexArray v 1)
      , decode unP (A.indexArray v 2)
      )
    _ -> error $ "cannot decode " ++ show p ++ " to (,,)"

-- instance (IsItem a, IsItem b, IsItem c) => IsItem (a, b, c) where
--   encode mkP (x, y, z) =
--     mkP $ Pair (encode mkP x) (mkP $ Pair (encode mkP y) (encode mkP z))
--   decode unP p = case unP p of
--     Pair x p' -> case unP p' of
--       Pair y z -> (decode unP x, decode unP y, decode unP z)
--     _ -> error $ "cannot decode " ++ show p ++ " to (,,)"

instance (IsItem a) => IsItem (Maybe a) where
  encode mkP = \case
    Nothing -> mkP . Tag 0 $ mkP Unit
    Just x  -> mkP . Tag 1 $ encode mkP x
  decode unP p = case unP p of
    Tag k x -> case k of
      0 -> Nothing
      1 -> Just (decode unP x)
    _ -> error $ "cannot decode " ++ show p ++ " to Maybe"

-- instance (IsItem a) => IsItem (Maybe a) where
--   encode mkP = \case
--     Nothing -> mkP . Union . Left  $ mkP Unit
--     Just x  -> mkP . Union . Right $ encode mkP x
--   decode unP p = case unP p of
--     Union u -> case u of
--       Left _  -> Nothing
--       Right x -> Just (decode unP x)
--     _ -> error $ "cannot decode " ++ show p ++ " to Maybe"

instance (IsItem a, IsItem b) => IsItem (Either a b) where
  encode mkP = \case
    Left x  -> mkP . Tag 0 $ encode mkP x
    Right y -> mkP . Tag 1 $ encode mkP y
  decode unP p = case unP p of
    Tag k x -> case k of
      0 -> Left  $ decode unP x
      1 -> Right $ decode unP x
    _ -> error $ "cannot decode " ++ show p ++ " to Either"

-- instance (IsItem a, IsItem b) => IsItem (Either a b) where
--   encode mkP = \case
--     Left x  -> mkP . Union . Left  $ encode mkP x
--     Right y -> mkP . Union . Right $ encode mkP y
--   decode unP p = case unP p of
--     Union u -> case u of
--       Left x  -> Left  $ decode unP x
--       Right y -> Right $ decode unP y
--     _ -> error $ "cannot decode " ++ show p ++ " to Either"

instance (IsItem a) => IsItem [a] where
  encode mkP = \case
    []      -> mkP . Tag 0 $ mkP Unit
    x : xs  -> mkP . Tag 1 $ mkP . Vec $
      A.fromListN 2 [encode mkP x, encode mkP xs]
  decode unP p = case unP p of
    Tag k p' -> case k of
      0 -> []
      1 ->
        let (x, xs) = decode unP p'
         in x : xs
    _ -> error $ "cannot decode " ++ show p ++ " to []"

-- instance (IsItem a) => IsItem [a] where
--   encode mkP = \case
--     []      -> mkP . Union . Left  $ mkP Unit
--     x : xs  -> mkP . Union . Right $
--       mkP $ Pair (encode mkP x) (encode mkP xs)
--   decode unP p = case unP p of
--     Union u -> case u of
--       Left _ -> []
--       Right p' ->
--         let (x, xs) = decode unP p'
--          in x : xs
--     _ -> error $ "cannot decode " ++ show p ++ " to []"


--------------------------------------------------
-- Global vars
--------------------------------------------------


-- | Retrieve the set of global variables bound in the pattern.
--
-- A variable is bound in the pattern if it gets bound during matching of the
-- pattern with an item.
--
-- Assumption: In case of the `Or` pattern, we assume that both branches
-- contain the same set of global variables.  This is non-trivial to check at
-- runtime (and hence is not enforced) due to `Rec` patterns.
globalVarsIn :: Pattern -> S.Set Var
globalVarsIn (P ip) = case ip of
--   Pair p1 p2 -> globalVarsIn p1 <> globalVarsIn p2
  Vec v -> foldMap globalVarsIn v
--   Union up -> case up of
--     Left p  -> globalVarsIn p
--     Right p -> globalVarsIn p
  Tag _ x -> globalVarsIn x
  _ -> S.empty
globalVarsIn (O op) = case op of
  Or x y -> globalVarsIn x <> globalVarsIn y
--     let xs = globalVarsIn x
--         ys = globalVarsIn y
--      in if xs == ys
--            then xs
--            else error "globalVarsIn: different sets of variables in Or"
  Via x y -> globalVarsIn x <> globalVarsIn y
  Label v -> S.singleton v
  Local _ -> error "globalVarsIn: encountered local variable!"
  Any -> S.empty
  Map _ p -> globalVarsIn p
  Map' f p ->
    let fs = globalVarsIn f
        ps = globalVarsIn p
     in if S.null fs
           then ps
           else error $ concat
              [ "globalVarsIn: functional pattern with global variables: "
              , show (S.toList fs)
              ]
  App _ -> S.empty
  -- Below, we don't inspect the condition, since it doesn't bind additional
  -- variables during matching
  With p _ -> globalVarsIn p
  -- Below, ignore `x` and `y`, which should contain local variables only
  Let x e y -> globalVarsIn e
  Fix p -> globalVarsIn p
  Rec -> S.empty


--------------------------------------------------
-- Pattern matching core
--------------------------------------------------


-- | Variable binding environment
type Env v = M.Map v Rigit


-- | Pattern matching state
data PMState = PMState
  { _genv :: Env Var
    -- ^ Global variable binding environment
  , _lenv :: Env LVar
    -- ^ Local variable binding environment
  , _fix :: Maybe Pattern
    -- ^ Fixed recursive pattern
  , _penv :: Env Pattern
    -- ^ Pattern binding environment (only relevant for lazy matching)
  } deriving (Show)
$( makeLenses [''PMState] )


-- | Pattern matching monad transformer
type MatchT m a =
--   P.ListT (RWS.RWST FunSet () PMState m) a
  P.ListT (RWS.RWST () () PMState m) a


-- | Lift the computation in the inner monad to `MatchT`.
lift :: (Monad m) => m a -> MatchT m a
lift = RWS.lift . RWS.lift


-- | Perform the matching computation for each element in the list.  Start each
-- matching from the current state (so that matching computations the
-- individual elements are independent).
forEach
  :: (Monad m)
  => [a]
  -> (a -> MatchT m b)
  -> MatchT m b
forEach xs m = do
  state <- RWS.get
  choice $ do
    x <- xs
    return $ do
      RWS.put state
      m x


-- | Run pattern matching computation with the underlying functions and
-- predicates.
runMatchT
  :: (Monad m)
--   => FunSet
  => MatchT m a
  -> m ()
runMatchT m = void $
  RWS.evalRWST (P.runListT m) ()  -- funSet
    (PMState M.empty M.empty Nothing M.empty)


-- | Look up the value assigned to the global variable.
lookupVar
  :: (Monad m)
  => Var
  -> MatchT m (Maybe Rigit)
-- lookupVar v@(Var "gamma") = do
--   x <- RWS.gets $ M.lookup v . getL genv
--   return $ trace ("!!! gamma = " ++ show x) x
lookupVar v = RWS.gets $ M.lookup v . getL genv


-- | Look up the value assigned to the local variable.
lookupLVar
  :: (Monad m)
  => LVar
  -> MatchT m (Maybe Rigit)
lookupLVar v = RWS.gets $ M.lookup v . getL lenv


-- | Retrieve the value bound to the given variable.
retrieveVar
  :: (Monad m)
  => Var
  -> MatchT m Rigit
retrieveVar v =
  lookupVar v >>= \case
    Nothing -> empty
    Just it -> return it


-- | Bind the item to the given variable.  If the variable is already bound,
-- make sure that the new item is equal to the old one.
bindVar
  :: (Monad m)
  => Var
  -> Rigit
  -> MatchT m ()
bindVar v it = do
  mayIt <- RWS.lift $ RWS.gets (M.lookup v . getL genv)
  case mayIt of
    Nothing -> RWS.modify' . modL genv $ M.insert v it
    Just it' -> guard $ it == it'


-- | Bind the item to the given local variable.
bindLVar
  :: (Monad m)
  => LVar
  -> Rigit
  -> MatchT m ()
bindLVar v it = RWS.modify' . modL lenv $ M.insert v it


-- | Look up the value bound to the given pattern.
lookupPatt
  :: (Monad m)
  => Pattern
  -> MatchT m (Maybe Rigit)
lookupPatt p = RWS.gets $ M.lookup p . getL penv


-- | Bind the item value to the given pattern.
bindPatt
  :: (Monad m)
  => Pattern
  -> Rigit
  -> MatchT m ()
bindPatt p it = do
  mayIt <- RWS.lift $ RWS.gets (M.lookup p . getL penv)
  case mayIt of
    Nothing -> RWS.modify' . modL penv $ M.insert p it
    Just it' -> guard $ it == it'


-- | Perform two alternative matches.  The environment is restored to its
-- original state after the first match.
alt
  :: (P.MonadIO m)
  => MatchT m a
  -> MatchT m a
  -> MatchT m a
alt m1 m2 = do
  state <- RWS.get
  m1 <|> do
    RWS.put state
    m2


-- -- | Perform the given patter matching in a local environment, restoring the
-- -- values of all the local variables at the end.
-- withLocalEnv
--   :: (P.MonadIO m)
--   => MatchT m a
--   -> MatchT m a
-- withLocalEnv m = do
--   mark <- (`mod` 1000) <$> P.liftIO (R.randomIO :: IO Int)
--   e <- RWS.gets (getL lenv)
--   P.liftIO $ do
--     putStr ">>> IN: "
--     print mark
-- 
--   next (P.enumerate m) >>= \case
--     Left _ -> do
--       restore e mark
--       empty
--     Right (x, p) -> do
--       go e mark x p
-- 
-- --   x <- m <|> do
-- --     restore e mark
-- --     empty
-- --   restore e mark
-- --   return x
-- 
--   where
-- 
--     go e mark x p = do
--       restore e mark
--       return x
--       next p >>= \case
--         Left _ -> undefined
--         Right (x', p') ->
--           go e mark x' p'
-- 
--     next p = RWS.lift (P.next p)
-- 
--     -- Restore the local environment
--     restore e mark = do
--       RWS.modify' (setL lenv e)
--       P.liftIO $ do
--         putStr "<<< OUT: "
--         print mark


-- | Perform the given patter matching in a local environment, restoring the
-- values of all the local variables at the end.
withLocalEnv
  :: (P.MonadIO m)
  => MatchT m a
  -> MatchT m a
withLocalEnv m = do
--   mark <- (`mod` 1000) <$> P.liftIO (R.randomIO :: IO Int)
  e <- RWS.gets (getL lenv)
--   P.liftIO $ do
--     putStr ">>> IN: "
--     print mark
  x <- m <|> do
    restore e  -- mark
    empty
  restore e  -- mark
  return x
  where
    -- Restore the local environment
--     restore e mark = do
    restore e = do
      RWS.modify' (setL lenv e)
--       P.liftIO $ do
--         putStr "<<< OUT: "
--         print mark


-- | Perform match with the recursive pattern.
withFix
  :: (Monad m)
  => Pattern
  -> MatchT m a
  -> MatchT m a
withFix p m = do
  -- Retrieve the old fix
  oldFix <- RWS.gets $ getL fix
  -- Register the new fix
  RWS.modify' $ setL fix (Just p)
  m <|> do
    -- Restore the old fix
    RWS.modify' $ setL fix oldFix
    empty


-- | Retrieve the fixed recursive pattern.
fixed :: (Monad m) => MatchT m Pattern
fixed = do
  mayFix <- RWS.gets $ getL fix
  case mayFix of
    Nothing -> empty
    Just p  -> return p


-- -- | Retrieve the predicate with the given name.  The function with the name
-- -- must exist, otherwise `retrievePred` thorws an error (alternatively, the
-- -- pattern match could simplify fail, but that could lead to hard-to-find
-- -- errors in deduction rules).
-- retrievePred
--   :: (Monad m)
--   => PredName
--   -> MatchT m (Rigit -> Bool)
-- retrievePred predName = do
--   mayFun <- RWS.asks (M.lookup predName . predMap)
--   case mayFun of
--     Nothing -> error $ concat
--       [ "retrievePred: function with name '"
--       , T.unpack $ unPredName predName
--       , "' does not exist"
--       ]
--     Just fun -> return fun


-- -- | Retrieve the symbol-level function with the given name.  The function with
-- -- the name must exist, otherwise `retrieveFun` thorws an error.
-- retrieveFun
--   :: (Monad m)
--   => FunName
--   -> MatchT m (Rigit -> [Rigit])
-- retrieveFun funName = do
--   mayFun <- RWS.asks (M.lookup funName . funMap)
--   case mayFun of
--     Nothing -> error $ concat
--       [ "retrieveFun: function with name '"
--       , T.unpack $ unFunName funName
--       , "' does not exist"
--       ]
--     Just fun -> return fun


--------------------------------------------------
-- High-level pattern matching
--------------------------------------------------


-- | Check if the pattern matches with the given item.
isMatch :: (P.MonadIO m) => Pattern -> Rigit -> m Bool
isMatch p x =
  not <$> P.null (P.enumerate (doMatch p x))


-- | Perform pattern matching and generate the list of possible global variable
-- binding environments which satisfy the match.
-- doMatch :: (P.MonadIO m) => Pattern -> Rigit -> P.ListT m (Env Var)
doMatch :: (P.MonadIO m) => Pattern -> Rigit -> P.ListT m Rigit
doMatch p x = do
  P.Select $
    _doMatch p x P.yield


-- | Lower-level handler-based `doMatch`.
_doMatch
  :: (P.MonadIO m)
  => Pattern
  -> Rigit
  -- -> (Env Var -> m ()) -- ^ Monadic handler
  -> (Rigit -> m ()) -- ^ Monadic handler
  -> m ()
_doMatch p x h =
  runMatchT $ do
    x <- match Strict p x
    lift $ h x
    -- e <- RWS.gets $ getL genv
    -- lift $ h e


--------------------------------------------------
-- Pattern matching
--------------------------------------------------


-- | Pattern matching strategy
data MatchingStrategy
  = Strict
  -- ^ Strict matching requires that, whenever a `Cond`ition is encountered, or
  -- a function `App`lication, all the variables necessary to their evaluation
  -- are already bound.  This should be considered as the default matching
  -- strategy.
  | Lazy
  -- ^ Lazy pattern matching can be performed in an environment where not all
  -- variables that are necessary to perform the evaluation are bound.  As a
  -- result of lazy matching, the pattern binding environment provides the
  -- values of selected patterns, which could not have been evaluated so far.
  deriving (Show, Eq, Ord)


-- | Match the pattern with the given item expression.  The resulting item is
-- not necessarily the same as the input item due to the `Let` pattern
-- construction, which allows to change the matching result.
match
  :: (P.MonadIO m)
  => MatchingStrategy
  -> Pattern
  -> Rigit
  -> MatchT m Rigit
match ms (P ip) (I it) =
  case (ip, it) of
    (Unit, Unit) -> pure unit
    (Sym x, Sym y) -> do
      guard $ x == y
      return $ sym x
--     (Pair p1 p2, Pair i1 i2) ->
--       pair <$> match ms p1 i1 <*> match ms p2 i2
    (Vec v1, Vec v2) -> do
      let n = A.sizeofArray v1
          m = A.sizeofArray v2
      if n /= m
         then error $ "match fail due to length mismatch: " ++ show (v1, v2)
         else return ()
      -- TODO: could this be optimized?
      ys <- forM [0..n-1] $ \k -> do
        match ms (A.indexArray v1 k) (A.indexArray v2 k)
        -- pair <$> match ms p1 i1 <*> match ms p2 i2
      return . vec $ A.fromListN n ys
--     (Union pu, Union iu) ->
--       case (pu, iu) of
--         (Left pl, Left il) ->
--           left <$> match ms pl il
--         (Right pr, Right ir) ->
--           right <$> match ms pr ir
--         -- Fail otherwise
--         _ -> empty
    (Tag k x, Tag k' y) -> do
      guard $ k == k'
      tag k <$> match ms x y
    _ -> error $ "match fail: " ++ show (ip, it)
match ms (O op) it =
  case (op, it) of
    (Label x, _) -> do
      bindVar x it
      return it
    (Local x, _) -> do
      bindLVar x it
      return it
    (Any, _) ->
      return it
--     (Map fname p, it) -> do
    (Map f p, it) -> do
      -- f <- retrieveFun fname
      let strict = do
            x <- close p
            it' <- each $ (fbody f) x
            guard $ it' == it
            return it
      case ms of
        Strict -> strict
        Lazy -> do
          closeable p >>= \case
            True -> strict
            False -> do
              bindPatt p it
              return it
    (Map' f p, it) -> do
      case ms of
        Strict -> do
          x <- close p
          it' <- match ms f x
          guard $ it' == it
          return it
        -- TODO: properly handle Lazy matching
        Lazy -> do
--           P.liftIO $ do
--             putStrLn "!!! Matching Map' (1)"
--             putStr "p   : " >> print p
--             putStr "it  : " >> print it
--             putStr "f   : " >> print f
          x <- close p
--           P.liftIO $ do
--             putStrLn "!!! Matching Map' (2)"
--             putStr "x   : " >> print x
          it' <- match ms f x
--           P.liftIO $ do
--             putStrLn "!!! Matching Map' (3)"
--             putStr "it' : " >> print it'
--             putStr "it == it': " >> print (it' == it)
          guard $ it' == it
--           P.liftIO $ do
--             putStrLn "!!! Matching Map' (4)"
          return it
--     (App fname, it) -> do
    (App f, it) -> do
      -- f <- retrieveFun fname
      each $ fbody f it
    -- NOTE: This could be alternatively called "Choice" operator (from
    -- "non-deterministic choice operator")
    (Or p1 p2, it) -> do
      -- NOTE: We retrieve and then restore the entire state, even though the
      -- fixed recursive pattern should never escape its syntactic scope so, in
      -- theory, it should not change between the first and the second branch
      -- of the `Or` pattern.  The same applies to local variables.  Perhaps
      -- this is something we could check dynamically, just in case?
      match ms p1 it `alt` match ms p2 it
    (Via p x, it) -> do
      -- NOTE: We return `it` at the end rather than the result of either of
      -- the two matches.  This matches nicely with how the types of the @via@
      -- pattern in the typed interface are defined.  A natural alternative
      -- would be to return the result of the second match -- we could provide
      -- this behavior with another operator if needed.
      it' <- match ms p it
      match ms x it'
      return it
    (With p c, it) -> do
      match ms p it
      check ms c
      return it
    (Let x e y, it) -> do
      mark <- (`mod` 1000) <$> P.liftIO (R.randomIO :: IO Int)
--       RWS.gets (getL lenv) >>= \lvs -> P.liftIO $ do
--         putStr "!!! Let0 #" >> print mark
--         putStr "lvs : " >> print lvs
      it' <- match ms e it
      -- Temporary test below
--       if (it /= it')
--          then error "it /= it'"
--          else return ()
      withLocalEnv $ do
--         RWS.gets (getL lenv) >>= \lvs -> P.liftIO $ do
--           -- putStr ("[" ++ show mark ++ "-2] ")
--           putStr "!!! Let1 #" >> print mark
--           putStr "x   : " >> print x
--           putStr "y   : " >> print y
--           putStr "it  : " >> print it
--           putStr "lvs : " >> print lvs
        match ms x it'
--         RWS.gets (getL lenv) >>= \lvs -> P.liftIO $ do
--           putStr "!!! Let2 #" >> print mark
--           putStr "lvs : " >> print lvs
        z <- close y
--         RWS.gets (getL lenv) >>= \lvs -> P.liftIO $ do
--           putStr "!!! Let3 #" >> print mark
--           putStr "z   : " >> print z
--           putStr "lvs : " >> print lvs
--           putStrLn "!!! Let4 END #"
        return z
    (Fix p, it) -> do
      withFix p $ do
        match ms p it
    (Rec, it) -> do
      p <- fixed
      match ms p it


-- | Check the side condition expression.
--
-- The `check` function does not modify the underlying state in case of
-- `Strict` matching.  In case of `Lazy` matching, `check` may update the
-- pattern binding envitonment (with `bindPatt`).
check :: (P.MonadIO m) => MatchingStrategy -> Cond Pattern -> MatchT m ()
check Strict = \case
  Eq px py  -> do
    x <- close px
    y <- close py
    guard $ x == y
-- --   Pred pname p -> do
-- --     flag <- retrievePred pname <*> close p
-- --     guard flag
--   Check pred p -> do
--     flag <- pbody pred <$> close p
--     guard flag
  And cx cy -> check Strict cx  >> check Strict cy
  OrC cx cy -> check Strict cx <|> check Strict cy
--   TrueC -> pure ()
  IsTrue p -> do
    x <- close p
    guard $ x == true I
check Lazy = \case
  Eq px py -> do
    cx <- closeable px
    cy <- closeable py
    case (cx, cy) of
      (True, True) -> do
        x <- close px
        y <- close py
        guard $ x == y
      (True, False) -> bindPatt py =<< close px
      (False, True) -> bindPatt px =<< close py
      (False, False) -> error "check Lazy: both patterns not closeable"
--   Check pred p -> do
--     -- pred <- retrievePred pname
--     closeable p >>= \case
--       True  -> do
--         flag <- pbody pred <$> close p
--         guard flag
--       False -> do
--         -- NB: We bind the pattern (see also `getLockVarsC`) with the unit
--         -- value to indicate that the value of the condition is True.
--         bindPatt (withP unitP (Check pred p)) unit
  And cx cy -> check Lazy cx >> check Lazy cy
  -- NB: Below, `alt` is necessary since `check` can modify the state in case
  -- of lazy evaluation
  OrC cx cy -> check Lazy cx `alt` check Lazy cy
  -- NB: The line below (commented out) is probably incorrect. In case of Lazy
  -- matching, some embedded check may succeed simply because we cannot
  -- determine its status yet (see (*) above).  Hence, negating the embedded
  -- result doesn't make sense.
  -- Neg c -> not <$> check Lazy c
--   TrueC -> pure ()
  IsTrue px -> do
    cx <- closeable px
    case cx of
      True -> do
        x <- close px
        guard $ x == true I
      False -> do
        bindPatt px (true I)


-- | Dummy pattern matching
--
-- Match the pattern against a dummy value by assuming that they match
-- perfectly.  The motivation behind `dummyMatch` is to bind the (global)
-- variables in the pattern (to some dummy values), so that we can later learn
-- what variables the pattern actually uses (and e.g. use `mkLock`).
--
-- Internally, the function (a) retrieves the set of global variables in @p@
-- and (b) binds them to unit values.
dummyMatch :: (Monad m) => Pattern -> MatchT m ()
dummyMatch p = do
  mapM_
    (flip bindVar unit)
    (S.toList $ globalVarsIn p)


-- | Convert the pattern to the corresponding item expression.  This is only
-- possible if the pattern contains no free variables nor wildcard patterns.
-- See also `strip`.
--
-- Note that `close` should not modify the underlying state/environment.
--
-- The behavior of the function is undefined for patterns containing any of the
-- following:
-- * `Via` patterns
-- * recursive patterns (`Fix` / `Rec`)
--
-- There is a subtle interaction between `close` and lazy matching.  It is
-- possible to `close` a pattern that actually contains free variables,
-- provided that the pattern binding environment provides the values of the
-- sub-patterns containing those variables (such variables are thus not truly
-- free, we don't know their value, but we know the values of certain patterns
-- that contain them).
close :: (P.MonadIO m) => Pattern -> MatchT m Rigit
close p =

  lookupPatt p >>= \case
    Just it -> pure it
    Nothing -> byCase p

  where

    byCase (P ip) = case ip of
--       Const it -> pure it
      Unit -> pure unit
      Sym x -> pure $ sym x
--       Pair p1 p2 -> pair <$> close p1 <*> close p2
      Vec v -> vec <$> mapM close v
--       Union up ->
--         case up of
--           Left lp  -> left <$> close lp
--           Right rp -> right <$> close rp
      Tag k x -> tag k <$> close x

    byCase (O op) = case op of
      -- Fail (silently) if variable x not bound
      Label v -> retrieveVar v
--         lookupVar v >>= \case
--           Just it -> pure it
--           Nothing -> error $ "close: Var not bound"
      Local v ->
        lookupLVar v >>= \case
          Just it -> pure it
          -- Local variables have syntactic scope, so the following should
          -- never happen
          Nothing -> error $ "close: LVar not bound"
      -- Fail in case of a wildcard pattern
      Any -> empty
--       LVar v ->
--         lookupLVar v >>= \case
--           Just it -> pure it
--           -- Local variables have syntactic scope, so the following should
--           -- never happen
--           Nothing -> error $ "close: LVar not bound"
--           -- Nothing -> empty
--       Map fname p -> do
      Map f p -> do
        -- f <- retrieveFun fname
        x <- close p
        y <- each $ fbody f x
        return y
      Map' f p -> do
        it <- close p
        match Strict f it
      App fname -> error "close App"
      Or p1 p2 ->
        -- NB: `alt` is not necessary, because `close` doesn't modify the state
        close p1 <|> close p2
      With p c -> do
        it <- close p
        check Strict c
        return it
      -- Not sure what to do with the two patterns below.  The intuitive
      -- implementations are commented out below, but they would not
      -- necessarily provide the desired behavior.  I guess we need some good
      -- examples showing what to do with those cases (if anything).
      Via _ _ -> error "close Via"
      Fix _ -> error "close Fix"
      Rec -> error "close Rec"
--       Fix p ->
--         withFix p $ do
--           close p
--       Rec -> do
--         p <- fixed
--         close p
--       -- Note that the implementation for `Via` requires performing the match
--       -- with possibly global variables.  One situation where this makes sense
--       -- is in the context of matching the @Let x e y@ pattern, where @y@ can
--       -- contain global variables (if we allow it, which seems useful).
--       Via p x -> do
--         it <- close p
--         match Strict x it


-- | Is the given pattern possible to close?
closeable :: (P.MonadIO m) => Pattern -> MatchT m Bool
closeable (P ip) = case ip of
--   Pair p1 p2 -> (&&) <$> closeable p1 <*> closeable p2
  Vec v -> and <$> mapM closeable v
--   Union up ->
--     case up of
--       Left lp  -> closeable lp
--       Right rp -> closeable rp
  Tag _ x -> closeable x
  Unit  -> pure True
  Sym _ -> pure True
closeable (O op) = case op of
--   Const it -> pure True
  Label v ->
    lookupVar v >>= \case
      Just it -> pure True
      Nothing -> pure False
  Local v ->
    lookupLVar v >>= \case
      Just it -> pure True
      Nothing -> pure False
  Any -> pure False
  Map _ p -> closeable p
  Map' f p -> (&&) <$> closeable f <*> closeable p
  App _ -> pure False
  Or p1 p2 -> do
    c1 <- closeable p1
    c2 <- closeable p2
    -- NB: The notion of being `closeable` relies on the status of global
    -- variables (bound or not) in the pattern.  We assume that the set of
    -- global variables is the same in both `Or` branches.
    if c1 == c2
       then return c1
       else error "closeable Or: different results for different branches"
  With p c -> (&&) <$> closeable p <*> closeableC c
  Let x e y -> closeable e
  Via _ _ -> error "closeable Via"
  Fix _ -> error "closeable Fix"
  Rec -> error "closeable Rec"


-- | Is the given side condition possible to close?
closeableC :: (P.MonadIO m) => Cond Pattern -> MatchT m Bool
closeableC = \case
  Eq px py -> (&&) <$> closeable py <*> closeable py
--   Check _ p -> closeable p
  And cx cy -> (&&) <$> closeableC cx <*> closeableC cy
  -- TODO: what about the case below?
  OrC cx cy -> undefined
  -- OrC cx cy -> (&&) <$> closeableC cx <*> closeableC cy
  -- Neg c -> closeableC c
--   TrueC -> pure True
  IsTrue p -> closeable p


--------------------------------------------------
-- Deduction rule
--------------------------------------------------


-- | Single deduction rule
data Rule = Rule
  { antecedents :: [Pattern]
    -- ^ The list of rule's antecedents
  , consequent :: Pattern
    -- ^ The rule's consequent
  , condition :: Cond Pattern
    -- ^ The rule's side condition
  } deriving (Show, Eq, Ord)


-- | Apply the deduction rule to the given items.  If the application succeeds,
-- the new chart item is returned.
--
-- The function treats the list of items as ordered and does not try other item
-- permutations when matching them with the `antecedents`.
apply :: (P.MonadIO m) => Rule -> [Rigit] -> MatchT m Rigit
apply Rule{..} items = do
  guard $ length antecedents == length items
  -- Match antecedents with the corresponding items
  mapM_
    (uncurry $ match Strict)
    (zip antecedents items)
  -- Make sure the side condition holds
  check Strict condition
  -- Convert the consequent to the resulting item
  close consequent


--------------------------------------------------
-- Directional rule
--------------------------------------------------


-- | Directional rule
data DirRule = DirRule
  { mainAnte :: Pattern
    -- ^ The main antecedent pattern
  , otherAntes :: [Pattern]
    -- ^ The other antecedent patterns
  , dirConseq :: Pattern
    -- ^ The rule's consequent
  } deriving (Show, Eq, Ord)


-- | Compile the rule to the list of directional rules.
directRule :: Rule -> [DirRule]
directRule rule = do
  (main, rest) <- pickOne $ antecedents rule
  case rest of
    [other] -> return $ DirRule
      { mainAnte = main
      , otherAntes = [withP other $ condition rule]
      , dirConseq = consequent rule
      }
    _ -> error "directRule: doesn't handle non-binary rules"


--------------------------------------------------
-- Indexing
--------------------------------------------------


-- | Lock determines the indexing structure.
--
-- Each `Item` (`Pattern`) can be matched with the `Lock` to produce the
-- corresponding `Key`(s).  These keys then allow to find the item (pattern) in
-- the index corresponding to the lock.
data Lock = Lock
  { lockTemplate :: Pattern
    -- ^ Lock's template
  , lockVars :: S.Set Pattern
    -- ^ Relevant variables and patterns, whose values need to be specified in
    -- the corresponding key
  } deriving (Show, Eq, Ord)


-- | Key assigns values to the variables (and patterns) in the corresponding
-- lock (in `lockVars`, more precisely).
type Key = M.Map Pattern Rigit


-- | Retrieve the bound variables and patterns for the lock.
getLockVars :: (P.MonadIO m) => Pattern -> MatchT m (S.Set Pattern)
getLockVars (P ip) = case ip of
--   Const _ -> pure S.empty
  Unit -> pure S.empty
  Sym _ -> pure S.empty
--   Pair p1 p2 -> (<>) <$> getLockVars p1 <*> getLockVars p2
  Vec v -> foldMap getLockVars v
--   Union up -> case up of
--     Left p -> getLockVars p
--     Right p -> getLockVars p
  Tag _ x -> getLockVars x
getLockVars (O op) = case op of
  Label v ->
    lookupVar v >>= \case
      Just it -> pure $ S.singleton (labelP v)
      Nothing -> pure S.empty
  Local v -> error "getLockVars: encountered local variable!"
  Any -> pure S.empty
  Map fn p -> do
    closeable p >>= \case
      True -> pure $ S.singleton (mapP fn p)
      False -> pure S.empty
  Map' f p -> do
    closeable p >>= \case
      True ->
        trace "getLockVars: doesn't handle Map' with a closeable pattern" $
          pure S.empty
      False -> pure S.empty
  App _ -> pure S.empty
  Or x y -> do
    -- NB: Since we assume that both @x@ and @y@ contain the same global
    -- variables (see `globalVarsIn`), @getLockVars x@ and @getLockVars y@
    -- should yield the same result.
    s1 <- getLockVars x
    s2 <- getLockVars y
    if s1 == s2
       then return s1
       else error "getLockVars Or: different results for different branches"
  -- Below, ignore `x` and `y`, which should contain local variables only
  Via p x -> (<>) <$> getLockVars p <*> getLockVars x
  With p c -> (<>) <$> getLockVars p <*> getLockVarsC c
  Let x e y -> getLockVars e
  Fix p -> getLockVars p
  Rec -> pure S.empty


-- | Retrieve the bound variables and patterns for the lock.
getLockVarsC :: (P.MonadIO m) => Cond Pattern -> MatchT m (S.Set Pattern)
getLockVarsC = \case
  Eq px py -> do
    cx <- closeable px
    cy <- closeable py
    case (cx, cy) of
      (True, False) -> pure $ S.singleton px
      (False, True) -> pure $ S.singleton py
      _ -> pure S.empty
--   Check pred p ->
--     closeable p >>= \case
--       -- NB: Below, we cast the predicate to a `With` pattern.  This is because
--       -- currently the lock only supports patterns, and not conditions.
--       True -> pure $ S.singleton (withP unitP (Check pred p))
--       False -> pure S.empty
  And c1 c2 -> (<>) <$> getLockVarsC c1 <*> getLockVarsC c2
  -- NB: `alt` is not necessary since `getLockVar` doesn't modify the state
  OrC c1 c2 -> getLockVarsC c1 <|> getLockVarsC c2
  -- Neg c -> getLockVarsC c
--   TrueC -> pure S.empty
  IsTrue p ->
    closeable p >>= \case
      True  -> pure $ S.singleton p
      False -> pure S.empty


-- | Retrieve the lock of the pattern.  The lock can be used to determine the
-- corresponding indexing structure.
mkLock :: (P.MonadIO m) => Pattern -> MatchT m Lock
mkLock p = Lock p <$> getLockVars p


-- | Generate all the locks for the given rule.
locksFor :: (P.MonadIO m) => DirRule -> P.ListT m Lock
locksFor rule  =
  P.Select $ _locksFor rule P.yield


-- | Generate all the locks for the given rule.
_locksFor
  :: (P.MonadIO m)
  => DirRule
  -> (Lock -> m ())  -- ^ Monadic lock handler
  -> m ()
_locksFor rule handler = do
  runMatchT $ do
    -- forEach (pickOne (antecedents rule)) $ \(main, rest) -> do
    dummyMatch $ mainAnte rule
    case otherAntes rule of
      [other] -> do
        lock <- mkLock other
        lift $ handler lock
      _ -> error "locksFor: doesn't handle non-binary rules"


-- | Group the set of locks by their templates.  Each group in the output list
-- will have the same `lockTemplate`.
groupByTemplate :: [Lock] -> [[Lock]]
groupByTemplate locks = M.elems . M.fromListWith (<>) $ do
  lock <- locks
  return (lockTemplate lock, [lock])


-- | Retrieve the key(s) of the item for the given set of locks with the same
-- template.
itemKeyFor
  :: (P.MonadIO m)
  => Rigit
  -> [Lock]
  -> P.ListT m (Lock, Key)
itemKeyFor item lockGroup = do
  P.Select $
    _itemKeyFor item lockGroup $
      \lock key -> P.yield (lock, key)


-- | Retrieve the key(s) of the item for the given lock.
_itemKeyFor
  :: (P.MonadIO m)
  => Rigit
  -> [Lock]
  -> (Lock -> Key -> m ()) -- ^ Monadic handler
  -> m ()
_itemKeyFor item lockGroup handler = do
  runMatchT $ do
--     P.liftIO $ do
--       putStrLn "??? Matching START"
    match Lazy groupTemplate item
--     P.liftIO $ do
--       putStrLn "??? Matching END"
    forEach lockGroup $ \lock -> do
      key <- keyFor $ lockVars lock
      lift $ handler lock key
  where
    groupTemplate =
      case S.toList groupTemplates of
        [template] -> template
        xs -> error $
          "itemKeyFor: expected one lock template, got " ++ show (length xs)
    groupTemplates = S.fromList $ do
      lock <- lockGroup
      return (lockTemplate lock)


-- | Retrieve the values of the global variables in the lock, thus creating the
-- key corresponding to the lock based on the current environment.
keyFor
  :: (P.MonadIO m)
  => S.Set Pattern
    -- ^ Lock variables
  -> MatchT m Key
keyFor vars = do
  let ps = S.toList vars
  fmap M.fromList . forM ps $ \p -> do
--     P.liftIO $ do
--       putStr ">>> Closing "
--       print p
    it <- close p
--     P.liftIO $ do
--       putStr ">>> Closed "
--       print p
--       putStr ">>> With "
--       print it
    return (p, it)


--------------------------------------------------
-- Utils
--------------------------------------------------


-- | Lift the list to `P.ListT`.
each :: (Monad m) => [a] -> P.ListT m a
each = P.Select . P.each


-- | Return subsets of the given size
subsets :: Int -> [a] -> [[a]]
subsets 0 _ = [[]]
subsets k xs = do
  (x, rest) <- pickOne xs
  subset <- subsets (k - 1) rest
  return $ x : subset


-- | All possible ways of picking one element from the (non-empty) list
pickOne :: [a] -> [(a, [a])]
pickOne [] = []
pickOne (x:xs) =
  here : there
  where
    here = (x, xs)
    there = do
      (y, ys) <- pickOne xs
      return (y, x:ys)


-- | @choice ps@ tries to apply the actions in the list @ps@ in order, until
-- one of them succeeds. Returns the value of the succeeding action.
choice :: Alternative f => [f a] -> f a
choice = foldr (<|>) empty
