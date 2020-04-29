{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE QuantifiedConstraints #-}


module ParComp.ItemDev.Untyped
  (

  -- * Core types
    Fun (..)
  , Pred
  , Var (..)

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

  -- ** IsPatt class
  , IsPatt (..)
  , encodeI
  , decodeI
  , encodeP
  , decodeP

  -- ** Smart constructors
  , unitP
  , symP
  , pairP
  , leftP
  , rightP

  , orP
  , viaP
  , appP
  , mapP
  , labelP
  , anyP
  , withP

  -- * Matching
  , MatchT
  , MatchingStrategy (..)
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


import           Control.Monad (guard, void, forM)
import qualified Control.Monad.RWS.Strict as RWS
import           Control.Applicative (Alternative, (<|>), empty)

import qualified Pipes as P

import           Data.Lens.Light

import           Data.Void (Void)
import           Data.String (IsString)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S


--------------------------------------------------
-- Item
--------------------------------------------------


-- | Chart item expression
data Item expr where
  Unit  :: Item expr
  Sym   :: T.Text -> Item expr
  Pair  :: expr -> expr -> Item expr
  Union :: Either expr expr -> Item expr
  deriving (Show, Eq, Ord)


-- | Rigid item expression
newtype Rigit = I (Item Rigit)
  deriving (Show, Eq, Ord)


-- | Extract the rigit item.
unI :: Rigit -> Item Rigit
unI (I x) = x


-- | Rigit constructors
unit      = I Unit
sym x     = I $ Sym x
pair x y  = I $ Pair x y
left x    = I . Union $ Left x
right y   = I . Union $ Right y


--------------------------------------------------
-- Functions and predicates
--------------------------------------------------


-- | Named function
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


-- | Named function
data Pred a = Pred
  { pname :: T.Text
    -- ^ The predicate's name
  , pred  :: a -> Bool
    -- ^ The predicate itself
  }

instance Show (Pred a) where
  show Pred{..} = T.unpack pname

instance Eq (Pred a) where
  x == y = pname x == pname y

instance Ord (Pred a) where
  x `compare` y = pname x `compare` pname y


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
newtype LVar = LVar {unLVar :: T.Text}
  deriving (Show, Eq, Ord)


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
  | Any
  -- ^ Any: match any item expression (wildcard pattern)
  | Map (Fun Rigit Rigit) t
  -- ^ Mapping: match the pattern with the item and apply the function to the
  -- result.
  | App (Fun Rigit Rigit)
  -- ^ Application: apply the function to the item before pattern matching.
  | With t (Cond t)
  -- ^ With: pattern match and (then) check the condition
  deriving (Show, Eq, Ord)


-- | Condition expression
--
-- Note that condition expression should contain no free variables, nor
-- wildcard patterns.  This is because side conditions are not matched against
-- items.
data Cond t
  = Eq t t
  -- ^ Check the equality between two patterns
  | Check (Pred Rigit) t
  -- ^ Check if the given predicate is satisfied
  | And (Cond t) (Cond t)
  -- ^ Logical conjunction
  | OrC (Cond t) (Cond t)
  -- ^ Logical disjunction
  | TrueC
  -- ^ Always True
  deriving (Show, Eq, Ord)


-- | Pattern expression
data Pattern
  = P (Item Pattern)
  -- ^ Item pattern
  | O (Op Pattern)
  -- ^ Operation pattern
  deriving (Show, Eq, Ord)


-- | Pattern constructors
unitP       = P Unit
symP x      = P $ Sym x
pairP x y   = P $ Pair x y
leftP x     = P . Union $ Left x
rightP y    = P . Union $ Right y

viaP x y    = O $ Via x y
orP x y     = O $ Or x y
appP f      = O $ App f
mapP f x    = O $ Map f x
labelP v    = O $ Label v
anyP        = O $ Any
withP p c   = O $ With p c


-- | Convert the pattern to the corresponding item expression, in case it does
-- not use any `Op`s (pattern specific operations/constructions).
strip :: Pattern -> Rigit
strip = \case
  P ip -> case ip of
    Unit  -> unit
    Sym x -> sym x
    Pair x y -> pair (strip x) (strip y)
    Union u -> case u of
      Left x  -> left  $ strip x
      Right y -> right $ strip y
  O op -> error $ "cannot strip pattern with Op: " ++ show (O op)


-- -- | The inverse of `strip`.
-- clothe :: Rigit -> Pattern
-- clothe = undefined


--------------------------------------------------
-- Item/pattern encoding
--------------------------------------------------


class IsPatt t where
  -- | Encode a value as an item
  encode :: (Item p -> p) -> t -> p
  -- | Decode a value from an item
  decode :: (Show p) => (p -> Item p) -> p -> t


-- | Encode a value as a `Rigit`. 
encodeI :: IsPatt t => t -> Rigit
encodeI = encode I


-- | Decode a value from a `Rigit`.
decodeI :: IsPatt t => Rigit -> t
decodeI = decode unI


-- | Encode a value as a `Pattern`. 
encodeP :: IsPatt t => t -> Pattern
encodeP = encode P


-- | Decode a value from a `Pattern`.
decodeP :: IsPatt t => Pattern -> t
decodeP = decode $ \case
  P x -> x
  O _ -> error "decodeP: cannot decode O"


instance IsPatt () where
  encode mkP _ = mkP Unit
  decode unP _ = ()

instance IsPatt Bool where
  encode mkP = \case
    False -> mkP . Union . Left  $ mkP Unit
    True  -> mkP . Union . Right $ mkP Unit
  decode unP x =
    case unP x of
      Union u -> case u of
        Left  _ -> False
        Right _ -> True
      _ -> error $ "cannot decode " ++ show x ++ " to Bool"

instance IsPatt Int where
  encode mkP = mkP . Sym . T.pack . show
  decode unP p = case unP p of
    Sym x -> read (T.unpack x)
    _ -> error $ "cannot decode " ++ show p ++ " to Int"

instance IsPatt T.Text where
  encode mkP = mkP . Sym
  decode unP p = case unP p of
    Sym x -> x
    _ -> error $ "cannot decode " ++ show p ++ " to Text"

instance (IsPatt a, IsPatt b) => IsPatt (a, b) where
  encode mkP (x, y) = mkP $ Pair (encode mkP x) (encode mkP y)
  decode unP p = case unP p of
    Pair x y -> (decode unP x, decode unP y)
    _ -> error $ "cannot decode " ++ show p ++ " to (,)"

instance (IsPatt a, IsPatt b, IsPatt c) => IsPatt (a, b, c) where
  encode mkP (x, y, z) =
    mkP $ Pair (encode mkP x) (mkP $ Pair (encode mkP y) (encode mkP z))
  decode unP p = case unP p of
    Pair x p' -> case unP p' of
      Pair y z -> (decode unP x, decode unP y, decode unP z)
    _ -> error $ "cannot decode " ++ show p ++ " to (,,)"

instance (IsPatt a) => IsPatt (Maybe a) where
  encode mkP = \case
    Nothing -> mkP . Union . Left  $ mkP Unit
    Just x  -> mkP . Union . Right $ encode mkP x
  decode unP p = case unP p of
    Union u -> case u of
      Left _  -> Nothing
      Right x -> Just (decode unP x)
    _ -> error $ "cannot decode " ++ show p ++ " to Maybe"

instance (IsPatt a, IsPatt b) => IsPatt (Either a b) where
  encode mkP = \case
    Left x  -> mkP . Union . Left  $ encode mkP x
    Right y -> mkP . Union . Right $ encode mkP y
  decode unP p = case unP p of
    Union u -> case u of
      Left x  -> Left  $ decode unP x
      Right y -> Right $ decode unP y
    _ -> error $ "cannot decode " ++ show p ++ " to Either"

instance (IsPatt a) => IsPatt [a] where
  encode mkP = \case
    []      -> mkP . Union . Left  $ mkP Unit
    x : xs  -> mkP . Union . Right $
      mkP $ Pair (encode mkP x) (encode mkP xs)
  decode unP p = case unP p of
    Union u -> case u of
      Left _ -> []
      Right p' ->
        let (x, xs) = decode unP p'
         in x : xs
    _ -> error $ "cannot decode " ++ show p ++ " to []"


--------------------------------------------------
-- Encoding patterns
--------------------------------------------------


-- class IsPattern t where
--   -- | Encode a value as a pattern
--   encode :: t -> Pattern
--   -- | Decode a value from a pattern
--   decode :: Pattern -> t
-- 
-- 
-- instance IsPattern () where
--   encode _ = unitP
--   decode _ = ()
-- 
-- instance IsPattern Bool where
--   encode = \case
--     False -> leftP unitP
--     True  -> rightP unitP
--   decode (P (Union u)) =
--     case u of
--       Left  _ -> False
--       Right _ -> True
--   decode p =
--     error $ "cannot decode " ++ show p ++ " to Bool"
-- 
-- instance IsPattern Int where
--   encode = symP . T.pack . show
--   decode (P (Sym x)) = read (T.unpack x)
--   decode p =
--     error $ "cannot decode " ++ show p ++ " to Int"
-- 
-- instance IsPattern T.Text where
--   encode = symP
--   decode (P (Sym x)) = x
--   decode p =
--     error $ "cannot decode " ++ show p ++ " to Text"
-- 
-- instance (IsPattern a, IsPattern b) => IsPattern (a, b) where
--   encode (x, y) = pairP (encode x) (encode y)
--   decode (P (Pair x y)) = (decode x, decode y)
--   decode p =
--     error $ "cannot decode " ++ show p ++ " to (,)"
-- 
-- instance (IsPattern a, IsPattern b, IsPattern c) => IsPattern (a, b, c) where
--   encode (x, y, z) = pairP (encode x) (pairP (encode y) (encode z))
--   decode (P (Pair x (P (Pair y z)))) = (decode x, decode y, decode z)
--   decode p =
--     error $ "cannot decode " ++ show p ++ " to (,,)"
-- 
-- instance (IsPattern a) => IsPattern (Maybe a) where
--   encode = \case
--     Nothing -> leftP unitP
--     Just x -> rightP $ encode x
--   decode (P (Union u)) =
--     case u of
--       Left _ -> Nothing
--       Right x -> Just (decode x)
--   decode p =
--     error $ "cannot decode " ++ show p ++ " to Maybe"
-- 
-- instance (IsPattern a, IsPattern b) => IsPattern (Either a b) where
--   encode = \case
--     Left x  -> leftP  $ encode x
--     Right y -> rightP $ encode y
--   decode (P (Union u)) =
--     case u of
--       Left x  -> Left  $ decode x
--       Right y -> Right $ decode y
--   decode p =
--     error $ "cannot decode " ++ show p ++ " to Either"
-- 
-- instance (IsPattern a) => IsPattern [a] where
--   encode = \case
--     x : xs  -> leftP $ pairP (encode x) (encode xs)
--     []      -> rightP unitP
--   decode (P (Union u)) =
--     case u of
--       Left p ->
--         let (x, xs) = decode p
--          in x : xs
--       Right _ -> []
--   decode p =
--     error $ "cannot decode " ++ show p ++ " to []"
-- 
-- -- -- | Generic pattern operation encoding
-- -- instance (IsPattern t) => IsPattern (Op t) where
-- --   encode = \case
-- --     Or x y -> O $ Or (encode x) (encode y)
-- --     Via x y -> O $ Via (encode x) (encode y)
-- --     Label v -> O $ Label v
-- --     Any -> O Any
-- --     Map fn x -> O $ Map fn (encode x)
-- --     App fn -> O $ App fn
-- --     With p c -> O $ With (encode p) (encodeC c)
-- --   decode (O op) =
-- --     case op of
-- --       Or x y -> Or (decode x) (decode y)
-- --       Any -> Any
-- --       _ -> error "Op decoding not implemented yet!"
-- --   decode p =
-- --     error $ "cannot decode " ++ show p ++ " to Op"
-- --
-- --
-- -- -- | Encode the pattern condition
-- -- encodeC :: IsPattern t => Cond t -> Cond Pattern
-- -- encodeC = \case
-- --   Eq x y    -> Eq (encode x) (encode y)
-- --   Check p x -> Check p (encode x)
-- --   And x y   -> And (encodeC x) (encodeC y)
-- --   OrC x y   -> OrC (encodeC x) (encodeC y)
-- --   TrueC     -> TrueC


--------------------------------------------------
-- Global vars
--------------------------------------------------


-- | Retrieve the set of global variables bound in the pattern.
--
-- A variable is bound in the pattern if it gets bound during matching of the
-- pattern with an item.
--
-- Assumption: In case of the `Or` pattern, we assume that both branches
-- contain the same set of global variables (this is currently checked at
-- runtime).
globalVarsIn :: Pattern -> S.Set Var
globalVarsIn (P ip) =
  case ip of
    Pair p1 p2 -> globalVarsIn p1 <> globalVarsIn p2
    Union up -> case up of
      Left p  -> globalVarsIn p
      Right p -> globalVarsIn p
    _ -> S.empty
globalVarsIn (O op) =
  case op of
    Or x y ->
      let xs = globalVarsIn x
          ys = globalVarsIn y
       in if xs == ys
             then xs
             else error "globalVarsIn: different sets of variables in Or"
    Via p x -> globalVarsIn p <> globalVarsIn x
    Label v -> S.singleton v
    Any -> S.empty
    Map _ p -> globalVarsIn p
    App _ -> S.empty
    With p _ -> globalVarsIn p

--     -- Below, ignore `x` and `y`, which should contain local variables only
--     Let x e y -> globalVarsIn e
--     Fix p -> globalVarsIn p
--     Rec -> Set.empty
--     -- Below, we don't inspect the condition, since it doesn't bind additional
--     -- variables during matching


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


-- | Perform the given patter matching in a local environment, restoring the
-- values of all the local variables at the end.
withLocalEnv
  :: (P.MonadIO m)
  => MatchT m a
  -> MatchT m a
withLocalEnv m = do
  e <- RWS.gets (getL lenv)
--   mark <- (`mod` 1000) <$> P.liftIO (R.randomIO :: IO Int)
--   P.liftIO $ do
--     putStr ">>> IN: "
--     print mark
  m <|> do
    -- Restore the local environment
    RWS.modify' (setL lenv e)
--     P.liftIO $ do
--       putStr "<<< OUT: "
--       print mark
    empty


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
    (Pair p1 p2, Pair i1 i2) ->
      pair <$> match ms p1 i1 <*> match ms p2 i2
    (Union pu, Union iu) ->
      case (pu, iu) of
        (Left pl, Left il) ->
          left <$> match ms pl il
        (Right pr, Right ir) ->
          right <$> match ms pr ir
        -- Fail otherwise
        _ -> empty
    _ -> error $ "match fail: " ++ show (ip, it)
match ms (O op) it =
  case (op, it) of
    (Label x, _) -> do
      bindVar x it
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
--     (App fname, it) -> do
    (App f, it) -> do
      -- f <- retrieveFun fname
      each $ fbody f it
    (Or p1 p2, it) -> do
      -- NOTE: we retrieve and then restore the entire state, even though the
      -- fixed recursive pattern should never escape its syntactic scope so, in
      -- theory, it should not change between the first and the second branch
      -- of the `Or` pattern.  The same applies to local variables.  Perhaps
      -- this is something we could check dynamically, just in case?
      match ms p1 it `alt` match ms p2 it
    (Via p x, it) -> do
      it' <- match ms p it
--       P.liftIO $ do
--         putStrLn "!!! Matching Via"
--         putStr "p: " >> print p
--         putStr "x: " >> print x
--         putStr "it: " >> print it
--         putStr "it': " >> print it'
      match ms x it'
    (With p c, it) -> do
      match ms p it
      check ms c
      return it

--     (Let x e y, it) -> do
--       it' <- match ms e it
--       withLocalEnv $ do
--         match ms x it'
--         close y
--     (Fix p, it) -> do
--       withFix p $ do
--         match ms p it
--     (Rec, it) -> do
--       p <- fixed
--       match ms p it


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
--   Pred pname p -> do
--     flag <- retrievePred pname <*> close p
--     guard flag
  And cx cy -> check Strict cx  >> check Strict cy
  OrC cx cy -> check Strict cx <|> check Strict cy
  TrueC -> pure ()
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
--   Pred pname p -> do
--     pred <- retrievePred pname
--     closeable p >>= \case
--       True  -> do
--         flag <- pred <$> close p
--         guard flag
--       False -> do
--         -- NB: We bind the pattern (see also `getLockVarsC`) with the unit
--         -- value to indicate that the value of the condition is True.
--         bindPatt (withP unitP (Pred pname p)) unit
  And cx cy -> check Lazy cx >> check Lazy cy
  -- NB: Below, `alt` is necessary since `check` can modify the state in case
  -- of lazy evaluation
  OrC cx cy -> check Lazy cx `alt` check Lazy cy
  -- NB: The line below (commented out) is probably incorrect. In case of
  -- Lazy matching, some embedded check may succeed simply because we cannot
  -- determine its status yet (see (*) above).  Hence, negating the embedded
  -- result doesn't make sense.
  -- Neg c -> not <$> check Lazy c
  TrueC -> pure ()


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
      Pair p1 p2 -> pair <$> close p1 <*> close p2
      Union up ->
        case up of
          Left lp  -> left <$> close lp
          Right rp -> right <$> close rp

    byCase (O op) = case op of
      -- Fail (silently) if variable x not bound
      Label v -> retrieveVar v
--         lookupVar v >>= \case
--           Just it -> pure it
--           Nothing -> error $ "close: Var not bound"
      Any -> empty
      -- Fail in case of a wildcard pattern
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
      App fname -> error "close App"
      Or p1 p2 ->
        -- NB: `alt` is not necessary, because `close` doesn't modify the state
        close p1 <|> close p2
      With p c -> do
        it <- close p
        check Strict c
        return it
      -- Not sure what to do with the three patterns below.  The intuitive
      -- implementations are given below, but they would not necessarily
      -- provide the desired behavior (especially in case of Fix/Ref).  In case
      -- of `Via`, the intuitive implementation would require performing the
      -- match with possibly global variables.  We could alternatively perform
      -- the @close x@ operation beforehand.  I guess we need some good
      -- examples showing what to do with those cases (if anything).
      Via _ _ -> error "close Via"
--       Fix _ -> error "close Fix"
--       Rec -> error "close Rec"


-- | Is the given pattern possible to close?
closeable :: (Monad m) => Pattern -> MatchT m Bool
closeable (P ip) = case ip of
  Pair p1 p2 -> (&&) <$> closeable p1 <*> closeable p2
  Union up ->
    case up of
      Left lp  -> closeable lp
      Right rp -> closeable rp
closeable (O op) = case op of
--   Const it -> pure True
  Label v ->
    lookupVar v >>= \case
      Just it -> pure True
      Nothing -> pure False
--   LVar v ->
--     lookupLVar v >>= \case
--       Just it -> pure True
--       Nothing -> pure False
  Any -> pure False
  Map _ p -> closeable p
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
--   Let x e y -> closeable e
  With p c -> (&&) <$> closeable p <*> closeableC c
  Via _ _ -> error "closeable Via"
--   Fix _ -> error "closeable Fix"
--   Rec -> error "closeable Rec"


-- | Is the given side condition possible to close?
closeableC :: (Monad m) => Cond Pattern -> MatchT m Bool
closeableC = \case
  Eq px py -> (&&) <$> closeable py <*> closeable py
--   Pred _ p -> closeable p
  And cx cy -> (&&) <$> closeableC cx <*> closeableC cy
  -- TODO: what about the case below?
  OrC cx cy -> undefined
  -- OrC cx cy -> (&&) <$> closeableC cx <*> closeableC cy
  -- Neg c -> closeableC c
  TrueC -> pure True


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
getLockVars :: (Monad m) => Pattern -> MatchT m (S.Set Pattern)
getLockVars (P ip) = case ip of
--   Const _ -> pure S.empty
  Unit -> pure S.empty
  Sym _ -> pure S.empty
  Pair p1 p2 -> (<>) <$> getLockVars p1 <*> getLockVars p2
  Union up -> case up of
    Left p -> getLockVars p
    Right p -> getLockVars p
getLockVars (O op) = case op of
  Label v ->
    lookupVar v >>= \case
      Just it -> pure $ S.singleton (labelP v)
      Nothing -> pure S.empty
--   LVar v -> error "getLockVars: encountered local variable!"
  Any -> pure S.empty
  Map fn p -> do
    closeable p >>= \case
      True -> pure $ S.singleton (mapP fn p)
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
--   Let x e y -> getLockVars e
  Via p x -> (<>) <$> getLockVars p <*> getLockVars x
--   Fix p -> getLockVars p
--   Rec -> pure S.empty
  With p c -> (<>) <$> getLockVars p <*> getLockVarsC c


-- | Retrieve the bound variables and patterns for the lock.
getLockVarsC :: (Monad m) => Cond Pattern -> MatchT m (S.Set Pattern)
getLockVarsC = \case
  Eq px py -> do
    cx <- closeable px
    cy <- closeable py
    case (cx, cy) of
      (True, False) -> pure $ S.singleton px
      (False, True) -> pure $ S.singleton py
      _ -> pure S.empty
--   Pred pn p ->
--     closeable p >>= \case
--       -- NB: Below, we cast the predicate to a `With` pattern.  This is because
--       -- currently the lock only supports patterns, and not conditions.
--       True -> pure $ S.singleton (withP unitP (Pred pn p))
--       False -> pure S.empty
  And c1 c2 -> (<>) <$> getLockVarsC c1 <*> getLockVarsC c2
  -- NB: `alt` is not necessary since `getLockVar` doesn't modify the state
  OrC c1 c2 -> getLockVarsC c1 <|> getLockVarsC c2
  -- Neg c -> getLockVarsC c
  TrueC -> pure S.empty


-- | Retrieve the lock of the pattern.  The lock can be used to determine the
-- corresponding indexing structure.
mkLock :: (Monad m) => Pattern -> MatchT m Lock
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
