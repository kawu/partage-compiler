{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE RecordWildCards #-}


-- | Core pattern-matching DSL module


module ParComp.Patt.Core
  ( Term (..)
  , Item (..)

  -- * Functions
  , FunName (..)
  , Fun (..)
  , PattFun (..)
  , varsIn
  , varsInFun
  , replaceVars
  , replaceFunVars

  , Var (..)
  , Op (..)
  , Cond (..)
  , Patt (..)
  ) where


import qualified Data.Set as S
import qualified Data.Foldable as F
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import qualified Data.Primitive.Array as A
import           Data.String (IsString)


--------------------------------------------------
-- Item
--------------------------------------------------


-- | Term expression
data Term expr where
  Unit  :: Term expr
  Sym   :: {-# UNPACK #-} !T.Text -> Term expr
  -- | Non-empty vector of expressions (to represent product types)
  -- (TODO: or maybe we could/should use it to represent unit, too?)
  Vec   :: !(A.Array expr) -> Term expr
  -- | Tagged expression (to represent sum types)
  Tag   :: {-# UNPACK #-} !Int -> expr -> Term expr
--   Num   :: {-# UNPACK #-} !Int -> Term expr
--   -- ^ Integral number
  deriving (Show, Eq, Ord)


-- | Chart item expression
newtype Item = I {unI :: Term Item}
  deriving (Eq, Ord)
  deriving newtype (Show)


--------------------------------------------------
-- Host/foreign functions
--------------------------------------------------


-- | Function name
newtype FunName = FunName {unFunName :: T.Text}
  deriving (Eq, Ord, IsString)

instance Show FunName where
  show = T.unpack . unFunName

-- | Named host/foreign function
data Fun = Fun
  { fname :: FunName
    -- ^ The function's name
  , fbody :: Item -> [Item]
    -- ^ The function itself (non-deterministic)
  }

instance Show Fun where
  show Fun{..} = show fname

instance Eq Fun where
  x == y = fname x == fname y

instance Ord Fun where
  x `compare` y = fname x `compare` fname y


---------------------------------------------------
-- Native functions
---------------------------------------------------


-- | Native, pattern-level function
data PattFun = PattFun
  { pfParams :: [Patt]
    -- ^ Formal parameters of a function
  , pfBody :: Patt
    -- ^ The body of a function is represented by a pattern which gets evaluated
    -- once the formal parameters are matched with the function's arguments
  } deriving (Show, Eq, Ord)


-- | Determine (non-recursively) the set of variables used in a function.
--
-- NOTE: This function is not recursive in the sense that, if there are function
-- applications embedded in its body, their variables will not be considered.
-- The same applies to `varsIn`, `replaceVars` and `replaceFunVars`.
varsInFun :: PattFun -> S.Set Var
varsInFun PattFun{..} =
  S.unions (map varsIn pfParams) `S.union`
  varsIn pfBody


-- | Determine the set of variables used in a pattern.
varsIn :: Patt -> S.Set Var
varsIn (P p) =
  case p of
    Unit -> S.empty
    Sym _ -> S.empty
    Vec v -> S.unions (map varsIn $ F.toList v)
    Tag _ p' -> varsIn p'
varsIn (O p) =
  case p of
    Var v -> S.singleton v
    Any -> S.empty
    Select _ p' -> varsIn p'
    Focus _ p' -> varsIn p'
    Seq p1 p2 -> varsIn p1 `S.union` varsIn p2
    Choice p1 p2 -> varsIn p1 `S.union` varsIn p2
    Apply _ p' -> varsIn p'
    -- NOTE: the embedded function is ignored due to non-recursivity
    ApplyP _f xs -> S.unions (map varsIn xs)
    Assign p q -> varsIn p `S.union` varsIn q
    Guard c -> varsInCond c


-- | Determine the set of variables used in a pattern.
varsInCond :: Cond Patt -> S.Set Var
varsInCond (Eq p q) = varsIn p `S.union` varsIn q
varsInCond (And x y) = varsInCond x `S.union` varsInCond y
varsInCond (Or x y) = varsInCond x `S.union` varsInCond y


-- | Substitute variables in a pattern.
replaceVars :: M.Map Var Var -> Patt -> Patt
replaceVars varMap (P p) =
  P $ case p of
    Unit -> Unit
    Sym x -> Sym x
    Vec v -> Vec . A.fromList $ map (replaceVars varMap) (F.toList v)
    Tag k p' -> Tag k $ replaceVars varMap p'
replaceVars varMap (O p) =
  O $ case p of
    Var v -> Var $ varMap M.! v
    Any -> Any
    Select k p' -> Select k (replaceVars varMap p')
    Focus k p' -> Focus k (replaceVars varMap p')
    Seq p1 p2 -> Seq (replaceVars varMap p1) (replaceVars varMap p2)
    Choice p1 p2 -> Choice (replaceVars varMap p1) (replaceVars varMap p2)
    Apply f p' -> Apply f (replaceVars varMap p')
    -- NOTE: the embedded function is ignored due to non-recursivity
    ApplyP f xs -> ApplyP f (map (replaceVars varMap) xs)
    Assign p q -> Assign (replaceVars varMap p) (replaceVars varMap q)
    Guard c -> Guard $ replaceCondVars varMap c


-- | Substitute variables in a condition.
replaceCondVars :: M.Map Var Var -> Cond Patt -> Cond Patt
replaceCondVars varMap c =
  case c of
    Eq p q -> Eq (replaceVars varMap p) (replaceVars varMap q)
    And x y -> And (replaceCondVars varMap x) (replaceCondVars varMap y)
    Or x y -> Or (replaceCondVars varMap x) (replaceCondVars varMap y)


-- | Substitute variables in a function.
replaceFunVars :: M.Map Var Var -> PattFun -> PattFun
replaceFunVars varMap PattFun{..} = PattFun
  { pfParams = map (replaceVars varMap) pfParams
  , pfBody = replaceVars varMap pfBody
  }


--------------------------------------------------
-- Pattern
--------------------------------------------------


-- | Variable
newtype Var = V {unV :: T.Text}
   deriving (Show, Eq, Ord, IsString)


-- | Pattern operation
data Op e where

  -- | Bind the current expression to a given variable
  Var     :: Var -> Op e
  -- | Match any item expression (wildcard pattern)
  Any     :: Op e

  -- | Select a given branch of a tagged expression
  Select  :: Int -> e -> Op e
  -- | Focus on a given branch of a product expression
  Focus   :: Int -> e -> Op e

  -- | Sequence: `Seq x y` first matches `x`, then `y`, with the item.  The
  -- result of the match with `y` is taken to be the result of the entire
  -- expression.
  Seq     :: e -> e -> Op e
  -- | Choice: `Choice x y` matches items which match either of the two
  -- patterns.  `Choice` provides non-determinism in pattern matching.
  Choice  :: e -> e -> Op e

  -- | Apply (foreign?) function to a pattern
  Apply   :: Fun -> e -> Op e
  -- | Apply (native?) function to a list of arguments
  ApplyP   :: PattFun -> [e] -> Op e
  -- | Pattern assignment
  Assign  :: e -> e -> Op e

  -- NOTE: Pattern assignment can be seen as a uni-directional analog of
  -- equality constraint, in which the right-hand side is a constructing pattern
  -- and the left-hand side is a matching pattern.

  -- | Pattern guard
  Guard   :: Cond e -> Op e

  deriving (Show, Eq, Ord)


-- | Condition expression
--
-- Note that condition expression should contain no free variables, nor wildcard
-- patterns.  This is because side conditions are not matched against items.
data Cond e where
  -- | Equality check between two constructing pattern expressions
  Eq    :: e -> e -> Cond e
  -- | Logical conjunction
  And   :: Cond e -> Cond e -> Cond e
  -- | Logical disjunction
  Or    :: Cond e -> Cond e -> Cond e
  deriving (Show, Eq, Ord)


-- | Pattern expression
data Patt
  = P (Term Patt)
  -- ^ Term pattern
  | O (Op Patt)
  -- ^ Operation pattern
  deriving (Show, Eq, Ord)
