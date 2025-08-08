{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}

module Grammar.EqualitySaturation (
    runEqualitySaturationOnTree
  , runEqualitySaturationOnTreeFull
  , TreeF
  , booleanRewrites
  , intRewrites
  , intComparisonRewrites
  , floatRewrites
  , listRewrites
  , listComparisonRewrites
  , pairRewrites
  , lambdaRewrites) where


import Data.Equality.Utils
import Data.Equality.Matching
import Data.Equality.Saturation
import Data.Equality.Analysis
import Data.Equality.Graph
import Data.Equality.Graph.Lens
import qualified Data.IntMap.Strict as IM


import Grammar.Core
import Grammar.Helpers
import Grammar.Eval
import Data.String (IsString(fromString))
import Data.Equality.Matching.Database (Subst)
import qualified Data.Maybe
import Data.Maybe (isJust)
import Pretty (Pretty(pretty))
import Data.Equality.Saturation.Scheduler (BackoffScheduler (BackoffScheduler))
import GHC.Base (divInt)
import qualified Data.Set    as S
import qualified Data.Foldable as F
import Data.Function ((&))


-- | Fixed point of the structure that represents a program written in this grammar
data TreeF a = LeafF !Terminal
             | NodeF !Operation ![a] deriving (Functor, Foldable, Traversable, Eq, Ord, Show)

_terminalF :: TreeF a -> Terminal
_terminalF (LeafF t) = t
_terminalF _         = error "Unexpected _termial call for NodeF"

_argsF :: TreeF a -> [a]
_argsF (NodeF _ args) = args
_argsF _              = error "Unexpected _args call for LeafF"

toTreeF :: Tree -> Fix TreeF
toTreeF (Leaf _ t)               = Fix $ LeafF t
toTreeF (Grammar.Core.Node _ op args) = Fix $ NodeF op (toTreeF <$> args)

-- | Transform Fixed point notation of Tree to only Tree, calculates Measure like in Grammar.Helpers#computeMeasure
toTree :: Fix TreeF -> Tree
toTree = toTree' 0
  where
    toTree' currentDepth (Fix (LeafF t))            = Leaf (Just (leafMeasure currentDepth)) t
    toTree' currentDepth (Fix (NodeF op args))      = Grammar.Core.Node (Just (nodeMeasure currentDepth measureArgs)) op measureArgs
      where
        measureArgs = toTree' (currentDepth + 1) <$> args
    leafMeasure cd       = MkMeasure { _currentDepth = cd, _height = 0, _nodeCount = 1}
    nodeMeasure cd margs = MkMeasure { _currentDepth = cd, _height = 1 + maximum (getHeight <$> margs), _nodeCount = 1 + sum (getNodeCount <$> margs)}

instance Analysis (Maybe Lit) TreeF where
  makeA :: TreeF (Maybe Lit) -> Maybe Lit
  makeA = \case
    LeafF (Literal l)       -> Just l
    LeafF (Arg _)           -> Nothing -- An argument of the function has no Literal Value at compile time similar to Symbol in SymExpr
    NodeF op args           -> sequenceA args >>= eval op

  joinA :: Maybe Lit -> Maybe Lit -> Maybe Lit
  joinA Nothing Nothing                           = Nothing
  joinA Nothing (Just l)                          = Just l
  joinA (Just l) Nothing                          = Just l
-- PROBLEM: hotgp-exe: ouch, that shouldn't have happened FloatLit (-4461.4644) != FloatLit (-4461.465)
-- Simplest solution trusting the simplification (drawback: potentialy hide errors in the rewrite rules)
  joinA (Just (FloatLit f1)) (Just (FloatLit f2)) = Just (FloatLit (max f1 f2))
  joinA (Just (IntLit i1)) (Just (IntLit i2))     = Just (IntLit (max i1 i2)) -- necessary for for fromIntegral
  joinA (Just l1) (Just l2)                       = if l1 == l2 then Just l1 else error ("ouch, that shouldn't have happened " ++ show l1 ++ " != " ++ show l2)

  modifyA :: ClassId -> EGraph (Maybe Lit) TreeF -> EGraph (Maybe Lit) TreeF
  modifyA c eg
    = case eg^._class c._data of
        Nothing -> eg
        Just l  ->
              -- Add constant as e-node
          let (c', eg')   = represent (Fix (LeafF (Literal l))) eg
              (rep, eg2)  = merge c c' eg'
                -- Prune all except leaf e-nodes
             in eg2 & _class rep._nodes %~ S.filter (F.null .unNode)

{- | The cost function to be applied in equality saturation.
Minimizes the depth of the tree
-}
cost :: CostFunction TreeF Int
cost = \case
  LeafF _    -> 1
  NodeF _ ns -> 2 * sum ns + 1


-- Auxiliary functions for the rewrite function
class LeafPetternable a where
  -- | Transforms the value in a LeafF of Pattern TreeF
  toLeafPat :: a -> Pattern TreeF

instance LeafPetternable Bool where
  -- | Transforms the Boo lvalue in a LeafF of Pattern TreeF
  toLeafPat :: Bool -> Pattern TreeF
  toLeafPat b = pat $ LeafF $ Literal $ BoolLit b

instance LeafPetternable Int where
  -- | Transforms the Int value in a LeafF of Pattern TreeF
  toLeafPat :: Int -> Pattern TreeF
  toLeafPat i = pat $ LeafF $ Literal $ IntLit i

instance LeafPetternable Float where
  -- | Transforms the Float value in a LeafF of Pattern TreeF
  toLeafPat :: Float -> Pattern TreeF
  toLeafPat f = pat $ LeafF $ Literal $ FloatLit f

-- | The Int zero
zeroI :: Int
zeroI = 0

-- | The Float zero
zeroF :: Float
zeroF = 0

-- | The Int one
oneI :: Int
oneI = 1

-- | The Float one
oneF :: Float
oneF = 1


-- | The rewrite rules to be applied in equality saturation for basic operations.
booleanRewrites :: [Rewrite (Maybe Lit) TreeF]
booleanRewrites = 
  [
    -- IF
      pat (NodeF If [toLeafPat True, "a", "b"])               := "a" -- If True then a else b  = a
    , pat (NodeF If [toLeafPat False, "a", "b"])              := "b" -- If False then a else b = b
    , pat (NodeF If ["a", toLeafPat True, toLeafPat False])   := "a" -- If a then True else False = a
    , pat (NodeF If ["a", toLeafPat False, toLeafPat True])   := pat (NodeF Not ["a"]) -- If a then False else True = !a
    , pat (NodeF If ["a", "b", toLeafPat False])              := pat (NodeF And ["a", "b"]) -- If a then b else False = a And b
    , pat (NodeF If ["a", "b", toLeafPat True])               := pat (NodeF Or [pat (NodeF Not ["a"]), "b"])  -- If a then b else True = !a Or b
    , pat (NodeF If ["a", toLeafPat False, "b"])              := pat (NodeF And [pat (NodeF Not ["a"]), "b"]) -- If a then False else b = !a And b
    , pat (NodeF If ["a", toLeafPat True, "b"])               := pat (NodeF Or ["a", "b"]) -- If a then True else b = a Or b
    , pat (NodeF If [pat (NodeF Not ["a"]), "b", "c"])        := pat (NodeF If ["a", "c", "b"]) -- If !a then b else c = IF a then c else b
    , pat (NodeF If [pat (NodeF GtInt ["a", "b"]), "b", "a"]) := pat (NodeF MinInt ["a", "b"]) -- If (a > b) then b else a = min a b
    , pat (NodeF If [pat (NodeF GtInt ["a", "b"]), "a", "b"]) := pat (NodeF MaxInt ["a", "b"]) -- If (a > b) then a else b = max a b
    , pat (NodeF If [pat (NodeF LtInt ["a", "b"]), "a", "b"]) := pat (NodeF MinInt ["a", "b"]) -- If (a < b) then a else b = min a b
    , pat (NodeF If [pat (NodeF LtInt ["a", "b"]), "b", "a"]) := pat (NodeF MaxInt ["a", "b"]) -- If (a < b) then b else a = max a b
    , pat (NodeF If ["a", "b", "b"]) := "b" -- If a then b else b = b
    -- BOOLEAN ALGEBRA
    , pat (NodeF Or ["a", "b"])                                             := pat (NodeF Or ["b", "a"]) -- a Or b = b Or a
    , pat (NodeF And ["a", "b"])                                            := pat (NodeF And ["b", "a"]) -- a And b = b And a
    , pat (NodeF Or [pat (NodeF Or ["a", "b"]), "c"])                       := pat (NodeF Or ["a", pat (NodeF Or ["b", "c"])]) -- (a Or b) Or c = a Or (b Or c)
    , pat (NodeF And [pat (NodeF And ["a", "b"]), "c"])                     := pat (NodeF And ["a", pat (NodeF And ["b", "c"])]) -- (a And b) And c = a And (b And c)
    , pat (NodeF Or [toLeafPat True, "a"])                                  := toLeafPat True -- True Or a  = True
    , pat (NodeF Or [toLeafPat False, "a"])                                 := "a" -- False Or a = a
    , pat (NodeF And [toLeafPat True, "a"])                                 := "a" -- True And a  = a
    , pat (NodeF And [toLeafPat False, "a"])                                := toLeafPat False -- False And a = False
    , pat (NodeF Not [pat (NodeF Not ["a"])])                               := "a" -- !!a = a
    , pat (NodeF Or [pat (NodeF And ["a", "c"]), pat (NodeF And ["b, c"])]) := pat (NodeF And [pat (NodeF Or ["a", "b"]), "c"]) -- (a And c) Or (b And c) = (a Or b) And c
    , pat (NodeF And [pat (NodeF Or ["a", "c"]), pat (NodeF Or ["b, c"])])  := pat (NodeF Or [pat (NodeF And ["a", "b"]), "c"]) -- (a Or c) And (b Or c) = (a And b) Or c
    , pat (NodeF And ["a", "a"])     := "a" -- a AND a = a
    , pat (NodeF Or ["a", "a"])      := "a" -- a OR a = a
  ]

-- | The rewrite rules to be applied in equality saturation for int operations.
intRewrites :: [Rewrite (Maybe Lit) TreeF]
intRewrites =
  [
      pat (NodeF MinInt ["a", "a"])  := "a" -- Min a a = a
    , pat (NodeF MaxInt ["a", "a"])  := "a" -- Max a a = a
    , pat (NodeF AddInt [toLeafPat zeroI, "a"])   := "a" -- 0 + a = a
    , pat (NodeF SubInt ["a", toLeafPat zeroI])   := "a" -- a - 0 = a
    , pat (NodeF SubInt ["a", "a"])   := toLeafPat zeroI  -- a - a = 0
    , pat (NodeF MultInt [toLeafPat oneI, "a"])   := "a" -- 1 * a = a
    , pat (NodeF MultInt [toLeafPat zeroI, "a"])   := toLeafPat zeroI -- 0 * a = 0
    , pat (NodeF DivInt ["a", toLeafPat oneI])   := "a" -- a / 1 = a
    , pat (NodeF DivInt ["a", "a"])   := toLeafPat oneI :| nonZero "a" -- a / a = 1
    , pat (NodeF ModInt ["a", toLeafPat oneI]) := toLeafPat zeroI -- a % 1 = 0
    , pat (NodeF ModInt [pat (NodeF MultInt ["a", "b"]), "a"]) := toLeafPat zeroI :| nonZero "a" -- (a * b) % a = 0
    , pat (NodeF MinInt ["a", pat (NodeF MultInt ["a", "a"])]) := "a" -- min (a a*a) = a
    , pat (NodeF MaxInt ["a", pat (NodeF MultInt ["a", "a"])]) := pat (NodeF MultInt ["a", "a"]) -- max (a a*a) = a*a
    , pat (NodeF Not [pat (NodeF EqInt ["a", pat (NodeF MinInt ["a", "b"])])]) := pat (NodeF GtInt ["a", "b"]) -- !(a == min a b) = a > b
    , pat (NodeF Not [pat (NodeF EqInt ["a", pat (NodeF MaxInt ["a", "b"])])]) := pat (NodeF LtInt ["a", "b"]) -- !(a == max a b) = a < b
  ]

-- | The rewrite rules to be applied in equality saturation for int comparison operations.
intComparisonRewrites :: [Rewrite (Maybe Lit) TreeF]
intComparisonRewrites =
  [
      pat (NodeF EqInt ["a", "a"])   := toLeafPat True -- a Eq a = True
    , pat (NodeF LtInt ["a", "a"])   := toLeafPat False -- a Lt a = False
    , pat (NodeF GtInt ["a", "a"])   := toLeafPat False -- a Gt a = False
    , pat (NodeF Not [pat (NodeF EqInt ["a", pat (NodeF MinInt ["a", "b"])])]) := pat (NodeF GtInt ["a", "b"]) -- !(a == min a b) = a > b
    , pat (NodeF Not [pat (NodeF EqInt ["a", pat (NodeF MaxInt ["a", "b"])])]) := pat (NodeF LtInt ["a", "b"]) -- !(a == max a b) = a < b
    , pat (NodeF GtInt [pat (NodeF MaxInt ["a", "b"]), "a"]) := pat (NodeF GtInt ["b", "a"]) -- max a b > a = b > a
    , pat (NodeF GtInt [pat (NodeF MinInt ["a", "b"]), "a"]) := pat (NodeF LtInt ["b", "a"]) -- max a b > a = b < a
    , pat (NodeF GtInt [pat (NodeF SubInt ["a", "b"]), toLeafPat zeroI]) := pat (NodeF GtInt ["a", "b"]) -- a - b > 0 = a > b
    , pat (NodeF LtInt [pat (NodeF SubInt ["a", "b"]), toLeafPat zeroI]) := pat (NodeF LtInt ["a", "b"]) -- a - b < 0 = a < b
  ]

-- | The rewrite rules to be applied in equality saturation for float operations.
floatRewrites :: [Rewrite (Maybe Lit) TreeF]
floatRewrites =
  [
      pat (NodeF AddFloat [toLeafPat zeroF, "a"]) := "a" -- 0.0 + a = a
    , pat (NodeF SubFloat ["a", toLeafPat zeroF]) := "a" -- a - 0.0 = a
    , pat (NodeF SubFloat ["a", "a"]) := toLeafPat zeroF -- a - a = 0.0
    , pat (NodeF MultFloat [toLeafPat oneF, "a"]) := "a" -- 1.0 * a = a
    , pat (NodeF MultFloat [toLeafPat zeroF, "a"]) := toLeafPat zeroF -- 0.0 * a = 0.0
    , pat (NodeF DivFloat ["a", toLeafPat oneF]) := "a" -- a / 1.0 = a
    , pat (NodeF DivFloat ["a", "a"]) := toLeafPat oneF :| nonZero "a" -- a / a = 1.0
  ]

-- | The rewrite rules to be applied in equality saturation for list operations.
listRewrites :: [Rewrite (Maybe Lit) TreeF]
listRewrites = 
  [
      pat (NodeF Len [pat (NodeF Reverse ["a"])])                    := pat (NodeF Len ["a"]) -- Len . Reverser = Len
    , pat (NodeF Head [pat (NodeF Singleton ["a"])])                 := "a" -- Head . Singleton = Id
    , pat (NodeF Reverse [pat (NodeF Singleton ["a"])])              := pat (NodeF Singleton ["a"]) -- Reverse . Singleton = Singleton
    , pat (NodeF Len [pat (NodeF Singleton ["a"])])                  := toLeafPat oneI -- Len . Singleton = 1
    , pat (NodeF ProductInts [pat (NodeF Singleton ["a"])])          := "a" -- Product . Singleton = Id
    , pat (NodeF SumInts [pat (NodeF Singleton ["a"])])              := "a" -- Sum . Singleton = Id
    , pat (NodeF Reverse [pat (NodeF Reverse ["a"])])                := "a" -- Reverse . Reverse = Id
    , pat (NodeF Take [pat (NodeF Len ["a"]), "a"])                  := "a" -- Take (Len a) a = a
    , pat (NodeF Take [toLeafPat oneI, pat (NodeF Singleton ["a"])]) := pat (NodeF Singleton ["a"]) -- Take 1 (Singleton a) = Singleton a
    , pat (NodeF Range ["a", "a", "a"])                              := pat (NodeF Singleton ["a"]) -- [a,a+a..a] = [a]
  ]

listComparisonRewrites :: [Rewrite (Maybe Lit) TreeF]
listComparisonRewrites = 
  [
      pat (NodeF MinInt [pat (NodeF Len ["a"]), toLeafPat zeroI]) := toLeafPat zeroI -- min (Len a) 0 = 0
  ]

-- | The rewrite rules to be applied in equality saturation for pair operations.
pairRewrites :: [Rewrite (Maybe Lit) TreeF]
pairRewrites =
  [
      pat (NodeF Fst [pat (NodeF ToPair ["a", "b"])]) := "a" -- Fst . ToPair $ a b = a
    , pat (NodeF Snd [pat (NodeF ToPair ["a", "b"])]) := "b" -- Snd . ToPair $ a b = b
  ]

-- | The rewrite rules to be applied in equality saturation for lambda expressions.
lambdaRewrites :: [Rewrite (Maybe Lit) TreeF]
lambdaRewrites =
  [

  ]


unsafeGetSubst :: Pattern TreeF -> Subst -> ClassId
unsafeGetSubst (NonVariablePattern _) _ = error "unsafeGetSubst: NonVariablePattern; expecting VariablePattern"
unsafeGetSubst (VariablePattern v) subst = case IM.lookup v subst of
      Nothing       -> error "Searching for non existent bound var in conditional"
      Just class_id -> class_id

nonZero :: Pattern TreeF -> RewriteCondition (Maybe Lit) TreeF
nonZero v subst egr =
      dataValue /= Just (IntLit zeroI)
  &&  dataValue /= Just (FloatLit zeroF)
  &&  isJust dataValue -- Argument or evaluation can potentialy result in zero
        where dataValue = egr^._class (unsafeGetSubst v subst)._data


runEqualitySaturationOnTree :: Int -> [Rewrite (Maybe Lit) TreeF] -> Tree -> Tree
runEqualitySaturationOnTree maxH rewrites t = if getHeight saturated <= maxH then saturated else t 
  where
    saturated = toTree $ fst (equalitySaturation' (BackoffScheduler 100 10) (toTreeF t) rewrites cost)

runEqualitySaturationOnTreeFull :: [Rewrite (Maybe Lit) TreeF] -> Tree -> Tree
runEqualitySaturationOnTreeFull = runEqualitySaturationOnTreeFull' 3

runEqualitySaturationOnTreeFull' :: Int -> [Rewrite (Maybe Lit) TreeF] -> Tree -> Tree
runEqualitySaturationOnTreeFull' i rwRules t | i == 0  = t
                                             | t == t' = t
                                             | otherwise = runEqualitySaturationOnTreeFull' (i - 1) rwRules t'
  where
    t' = toTree $ fst (equalitySaturation (toTreeF t) rwRules cost) 