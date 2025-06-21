{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}

module Grammar.EqualitySaturation (runEqualitySaturationOnTree) where


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

-- Transform Fixed point notation of Tree to only Tree, calculates Measure like in Grammar.Helpers#computeMeasure
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
          let (c', eg') = represent (Fix (LeafF (Literal l))) eg
           in snd $ merge c c' eg'

-- The cost function
costTreeF :: CostFunction TreeF Int
costTreeF = \case
  -- LeafF
  LeafF ter              -> 1
  -- NodeF
  --   Int
  NodeF AddInt ns        -> sum ns + 3
  NodeF SubInt ns        -> sum ns + 3
  NodeF DivInt ns        -> sum ns + 2
  --   Float
  NodeF AddFloat ns      -> sum ns + 3
  NodeF SubFloat ns      -> sum ns + 3
  NodeF DivFloat ns      -> sum ns + 2
  NodeF Sqrt ns          -> sum ns + 2
  --   If
  NodeF If ns            -> sum ns + 2
  -- Defaul Cost
  NodeF _ ns             -> sum ns + 1


-- Auxiliary functions for the rewrite function
class LeafPetternable a where
  toLeafPat :: a -> Pattern TreeF

instance LeafPetternable Bool where
  toLeafPat :: Bool -> Pattern TreeF
  toLeafPat b = pat $ LeafF $ Literal $ BoolLit b

instance LeafPetternable Int where
  toLeafPat :: Int -> Pattern TreeF
  toLeafPat i = pat $ LeafF $ Literal $ IntLit i

instance LeafPetternable Float where
  toLeafPat :: Float -> Pattern TreeF
  toLeafPat f = pat $ LeafF $ Literal $ FloatLit f

zeroI :: Int
zeroI = 0

zeroF :: Float
zeroF = 0

oneI :: Int
oneI = 1

oneF :: Float
oneF = 1

rewritesTreeF :: [Rewrite (Maybe Lit) TreeF]
rewritesTreeF =
  [ -- IF
      pat (NodeF If [toLeafPat True, "a", "b"])             := "a" -- If True then a else b  = a
    , pat (NodeF If [toLeafPat False, "a", "b"])            := "b" -- If False then a else b = b
    , pat (NodeF If ["a", toLeafPat True, toLeafPat False]) := "a" -- If a then True else False = a
    , pat (NodeF If ["a", toLeafPat False, toLeafPat True]) := pat (NodeF Not ["a"]) -- If a then False else True = !a
    , pat (NodeF If ["a", "b", toLeafPat False])            := pat (NodeF And ["a", "b"]) -- If a then b else False = a And b
    , pat (NodeF If ["a", "b", toLeafPat True])             := pat (NodeF Or [pat (NodeF Not ["a"]), "b"])  -- If a then b else True = !a Or b
    , pat (NodeF If ["a", toLeafPat False, "b"])            := pat (NodeF And [pat (NodeF Not ["a"]), "b"]) -- If a then False else b = !a And b
    , pat (NodeF If ["a", toLeafPat True, "b"])             := pat (NodeF Or ["a", "b"]) -- If a then True else True = a Or b
    , pat (NodeF If [pat (NodeF Not ["a"]), "b", "c"])      := pat (NodeF If ["a", "c", "b"]) -- If !a then b else c = IF a then c else b
    -- PAIR
    , pat (NodeF Fst [pat (NodeF ToPair ["a", "b"])]) := "a" -- Fst . ToPair $ a b = a
    , pat (NodeF Snd [pat (NodeF ToPair ["a", "b"])]) := "b" -- Snd . ToPair $ a b = b
    -- EQUALS EXPRESSIONS
    , pat (NodeF EqInt ["a", "a"])   := toLeafPat True -- a Eq a = True
    , pat (NodeF LtInt ["a", "a"])   := toLeafPat False -- a Lt a = False
    , pat (NodeF GtInt ["a", "a"])   := toLeafPat False -- a Gt a = False
    , pat (NodeF MinInt ["a", "a"])  := "a" -- Min a a = a
    , pat (NodeF MaxInt ["a", "a"])  := "a" -- Max a a = a
    , pat (NodeF And ["a", "a"])     := "a" -- a AND a = a
    , pat (NodeF Or ["a", "a"])      := "a" -- a OR a = a
    , pat (NodeF If ["a", "b", "b"]) := "b" -- If a then b else b = b
    -- BOOLEAN ALGEBRA
    , pat (NodeF Or ["a", "b"])                                             := pat (NodeF Or ["b", "a"]) -- a Or b = b Or a
    , pat (NodeF And ["a", "b"])                                            := pat (NodeF And ["b", "a"]) -- a And b = b And a
    , pat (NodeF Or [toLeafPat True, "a"])                                  := toLeafPat True -- True Or a  = True
    , pat (NodeF Or [toLeafPat False, "a"])                                 := "a" -- False Or a = a
    , pat (NodeF And [toLeafPat True, "a"])                                 := "a" -- True And a  = a
    , pat (NodeF And [toLeafPat False, "a"])                                := toLeafPat False -- False And a = False
    , pat (NodeF Not [pat (NodeF Not ["a"])])                               := "a" -- !!a = a
    , pat (NodeF Or [pat (NodeF And ["a", "c"]), pat (NodeF And ["b, c"])]) := pat (NodeF And [pat (NodeF Or ["a", "b"]), "c"]) -- (a And c) Or (b And c) = (a Or b) And c
    , pat (NodeF And [pat (NodeF Or ["a", "c"]), pat (NodeF Or ["b, c"])])  := pat (NodeF Or [pat (NodeF And ["a", "b"]), "c"]) -- (a Or c) And (b Or c) = (a And b) Or c
    --  ARITHMETICS
    --    ADDITION
    --      ADD BY 0
    , pat (NodeF AddInt [toLeafPat zeroI, "a"])     := "a" -- 0 + a = a
    , pat (NodeF AddFloat [toLeafPat zeroF, "a"]) := "a" -- 0.0 + a = a
    --      ASSOCIATIVE
    , pat (NodeF AddInt ["a", pat (NodeF AddInt ["b", "c"])])     := pat (NodeF AddInt [pat (NodeF AddInt ["a", "b"]), "c"]) -- a + (b + c) = (a + b) + c
    , pat (NodeF AddFloat ["a", pat (NodeF AddFloat ["b", "c"])]) := pat (NodeF AddFloat [pat (NodeF AddFloat ["a", "b"]), "c"]) -- a + (b + c) = (a + b) + c
    --      COMUTATIVE
    , pat (NodeF AddInt ["a", "b"])   := pat (NodeF AddInt ["b", "a"]) -- a + b = b + a
    , pat (NodeF AddFloat ["a", "b"]) := pat (NodeF AddFloat ["b", "a"]) -- a + b = b + a
    --    SUBTRACTION
    --      SUBTRACT BY 0
    , pat (NodeF SubInt ["a", toLeafPat zeroI])   := "a" -- a - 0 = a
    , pat (NodeF SubFloat ["a", toLeafPat zeroF]) := "a" -- a - 0.0 = a
    --      SUBTRACT BY ITSELF
    , pat (NodeF SubInt ["a", "a"])   := toLeafPat zeroI  -- a - a = 0
    , pat (NodeF SubFloat ["a", "a"]) := toLeafPat zeroF -- a - a = 0.0
    --    MULTIPLICATION
    --      MULTIPLY BY 1
    , pat (NodeF MultInt [toLeafPat oneI, "a"])   := "a" -- 1 * a = a
    , pat (NodeF MultFloat [toLeafPat oneF, "a"]) := "a" -- 1.0 * a = a
    --      MULTIPLY BY 0
    , pat (NodeF MultInt [toLeafPat zeroI, "a"])   := toLeafPat zeroI-- 0 * a = 0
    , pat (NodeF MultFloat [toLeafPat zeroF, "a"]) := toLeafPat zeroF -- 0.0 * a = 0.0
    --      ASSOCIATIVE
    , pat (NodeF MultInt ["a", pat (NodeF MultInt ["b", "c"])])     := pat (NodeF MultInt [pat (NodeF MultInt ["a", "b"]), "c"]) -- a * (b * c) = (a * b) * c
    , pat (NodeF MultFloat ["a", pat (NodeF MultFloat ["b", "c"])]) := pat (NodeF MultFloat [pat (NodeF MultFloat ["a", "b"]), "c"]) -- a * (b * c) = (a * b) * c
    --      COMUTATIVE
    , pat (NodeF MultInt ["a", "b"])   := pat (NodeF MultInt ["b", "a"]) -- a * b = b * a
    , pat (NodeF MultFloat ["a", "b"]) := pat (NodeF MultFloat ["b", "a"]) -- a * b = b * a
    --    DIVISION
    --      DIVISION BY 1
    , pat (NodeF DivInt ["a", toLeafPat oneI])   := "a" -- a / 1 = a
    , pat (NodeF DivFloat ["a", toLeafPat oneF]) := "a" -- a / 1.0 = a
    --      DIVISION BY ITSELF
    , pat (NodeF DivInt ["a", "a"])   := toLeafPat oneI :| nonZero "a" -- a / a = 1
    , pat (NodeF DivFloat ["a", "a"]) := toLeafPat oneF :| nonZero "a" -- a / a = 1.0
    --      CANCELATION
    , pat (NodeF DivInt [pat (NodeF MultInt ["a", "b"]), "a"])     := "b"  :| nonZero "a" -- a * b / a = b
    , pat (NodeF DivFloat [pat (NodeF MultFloat ["a", "b"]), "a"]) := "b"  :| nonZero "a" -- a * b / a = b
    --      REMAINDER MOD 1
    , pat (NodeF ModInt ["a", toLeafPat oneI]) := toLeafPat zeroI -- a % 1 = 0
    --      REMAINDER DIVISION OF A MULTIPLE
    , pat (NodeF ModInt [pat (NodeF MultInt ["a", "b"]), "a"]) := toLeafPat zeroI :| nonZero "a" -- (a * b) % a = 0
    --  LIST
    , pat (NodeF Len [pat (NodeF Reverse ["a"])])           := pat (NodeF Len ["a"]) -- Len . Reverser = Len
    , pat (NodeF Head [pat (NodeF Singleton ["a"])])        := "a" -- Head . Singleton = Id
    , pat (NodeF Reverse [pat (NodeF Singleton ["a"])])     := pat (NodeF Singleton ["a"]) -- Reverse . Singleton = Singleton
    , pat (NodeF Len [pat (NodeF Singleton ["a"])])         := toLeafPat oneI -- Len . Singleton = 1
    , pat (NodeF ProductInts [pat (NodeF Singleton ["a"])]) := "a" -- Product . Singleton = Id
    , pat (NodeF SumInts [pat (NodeF Singleton ["a"])])     := "a" -- Sum . Singleton = Id
    , pat (NodeF Reverse [pat (NodeF Reverse ["a"])])       := "a" -- Reverse . Reverse = Id
    , pat (NodeF Take [pat (NodeF Len ["a"]), "a"])         := "a" -- Take (Len a) a = a 
    , pat (NodeF Range ["a", "a", "a"])                     := pat (NodeF Singleton ["a"]) -- [a,a+a..a] = [a]
    -- INT COMPARISON
    , pat (NodeF EqInt ["a", "b"])  := pat (NodeF EqInt ["b", "a"]) -- a == b = b == a
    , pat (NodeF MinInt ["a", "b"]) := pat (NodeF MinInt ["b", "a"]) -- min a b = min b a
    , pat (NodeF MaxInt ["a", "b"]) := pat (NodeF MaxInt ["b", "a"]) -- max a b = max b a
    , pat (NodeF MinInt [pat (NodeF MinInt ["a", "b"]), "c"]) := pat (NodeF MinInt ["a", pat (NodeF MinInt ["b", "c"])]) -- min (min a b) c = min a (min b c)
    , pat (NodeF MaxInt [pat (NodeF MaxInt ["a", "b"]), "c"]) := pat (NodeF MaxInt ["a", pat (NodeF MaxInt ["b", "c"])]) -- min (min a b) c = min a (min b c)
    -- NOT GEQ == LT and NOT LEQ == GT
    , pat (NodeF Not [pat (NodeF EqInt ["a", pat (NodeF MinInt ["a", "b"])])]) := pat (NodeF GtInt ["a", "b"]) -- !(a == min a b) = a > b
    , pat (NodeF Not [pat (NodeF EqInt ["a", pat (NodeF MaxInt ["a", "b"])])]) := pat (NodeF LtInt ["a", "b"]) -- !(a == max a b) = a < b
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


runEqualitySaturationOnTree :: Tree -> Tree
runEqualitySaturationOnTree t = toTree $ fst (equalitySaturation (toTreeF t) rewritesTreeF costTreeF)
