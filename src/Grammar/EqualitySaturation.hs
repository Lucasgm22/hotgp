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
  NodeF AddInt ns        -> sum ns + 4
  NodeF SubInt ns        -> sum ns + 4
  NodeF MultInt ns       -> sum ns + 2
  NodeF DivInt ns        -> sum ns + 3
  --   Float
  NodeF AddFloat ns      -> sum ns + 4
  NodeF SubFloat ns      -> sum ns + 4
  NodeF DivFloat ns      -> sum ns + 3
  NodeF Sqrt ns          -> sum ns + 3
  --   Lists
  NodeF SumFloats ns     -> sum ns + 3
  NodeF SumInts ns       -> sum ns + 3
  -- Defaul Cost
  NodeF _ ns             -> sum ns + 2


-- Auxiliary functions for the rewrite function
boolLeafFPattern :: Bool -> TreeF (Pattern TreeF)
boolLeafFPattern b = LeafF (Literal (BoolLit b))

intLeafFPattner :: Int -> TreeF (Pattern TreeF)
intLeafFPattner i = LeafF (Literal (IntLit i))

floatLeafFPattner :: Float -> TreeF (Pattern TreeF)
floatLeafFPattner f = LeafF (Literal (FloatLit f))

rewritesTreeF :: [Rewrite (Maybe Lit) TreeF]
rewritesTreeF =
  [ -- IF
      pat (NodeF If [pat (boolLeafFPattern True), "a", "b"])  := "a"  -- If True then a else b  = a
    , pat (NodeF If [pat (boolLeafFPattern False), "a", "b"]) := "b"  -- If False then a else b = b
    , pat (NodeF If ["a", pat (boolLeafFPattern True), pat (boolLeafFPattern True)])   := pat (boolLeafFPattern True)  -- If a then True else True = True
    , pat (NodeF If ["a", pat (boolLeafFPattern False), pat (boolLeafFPattern False)]) := pat (boolLeafFPattern False) -- If a then False else False = False
    , pat (NodeF If ["a", pat (boolLeafFPattern True), pat (boolLeafFPattern False)])  := "a"                   -- If a then True else False = a
    , pat (NodeF If ["a", pat (boolLeafFPattern False), pat (boolLeafFPattern True)])  := pat (NodeF Not ["a"]) -- If a then False else True = !a
    , pat (NodeF If ["a", "b", pat (boolLeafFPattern False)])  := pat (NodeF And ["a", "b"])                    -- If a then b else False = a And b
    , pat (NodeF If ["a", "b", pat (boolLeafFPattern True)])   := pat (NodeF Or [pat (NodeF Not ["a"]), "b"])   -- If a then b else True = !a Or b
    , pat (NodeF If ["a", pat (boolLeafFPattern False), "b"])  := pat (NodeF And [pat (NodeF Not ["a"]), "b"])  -- If a then False else b = !a And b
    , pat (NodeF If ["a", pat (boolLeafFPattern True), "b"])   := pat (NodeF Or ["a", "b"])                     -- If a then True else True = a Or b
    , pat (NodeF If [pat (NodeF Not ["a"]), "b", "c"])        := pat (NodeF If ["a", "c", "b"])                 -- If !a then b else c = IF a then c else b
    -- PAIR
    , pat (NodeF Fst [pat (NodeF ToPair ["a", "b"])]) := "a" -- Fst
    , pat (NodeF Snd [pat (NodeF ToPair ["a", "b"])]) := "b" -- Snd
    -- EQUALS EXPRESSIONS
    , pat (NodeF EqInt ["a", "a"])   := pat (boolLeafFPattern True)  -- a Eq a             = True
    , pat (NodeF LtInt ["a", "a"])   := pat (boolLeafFPattern False) -- a Lt a             = False
    , pat (NodeF GtInt ["a", "a"])   := pat (boolLeafFPattern False) -- a Gt a             = False
    , pat (NodeF MinInt ["a", "a"])  := "a"                          -- Min a a            = a
    , pat (NodeF MaxInt ["a", "a"])  := "a"                          -- Max a a            = a
    , pat (NodeF And ["a", "a"])     := "a"                          -- a AND a            = a
    , pat (NodeF Or ["a", "a"])      := "a"                          -- a OR a             = a
    , pat (NodeF If ["a", "b", "b"]) := "b"                          -- IF a then b else b = b
    -- BOOLEAN ALGEBRA
    , pat (NodeF Or ["a", "b"])                               := pat (NodeF Or ["b", "a"])      -- a Or b = b Or a
    , pat (NodeF And ["a", "b"])                              := pat (NodeF And ["b", "a"])     -- a And b = b And a
    , pat (NodeF Or [pat (boolLeafFPattern True), "a"])       := pat (boolLeafFPattern True)    -- True Or a  = True
    , pat (NodeF Or ["a", pat (boolLeafFPattern True)])       := pat (boolLeafFPattern True)    -- a Or True  = True
    , pat (NodeF Or [pat (boolLeafFPattern False), "a"])      := "a"                            -- False Or a = a
    , pat (NodeF Or ["a", pat (boolLeafFPattern False)])      := "a"                            -- a Or False = a
    , pat (NodeF And [pat (boolLeafFPattern True), "a"])      := "a"                            -- True And a  = a
    , pat (NodeF And ["a", pat (boolLeafFPattern True)])      := "a"                            -- a And True  = a
    , pat (NodeF And [pat (boolLeafFPattern False), "a"])     := pat (boolLeafFPattern False)   -- False And a = False
    , pat (NodeF And ["a", pat (boolLeafFPattern False)])     := pat (boolLeafFPattern False)   -- a And False = False
    , pat (NodeF Not [pat (NodeF Not ["a"])])                 := "a"                            -- !!a = a
    , pat (NodeF Or [pat (NodeF And ["a", "c"]), pat (NodeF And ["b, c"])]) := pat (NodeF And [pat (NodeF Or ["a", "b"]), "c"])  -- (a And c) Or (b And c) = (a Or b) And c
    , pat (NodeF And [pat (NodeF Or ["a", "c"]), pat (NodeF Or ["b, c"])])  := pat (NodeF Or [pat (NodeF And ["a", "b"]), "c"])  -- (a Or c) And (b Or c) = (a And b) Or c
    --  ARITHMETICS
    --    ADDITION
    --      ADD BY 0
    , pat (NodeF AddInt [pat (intLeafFPattner 0), "a"])     := "a" -- 0 + a = a
    , pat (NodeF AddInt ["a", pat (intLeafFPattner 0)])     := "a" -- a + 0 = a
    , pat (NodeF AddFloat [pat (floatLeafFPattner 0), "a"]) := "a" -- 0.0 + a = a
    , pat (NodeF AddFloat ["a", pat (floatLeafFPattner 0)]) := "a" -- a + 0.0 = a
    --      ASSOCIATIVE
    , pat (NodeF AddInt ["a", pat (NodeF AddInt ["b", "c"])])     := pat (NodeF AddInt [pat (NodeF AddInt ["a", "b"]), "c"])     -- a + (b + c) = (a + b) + c
    , pat (NodeF AddFloat ["a", pat (NodeF AddFloat ["b", "c"])]) := pat (NodeF AddFloat [pat (NodeF AddFloat ["a", "b"]), "c"]) -- a + (b + c) = (a + b) + c
    --      COMUTATIVE
    , pat (NodeF AddInt ["a", "b"])   := pat (NodeF AddInt ["b", "a"])   -- a + b = b + a
    , pat (NodeF AddFloat ["a", "b"]) := pat (NodeF AddFloat ["b", "a"]) -- a + b = b + a
    --    SUBTRACTION
    --      SUBTRACT BY 0
    , pat (NodeF SubInt ["a", pat (intLeafFPattner 0)])     := "a" -- a - 0 = a
    , pat (NodeF SubFloat ["a", pat (floatLeafFPattner 0)]) := "a" -- a - 0.0 = a
    --      SUBTRACT BY ITSELF
    , pat (NodeF SubInt ["a", "a"])   := pat (intLeafFPattner 0)   -- a - a = 0
    , pat (NodeF SubFloat ["a", "a"]) := pat (floatLeafFPattner 0) -- a - a = 0.0
    --    MULTIPLICATION
    --      MULTIPLY BY 1
    , pat (NodeF MultInt [pat (intLeafFPattner 1), "a"])        := "a" -- 1 * a = a
    , pat (NodeF MultInt ["a", pat (intLeafFPattner 1)])        := "a" -- a * 1 = a
    , pat (NodeF MultFloat [pat (floatLeafFPattner 1), "a"])    := "a" -- 1.0 * a = a
    , pat (NodeF MultFloat ["a", pat (floatLeafFPattner 1)])    := "a" -- a * 1.0 = a
    --      MULTIPLY BY 0
    , pat (NodeF MultInt [pat (intLeafFPattner 0), "a"])        := pat (intLeafFPattner 0)   -- 0 * a = 0
    , pat (NodeF MultInt ["a", pat (intLeafFPattner 0)])        := pat (intLeafFPattner 0)   -- a * 0 = 0
    , pat (NodeF MultFloat [pat (floatLeafFPattner 0), "a"])    := pat (floatLeafFPattner 0) -- 0.0 * a = 0
    , pat (NodeF MultFloat ["a", pat (floatLeafFPattner 0)])    := pat (floatLeafFPattner 0) -- a * 0.0 = 0
    --      ASSOCIATIVE
    , pat (NodeF MultInt ["a", pat (NodeF MultInt ["b", "c"])])     := pat (NodeF MultInt [pat (NodeF MultInt ["a", "b"]), "c"])     -- a * (b * c) = (a * b) * c
    , pat (NodeF MultFloat ["a", pat (NodeF MultFloat ["b", "c"])]) := pat (NodeF MultFloat [pat (NodeF MultFloat ["a", "b"]), "c"]) -- a * (b * c) = (a * b) * c
    --      COMUTATIVE
    , pat (NodeF MultInt ["a", "b"])   := pat (NodeF MultInt ["b", "a"])   -- a * b = b * a
    , pat (NodeF MultFloat ["a", "b"]) := pat (NodeF MultFloat ["b", "a"]) -- a * b = b * a
    --    DIVISION
    --      DIVISION BY 1
    , pat (NodeF DivInt ["a", pat (intLeafFPattner 1)])     := "a" -- a / 1 = a
    , pat (NodeF DivFloat ["a", pat (floatLeafFPattner 1)]) := "a" -- a / 1.0 = a
    --      DIVISION BY ITSELF
    , pat (NodeF DivInt ["a", "a"])   := pat (intLeafFPattner 1)   :| nonZero  "a"   -- a / a = 1
    , pat (NodeF DivFloat ["a", "a"]) := pat (floatLeafFPattner 1) :| nonZero "a"-- a / a = 1.0
    --      CANCELATION
    , pat (NodeF DivInt [pat (NodeF MultInt ["a", "b"]), "a"])     := "b"  :| nonZero "a" -- a * b / a = b
    , pat (NodeF DivInt [pat (NodeF MultInt ["a", "b"]), "b"])     := "a"  :| nonZero "b" -- a * b / b = a
    , pat (NodeF DivFloat [pat (NodeF MultFloat ["a", "b"]), "a"]) := "b"  :| nonZero "a" -- a * b / a = b
    , pat (NodeF DivFloat [pat (NodeF MultFloat ["a", "b"]), "b"]) := "a"  :| nonZero "b" -- a * b / b = a
    --      REMAINDER MOD 1
    , pat (NodeF ModInt ["a", pat (intLeafFPattner 1)]) := pat (intLeafFPattner 0) -- a % 1 = 0
    --      REMAINDER MOD DIVISOR
    , pat (NodeF ModInt [pat (NodeF MultInt ["a", "b"]), "a"]) := pat (intLeafFPattner 0) :| nonZero "a" -- (a * b) % a = 0
    , pat (NodeF ModInt [pat (NodeF MultInt ["a", "b"]), "b"]) := pat (intLeafFPattner 0) :| nonZero "b" -- (a * b) % b = 0
    --  LIST
    , pat (NodeF Len [pat (NodeF Reverse ["a"])])           := pat (NodeF Len ["a"])       -- Len . Reverser = Len
    , pat (NodeF Head [pat (NodeF Singleton ["a"])])        := "a"                         -- Head . Singleton = Id
    , pat (NodeF Reverse [pat (NodeF Singleton ["a"])])     := pat (NodeF Singleton ["a"]) -- Reverse . Singleton = Singleton
    , pat (NodeF Len [pat (NodeF Singleton ["a"])])         := pat (intLeafFPattner 1)     -- Len . Singleton = 1
    , pat (NodeF ProductInts [pat (NodeF Singleton ["a"])]) := "a"                         -- Product . Singleton = Id
    , pat (NodeF SumInts [pat (NodeF Singleton ["a"])])     := "a"                         -- Sum . Singleton = Id
    , pat (NodeF Reverse [pat (NodeF Reverse ["a"])])       := "a"                         -- Reverse . Reverse = Id
    , pat (NodeF Take [pat (NodeF Len ["a"]), "a"])         := "a"                         -- Take (Len a) a = a 
    , pat (NodeF Range ["a", "a", "a"])                     := pat (NodeF Singleton ["a"]) -- [a,a+a..a] = [a]
    -- INT COMPARISON
    , pat (NodeF EqInt ["a", "b"])  := pat (NodeF EqInt ["b", "a"])  -- a == b = b == a
    , pat (NodeF MinInt ["a", "b"]) := pat (NodeF MinInt ["b", "a"]) -- min a b = min b a
    , pat (NodeF MaxInt ["a", "b"]) := pat (NodeF MaxInt ["b", "a"]) -- max a b = max b a
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
      dataValue /= Just (IntLit 0)
  &&  dataValue /= Just (FloatLit 0)
  &&  isJust dataValue -- Argument or evaluation can potentialy result in zero
        where dataValue = egr^._class (unsafeGetSubst v subst)._data


runEqualitySaturationOnTree :: Tree -> Tree
runEqualitySaturationOnTree t = toTree $ fst (equalitySaturation (toTreeF t) rewritesTreeF costTreeF)
