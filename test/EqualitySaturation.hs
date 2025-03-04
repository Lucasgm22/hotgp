{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
module EqualitySaturation where

import Test.Tasty
import Test.Tasty.HUnit

import Data.Equality.Utils
import Data.Equality.Matching
import Data.Equality.Saturation
import Data.Equality.Analysis
import Data.Equality.Graph
import Data.Equality.Graph.Lens
import Grammar

data SymExpr a = Const Double
               | Symbol String
               | a :+: a
               | a :*: a
               | a :/: a
               deriving (Functor, Foldable, Traversable, Eq, Ord, Show)
infix 6 :+:
infix 7 :*:, :/:

tests :: [TestTree]
tests =
    [
        simpleSymTests
      , treeFTests
    ]

instance Analysis (Maybe Double) SymExpr where
  makeA :: SymExpr (Maybe Double) -> Maybe Double
  makeA = \case
    Const x -> Just x
    Symbol _ -> Nothing
    x :+: y -> (+) <$> x <*> y
    x :*: y -> (*) <$> x <*> y
    x :/: y -> (/) <$> x <*> y

  joinA :: Maybe Double -> Maybe Double -> Maybe Double
  joinA Nothing (Just x) = Just x
  joinA (Just x) Nothing = Just x
  joinA Nothing Nothing  = Nothing
  joinA (Just x) (Just y) = if x == y then Just x else error "ouch, that shouldn't have happened"

  modifyA :: ClassId -> EGraph (Maybe Double) SymExpr -> EGraph (Maybe Double) SymExpr
  modifyA c eg
    = case eg^._class c._data of
        Nothing -> eg
        Just i  ->
          let (c', eg') = represent (Fix (Const i)) eg
           in snd $ merge c c' eg'

cost :: CostFunction SymExpr Int
cost = \case
  Const  _ -> 1
  Symbol _ -> 1
  c1 :+: c2 -> c1 + c2 + 2
  c1 :*: c2 -> c1 + c2 + 3
  c1 :/: c2 -> c1 + c2 + 4

rewrites :: [Rewrite (Maybe Double) SymExpr]
rewrites =
  [ 
      pat (pat ("a" :*: "b") :/: "c") := pat ("a" :*: pat ("b" :/: "c"))
    , pat ("x" :/: "x")               := pat (Const 1)
    , pat ("x" :*: pat (Const 1))     := "x"
  ]

rewrite :: Fix SymExpr -> Fix SymExpr
rewrite e = fst (equalitySaturation e rewrites cost)

e1 :: Fix SymExpr
e1 = Fix (Fix (Fix (Symbol "x") :*: Fix (Const 2)) :/: Fix (Const 2)) -- (x*2)/2

simpleSymTests :: TestTree
simpleSymTests = testGroup "Simple Sym"
    [ 
        testCase "(a*2)/2 = a"  $ rewrite e1 @?= Fix (Symbol "x")
      , testCase "(3+(x/x)+1) = 4" $ rewrite (Fix $ Fix (Const 3) :+: Fix (Fix (Symbol "x") :/: Fix (Symbol "x"))) @?= Fix (Const 4)
    ]
-- TODO: Write the Program tree test

-- | Fixed point of the structure that represents a program written in this grammar
data TreeF a = LeafF !Terminal
             | NodeF !Operation ![a] deriving (Functor, Foldable, Traversable, Eq, Ord, Show)

{-
A perfect solution found by hotgp for the compare string lenghts problem
stringRep:
(if ((length x2) > (length x1)) 
  then ((length x0) < (length (reverse x1))) 
  else ((length x1) < (length (reverse x2)))) || ((length (if False then x0 else x0)) > (length x0))
stringRepSimple:
(if ((length x2) > (length x1)) 
  then ((length x0) < (length x1)) 
  else ((length x1) < (length x2))) || ((length x0) > (length x0))
-}
solutionForCompareStringLengths :: Tree
solutionForCompareStringLengths = Grammar.Node {_measure = Just (MkMeasure {_currentDepth = 0, _height = 5, _nodeCount = 27}), _operation = Or, Grammar._args = [Grammar.Node {_measure = Just (MkMeasure {_currentDepth = 1, _height = 4, _nodeCount = 18}), _operation = If, Grammar._args = [Grammar.Node {_measure = Just (MkMeasure {_currentDepth = 2, _height = 2, _nodeCount = 5}), _operation = GtInt, Grammar._args = [Grammar.Node {_measure = Just (MkMeasure {_currentDepth = 3, _height = 1, _nodeCount = 2}), _operation = Len, Grammar._args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 4, _height = 0, _nodeCount = 1}), Grammar._terminal = Arg 2}]},Grammar.Node {_measure = Just (MkMeasure {_currentDepth = 3, _height = 1, _nodeCount = 2}), _operation = Len, Grammar._args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 4, _height = 0, _nodeCount = 1}), Grammar._terminal = Arg 1}]}]},Grammar.Node {_measure = Just (MkMeasure {_currentDepth = 2, _height = 3, _nodeCount = 6}), _operation = LtInt, Grammar._args = [Grammar.Node {_measure = Just (MkMeasure {_currentDepth = 3, _height = 1, _nodeCount = 2}), _operation = Len, Grammar._args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 4, _height = 0, _nodeCount = 1}), Grammar._terminal = Arg 0}]},Grammar.Node {_measure = Just (MkMeasure {_currentDepth = 3, _height = 2, _nodeCount = 3}), _operation = Len, Grammar._args = [Grammar.Node {_measure = Just (MkMeasure {_currentDepth = 4, _height = 1, _nodeCount = 2}), _operation = Reverse, Grammar._args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 5, _height = 0, _nodeCount = 1}), Grammar._terminal = Arg 1}]}]}]},Grammar.Node {_measure = Just (MkMeasure {_currentDepth = 2, _height = 3, _nodeCount = 6}), _operation = LtInt, Grammar._args = [Grammar.Node {_measure = Just (MkMeasure {_currentDepth = 3, _height = 1, _nodeCount = 2}), _operation = Len, Grammar._args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 4, _height = 0, _nodeCount = 1}), Grammar._terminal = Arg 1}]},Grammar.Node {_measure = Just (MkMeasure {_currentDepth = 3, _height = 2, _nodeCount = 3}), _operation = Len, Grammar._args = [Grammar.Node {_measure = Just (MkMeasure {_currentDepth = 4, _height = 1, _nodeCount = 2}), _operation = Reverse, Grammar._args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 5, _height = 0, _nodeCount = 1}), Grammar._terminal = Arg 2}]}]}]}]},Grammar.Node {_measure = Just (MkMeasure {_currentDepth = 1, _height = 3, _nodeCount = 8}), _operation = GtInt, Grammar._args = [Grammar.Node {_measure = Just (MkMeasure {_currentDepth = 2, _height = 2, _nodeCount = 5}), _operation = Len, Grammar._args = [Grammar.Node {_measure = Just (MkMeasure {_currentDepth = 3, _height = 1, _nodeCount = 4}), _operation = If, Grammar._args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 4, _height = 0, _nodeCount = 1}), Grammar._terminal = Literal (BoolLit False)},Leaf {_measure = Just (MkMeasure {_currentDepth = 4, _height = 0, _nodeCount = 1}), Grammar._terminal = Arg 0},Leaf {_measure = Just (MkMeasure {_currentDepth = 4, _height = 0, _nodeCount = 1}), Grammar._terminal = Arg 0}]}]},Grammar.Node {_measure = Just (MkMeasure {_currentDepth = 2, _height = 1, _nodeCount = 2}), _operation = Len, Grammar._args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 3, _height = 0, _nodeCount = 1}), Grammar._terminal = Arg 0}]}]}]}

fromTreeToFixTreeF :: Tree -> Fix TreeF
fromTreeToFixTreeF (Leaf _ t)               = Fix $ LeafF t
fromTreeToFixTreeF (Grammar.Node _ op args) = Fix $ NodeF op (fromTreeToFixTreeF <$> args)

_terminal :: TreeF a -> Terminal
_terminal (LeafF t) = t
_terminal _           = error "Unexpected _termial call for NodeF"

_args :: TreeF a -> [a]
_args (NodeF _ args) = args
_args _                = error "Unexpected _args call for LeafF"

instance Analysis (Maybe Lit) TreeF where
  makeA :: TreeF (Maybe Lit) -> Maybe Lit
  makeA = \case
    LeafF (Literal l)       -> Just l
    LeafF (Arg _)           -> Nothing -- An argument of the function has no Literal Value at compile time similar to Symbol in SymExpr
    NodeF op args           -> sequenceA args >>= eval op

  joinA :: Maybe Lit -> Maybe Lit -> Maybe Lit
  joinA Nothing Nothing     = Nothing
  joinA Nothing (Just l)    = Just l
  joinA (Just l) Nothing    = Just l
  joinA (Just l1) (Just l2) = if l1 == l2 then Just l1 else error "ouch, that shouldn't have happened"

  modifyA :: ClassId -> EGraph (Maybe Lit) TreeF -> EGraph (Maybe Lit) TreeF
  modifyA c eg
    = case eg^._class c._data of
        Nothing -> eg
        Just l  ->
          let (c', eg') = represent (Fix (LeafF (Literal l))) eg
           in snd $ merge c c' eg'

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
  NodeF ModInt ns        -> sum ns + 2
  NodeF MaxInt ns        -> sum ns + 2
  NodeF MinInt ns        -> sum ns + 2
  --   Bool
  NodeF And ns           -> sum ns + 2
  NodeF Or ns            -> sum ns + 2
  NodeF Not ns           -> sum ns + 2
  NodeF If ns            -> sum ns + 2
  --   Float
  NodeF AddFloat ns      -> sum ns + 4
  NodeF SubFloat ns      -> sum ns + 4
  NodeF MultFloat ns     -> sum ns + 2
  NodeF DivFloat ns      -> sum ns + 3
  NodeF Sqrt ns          -> sum ns + 3
  --   Char + Bool
  NodeF EqChar ns        -> sum ns + 2
  NodeF IsLetter ns      -> sum ns + 2
  NodeF IsDigit ns       -> sum ns + 2
  --   Float + Int
  NodeF IntToFloat ns    -> sum ns + 2
  NodeF Floor ns         -> sum ns + 2
  --   Int + Bool
  NodeF GtInt ns         -> sum ns + 2
  NodeF LtInt ns         -> sum ns + 2
  NodeF EqInt ns         -> sum ns + 2
  --   Lists
  NodeF Len ns           -> sum ns + 2
  NodeF Reverse ns       -> sum ns + 2
  NodeF Singleton ns     -> sum ns + 2
  NodeF Cons ns          -> sum ns + 2
  NodeF Head ns          -> sum ns + 2
  NodeF Range ns         -> sum ns + 2
  NodeF Map ns           -> sum ns + 2
  NodeF Filter ns        -> sum ns + 2
  NodeF Concat ns        -> sum ns + 2
  NodeF Zip ns           -> sum ns + 2
  NodeF Take ns          -> sum ns + 2
  NodeF SumFloats ns     -> sum ns + 3
  NodeF ProductFloats ns -> sum ns + 2
  NodeF SumInts ns       -> sum ns + 3
  NodeF ProductInts ns   -> sum ns + 2
  --   String
  NodeF Unlines ns       -> sum ns + 2
  NodeF ShowInt ns       -> sum ns + 2
  --   Pair
  NodeF ToPair ns        -> sum ns + 2
  NodeF Fst ns           -> sum ns + 2
  NodeF Snd ns           -> sum ns + 2

boolLeafFPattern :: Bool -> TreeF (Pattern TreeF)
boolLeafFPattern b = LeafF (Literal (BoolLit b))

intLeafFPattner :: Int -> TreeF (Pattern TreeF)
intLeafFPattner i = LeafF (Literal (IntLit i))

floatLeafFPattner :: Float -> TreeF (Pattern TreeF)
floatLeafFPattner f = LeafF (Literal (FloatLit f))


rewritesTreeF :: [Rewrite (Maybe Lit) TreeF]
rewritesTreeF =
  [ -- IF
      pat (NodeF If [pat (boolLeafFPattern True), "a", "b"])  := "a"  -- IF True a else b  = a
    , pat (NodeF If [pat (boolLeafFPattern False), "a", "b"]) := "b"  -- IF False a else b = b
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
    -- TODO OR/AND ARE COMMUTATIVE AND ASSOCIATIVE
    , pat (NodeF Or [pat (boolLeafFPattern True), "a"])       := pat (boolLeafFPattern True)           -- True Or a  = True
    , pat (NodeF Or ["a", pat (boolLeafFPattern True)])       := pat (boolLeafFPattern True)           -- a Or True  = True
    , pat (NodeF Or [pat (boolLeafFPattern False), "a"])      := "a"                                   -- False Or a = a
    , pat (NodeF Or ["a", pat (boolLeafFPattern False)])      := "a"                                   -- a Or False = a
    , pat (NodeF And [pat (boolLeafFPattern True), "a"])      := "a"                                   -- True And a  = a
    , pat (NodeF And ["a", pat (boolLeafFPattern True)])      := "a"                                   -- a And True  = a
    , pat (NodeF And [pat (boolLeafFPattern False), "a"])     := pat (boolLeafFPattern False)          -- False And a = False
    , pat (NodeF And ["a", pat (boolLeafFPattern False)])     := pat (boolLeafFPattern False)          -- a And False = False
    , pat (NodeF If [pat (NodeF Not ["a"]), "b", "c"])        := pat (NodeF If ["a", "c", "b"])        -- IF !a then b else c = IF a then c else b
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
    , pat (NodeF AddInt ["a", "b"])   := pat (NodeF AddInt ["b", "c"])   -- a + b = b + a
    , pat (NodeF AddFloat ["a", "b"]) := pat (NodeF AddFloat ["b", "a"]) -- a + b = b + a
    --    SUBTRACTION
    --      SUBTRACT BY 0
    , pat (NodeF SubInt [pat (intLeafFPattner 0), "a"])     := "a"                       -- a - 0 = a
    , pat (NodeF SubFloat ["a", pat (floatLeafFPattner 0)]) := "a"                       -- a - 0.0 = a
    --      SUBTRACT BY ITSELF
    , pat (NodeF SubInt ["a", "a"])                         := pat (intLeafFPattner 0)   -- a - a = 0
    , pat (NodeF SubFloat ["a", "a"])                       := pat (floatLeafFPattner 0) -- a - a = 0.0
    --    MULTIPLICATION
    --      MULTIPLY BY 1
    , pat (NodeF MultInt [pat (intLeafFPattner 1), "a"])        := "a" -- 1 * a = a
    , pat (NodeF MultInt ["a", pat (intLeafFPattner 1)])        := "a" -- a * 1 = a
    , pat (NodeF MultFloat [pat (floatLeafFPattner 1), "a"])    := "a" -- 1.0 * a = a
    , pat (NodeF MultFloat ["a", pat (floatLeafFPattner 1)])    := "a" -- a * 1.0 = a
    --      MULTIPLY BY 0
    , pat (NodeF MultInt [pat (intLeafFPattner 0), "a"])        := pat (intLeafFPattner 0)   -- 0 * a = 0
    , pat (NodeF MultInt ["a", pat (intLeafFPattner 0)])        := pat (intLeafFPattner 0)   -- a * , = 0
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
    , pat (NodeF DivInt ["a", "a"])   := pat (intLeafFPattner 1)   -- a / a = 1
    , pat (NodeF DivFloat ["a", "a"]) := pat (floatLeafFPattner 1) -- a / a = 1.0
    --      CANCELATION
    , pat (NodeF DivInt [pat (NodeF MultInt ["a", "b"]), "a"])     := "b" -- a * b / a = b
    , pat (NodeF DivInt [pat (NodeF MultInt ["a", "b"]), "b"])     := "a" -- a * b / b = a
    , pat (NodeF DivFloat [pat (NodeF MultFloat ["a", "b"]), "a"]) := "b" -- a * b / a = b
    , pat (NodeF DivFloat [pat (NodeF MultFloat ["a", "b"]), "b"]) := "a" -- a * b / b = a
    --      REMAINDER MOD 1
    , pat (NodeF ModInt ["a", pat (intLeafFPattner 1)]) := pat (intLeafFPattner 0) -- a % 1 = 0
    --      REMAINDER MOD DIVISOR
    , pat (NodeF ModInt [pat (NodeF MultInt ["a", "b"]), "a"]) := pat (intLeafFPattner 0) -- (a * b) % a = 0
    , pat (NodeF ModInt [pat (NodeF MultInt ["a", "b"]), "b"]) := pat (intLeafFPattner 0) -- (a * b) % b = 0
    --  LIST
    , pat (NodeF Len [pat (NodeF Reverse ["a"])])    := pat (NodeF Len ["a"])          -- Len . Reverser = Len
    , pat (NodeF Head [pat (NodeF Singleton ["a"])]) := "a"                            -- Head . Singleton = Id
    , pat (NodeF Reverse [pat (NodeF Singleton ["a"])]) := pat (NodeF Singleton ["a"]) -- Reverse . Singleton = Singleton
    , pat (NodeF Len [pat (NodeF Singleton ["a"])]) := pat (intLeafFPattner 1)         -- Len . Singleton = 1
    , pat (NodeF ProductInts [pat (NodeF Singleton ["a"])]) := "a"                     -- Product . Singleton = Id
    , pat (NodeF SumInts [pat (NodeF Singleton ["a"])]) := "a"                         -- Sum . Singleton = Id
    , pat (NodeF Reverse [pat (NodeF Reverse ["a"])]) := "a"                           -- Reverse . Reverse = Id
    , pat (NodeF Take [pat (NodeF Len ["a"]), "a"]) := "a"                             -- Take (Len a) a = a 
    , pat (NodeF Range ["a", "a", "a"]) := pat (NodeF Singleton ["a"])                 -- [a,a+a..a] = [a]
  ]


rewriteTreeF :: Fix TreeF -> Fix TreeF
rewriteTreeF t = fst (equalitySaturation t rewritesTreeF costTreeF)

treeFTests :: TestTree
treeFTests = testGroup "TreeF"
  [ 
      testCase "rewrite solutionForCompareStringLengths"  $ rewriteTreeF (fromTreeToFixTreeF solutionForCompareStringLengths) @?= Fix (LeafF (Literal (BoolLit False)))
  ]

