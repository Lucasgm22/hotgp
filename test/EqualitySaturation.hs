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
  [ pat (pat ("a" :*: "b") :/: "c") := pat ("a" :*: pat ("b" :/: "c"))
  , pat ("x" :/: "x")               := pat (Const 1)
  , pat ("x" :*: pat (Const 1))     := "x"
  ]

rewrite :: Fix SymExpr -> Fix SymExpr
rewrite e = fst (equalitySaturation e rewrites cost)

e1 :: Fix SymExpr
e1 = Fix (Fix (Fix (Symbol "x") :*: Fix (Const 2)) :/: Fix (Const 2)) -- (x*2)/2

simpleSymTests :: TestTree
simpleSymTests = testGroup "Simple Sym"
    [ testCase "(a*2)/2 = a"  $ rewrite e1 @?= Fix (Symbol "x")
    , testCase "(x/x)+1) = 4" $ rewrite (Fix $ Fix (Const 3) :+: Fix (Fix (Symbol "x") :/: Fix (Symbol "x"))) @?= Fix (Const 4)
    ]
-- TODO: Write the Program tree test

-- | Fixed point of the structure that represents a program written in this grammar
data TreeF a = LeafF !Terminal !(Maybe Measure)
             | NodeF !Operation ![a] !(Maybe Measure) deriving (Functor, Foldable, Traversable, Eq, Ord, Show)

_measure :: TreeF a -> Maybe Measure
_measure (LeafF _ mm)   = mm
_measure (NodeF _ _ mm) = mm

_terminal :: TreeF a -> Terminal
_terminal (LeafF t _) = t
_terminal _           = error "Unexpected _termial call for NodeF"

_args :: TreeF a -> [a]
_args (NodeF _ args _) = args
_args _                = error "Unexpected _args call for LeafF"

instance Analysis (Maybe Lit) TreeF where
  makeA :: TreeF (Maybe Lit) -> Maybe Lit
  makeA = \case
    LeafF (Literal l) _       -> Just l
    LeafF (Arg _) _           -> Nothing -- I am not really sure here
    NodeF op args _           -> sequenceA args >>= eval op

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
          let (c', eg') = represent (Fix (LeafF (Literal l) Nothing)) eg
           in snd $ merge c c' eg'
  
