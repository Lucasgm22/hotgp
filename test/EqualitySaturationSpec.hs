module EqualitySaturationSpec where

import Test.Tasty
import Test.Tasty.HUnit

import Grammar

tests :: [TestTree]
tests =
    [
        treeFTests
    ]

{-
A perfect solution found by HOTGP for the compare string lenghts problem
stringRep: (this is the string representation of the solution, actual content)
(if ((length x2) > (length x1)) 
  then ((length x0) < (length (reverse x1))) 
  else ((length x1) < (length (reverse x2)))) 
  || ((length (if False then x0 else x0)) > (length x0))
stringRepSimple: (this is the string representation of this solution after simplify)
(if ((length x2) > (length x1)) 
  then ((length x0) < (length x1)) 
  else ((length x1) < (length x2)))
  || ((length x0) > (length x0))
-}
solutionForCompareStringLengths :: Tree
solutionForCompareStringLengths = Node {_measure = Just (MkMeasure {_currentDepth = 0, _height = 5, _nodeCount = 27}), _operation = Or, _args = [Node {_measure = Just (MkMeasure {_currentDepth = 1, _height = 4, _nodeCount = 18}), _operation = If, _args = [Node {_measure = Just (MkMeasure {_currentDepth = 2, _height = 2, _nodeCount = 5}), _operation = GtInt, _args = [Node {_measure = Just (MkMeasure {_currentDepth = 3, _height = 1, _nodeCount = 2}), _operation = Len, _args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 4, _height = 0, _nodeCount = 1}), _terminal = Arg 2}]},Node {_measure = Just (MkMeasure {_currentDepth = 3, _height = 1, _nodeCount = 2}), _operation = Len, _args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 4, _height = 0, _nodeCount = 1}), _terminal = Arg 1}]}]},Node {_measure = Just (MkMeasure {_currentDepth = 2, _height = 3, _nodeCount = 6}), _operation = LtInt, _args = [Node {_measure = Just (MkMeasure {_currentDepth = 3, _height = 1, _nodeCount = 2}), _operation = Len, _args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 4, _height = 0, _nodeCount = 1}), _terminal = Arg 0}]},Node {_measure = Just (MkMeasure {_currentDepth = 3, _height = 2, _nodeCount = 3}), _operation = Len, _args = [Node {_measure = Just (MkMeasure {_currentDepth = 4, _height = 1, _nodeCount = 2}), _operation = Reverse, _args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 5, _height = 0, _nodeCount = 1}), _terminal = Arg 1}]}]}]},Node {_measure = Just (MkMeasure {_currentDepth = 2, _height = 3, _nodeCount = 6}), _operation = LtInt, _args = [Node {_measure = Just (MkMeasure {_currentDepth = 3, _height = 1, _nodeCount = 2}), _operation = Len, _args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 4, _height = 0, _nodeCount = 1}), _terminal = Arg 1}]},Node {_measure = Just (MkMeasure {_currentDepth = 3, _height = 2, _nodeCount = 3}), _operation = Len, _args = [Node {_measure = Just (MkMeasure {_currentDepth = 4, _height = 1, _nodeCount = 2}), _operation = Reverse, _args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 5, _height = 0, _nodeCount = 1}), _terminal = Arg 2}]}]}]}]},Node {_measure = Just (MkMeasure {_currentDepth = 1, _height = 3, _nodeCount = 8}), _operation = GtInt, _args = [Node {_measure = Just (MkMeasure {_currentDepth = 2, _height = 2, _nodeCount = 5}), _operation = Len, _args = [Node {_measure = Just (MkMeasure {_currentDepth = 3, _height = 1, _nodeCount = 4}), _operation = If, _args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 4, _height = 0, _nodeCount = 1}), _terminal = Literal (BoolLit False)},Leaf {_measure = Just (MkMeasure {_currentDepth = 4, _height = 0, _nodeCount = 1}), _terminal = Arg 0},Leaf {_measure = Just (MkMeasure {_currentDepth = 4, _height = 0, _nodeCount = 1}), _terminal = Arg 0}]}]},Node {_measure = Just (MkMeasure {_currentDepth = 2, _height = 1, _nodeCount = 2}), _operation = Len, _args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 3, _height = 0, _nodeCount = 1}), _terminal = Arg 0}]}]}]}

expectedSymplification :: Tree
expectedSymplification = Node {_measure = Just (MkMeasure {_currentDepth = 0, _height = 3, _nodeCount = 16}), _operation = If, _args = [Node {_measure = Just (MkMeasure {_currentDepth = 1, _height = 2, _nodeCount = 5}), _operation = GtInt, _args = [Node {_measure = Just (MkMeasure {_currentDepth = 2, _height = 1, _nodeCount = 2}), _operation = Len, _args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 3, _height = 0, _nodeCount = 1}), _terminal = Arg 2}]},Node {_measure = Just (MkMeasure {_currentDepth = 2, _height = 1, _nodeCount = 2}), _operation = Len, _args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 3, _height = 0, _nodeCount = 1}), _terminal = Arg 1}]}]},Node {_measure = Just (MkMeasure {_currentDepth = 1, _height = 2, _nodeCount = 5}), _operation = LtInt, _args = [Node {_measure = Just (MkMeasure {_currentDepth = 2, _height = 1, _nodeCount = 2}), _operation = Len, _args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 3, _height = 0, _nodeCount = 1}), _terminal = Arg 0}]},Node {_measure = Just (MkMeasure {_currentDepth = 2, _height = 1, _nodeCount = 2}), _operation = Len, _args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 3, _height = 0, _nodeCount = 1}), _terminal = Arg 1}]}]},Node {_measure = Just (MkMeasure {_currentDepth = 1, _height = 2, _nodeCount = 5}), _operation = LtInt, _args = [Node {_measure = Just (MkMeasure {_currentDepth = 2, _height = 1, _nodeCount = 2}), _operation = Len, _args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 3, _height = 0, _nodeCount = 1}), _terminal = Arg 1}]},Node {_measure = Just (MkMeasure {_currentDepth = 2, _height = 1, _nodeCount = 2}), _operation = Len, _args = [Leaf {_measure = Just (MkMeasure {_currentDepth = 3, _height = 0, _nodeCount = 1}), _terminal = Arg 2}]}]}]}

treeFTests :: TestTree
treeFTests = testGroup "TreeF"
  [
      -- Equality saturation must run two times in this case in order to fully simplify the tree
      testCase "rewrite solution for compare string lengths"  $ runEqualitySaturationOnTree 30 (runEqualitySaturationOnTree 30 solutionForCompareStringLengths) @?= expectedSymplification
  ]

