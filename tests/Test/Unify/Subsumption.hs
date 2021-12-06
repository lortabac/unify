module Test.Unify.Subsumption where

import Logic.Unify
import Test.Tasty
import Test.Tasty.HUnit
import Test.Unify.Types

subsumptionTests :: TestTree
subsumptionTests =
  testGroup
    "Subsumption"
    [ testCase "equal" $ do
        let res = evalUnify $ do
              subsumes (Int 1) (Int 1)
        res @=? Unified,
      testCase "more general" $ do
        let res = evalUnify $ do
              x <- Var <$> newVar
              subsumes x (Int 1)
        res @=? Unified,
      testCase "more specific" $ do
        let res = evalUnify $ do
              x <- Var <$> newVar
              subsumes (Int 1) x
        res @=? SubsumptionFailure (Int 1) (Var (UVar 0))
    ]
