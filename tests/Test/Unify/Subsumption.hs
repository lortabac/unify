{-# LANGUAGE TypeApplications #-}
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
        let res = evalUnify @Term $ do
              subsumes (Int 1) (Int 1)
        res @=? Unified,
      testCase "more general" $ do
        let res = evalUnify $ do
              x <- newMetavar
              subsumes x (Int 1)
        res @=? Unified,
      testCase "more specific" $ do
        let res = evalUnify $ do
              x <- newMetavar
              subsumes (Int 1) x
        res @=? SubsumptionFailure (Int 1) (Var (UVar 0)),
      testCase "vars" $ do
        let res = evalUnify $ do
              x <- newMetavar
              y <- newMetavar
              subsumes (F2 x x) (F2 y y)
        res @=? Unified
    ]
