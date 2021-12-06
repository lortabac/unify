module Test.Unify.Unification where

import Data.Functor.Identity
import Logic.Unify
import Test.Tasty
import Test.Tasty.HUnit
import Test.Unify.Types

unificationTests :: TestTree
unificationTests =
  testGroup
    "Unification"
    [ testCase "var-const" $ do
        let res = evalUnify $ do
              x <- Var <$> newVar
              _ <- unify x (Int 1)
              applyBindings x
        res @=? Just (Int 1),
      testCase "mixed-const" $ do
        let res = evalUnify $ do
              x <- Var <$> newVar
              _ <- unify (F2 x (Int 2)) (F2 (Int 1) (Int 2))
              applyBindings x
        res @=? Just (Int 1),
      testCase "var-var" $ do
        let (v1, v2) = evalUnify $ do
              x <- Var <$> newVar
              y <- Var <$> newVar
              _ <- unify x y
              x' <- applyBindings x
              pure (x', y)
        v1 @=? Just v2,
      testCase "aliasing" $ do
        let res = evalUnify $ do
              x <- Var <$> newVar
              y <- Var <$> newVar
              _ <- unify x y
              _ <- unify y (Int 1)
              applyBindings x
        res @=? Just (Int 1),
      testCase "const-const (fail)" $
        testUnificationFailure $
          unify (Int 1) (Int 2),
      testCase "f2-f2 (fail)" $
        testUnificationFailure $
          unify (F2 (Int 1) (Int 2)) (F2 (Int 1) (Int 3)),
      testCase "var-mixed (occurs)" $
        testOccursCheck $ do
          x <- Var <$> newVar
          unifyOccursCheck x (F1 x),
      testCase "var-const (lazy occurs)" $ do
        let res = evalUnify $ do
              x <- Var <$> newVar
              _ <- unify x (F1 x)
              applyBindings x
        res @=? Nothing
    ]

testUnificationFailure ::
  (Eq t, Show t) =>
  UnifyT t Identity (UnificationResult t) ->
  IO ()
testUnificationFailure m = case evalUnify m of
  UnificationFailure _ _ -> assertBool "unification failure" True
  r -> assertBool ("unification failure: " <> show r) False

testOccursCheck ::
  (Eq t, Show t) =>
  UnifyT t Identity (UnificationResult t) ->
  IO ()
testOccursCheck m = case evalUnify m of
  OccursFailure _ _ -> assertBool "occurs failure" True
  r -> assertBool ("occurs failure: " <> show r) False
