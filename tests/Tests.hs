{-# LANGUAGE DeriveDataTypeable #-}

module Main where

import Data.Data
import Data.Functor.Identity
import Logic.Unify
import Test.Tasty
import Test.Tasty.HUnit

data Term
  = Var UVar
  | Int Int
  | F1 Term
  | F2 Term Term
  deriving (Eq, Show, Data)

instance Unifiable Term where
  getVar (Var v) = Just v
  getVar _ = Nothing
  constructVar = Var

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "Tests"
    [ testCase "var-const" $ do
        let res = runUnify $ do
              x <- Var <$> freshUVar
              _ <- unify x (Int 1)
              applyBindings x
        res @=? Int 1,
      testCase "mixed-const" $ do
        let res = runUnify $ do
              x <- Var <$> freshUVar
              _ <- unify (F2 x (Int 2)) (F2 (Int 1) (Int 2))
              applyBindings x
        res @=? Int 1,
      testCase "var-var" $ do
        let (v1, v2) = runUnify $ do
              x <- Var <$> freshUVar
              y <- Var <$> freshUVar
              _ <- unify x y
              x' <- applyBindings x
              pure (x', y)
        v1 @=? v2,
      testCase "const-const (fail)" $
        testUnificationFailure $
          unify (Int 1) (Int 2),
      testCase "f2-f2 (fail)" $
        testUnificationFailure $
          unify (F2 (Int 1) (Int 2)) (F2 (Int 1) (Int 3)),
      testCase "var-mixed (occurs)" $
        testOccursCheck $ do
          x <- Var <$> freshUVar
          unify x (F1 x)
    ]

testUnificationFailure ::
  (Eq t, Show t) =>
  UnifyT t Identity (UnificationResult t) ->
  IO ()
testUnificationFailure m = case runUnify m of
  UnificationFailure _ _ -> assertBool "unification failure" True
  r -> assertBool ("unification failure: " <> show r) False

testOccursCheck ::
  (Eq t, Show t) =>
  UnifyT t Identity (UnificationResult t) ->
  IO ()
testOccursCheck m = case runUnify m of
  OccursFailure _ _ -> assertBool "occurs failure" True
  r -> assertBool ("occurs failure: " <> show r) False
