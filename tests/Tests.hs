module Main where

import Test.Tasty
import Test.Unify.Subsumption
import Test.Unify.Unification
import Test.Unify.Vars

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unificationTests, getVarsTest, subsumptionTests]
