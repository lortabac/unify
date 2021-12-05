module Test.Unify.Vars where

import Data.Maybe (mapMaybe)
import Logic.Unify
import Test.Tasty
import Test.Tasty.HUnit
import Test.Unify.Types

getVarsTest :: TestTree
getVarsTest =
  testGroup "getVars"
    [ testCase "empty" $
        getVars (Int 1) @=? [],
      testCase "F1 var" $ do
        let (vars, x') = runUnify $ do
              x <- Var <$> newVar
              let e = F1 x
              pure (getVars e, x)
        vars @=? mapMaybe getVar [x'],
      testCase "F2 var" $ do
        let (vars, x') = runUnify $ do
              x <- Var <$> newVar
              let e = F2 x (Int 1)
              pure (getVars e, x)
        vars @=? mapMaybe getVar [x'],
      testCase "nested var" $ do
        let (vars, x', y') = runUnify $ do
              x <- Var <$> newVar
              y <- Var <$> newVar
              let e = F2 x (F2 (Int 1) y)
              pure (getVars e, x, y)
        vars @=? mapMaybe getVar [x', y']
    ]
