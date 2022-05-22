{-# LANGUAGE DeriveDataTypeable #-}

module Test.Unify.Types where

import Control.Lens (Plated, children, transformM)
import Data.Data (Data)
import Data.Proxy
import Logic.Unify

data Term
  = Var UVar
  | Int Int
  | F1 Term
  | F2 Term Term
  deriving (Eq, Show, Data)

instance Plated Term

instance Unifiable Term where
  getVar (Var v) = Just v
  getVar _ = Nothing
  transformTermM = transformM
  termChildren = children

newMetavar :: Unify Term Term
newMetavar = Var <$> newVar (Proxy :: Proxy Term)
