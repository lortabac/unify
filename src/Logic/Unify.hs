{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Logic.Unify
  ( UnifyT,
    runUnifyT,
    runUnify,
    UVar (..),
    Unifiable (..),
    UnificationResult (..),
    freshUVar,
    freshBoundUVar,
    unify,
    unifyNoOccursCheck,
    applyBindings,
  )
where

import Control.Monad.Trans.State
import Data.Data
import Data.Functor.Identity
import Data.Generics.Uniplate.Data
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Monoid (Any (..))

-- | Unification monad
newtype UnifyT t m a = UnifyT (StateT (UState t) m a)
  deriving (Functor, Applicative, Monad)

-- | Run a computation in the unification monad
runUnifyT :: Monad m => UnifyT t m a -> m a
runUnifyT (UnifyT m) = evalStateT m emptyUState

runUnify :: UnifyT t Identity a -> a
runUnify = runIdentity . runUnifyT

-- | Unification variable
newtype UVar = UVar Int
  deriving (Eq, Ord, Show, Data)

-- | Class of terms that can be unified
class (Eq a, Data a) => Unifiable a where
  -- | Does the term contain a variable?
  getVar :: a -> Maybe UVar
  -- | Construct a term that contains a variable
  constructVar :: UVar -> a

-- | Create a fresh unification variable
freshUVar :: Monad m => UnifyT t m UVar
freshUVar = UnifyT $ do
  i <- gets counter
  modify (\s -> s {counter = counter s + 1})
  pure $ UVar i

-- | Create a fresh unification variable
--   and bind it immediately to a term
freshBoundUVar :: Monad m => t -> UnifyT t m UVar
freshBoundUVar t = do
  UVar i <- freshUVar
  setBinding i t
  pure $ UVar i

data UnificationResult t
  = Unified
  | OccursFailure UVar t
  | UnificationFailure t t
  deriving (Eq, Show)

instance Semigroup (UnificationResult t) where
  Unified <> Unified = Unified
  OccursFailure v t <> _ = OccursFailure v t
  UnificationFailure t1 t2 <> _ = UnificationFailure t1 t2
  Unified <> r = r

instance Monoid (UnificationResult t) where
  mempty = Unified

-- | Unify two terms with occurs-check
unify ::
  (Monad m, Unifiable a) =>
  a ->
  a ->
  UnifyT a m (UnificationResult a)
unify = unify' True

-- | Unify two terms without performing the occurs-check
unifyNoOccursCheck ::
  (Monad m, Unifiable a) =>
  a ->
  a ->
  UnifyT a m (UnificationResult a)
unifyNoOccursCheck = unify' False

-- | Apply the current bindings to a term
applyBindings :: (Monad m, Unifiable t) => t -> UnifyT t m t
applyBindings = transformM substVar
  where
    substVar t = case matchTerm t of
      MatchVar (UVar i) -> do
        b <- lookupBinding i
        case b of
          Just t' -> pure t'
          Nothing -> pure t
      _ -> pure t

unify' ::
  (Monad m, Unifiable a) =>
  Bool ->
  a ->
  a ->
  UnifyT a m (UnificationResult a)
unify' oc t1 t2 = case (matchTerm t1, matchTerm t2) of
  (MatchConst _ [], MatchConst _ []) ->
    if t1 == t2
      then pure Unified
      else pure $ UnificationFailure t1 t2
  (MatchConst f1 subs1, MatchConst f2 subs2) ->
    -- FIXME Remove length check
    if f1 == f2 && length subs1 == length subs2
      then mconcat <$> traverse (uncurry (unify' oc)) (zip subs1 subs2)
      else pure $ UnificationFailure t1 t2
  (MatchConst {}, MatchVar (UVar i)) -> do
    if oc && occursInTerm i t1
      then pure $ OccursFailure (UVar i) t1
      else do
        b <- lookupBinding i
        case b of
          Nothing -> do
            setBinding i t1
            pure Unified
          Just t2' -> unify' oc t1 t2'
  (MatchVar (UVar i), MatchConst {}) -> do
    if oc && occursInTerm i t2
      then pure $ OccursFailure (UVar i) t2
      else do
        b <- lookupBinding i
        case b of
          Nothing -> do
            setBinding i t2
            pure Unified
          Just t1' -> unify' oc t1' t2
  (MatchVar (UVar i1), MatchVar (UVar i2)) -> do
    b1 <- lookupBinding i1
    b2 <- lookupBinding i2
    case (b1, b2) of
      (Nothing, Nothing) -> do
        setBinding i1 t2
        pure Unified
      (Nothing, Just _) -> do
        setBinding i1 t2
        pure Unified
      (Just _, Nothing) -> do
        setBinding i2 t1
        pure Unified
      (Just t1', Just t2') -> unify' oc t1' t2'

data TermMatch a = MatchVar UVar | MatchConst Int [a]

matchTerm :: Unifiable a => a -> TermMatch a
matchTerm t = case getVar t of
  Just v -> MatchVar v
  Nothing -> MatchConst termIndex (children t)
  where
    termIndex = constrIndex (toConstr t)

occursInTerm :: Unifiable t => Int -> t -> Bool
occursInTerm i = getAny . occursInTerm' i

occursInTerm' :: Unifiable t => Int -> t -> Any
occursInTerm' i t = case matchTerm t of
  MatchVar (UVar j) -> Any (i == j)
  MatchConst _ subs -> mconcat $ map (occursInTerm' i) subs

lookupBinding :: Monad m => Int -> UnifyT t m (Maybe t)
lookupBinding i = UnifyT $ gets (IntMap.lookup i . bindings)

setBinding :: Monad m => Int -> t -> UnifyT t m ()
setBinding i t =
  UnifyT $
    modify (\s -> s {bindings = IntMap.insert i t (bindings s)})

data UState a = UState
  { bindings :: IntMap a,
    counter :: Int
  }

emptyUState :: UState a
emptyUState = UState mempty 0
