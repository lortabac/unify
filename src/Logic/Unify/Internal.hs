{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Logic.Unify.Internal where

import Control.Applicative (Alternative)
import Control.Monad.Except
import Control.Monad.Logic.Class
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Data
import Data.Functor.Identity
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Monoid (Any (..))
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic)

-- | Unification monad
newtype UnifyT t m a = UnifyT (StateT (UState t) m a)
  deriving newtype (Functor, Applicative, Monad, MonadTrans, MonadIO)

instance MonadReader r m => MonadReader r (UnifyT t m) where
  ask = lift ask
  local f (UnifyT m) = UnifyT (local f m)

instance MonadState s m => MonadState s (UnifyT t m) where
  get = lift get
  put = lift . put
  state = lift . state

deriving newtype instance MonadPlus m => Alternative (UnifyT t m)

deriving newtype instance MonadPlus m => MonadPlus (UnifyT t m)

instance (MonadLogic m, MonadPlus m) => MonadLogic (UnifyT t m) where
  msplit (UnifyT m) = UnifyT $ do
    split <- msplit m
    case split of
      Just (x, mx) -> pure $ Just (x, UnifyT mx)
      Nothing -> pure Nothing

type Unify t a = UnifyT t Identity a

-- | Unification state
data UState a = UState
  { bindings :: IntMap (Binding a),
    counter :: Int
  }

deriving instance (Eq a, Eq (Attr a)) => Eq (UState a)

deriving instance (Ord a, Ord (Attr a)) => Ord (UState a)

deriving instance (Show a, Show (Attr a)) => Show (UState a)

emptyUState :: UState a
emptyUState = UState mempty 0

-- | Run a computation in the unification monad
evalUnifyT :: Monad m => UnifyT t m a -> m a
evalUnifyT (UnifyT m) = evalStateT m emptyUState

evalUnify :: Unify t a -> a
evalUnify = runIdentity . evalUnifyT

-- | Run a computation in the unification monad,
--   with explicit initial and final state
runUnifyT :: Monad m => UState t -> UnifyT t m a -> m (a, UState t)
runUnifyT s (UnifyT m) = runStateT m s

runUnify :: UState t -> Unify t a -> (a, UState t)
runUnify s = runIdentity . runUnifyT s

-- | Unification variable
newtype UVar = UVar Int
  deriving (Eq, Ord, Show, Data, Generic)

-- | Class of terms that can be unified
class Eq t => Unifiable t where
  type Attr t
  type Attr t = ()

  -- | Does this constructor take a 'UVar' argument?
  getVar :: t -> Maybe UVar

  transformTermM :: Monad m => (t -> m t) -> t -> m t

  termChildren :: t -> [t]

  -- | Get the index of the constructor of a term
  constructorIndex :: t -> Int
  default constructorIndex :: Data t => t -> Int
  constructorIndex = constrIndex . toConstr

-- | Create a fresh unification variable
newVar :: Monad m => UnifyT t m UVar
newVar = UnifyT $ do
  i <- gets counter
  modify (\s -> s {counter = counter s + 1})
  pure $ UVar i

data UnificationResult t
  = Unified
  | OccursFailure UVar t
  | UnificationFailure t t
  | SubsumptionFailure t t
  deriving (Eq, Show)

instance Semigroup (UnificationResult t) where
  Unified <> r = r
  OccursFailure v t <> _ = OccursFailure v t
  UnificationFailure t1 t2 <> _ = UnificationFailure t1 t2
  SubsumptionFailure t1 t2 <> _ = SubsumptionFailure t1 t2

instance Monoid (UnificationResult t) where
  mempty = Unified

data Binding a = Bound a | Attr (Attr a)

deriving instance (Eq a, Eq (Attr a)) => Eq (Binding a)

deriving instance (Ord a, Ord (Attr a)) => Ord (Binding a)

deriving instance (Show a, Show (Attr a)) => Show (Binding a)

-- | Apply the current bindings to a term,
--   returning 'Nothing' in case of a cyclic term.
applyBindings :: (Monad m, Unifiable t) => t -> UnifyT t m (Either UVar t)
applyBindings = runExceptT . applyBindings' mempty

-- | Get all the variables in a term
getVars :: Unifiable t => t -> [UVar]
getVars = go []
  where
    go acc t = case getVar t of
      Just v -> v : acc
      Nothing -> concatMap (go acc) (termChildren t)

lookupBinding :: Monad m => UVar -> UnifyT t m (Maybe (Binding t))
lookupBinding (UVar v) = UnifyT $ gets (IntMap.lookup v . bindings)

applyBindings' :: (Monad m, Unifiable t) => Set Int -> t -> ExceptT UVar (UnifyT t m) t
applyBindings' vs = transformTermM substVar
  where
    substVar t = case matchTerm t of
      MatchVar v@(UVar i) -> do
        if Set.member i vs
          then throwError v
          else do
            b <- lift $ lookupBinding v
            case b of
              Just (Bound t') -> applyBindings' (Set.insert i vs) t'
              Just (Attr _) -> pure t
              Nothing -> pure t
      _ -> pure t

unify' ::
  (Monad m, Unifiable t) =>
  Bool ->
  (Attr t -> t -> UnifyT t m Bool) ->
  t ->
  t ->
  UnifyT t m (UnificationResult t)
unify' oc hook t1 t2 = case (matchTerm t1, matchTerm t2) of
  (MatchConst _ [], MatchConst _ []) ->
    if t1 == t2
      then pure Unified
      else pure $ UnificationFailure t1 t2
  (MatchConst f1 subs1, MatchConst f2 subs2) ->
    -- FIXME Remove length check
    if f1 == f2 && length subs1 == length subs2
      then mconcat <$> traverse (uncurry (unify' oc hook)) (zip subs1 subs2)
      else pure $ UnificationFailure t1 t2
  (MatchConst {}, MatchVar v@(UVar i)) -> do
    if oc && occursInTerm i t1
      then pure $ OccursFailure (UVar i) t1
      else do
        b <- lookupBinding v
        case b of
          Nothing -> do
            setBinding v (Bound t1)
            pure Unified
          Just (Bound t2') -> unify' oc hook t1 t2'
          Just (Attr attr) -> runHookAndUnify oc hook attr t1 t1 t2
  (MatchVar v@(UVar i), MatchConst {}) -> do
    if oc && occursInTerm i t2
      then pure $ OccursFailure (UVar i) t2
      else do
        b <- lookupBinding v
        case b of
          Nothing -> do
            setBinding v (Bound t2)
            pure Unified
          Just (Bound t1') -> unify' oc hook t1' t2
          Just (Attr attr) -> runHookAndUnify oc hook attr t2 t1 t2
  (MatchVar v1@UVar {}, MatchVar v2@UVar {}) -> do
    b1 <- lookupBinding v1
    b2 <- lookupBinding v2
    case (b1, b2) of
      (Nothing, Nothing) -> do
        setBinding v1 (Bound t2)
        pure Unified
      (Nothing, Just b) -> do
        unless (getBindingVar b == Just v1) $
          setBinding v1 (Bound t2)
        pure Unified
      (Just b, Nothing) -> do
        unless (getBindingVar b == Just v2) $
          setBinding v2 (Bound t1)
        pure Unified
      (Just (Bound t1'), Just (Bound t2')) -> unify' oc hook t1' t2'
      (Just (Attr attr), _) -> runHookAndUnify oc hook attr t2 t1 t2
      (_, Just (Attr attr)) -> runHookAndUnify oc hook attr t1 t1 t2

getBindingVar :: Unifiable a => Binding a -> Maybe UVar
getBindingVar (Bound x) = getVar x
getBindingVar _ = Nothing

runHookAndUnify ::
  (Monad m, Unifiable t) =>
  Bool ->
  (Attr t -> t -> UnifyT t m Bool) ->
  Attr t ->
  t ->
  t ->
  t ->
  UnifyT t m (UnificationResult t)
runHookAndUnify oc hook attr t t1 t2 = do
  s <- getUState
  res <- hook attr t
  if res
    then unify' oc hook t1 t2
    else do
      putUState s
      pure $ UnificationFailure t1 t2

data TermMatch a = MatchVar UVar | MatchConst Int [a]

matchTerm :: Unifiable a => a -> TermMatch a
matchTerm t = case getVar t of
  Just v -> MatchVar v
  Nothing -> MatchConst (constructorIndex t) (termChildren t)

occursInTerm :: Unifiable t => Int -> t -> Bool
occursInTerm i = getAny . occursInTerm' i

occursInTerm' :: Unifiable t => Int -> t -> Any
occursInTerm' i t = case matchTerm t of
  MatchVar (UVar j) -> Any (i == j)
  MatchConst _ subs -> mconcat $ map (occursInTerm' i) subs

setBinding :: Monad m => UVar -> Binding t -> UnifyT t m ()
setBinding (UVar v) t =
  UnifyT $
    modify (\s -> s {bindings = IntMap.insert v t (bindings s)})

getUState :: Monad m => UnifyT t m (UState t)
getUState = UnifyT get

putUState :: Monad m => UState t -> UnifyT t m ()
putUState = UnifyT . put
