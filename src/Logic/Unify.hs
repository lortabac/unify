{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Logic.Unify
  ( UnifyT,
    runUnifyT,
    runUnify,
    UVar (..),
    Unifiable (..),
    UnificationResult (..),
    Binding (..),
    bindVar,
    setAttr,
    lookupBinding,
    newVar,
    newBoundVar,
    newAttVar,
    unify,
    unify_,
    unifyOccursCheck,
    unifyOccursCheck_,
    unifyWithAttrHook,
    unifyWithAttrHook_,
    unifiable,
    unifiable_,
    unifyOrUndo,
    unifyOrUndo_,
    subsumes,
    subsumes_,
    applyBindings,
    getVars,
  )
where

import Control.Applicative (Alternative)
import Control.Monad (MonadPlus, when)
import Control.Monad.Logic.Class
import Control.Monad.Trans.Class (MonadTrans (lift))
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State
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
  deriving newtype (Functor, Applicative, Monad)

deriving newtype instance MonadPlus m => Alternative (UnifyT t m)

deriving newtype instance MonadPlus m => MonadPlus (UnifyT t m)

instance (MonadLogic m, MonadPlus m) => MonadLogic (UnifyT t m) where
  msplit (UnifyT m) = UnifyT $ do
    split <- msplit m
    case split of
      Just (x, mx) -> pure $ Just (x, UnifyT mx)
      Nothing -> pure Nothing

-- | Run a computation in the unification monad
runUnifyT :: Monad m => UnifyT t m a -> m a
runUnifyT (UnifyT m) = evalStateT m emptyUState

runUnify :: UnifyT t Identity a -> a
runUnify = runIdentity . runUnifyT

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

-- | Create a fresh unification variable
--   and bind it immediately to a term
newBoundVar :: Monad m => t -> UnifyT t m UVar
newBoundVar t = do
  v <- newVar
  setBinding v (Bound t)
  pure v

-- | Create a fresh unification variable
--   and set the provided attribute immediately
newAttVar :: Monad m => Attr t -> UnifyT t m UVar
newAttVar attr = do
  v <- newVar
  setAttr v attr
  pure v

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

-- | Unify two terms without performing the occurs-check
unify ::
  (Monad m, Unifiable a) =>
  a ->
  a ->
  UnifyT a m (UnificationResult a)
unify = unify' False (\_ _ -> pure True)

-- | Like 'unify', but returns a boolean
unify_ ::
  (Monad m, Unifiable a) =>
  a ->
  a ->
  UnifyT a m Bool
unify_ x y = (== Unified) <$> unify x y

-- | Unify two terms with the occurs-check.
--   This function is slow.
--   If possible use 'unify' and let 'applyBindings' detect cyclic terms lazily.
unifyOccursCheck ::
  (Monad m, Unifiable a) =>
  a ->
  a ->
  UnifyT a m (UnificationResult a)
unifyOccursCheck = unify' True (\_ _ -> pure True)

-- | Like 'unifyOccursCheck', but returns a boolean
unifyOccursCheck_ ::
  (Monad m, Unifiable a) =>
  a ->
  a ->
  UnifyT a m Bool
unifyOccursCheck_ x y = (== Unified) <$> unifyOccursCheck x y

-- | Unify two terms.
--   The provided action is run before unification
--   whenever the left term contains an attribute.
--   Unification fails if the action returns 'False'.
unifyWithAttrHook ::
  (Monad m, Unifiable a) =>
  (Attr a -> a -> UnifyT a m Bool) ->
  a ->
  a ->
  UnifyT a m (UnificationResult a)
unifyWithAttrHook = unify' False

-- | Like 'unifyWithAttrHook', but returns a boolean
unifyWithAttrHook_ ::
  (Monad m, Unifiable a) =>
  (Attr a -> a -> UnifyT a m Bool) ->
  a ->
  a ->
  UnifyT a m Bool
unifyWithAttrHook_ hook x y = (== Unified) <$> unifyWithAttrHook hook x y

-- | Like unify, but undoes all the bindings
unifiable ::
  (Monad m, Unifiable a, Eq (Attr a)) =>
  a ->
  a ->
  UnifyT a m (UnificationResult a)
unifiable t1 t2 = do
  oldState <- getUState
  res <- unify t1 t2
  putUState oldState
  pure res

-- | Like 'unifiable', but returns a boolean
unifiable_ ::
  (Monad m, Unifiable a, Eq (Attr a)) =>
  a ->
  a ->
  UnifyT a m Bool
unifiable_ x y = (== Unified) <$> unifiable x y

-- | Like unify, but undoes all the bindings upon failure
unifyOrUndo ::
  (Monad m, Unifiable a, Eq (Attr a)) =>
  a ->
  a ->
  UnifyT a m (UnificationResult a)
unifyOrUndo t1 t2 = do
  oldState <- getUState
  res <- unify t1 t2
  when (res /= Unified) (putUState oldState)
  pure res

-- | Like unifyOrUndo, but returns a boolean
unifyOrUndo_ ::
  (Monad m, Unifiable a, Eq (Attr a)) =>
  a ->
  a ->
  UnifyT a m Bool
unifyOrUndo_ x y = (== Unified) <$> unifyOrUndo x y

-- | Check whether the left term is more general than the right term
subsumes ::
  (Monad m, Unifiable a, Eq (Attr a)) =>
  a ->
  a ->
  UnifyT a m (UnificationResult a)
subsumes t1 t2 = do
  oldState <- getUState
  let oldBindings = bindings oldState
  unified <- unify t1 t2
  newState <- getUState
  let newBindings = bindings newState
      vars = getVars t2
      res = case unified of
        Unified ->
          if eqBindings oldBindings newBindings vars
            then Unified
            else SubsumptionFailure t1 t2
        r -> r
  putUState oldState
  pure res
  where
    getBindings bs = map (\(UVar v) -> IntMap.lookup v bs)
    eqBindings b1 b2 vs = getBindings b1 vs == getBindings b2 vs

-- | Like 'subsumes', but returns a boolean
subsumes_ ::
  (Monad m, Unifiable a, Eq (Attr a)) =>
  a ->
  a ->
  UnifyT a m Bool
subsumes_ x y = (== Unified) <$> subsumes x y

-- | Apply the current bindings to a term,
--   returning 'Nothing' in case of a cyclic term.
applyBindings :: (Monad m, Unifiable t) => t -> UnifyT t m (Maybe t)
applyBindings = runMaybeT . applyBindings' mempty

-- | Get all the variables in a term
getVars :: Unifiable t => t -> [UVar]
getVars = go []
  where
    go acc t = case getVar t of
      Just v -> v : acc
      Nothing -> concatMap (go acc) (termChildren t)

lookupBinding :: Monad m => UVar -> UnifyT t m (Maybe (Binding t))
lookupBinding (UVar v) = UnifyT $ gets (IntMap.lookup v . bindings)

bindVar :: Monad m => UVar -> t -> UnifyT t m ()
bindVar v b = setBinding v (Bound b)

setAttr :: Monad m => UVar -> Attr t -> UnifyT t m ()
setAttr v attr = setBinding v (Attr attr)

applyBindings' :: (Monad m, Unifiable t) => Set Int -> t -> MaybeT (UnifyT t m) t
applyBindings' vs = transformTermM substVar
  where
    substVar t = case matchTerm t of
      MatchVar v@(UVar i) -> do
        if Set.member i vs
          then fail "Cyclic term"
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
      (Nothing, Just _) -> do
        setBinding v1 (Bound t2)
        pure Unified
      (Just _, Nothing) -> do
        setBinding v2 (Bound t1)
        pure Unified
      (Just (Bound t1'), Just (Bound t2')) -> unify' oc hook t1' t2'
      (Just (Attr attr), _) -> runHookAndUnify oc hook attr t2 t1 t2
      (_, Just (Attr attr)) -> runHookAndUnify oc hook attr t1 t1 t2

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

data UState a = UState
  { bindings :: IntMap (Binding a),
    counter :: Int
  }

emptyUState :: UState a
emptyUState = UState mempty 0

getUState :: Monad m => UnifyT t m (UState t)
getUState = UnifyT get

putUState :: Monad m => UState t -> UnifyT t m ()
putUState = UnifyT . put
