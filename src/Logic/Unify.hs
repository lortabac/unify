{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Logic.Unify
  ( UnifyT,
    Unify,
    MonadUnify (..),
    UState,
    evalUnifyT,
    evalUnify,
    runUnifyT,
    runUnify,
    UVar (..),
    Unifiable (..),
    UnificationResult (..),
    Binding (..),
    newBoundVar,
    newAttVar,
    bindVar,
    getVars,
    unify,
    unify_,
    unifyOccursCheck,
    unifyOccursCheck_,
    unifyWithAttrHook,
    unifyWithAttrHook_,
    unifyOrUndo,
    unifyOrUndo_,
    unifiable,
    unifiable_,
    subsumes,
    subsumes_,
  )
where

import Control.Monad (when)
import Data.Proxy
import Logic.Unify.Internal hiding
  ( applyBindings,
    getUState,
    lookupBinding,
    newVar,
    putUState,
    setBinding,
    unify',
  )
import qualified Logic.Unify.Internal as U

class Monad m => MonadUnify t m where
  newVar :: Proxy t -> m UVar
  getUState :: m (UState t)
  putUState :: UState t -> m ()
  lookupBinding :: UVar -> m (Maybe (Binding t))
  setBinding :: UVar -> Binding t -> m ()
  unify' ::
    Unifiable t =>
    Bool ->
    (Attr t -> t -> m Bool) ->
    t ->
    t ->
    m (UnificationResult t)
  applyBindings :: t -> m (Either UVar t)

instance (Monad m, Unifiable t) => MonadUnify t (UnifyT t m) where
  newVar _ = U.newVar
  getUState = U.getUState
  putUState = U.putUState
  lookupBinding = U.lookupBinding
  setBinding = U.setBinding
  unify' = U.unify'
  applyBindings = U.applyBindings

-- | Create a fresh unification variable
--   and bind it immediately to a term
newBoundVar :: forall t m. MonadUnify t m => t -> m UVar
newBoundVar t = do
  v <- newVar (Proxy :: Proxy t)
  setBinding v (Bound t)
  pure v

-- | Create a fresh unification variable
--   and set the provided attribute immediately
newAttVar :: forall t m. MonadUnify t m => Proxy t -> Attr t -> m UVar
newAttVar _ attr = do
  v <- newVar (Proxy :: Proxy t)
  setAttr (Proxy :: Proxy t) v attr
  pure v

bindVar :: MonadUnify t m => UVar -> t -> m ()
bindVar v b = setBinding v (Bound b)

setAttr :: forall t m. MonadUnify t m => Proxy t -> UVar -> Attr t -> m ()
setAttr _ v attr = setBinding v (Attr @t attr)

-- | Unify two terms without performing the occurs-check
unify ::
  (MonadUnify t m, Unifiable t) =>
  t ->
  t ->
  m (UnificationResult t)
unify = unify' False (\_ _ -> pure True)

-- | Like 'unify', but returns a boolean
unify_ ::
  (MonadUnify t m, Unifiable t) =>
  t ->
  t ->
  m Bool
unify_ x y = (== Unified) <$> unify x y

-- | Unify two terms with the occurs-check.
--   This function is slow.
--   If possible use 'unify' and let 'applyBindings' detect cyclic terms lazily.
unifyOccursCheck ::
  (MonadUnify t m, Unifiable t) =>
  t ->
  t ->
  m (UnificationResult t)
unifyOccursCheck = unify' True (\_ _ -> pure True)

-- | Like 'unifyOccursCheck', but returns a boolean
unifyOccursCheck_ ::
  (MonadUnify t m, Unifiable t) =>
  t ->
  t ->
  m Bool
unifyOccursCheck_ x y = (== Unified) <$> unifyOccursCheck x y

-- | Unify two terms.
--   The provided action is run before unification
--   whenever the left term contains an attribute.
--   Unification fails if the action returns 'False'.
unifyWithAttrHook ::
  (MonadUnify t m, Unifiable t) =>
  (Attr t -> t -> m Bool) ->
  t ->
  t ->
  m (UnificationResult t)
unifyWithAttrHook = unify' False

-- | Like 'unifyWithAttrHook', but returns a boolean
unifyWithAttrHook_ ::
  (MonadUnify t m, Unifiable t) =>
  (Attr t -> t -> m Bool) ->
  t ->
  t ->
  m Bool
unifyWithAttrHook_ hook x y = (== Unified) <$> unifyWithAttrHook hook x y

-- | Like unify, but undoes all the bindings
unifiable ::
  forall t m.
  (MonadUnify t m, Unifiable t, Eq (Attr t)) =>
  t ->
  t ->
  m (UnificationResult t)
unifiable t1 t2 = do
  oldState <- getUState @t
  res <- unify t1 t2
  putUState oldState
  pure res

-- | Like 'unifiable', but returns a boolean
unifiable_ ::
  (MonadUnify t m, Unifiable t, Eq (Attr t)) =>
  t ->
  t ->
  m Bool
unifiable_ x y = (== Unified) <$> unifiable x y

-- | Like unify, but undoes all the bindings upon failure
unifyOrUndo ::
  forall t m.
  (MonadUnify t m, Unifiable t, Eq (Attr t)) =>
  t ->
  t ->
  m (UnificationResult t)
unifyOrUndo t1 t2 = do
  oldState <- getUState @t
  res <- unify t1 t2
  when (res /= Unified) (putUState oldState)
  pure res

-- | Like unifyOrUndo, but returns a boolean
unifyOrUndo_ ::
  (MonadUnify t m, Unifiable t, Eq (Attr t)) =>
  t ->
  t ->
  m Bool
unifyOrUndo_ x y = (== Unified) <$> unifyOrUndo x y

-- | Check whether the left term is more general than the right term
subsumes ::
  forall t m.
  (Show t, Show (Attr t), MonadUnify t m, Unifiable t, Eq (Attr t)) =>
  t ->
  t ->
  m (UnificationResult t)
subsumes t1 t2 = do
  oldState <- getUState @t
  let oldVars = getVars t2
  unified <- unify t1 t2
  maybeNewT2 <- applyBindings t2
  let res = case maybeNewT2 of
        Left v -> OccursFailure v t2
        Right newT2 -> do
          let newVars = getVars newT2
          case unified of
                Unified ->
                  if oldVars == newVars
                    then Unified
                    else SubsumptionFailure t1 t2
                r -> r
  putUState oldState
  pure res

-- | Like 'subsumes', but returns a boolean
subsumes_ ::
  (Show t, Show (Attr t), MonadUnify t m, Unifiable t, Eq (Attr t)) =>
  t ->
  t ->
  m Bool
subsumes_ x y = (== Unified) <$> subsumes x y
