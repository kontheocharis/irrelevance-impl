-- All the declarative reduction rules for primitives.
module Core.Primitives.Rules

import Data.Singleton
import Common
import Core.Base
import Core.Primitives.Definitions
import Core.Syntax
import Core.Evaluation
import Debug.Trace
import Utils

%default covering

-- Some shorthands

-- Type of types.
public export
type : Ty ns
type = SynPrimNormal (PrimTYPE $$ [])

-- Reduction rules:

-- Note: for every primitive that might reduce on an argument, in addition to
-- matching the the actual shape that it reduces on, we must also match on
-- (Glued _). We must do this for each argument that might cause a reduction. In
-- each case we must form a new glued term as a result, which lazily unfolds the
-- argument and recurses.

primApps : Primitive k PrimReducible na ar -> Spine ar (Term Value) ns -> Maybe (Term Value ns)
primApps' : {k : _} -> Primitive k PrimReducible na ar -> Spine ar (Term Value) ns -> Term Value ns

public export
Eval (Term Value) (PrimitiveApplied k Syntax e) (Term Value) where
  eval env (($$) {r = PrimIrreducible} {k = PrimNorm} p sp) = SimpPrimNormal (SimpApplied p (eval env sp))
  eval env (($$) {r = PrimIrreducible} {k = PrimNeu} p sp) = SimpApps (PrimNeutral (SimpApplied p (eval env sp)) $$ [])
  eval env (($$) {r = PrimReducible} x sp) = primApps' x (eval env sp)

primApps PrimFIX sp@[_, (_, x)] =
  let wrap = \s : Lazy (Val ns) => Glued (LazyApps (PrimNeutral (LazyApplied PrimFIX sp s) $$ []) s) in
  let simplified : Lazy (Val ns)
      simplified = delay $ apps x [(Val ((Explicit, Unres), "x"), wrap simplified)]
  in Just (wrap simplified)

primApps' p sp = case primApps p sp of
  Just r => r
  Nothing => case k of
    PrimNorm => SimpPrimNormal (SimpApplied p sp)
    PrimNeu => SimpApps (PrimNeutral (SimpApplied p sp) $$ [])

-- Context-aware domain
-- 
-- This is so that operations can be generic over the domain. However,
-- to do this we need the size of the context to be known when the domain is
-- a value, so that we can eval/quote freely.
public export
data DomainIn : Domain -> Ctx -> Type where
  SyntaxIn : DomainIn Syntax ns
  ValueIn : Size ns -> DomainIn Value ns

-- Create a primitive value
--
-- Always calls eval if the primitive is reducible, to wrap it in lazy if needed.
public export covering
vPrim : Size ns => {k : PrimitiveClass} -> {r : PrimitiveReducibility} -> Primitive k r na ar -> Spine ar Val ns -> Val ns
vPrim {k = PrimNorm} {r = PrimIrreducible} p sp = SimpPrimNormal (SimpApplied p sp)
vPrim {k = PrimNeu} {r = PrimIrreducible} p sp = SimpApps (PrimNeutral (SimpApplied p sp) $$ [])
vPrim {r = PrimReducible} p sp = eval id $ sPrim p (quote sp)

export
primResolver : Monad m => Resolver m (Val ns)
primResolver = repeatedly $ \case
  (SimpApps ((PrimNeutral (SimpApplied {r = PrimReducible} p sp)) $$ sp')) => pure $ apps <$> primApps p sp <*> pure sp'
  (SimpPrimNormal (SimpApplied {r = PrimReducible} p sp)) => pure $ primApps p sp
  _ => pure Nothing