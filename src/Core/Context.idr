-- General context utilities, precursor to typechecking
module Core.Context

import Utils
import Common
import Decidable.Equality
import Data.Singleton
import Data.String
import Data.DPair
import Data.Maybe
import Core.Base
import Core.Primitives.Definitions
import Core.Syntax
import Core.Evaluation
import Core.Primitives.Rules
import Core.Atoms

%default covering

-- Context for typechecking
public export
record Context (bs : Ctx) (ns : Ctx) where
  --            ^ bindings  ^ bindings + lets
  constructor MkContext
  -- All the identifiers in scope
  idents : Singleton ns
  -- All the bindings in scope
  bindIdents : Singleton bs
  -- The current context (types)
  con : Con AtomTy ns
  -- The definitions in the context
  scope : Scope bs Atom ns
  -- The bound variables in the context, in the form of a spine ready to be applied
  -- to a metavariable.
  binds : Spine (ctxToArity bs) AtomTy ns
  
public export
emptyContext : Context [<] [<]
emptyContext =
  MkContext (Val [<]) (Val [<]) [<] (MkScope SZ SZ [<]) []
 
-- A goal is a hole in a context.
public export
record Goal where
  constructor MkGoal
 
  {0 conNs : Ctx}

  -- The name of the goal hole, if given
  name : Maybe Name

  -- The actual hole term and its type
  hole : Expr conNs

  -- The context in which the goal exists
  ctx : Context bindNs conNs
  
public export
%hint
ctxSize : Context bs ns -> Size ns
ctxSize f = f.scope.sizeNames
  
public export
%hint
bindsSize : Context bs ns -> Size bs
bindsSize f = f.scope.sizeBinds

-- Find a name in the context
public export
lookup : Context bs ns -> Name -> Maybe (Idx ns)
lookup ctx n = findIdx ctx.idents n
  where
    findIdx : forall ns . Singleton ns -> Name -> Maybe (Idx ns)
    findIdx (Val [<]) n = Nothing
    findIdx (Val (ns :< (i, n'))) n = case n == n' of
      True => Just IZ
      False => do
        idx <- findIdx (Val ns) n
        pure $ IS idx

-- Add a binding with no value to the context.
public export
bind : (n : Ident) -> Annot ns -> Context bs ns -> Context (bs :< n) (ns :< n)
bind n ty (MkContext (Val idents) (Val bi) con defs bounds) =
  MkContext (Val (idents :< n)) (Val (bi :< n)) (con :< ty) (lift defs) (wkS bounds ++ [(Val _, here)])

-- Add a definition to the context.
public export
define : (n : Ident) -> Expr ns -> Context bs ns -> Context bs (ns :< n)
define n (MkExpr tm ty) (MkContext (Val idents) (Val bindIdents) con defs bounds) =
  MkContext (Val (idents :< n)) (Val bindIdents) (con :< ty) (defs :< tm) (wkS bounds)