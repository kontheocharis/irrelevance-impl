-- Typing rules for the core primitives.
-- Relies on the "Atoms" module.
module Core.Primitives.Typing

import Data.DPair
import Common
import Decidable.Equality
import Data.Singleton
import Core.Base
import Core.Primitives.Definitions
import Core.Syntax
import Core.Evaluation
import Core.Metavariables
import Core.Unification
import Core.Primitives.Rules
import Core.Atoms
import Core.Combinators
import Core.Context
%hide Prelude.Interfaces.($>)

arg : {n : _} -> Annot ns -> (Singleton n, Annot ns)
arg e = (Val _, e)

argN : {m : _} -> (n : String) -> Annot ns -> (Singleton (m, n), Annot ns)
argN _ e = (Val _, e)

-- Typing rules for all the *native* primitives
-- 
-- Typing for the rest of the primitives is given in the prelude.
public export covering
primAnnot : Size ns => (p : Primitive k r PrimNative ar) -> Op ar ns
primAnnot PrimTYPE = ([], PrimTYPE $> [])
primAnnot PrimUNIT = ([], PrimTYPE $> [])
primAnnot PrimTT = ([], PrimUNIT $> [])
primAnnot PrimFIX = ([
      argN "A" $ PrimTYPE $> [],
      argN "a" $ (pi ((Explicit, Unres), "x") (v "A") (close idS $ v "A")).tm
    ],
    (v "A")
  )

-- The argument types for the given primitive
public export covering
0 PrimArgs : Primitive k r n ar -> (Ctx -> Type) -> Ctx -> Type
PrimArgs _ tm = Spine ar tm

-- Create a primitive expression with the given data.
public export covering
prim : Size ns => {k : PrimitiveClass} -> {r : PrimitiveReducibility}
  -> Primitive k r l ar
  -> Spine ar Atom ns
  -> Annot (ns ::< ar)
  -> Expr ns
prim @{s} p sp pRet =
  let ret = sub {sms = s + sp.count} (idS ::< sp) pRet in
  MkExpr (Choice (sPrim p sp.syn) (vPrim p sp.val)) ret

public export
data ForceTo : (tm : Ctx -> Type) -> (info : Ctx -> Type) -> Ctx -> Type where
  Matching : forall tm . info ns -> ForceTo tm info ns
  NonMatching : forall tm . tm ns -> ForceTo tm info ns