module Core.Combinators

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
import Core.Context
import Utils

%hide Prelude.Interfaces.($>)

-- Annotation versions of syntax
-- All these should only be called on *well-typed terms!*

public export covering
matchOnNf : HasMetas m => Size ns => Scope bs Atom ns -> Atom ns -> m sm (Atom ns)
matchOnNf sc x = do
  x' <- resolve (glueAndMetaResolver <+> varResolver sc) x.val
  pure $ promote x'

public export covering
($>) : Size ns => {k : PrimitiveClass} -> {r : PrimitiveReducibility}
    -> Primitive k r na ar
    -> Spine ar Atom ns
    -> Atom ns
($>) p sp = Choice (sPrim p sp.syn) (vPrim p sp.val)

-- Language items

-- Create a metavariable atom.
public export covering
aMeta : Size ns => MetaVar -> Spine ar Atom ns -> Atom ns
aMeta m sp = promote $ SimpApps (ValMeta m $$ map (force . (.val)) sp)

-- Create a metavariable expression.
public export covering
meta : Size ns => MetaVar -> Spine ar Atom ns -> Annot ns -> Expr ns
meta m sp annot = MkExpr (aMeta m sp) annot

-- Create a fresh metavariable
public export covering
freshMetaAtom : HasMetas m => Context bs ns -> Maybe Name -> Mode -> m sm (Atom ns)
freshMetaAtom {ns = ns} ctx n md = do
  m <- newMeta n
  -- Get all the bound variables in the context, and apply them to the
  -- metavariable. This will later result in the metavariable being solved as a
  -- lambda of all these variables.
  pure $ aMeta m ctx.binds

-- Create a fresh metavariable
public export covering
freshMeta : HasMetas m => Context bs ns -> Maybe Name -> Mode -> Annot ns -> m sm (Expr ns)
freshMeta ctx n md annot = do -- @@Todo: use type
  m <- newMeta n
  -- Get all the bound variables in the context, and apply them to the
  -- metavariable. This will later result in the metavariable being solved as a
  -- lambda of all these variables.
  pure $ meta m ctx.binds annot
  
-- Create a lambda expression
public export covering
lam : Size ns
  => (piIdent : Ident)
  -> (lamIdent : Ident)
  -> (bindAnnot : AtomTy ns)
  -> (bodyAnnot : AtomBody piIdent ns)
  -> (body : AtomBody lamIdent ns)
  -> Expr ns
lam piIdent lamIdent bindTy bodyClosure body = MkExpr
  (promote $ sLam lamIdent body.open.syn)
  (promote $ vPi piIdent bindTy.val bodyClosure.val)
  
-- Create a universe type
public export covering
aType : Size ns => Annot ns
aType = promote type
  
-- Create a universe expression
public export covering
type : Size ns => Expr ns
type = MkExpr aType aType
          
-- Create a pi expression
public export covering
pi : Size ns
  =>(piIdent : Ident)
  -> (bindAnnot : AtomTy ns)
  -> (bodyAnnot : AtomBody piIdent ns)
  -> Expr ns
pi piIdent bindAnnot bodyAnnot = MkExpr (promote $ sPi piIdent bindAnnot.syn bodyAnnot.open.syn) (promote type)
    
public export
record PiData  (ns : Ctx) where
  constructor MkPiData
  resolvedPi : AtomTy ns
  piIdent : Ident
  a : Atom ns
  b : AtomBody piIdent ns

public export
data ForcePi : Ctx -> Type where
  -- Matching pi
  MatchingPi : PiData ns -> ForcePi ns
  -- Not a pi
  OtherwiseNotPi : AtomTy ns -> ForcePi ns

public export
data ForcePiAt : Ctx -> Type where
  -- Matching pi
  MatchingPiAt : PiData ns -> ForcePiAt ns
  -- Mismatching pi with the given stage
  MismatchingPiAt : PiData ns -> ForcePiAt ns
  -- Not a pi
  OtherwiseNotPiAt : AtomTy ns -> ForcePiAt ns

-- Given a `potentialPi`, try to force it to be a pi type
public export covering
forcePi : HasMetas m => Size ns => Scope bs Atom ns -> (potentialPi : AtomTy ns) -> m sm (ForcePi ns)
forcePi sc potentialPi
  = matchOnNf sc potentialPi >>= \a => case a.val of
    resolvedPi@(RigidBinding (Bound (BindPi (piIdiom, piName) a) b)) =>
      let
        piData = MkPiData (promote resolvedPi) (piIdiom, piName) (promote a) (promoteBody b)
      in pure $ MatchingPi piData
    v => pure $ OtherwiseNotPi (newVal v potentialPi)

-- Given a `potentialPi`, try to match it given that we expect something in
-- the kind given by `ident`. DOES NOT check modes.
public export covering
forcePiAt : HasMetas m => Size ns
  => Scope bs Atom ns
  -> (ident : Ident)
  -> (potentialPi : AtomTy ns)
  -> m sm (ForcePiAt ns)
forcePiAt sc ((kind, _), name) potentialPi = forcePi sc potentialPi >>= \case
  MatchingPi piData@(MkPiData resolvedPi ((piKind, piMode), piName) a b) =>
    pure $ case decEq piKind kind of
      Yes Refl => MatchingPiAt piData
      _ => MismatchingPiAt piData
  OtherwiseNotPi tm => pure $ OtherwiseNotPiAt tm
  
public export
data ForceLam : Ctx -> Type where
  MatchingLam : AtomBinder Callable n ns -> AtomBody n ns -> ForceLam ns
  OtherwiseNotLam : Atom ns -> ForceLam ns

-- Given a `potentialLam`, try to force it to be a lambda
public export covering
forceLam : HasMetas m => Size ns => Scope bs Atom ns -> (potentialLam : Atom ns) -> m sm (ForceLam ns)
forceLam sc potentialLam = matchOnNf sc potentialLam >>= \a => case a.val of
  CallableTm (Bound binder body) => pure $ MatchingLam (promoteBinder binder) (promoteBody body)
  -- @@Consider: Do we need to handle the glued stuff?
  v => pure $ OtherwiseNotLam (newVal v potentialLam)

-- Shorthand for pis.
public export covering
aPi : Size ns => (n : Ident) -> AtomTy ns -> AtomTy (ns :< n) -> Atom ns
aPi piIdent bindTy bodyTy = (pi piIdent bindTy (close idS bodyTy)).tm
          
-- Create a variable expression with the given index and annotation.
public export covering
var : Size ns => Idx ns -> Annot ns -> Expr ns
var idx annot = MkExpr (promote (varIdx idx)) annot

public export covering
apps : Size ns => Expr ns -> Spine ar Expr ns -> Annot ns -> Expr ns
apps f xs a = MkExpr (promote $ sApps f.tm.syn (map (.tm.syn) xs)) a

public export covering
internalLam : Size ns => (0 n : Ident) -> Atom (ns :< n) -> Atom ns
internalLam n body = promote (internalLam n body.syn)

-- @@Todo: Make this non-internal!
public export covering
internalLams : Size ns => (ar : Arity) -> Atom (ns ::< ar) -> Atom ns
internalLams [] body = body
internalLams (n :: xs) body = let body' = internalLams xs body in promote $ internalLam n body'.syn

-- @@Todo: Make this non-internal!
public export covering
fix : Size ns => Atom (ns :< n) -> Annot ns -> Atom ns
fix atom ty =
  (PrimFIX $> [(Val _, ty), (Val _, internalLam _ atom)])

-- Find a variable by its name in the context.
public export covering
v : Size ns => (n : String) -> {auto prf : In n ns} -> Atom ns
v n = promote (var n)

public export
data GatherPis : Arity -> Ctx -> Type where
  Gathered : (ar' : Arity) -> length ar' = length ar -> Tel ar' Annot ns -> Annot (ns ::< ar') -> GatherPis ar ns
  TooMany : (extra : Count ar) -> (under : Count ar') -> AtomTy (ns ::< ar') -> GatherPis ar ns

public export covering
gatherPis : HasMetas m => (sns : Size ns) => Scope bs Atom ns -> Annot ns -> (ar : Arity) -> m sm (GatherPis ar ns)
gatherPis sc x [] = pure $ Gathered [] Refl [] x
gatherPis sc x ar@(n :: ns) = forcePi sc x >>= \case
  MatchingPi (MkPiData resolvedPi piIdent a b) => gatherPis (lift {a = piIdent} sc) b.open ns >>= \case
    Gathered ar' p params ret => pure $ Gathered (piIdent :: ar') (cong S p) ((Val _, a) :: params) ret
    TooMany c u t => pure $ TooMany (CS ns.count) (CS u) t
  OtherwiseNotPi t => pure $ TooMany (CS ns.count) CZ t