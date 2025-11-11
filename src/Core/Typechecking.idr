-- Typechecking combinators for the core language.
module Core.Typechecking

import Utils
import Common
import Decidable.Equality
import Data.Singleton
import Data.DPair
import Data.Maybe
import Core.Base
import Core.Primitives.Definitions
import Core.Syntax
import Core.Evaluation
import Core.Primitives.Rules
import Core.Metavariables
import Core.Unification
import Core.Atoms
import Core.Combinators
import Core.Primitives.Typing
import Core.Context
import Debug.Trace

%default covering

-- Typechecking modes
public export
data TcMode : Type where
  -- Check against a type, produce an elaborated term
  Check : TcMode
  -- Infer to produce an elaborated term and type
  Infer : TcMode

-- Typechecking errors, context-aware
public export
data TcErrorAt : Ctx -> Type where
  WhenUnifying : Atom ns -> Atom ns -> Unification ns -> TcErrorAt ns
  WrongPiKind : PiKind -> AtomTy ns -> TcErrorAt ns
  CannotInferMode : TcErrorAt ns
  UnknownName : Name -> TcErrorAt ns
  TooManyApps : (less : Count ar) -> TcErrorAt ns
  TooFewApps : (more : Count ar) -> TcErrorAt ns
  NotAPi : (subj : AtomTy ns) -> (extra : Count ar) -> TcErrorAt ns
  PrimitiveNotFound : (name : Name) -> TcErrorAt ns
  PrimitiveWrongArity : (name : Name) -> TcErrorAt ns
  PrimitiveDeclsMustBeTopLevel : TcErrorAt ns

-- Packaging an error with its context
public export
record TcError where
  constructor MkTcError
  {0 bindNs : Ctx}
  {0 conNs : Ctx}
  -- The context in which the error occurred
  con : Context bindNs conNs
  -- The location of the error in the source file
  loc : Loc
  -- The error itself
  err : TcErrorAt conNs

export
(ns : Ctx) => ShowSyntax => Show (TcErrorAt ns) where
  show (WhenUnifying x y z) = "When unifying `\{show x}` with `\{show y}`: \{show z}"
  show (WrongPiKind mode ty) = "Wrong pi mode \{show mode} for type `\{show ty}`"
  show CannotInferMode = "Cannot infer mode"
  show (UnknownName name) = "Unknown name: `\{name}`"
  show (TooManyApps count) = "Too many applications (expected \{show count} fewer)"
  show (TooFewApps count) = "Too few applications (expected \{show count} more)"
  show (NotAPi subj extra) = "The type of the subject is `\{
      show subj
    }` but tried to apply it to \{
      show extra
    } argument(s), which is too many"
  show (PrimitiveNotFound prim) = "Primitive `\{prim}` does not exist"
  show (PrimitiveWrongArity prim) = "Primitive `\{prim}` has been declared with the wrong arity"
  show PrimitiveDeclsMustBeTopLevel = "Primitive declarations can only appear at the top level"
  
export
ShowSyntax => Show TcError where
  show (MkTcError con loc err) = let Val _ = con.idents in
      "Typechecking error at \{show loc}:\n\{show err}"

public export
Goals : Type
Goals = SnocList Goal

-- Typechecking has access to metas
public export
interface (Monad m, Dbg m, HasState Loc m, HasState Goals m) => HasTc m where
  
  -- Explicit instance of metas so that the resolution doesn't die..
  0 metasM : SolvingMode -> Type -> Type
  enterMetas : {sm : SolvingMode} -> metasM sm t -> m t
  metas : HasMetas metasM

  -- Throw a typechecking error
  tcError : forall a . Context bs ns -> TcErrorAt ns -> m a

  -- The signature of a declared primitive
  definedPrimAnnot : Primitive k r PrimDeclared ar -> m (Op ar [<])
  setDefinedPrimAnnot : Primitive k r PrimDeclared ar -> Op ar [<] -> m ()

-- Add a user goal
addGoal : HasTc m => Goal -> m ()
addGoal g = modify (:< g)

-- Get all the goals that have been seen
getGoals : HasTc m => m (SnocList Goal)
getGoals = get (SnocList Goal)
  
-- What inputs a TC operation takes, depending on mode
public export
data TcInput : TcMode -> Ctx -> Type where
  CheckInput : (s : Mode) -> Annot ms -> TcInput Check ms
                    -- this should be a deep maybe
  InferInput : (s : Maybe Mode) -> TcInput Infer ms
  
export
WeakSized (TcInput md) where
  weakS e (CheckInput s a) = CheckInput s (weakS e a)
  weakS e (InferInput s) = InferInput s
  
public export
(.mode) : TcInput md ns -> Maybe Mode
(.mode) (CheckInput s _) = Just s
(.mode) (InferInput s) = s
  
public export
0 weakPreservesMode : Size ns => Size ms
  => {e : Wk ns ms}
  -> {i : TcInput md ms}
  -> (weakS e i).mode = i.mode
weakPreservesMode {i = CheckInput s a} = Refl
weakPreservesMode {i = InferInput s} = Refl
  
-- Outputs are expressions corresponding to the inputs
public export
0 TcOutput : (md : TcMode) -> (ms : Ctx) -> TcInput md ms -> Type
TcOutput md ms i = Expr ms
  
-- This is the type over which we build the typechecking combinators.
--
-- `TcOp m md ns` is a typechecking operation in mode md.
--
-- It can be executed to produce an elaborated expression, depending on what `md` is.
public export
0 TcOp : (md : TcMode) -> (0 m : Type -> Type) -> Ctx -> Type
TcOp md m ms = (i : TcInput md ms) -> m (TcOutput md ms i)

-- Typechecking in any context
--
-- This is what is mostly used to work with, since a lot of the time we don't know which
-- context we will switch in ahead of time (due to things like inserted lambdas).
public export
0 TcAt : (md : TcMode) -> (0 m : Type -> Type) -> Type
TcAt md m = forall bs, ns . Context bs ns -> TcOp md m ns

-- Typechecking at any mode and context.
public export
0 Tc : (m : Type -> Type) -> Type
Tc m = (md : TcMode) -> TcAt md m

public export
atMode : HasTc m => (md : TcMode) -> Tc m -> TcAt md m
atMode md f = f md

-- Wrap a parametric monadic operation over Tc.
public export
wrap : HasTc m => (forall a . m a -> m a) -> Tc m -> Tc m
wrap f x Check = \ctx, as => f (x Check ctx as)
wrap f x Infer = \ctx, s => f (x Infer ctx s)

-- Run some operation after the given typechecking operation.
public export
modifyInputs : HasTc m => (forall bs, ns . Context bs ns -> Context bs ns) -> Tc m -> Tc m
modifyInputs f x Check = \ctx, as => x Check (f ctx) as
modifyInputs f x Infer = \ctx, s => x Infer (f ctx) s

-- Run some operation after the given typechecking operation.
public export
runAfter : HasTc m => (forall bs, ns . Context bs ns -> Expr ns -> m ()) -> Tc m -> Tc m
runAfter f x Check = \ctx, as => do
  y <- x Check ctx as
  f ctx y
  pure y
runAfter f x Infer = \ctx, s => do
  y <- x Infer ctx s
  f ctx y
  pure y
  
-- Run some operation before the given typechecking operation.
public export
runBefore : HasTc m => (forall bs, ns . Context bs ns -> m ()) -> Tc m -> Tc m
runBefore f x Check = \ctx, as => do
  f ctx
  x Check ctx as
runBefore f x Infer = \ctx, as => do
  f ctx
  x Infer ctx as

-- Some useful shorthands

-- This should probably never be used.
-- promoteWithoutDefs : Size ns -> {d : Domain} -> Term d ns -> Atom ns
-- promoteWithoutDefs s {d = Syntax} tm = Choice tm (eval id tm)
-- promoteWithoutDefs s {d = Value} val = Choice (quote val) val

solving : HasTc m => (forall m' . HasMetas m' => m' SolvingAllowed t) -> m t
solving @{tc} f = enterMetas (f {m' = metasM @{tc}} @{metas @{tc}})

reading : HasTc m => (forall m' . HasMetas m' => m' SolvingNotAllowed t) -> m t
reading @{tc} f = enterMetas (f {m' = metasM @{tc}} @{metas @{tc}})

-- Unify two values in the given context.
--
-- Succeeds if the unification says `AreSame`.
public export
unify : HasTc m => Context bs ns -> Atom ns -> Atom ns -> m ()
unify @{tc} ctx a b = do
  val : Unification _ <- solving (unify ctx.scope a b)
  case val of
    AreSame => pure ()
    failure => tcError ctx $ WhenUnifying a b failure

public export
areEqual : HasTc m => Context bs ns -> Atom ns -> Atom ns -> m (Unification ns)
areEqual @{tc} ctx a b = enterMetas
  (unify {sm = SolvingNotAllowed} @{metas} ctx.scope a b)

-- Ensure that the given `Maybe Stage` is `Just _`, eliminating with the
-- supplied method.
ensureKnownMode : HasTc m
  => (Context bs ns -> (s : Mode) -> m (Expr ns))
  -> Context bs ns
  -> (i : TcInput Infer ns)
  -> m (Expr ns)
ensureKnownMode f ctx (InferInput (Just s)) = f ctx s
ensureKnownMode f ctx (InferInput Nothing) = tcError ctx CannotInferMode

-- Insert all implicit applications in a type-directed manner, without regard
-- for what the expression is.
insertAll : HasTc m => Context bs ns -> m (Expr ns) -> m (Expr ns)
insertAll ctx mExpr = mExpr >>= insertAll' ctx
  where
    insertAll' : forall ns, m . HasTc m => Context bs ns -> Expr ns -> m (Expr ns)
    insertAll' ctx expr = do
      let (MkExpr tm ty) = expr
      reading (forcePi ctx.scope ty) >>= \case
        MatchingPi (MkPiData resolvedPi ((Implicit, md), piName) a b) => do
          subject <- reading (freshMeta ctx Nothing md a)
          let res = apps expr
                [(Val ((Implicit, md), piName), subject)]
                (apply b subject.tm)
          insertAll' ctx res  -- @@TODO: adjust?
        _ => pure $ MkExpr tm ty

-- Insert all implicit applications in a type-directed manner, unless the given expression is a
-- matching implicit lambda.
insert : (HasTc m) => Context bs ns -> m (Expr ns) -> m (Expr ns)
insert ctx mExpr = do
  expr@(MkExpr tm ty) <- mExpr
  reading (forceLam ctx.scope tm) >>= \case
    MatchingLam (BindLam ((Implicit, piMode), name)) body => pure expr
    _ => insertAll ctx (pure expr)

-- Force a typechecking operation to be in checking mode. This might involve unifying with an
-- inferred type.
public export
switch : HasTc m => TcAt Infer m -> Tc m
switch f Infer = f
switch f Check = \ctx, (CheckInput idiom annot) => do
  result <- insert ctx $ f ctx (InferInput (Just idiom))
  unify ctx annot result.annot
  pure result

-- Insert (some kind of an implicit) lambda from the given information.
--
-- This adds the binder to the subject and 'recurses', yielding a lambda with the
-- given Pi type.
insertLam : HasTc m => Context bs ns -> Mode
  -> (piIdent : Ident)
  -> (bindAnnot : Annot ns)
  -> (bodyAnnot : AtomBody piIdent ns)
  -> (subject : TcAt Check m)
  -> m (Expr ns)
insertLam ctx md piIdent bindAnnot bodyAnnot subject = do
  s <- subject
    (bind piIdent bindAnnot ctx)
    (CheckInput md bodyAnnot.open)
  pure $ lam piIdent piIdent bindAnnot bodyAnnot (close idS s.tm)
  
-- -- Check a spine against a telescope.
-- --
-- -- Returns the checked spine.
-- tcSpineExact : HasTc m
--   => Context bs ns
--   -> List (Ident, Tc m)
--   -> Tel ar Annot ns
--   -> m (Spine ar Expr ns)
-- tcSpineExact ctx [] [] = pure []
-- tcSpineExact ctx tms [] = tcError ctx (TooManyApps (map fst tms).count)
-- tcSpineExact ctx [] annots = tcError ctx (TooFewApps annots.count)
-- tcSpineExact ctx (((md, name), tm) :: tms) ((Val (piMd, piName), annot) :: annots) with (decEq md piMd)
--   tcSpineExact ctx (((md, name), tm) :: tms) ((Val (md, piName), annot) :: annots) | Yes Refl = do
--     -- use the term directly
--     tm' <- tm Check ctx (CheckInput (snd md) annot)
--     tms' <- tcSpineExact ctx tms (sub (idS :< tm'.tm) annots)
--     pure ((Val _, tm') :: tms')
--   tcSpineExact ctx ((((Explicit, md'), name), tm) :: tms) ((Val ((Implicit, md), piName), annot) :: annots) | No _ = do
--     -- insert application
--     tm' <- reading (freshMeta ctx Nothing md annot)
--     tms' <- tcSpineExact ctx ((((Explicit, md'), name), tm) :: tms) (sub (idS :< tm'.tm) annots)
--     pure ((Val _, tm') :: tms')
--   tcSpineExact ctx ((((Implicit, md'), name), tm) :: tms) ((Val ((Explicit, md), piName), annot) :: annots) | No _ = do
--     tcError ctx $ WrongPiKind Implicit annot
--   tcSpineExact ctx ((((Explicit, Zero), name), tm) :: tms) ((Val ((Explicit, Zero), piName), annot) :: annots) | No p = absurd $ p Refl
--   tcSpineExact ctx ((((Explicit, Unres), name), tm) :: tms) ((Val ((Explicit, Unres), piName), annot) :: annots) | No p = absurd $ p Refl
--   tcSpineExact ctx ((((Implicit, Zero), name), tm) :: tms) ((Val ((Implicit, Zero), piName), annot) :: annots) | No p = absurd $ p Refl
--   tcSpineExact ctx ((((Implicit, Unres), name), tm) :: tms) ((Val ((Implicit, Unres), piName), annot) :: annots) | No p = absurd $ p Refl

-- Check a spine against a type.
--
-- Ignores ALL modes in the spine.
--
-- Returns the checked spine and the result type.
tcSpine : HasTc m
  => Context bs ns
  -> List (Ident, Tc m)
  -> Annot ns
  -> m (ar ** (Annot ns, Spine ar Expr ns))
tcSpine ctx [] ann = pure ([] ** (ann, []))
tcSpine ctx allTms@((((kind, _), name), tm) :: tms) ann = reading (forcePi ctx.scope ann) >>= \case
  MatchingPi (MkPiData resolvedPi ((piKind, piMd), piName) a b) => case decEq kind piKind of
    Yes Refl => do
      -- use the term directly
      tm' <- tm Check ctx (CheckInput piMd a)
      (ar ** (ann', tms')) <- tcSpine ctx tms (apply b tm'.tm)
      pure (((kind, piMd), name) :: ar ** (ann', (Val _, tm') :: tms'))
    No p => case piKind of
      Explicit => case kind of
        Explicit => absurd $ p Refl
        Implicit => tcError ctx $ WrongPiKind Implicit ann
      Implicit => case kind of
        Explicit => do
          -- insert application
          tm' <- reading (freshMeta ctx Nothing piMd a)
          (ar ** (ann', tms')) <- tcSpine ctx allTms (apply b tm'.tm)
          pure (((piKind, piMd), piName) :: ar ** (ann', (Val _, tm') :: tms'))
        Implicit => absurd $ p Refl
  OtherwiseNotPi t => tcError ctx (TooManyApps (map fst tms).count)
  
-- -- Main combinators:

-- -- Introduce a metavariable
-- public export
-- tcMeta : HasTc m => {default Nothing name : Maybe Name} -> Tc m
-- tcMeta {name = name} Check = \ctx, (CheckInput _ annot) => do
--   mta <- reading (freshMeta ctx name annot)
--   whenJust name $ \n => addGoal (MkGoal (Just n) mta.p ctx)
--   pure mta
-- tcMeta {name = name} Infer = ensureKnownStage $ \ctx, stage => do
--   annot <- reading (freshMetaAnnot ctx stage Dyn) -- remember, sized < dyn
--   mta <- reading (freshMeta ctx name annot)
--   whenJust name $ \n => addGoal (MkGoal (Just n) mta.p ctx)
--   pure mta

-- -- Check a function type.
-- public export
-- tcPi : HasTc m
--   => Ident
--   -> Tc m
--   -> Tc m
--   -> Tc m
-- tcPi x a b = switch $ ensureKnownStage $ \ctx, stage => case stage of
--   -- @@Reconsider: Kovacs infers the stage from the domain if it is not given..
--   -- This is more annoying here because of byte metas, but also I am not
--   -- convinced that it is the right thing to do. It might lead to some weird elab results.
--   Mta => do
--     a' <- a Check ctx (CheckInput _ mtaA.f)
--     b' <- b Check (bind x (mta a'.tm).f.a ctx) (CheckInput _ mtaA.f)
--     pure $ pi Mta x (MkAnnotFor MtaSort a'.tm) (MkAnnotFor MtaSort (close idS b'.tm))
--   Obj => do
--     ba <- reading (freshMeta ctx Nothing layoutStaA.f)
--     bb <- reading (freshMeta ctx Nothing layoutStaA.f)
--     a' <- a Check ctx (CheckInput _ (objStaA ba.tm).f)
--     b' <- b Check (bind x (obj ba.tm a'.tm).a.f ctx) (CheckInput _ (wkS $ objStaA bb.tm).f)
--     pure $ pi Obj x
--       (MkAnnotFor (ObjSort Sized ba.tm) a'.tm)
--       (MkAnnotFor (ObjSort Sized bb.tm) (close idS b'.tm))

-- -- Check a lambda abstraction.
-- public export
-- tcLam : HasTc m
--   => (n : Ident)
--   -> (bindTy : Maybe (Tc m))
--   -> (body : Tc m)
--   -> Tc m
-- tcLam lamIdent bindTy body Check = \ctx, (CheckInput stage annot@(MkAnnotAt ty sort)) => do
--   reading (forcePiAt ctx.scope stage lamIdent ty) >>= \case
--     MatchingPiAt (MkPiData resolvedPi piIdent a b) => do
--       -- Pi matches
--       whenJust bindTy $ \bindTy' => do
--         MkExpr bindPi _ <- tcPi lamIdent bindTy' tcMeta Infer ctx (InferInput (Just stage))
--         unify ctx resolvedPi bindPi
--       body' <- body Check
--         (bind lamIdent (a.asAnnot) ctx)
--         (CheckInput _ (b.open.asAnnot))
--       pure $ lam stage piIdent lamIdent a b (close idS body'.tm)
--     MismatchingPiAt piStage (MkPiData resolvedPi piIdent a b) => case fst piIdent of
--       -- Wasn't the right kind of pi; if it was implicit, insert a lambda
--       Implicit => do
--         tm' <- insertLam ctx piStage piIdent a b (tcLam lamIdent bindTy body Check)
--         adjustStage ctx tm'.p stage
--       -- Otherwise, we have the wrong kind of pi.
--       _ => tcError ctx (WrongPiKind (fst piIdent) resolvedPi)
--     OtherwiseNotPiAt other => do
--       -- Otherwise try unify with a constructed pi
--       createdPi <- tcPi lamIdent tcMeta tcMeta Infer ctx (InferInput (Just stage))
--       unify ctx other createdPi.tm
--       tcLam lamIdent bindTy body Check ctx (CheckInput stage createdPi.a)
-- tcLam lamIdent bindTy body Infer = ensureKnownStage $ \ctx, stage => do
--   -- @@Reconsider: Same remark as for pis.
--   -- We have a stage, but no type, so just instantiate a meta..
--   annot <- reading (freshMetaAnnot ctx stage Sized)
--   tcLam lamIdent bindTy body Check ctx (CheckInput _ annot)

-- -- Check a variable, by looking up in the context
-- public export
-- tcVar : HasTc m => Name -> Tc m
-- tcVar n = switch $ \ctx, (InferInput stage') => case lookup ctx n of
--     Nothing => tcError ctx $ UnknownName n
--     Just idx => do
--       let tm = var idx (MkAnnotAt {s = ctx.stages.indexS idx}
--             (ctx.con.indexS idx)
--             (ctx.sorts.indexS idx))
--       adjustStageIfNeeded ctx tm.p stage'

-- -- Infer or switch a user-supplied hole
-- --
-- -- We should at least know the stage of the hole. User holes are added to the
-- -- list of goals, which can be displayed after typechecking.
-- public export
-- tcHole : HasTc m => Maybe Name -> Tc m
-- tcHole n = tcMeta {name = n}

-- -- Check an application
-- public export
-- tcApps : HasTc m
--   => Tc m
--   -> List (Ident, Tc m)
--   -> Tc m
-- tcApps subject args = switch $ \ctx, (InferInput reqStage) => do
--   subject'@(MkExpr _ fnAnnot) <- (.mp) <$> subject Infer ctx (InferInput reqStage)
--   (ar' ** (ret, args')) <- tcSpine ctx args fnAnnot
--   let result = apps subject' args' ret.f
--   adjustStageIfNeeded ctx result.p reqStage

-- -- Check a primitive
-- public export
-- tcPrimUser : HasTc m
--   => {ar : _}
--   -> {r : PrimitiveReducibility}
--   -> {k : PrimitiveClass}
--   -> {l : PrimitiveLevel}
--   -> Primitive k r l ar
--   -> List (Ident, Tc m)
--   -> Tc m
-- tcPrimUser p args = switch $ \ctx, (InferInput stage) => do
--   (pParams, pRet) : Op _ _ <- case l of
--     PrimNative => pure $ primAnnot p
--     PrimDeclared => do
--      (pParams, pRet) <- definedPrimAnnot p
--      pure (
--         sub {over = Atom} [<] pParams,
--         sub {sns = ctxSize ctx + ar.count} {sms = SZ + ar.count} (liftSMany [<]) pRet
--       )
--   sp <- tcSpineExact ctx args pParams
--   adjustStageIfNeeded ctx (prim p (map (.tm) sp) pRet) stage
  
-- -- Check a primitive
-- public export
-- tcPrim : HasTc m
--   => {ar : _}
--   -> {r : PrimitiveReducibility}
--   -> {k : PrimitiveClass}
--   -> {l : PrimitiveLevel}
--   -> Primitive k r l ar
--   -> DispList ar (Tc m)
--   -> Tc m
-- tcPrim p args = tcPrimUser p (dispToList args)
  
-- inferStageIfNone : HasTc m => Maybe Stage -> (Stage -> Tc m) -> Tc m
-- inferStageIfNone (Just s) m = m s
-- inferStageIfNone Nothing m = \md, ctx, inp => case inp of
--   CheckInput s _ => m s md ctx inp
--   InferInput (Just s) => m s md ctx inp
--   InferInput Nothing => tcError ctx CannotInferStage
  
-- -- Check a let statement.
-- public export
-- tcLet : HasTc m
--   => (name : Name)
--   -> (stage : Maybe Stage)
--   -> (ty : (Maybe (Tc m)))
--   -> (tm : Tc m)
--   -> (rest : Tc m)
--   -> Tc m
-- tcLet name stage ty tm rest = inferStageIfNone stage $ \stage, md, ctx, inp => do
--   let Val ns = ctx.idents
--   tm' : ExprAt stage ns <- case ty of
--     Just ty => do
--       tySort <- solving (freshSortData ctx stage Sized <&> .a)
--       ty' <- ty Check ctx (CheckInput stage tySort)
--       tm Check ctx (CheckInput stage ty'.a)
--     Nothing => tm Infer ctx (InferInput (Just stage))
--   rest' <- rest md (define (Explicit, name) tm' ctx) (wkS inp)
--   let result = sub @{evalExprAtMaybe} {sns = ctxSize ctx} {sms = SS $ ctxSize ctx} (idS :< tm'.tm) rest'
--   pure $ replace {p = \s => ExprAtMaybe s ns} weakPreservesStage result
  
-- -- Check a primitive declaration statement.
-- public export
-- tcPrimDecl : HasTc m
--   => (name : Name)
--   -> (stage : Maybe Stage)
--   -> (ty : Tc m)
--   -> (rest : Tc m)
--   -> Tc m
-- tcPrimDecl name stage ty rest = inferStageIfNone stage $ \stage, md, ctx, inp => do
--   -- Ensure we are in root scope, otherwise there might be bindings!
--   let SZ = ctx.scope.sizeBinds
--     | SS k => tcError ctx $ PrimitiveDeclsMustBeTopLevel
--   let Val ns = ctx.idents

--   -- Lookup the primitive
--   let Just (MkPrimitiveAny {arity = ar} {level = lvl} p) = nameToPrim name
--     | Nothing => tcError ctx $ PrimitiveNotFound name

--   -- Turn the type signature into an operation signature
--   tySort <- solving (freshSortData ctx stage Sized <&> .a)
--   ty' <- ty Check ctx (CheckInput stage tySort)
--   Gathered ar' _ params ret <- reading (gatherPis ctx.scope ty'.p.a ar)
--     | TooMany extra under p => tcError ctx $ NotAPi ty'.tm extra
--   let Yes Refl = decEq ar' ar
--     | No _ =>  tcError ctx $ PrimitiveWrongArity name

--   let arC = ar.count
--   let nsS = ctxSize ctx
--   let closing = ctx.scope.defs.asSub
--   let paramsClosed = sub closing params
--   let retClosed = sub {sms = nsS + arC} {sns = SZ + arC} (liftSMany closing) ret

--   -- Close the primitive with lambdas
--   let tmAtom : Atom [<] = internalLams ar
--           (prim @{SZ + arC} p (heres _)
--             (weakS {sz = SZ + arC + arC} {sz' = SZ + arC}
--               (dropManyAr arC Id) retClosed)).tm
--   let tm' : Expr [<] = MkExpr tmAtom (sub closing ty'.p.a)
                
--   -- If it is a declared primitive, save it to primitives
--   case lvl of
--     PrimDeclared => setDefinedPrimAnnot p (paramsClosed, retClosed)
--     PrimNative => pure ()

--   -- Thin it back to the names scope
--   let tmTh : Expr ns = thin ctx.scope.defs.inv tm'
--   rest' <- rest md (define (Explicit, name) tmTh.f ctx) (wkS inp)
--   let result = sub @{evalExprAtMaybe} {sns = nsS} {sms = SS nsS} (idS :< tmTh.tm) rest'
--   pure $ replace {p = \s => ExprAtMaybe s ns} weakPreservesStage result
  
-- -- Check a let-rec statement.
-- public export
-- tcLetRec : HasTc m
--   => (name : Name)
--   -> (stage : Maybe Stage)
--   -> (ty : (Tc m))
--   -> (tm : Tc m)
--   -> (rest : Tc m)
--   -> Tc m
-- tcLetRec name stage ty tm rest = inferStageIfNone stage $ \stage, md, ctx, inp => do
--   let Val ns = ctx.idents
--   let Val bs = ctx.bindIdents
--   tySortData <- solving (freshSortData ctx stage Sized)
--   let tySort = tySortData.a
--   ty' <- ty Check ctx (CheckInput stage tySort)
--   let n = (Explicit, name)
--   let ctx' : Context (bs :< n) (ns :< n)
--       ctx' = bind n ty'.a ctx
--   tm' : ExprAt stage (ns :< n) <- tm Check ctx' (CheckInput stage (wkS ty'.a))
--   let fixTm : Atom ns = fix stage tm'.tm (MkAnnotFor tySortData ty'.tm)
--   rest' <- rest md (define n (MkExpr fixTm ty'.a) ctx) (wkS inp)
--   let result = sub @{evalExprAtMaybe} {sns = ctxSize ctx} {sms = SS $ ctxSize ctx} (idS :< fixTm) rest'
--   pure $ replace {p = \s => ExprAtMaybe s ns} weakPreservesStage result