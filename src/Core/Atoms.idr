-- A representation of terms which lazily stores both syntax and values.
module Core.Atoms

import Data.DPair
import Common
import Decidable.Equality
import Data.Singleton
import Core.Base
import Utils
import Core.Primitives.Definitions
import Core.Syntax
import Core.Evaluation
import Core.Primitives.Rules

public export
record AnyDomain (tm : Domain -> Ctx -> Type) (ns : Ctx) where
  constructor Choice
  syn : Lazy (tm Syntax ns)
  val : Lazy (tm Value ns)
  
-- All syntactic presheaf related bounds
public export
0 Psh : (Domain -> Ctx -> Type) -> Type
Psh tm
  = (Eval (Term Value) (tm Syntax) (tm Value),
    Quote (tm Value) (tm Syntax),
    Weak (tm Value))
  
-- Promote a term or value to an `AnyDomain` type.
public export covering
promote : Psh tm
  => Size ns
  => {d : Domain}
  -> Lazy (tm d ns)
  -> AnyDomain tm ns
promote {d = Syntax} tm = Choice tm (eval id tm) 
promote {d = Value} val = Choice (quote val) val
  
public export
newSyn : tm Syntax ns -> AnyDomain tm ns -> AnyDomain tm ns
newSyn syn' (Choice syn val) = Choice syn' val

public export
newVal : tm Value ns -> AnyDomain tm ns -> AnyDomain tm ns
newVal val' (Choice syn val) = Choice syn val'
  
-- An atom is a term and a value at the same time.
public export
Atom : Ctx -> Type
Atom = AnyDomain Term

public export
AtomTy : Ctx -> Type
AtomTy = AnyDomain Term

namespace ValSpine
  public export
  (.val) : Spine ar (AnyDomain tm) ns -> Spine ar (tm Value) ns
  (.val) sp = map (force . (.val)) sp

  public export
  (.syn) : Spine ar (AnyDomain tm) ns -> Spine ar (tm Syntax) ns
  (.syn) sp = map (force . (.syn)) sp
  
  public export covering
  promoteSpine : Size ns => {d : _} -> Spine ar (Term d) ns -> Spine ar Atom ns
  promoteSpine sp = map (\x => promote x) sp

public export
(WeakSized (tm Syntax), Weak (tm Value)) => WeakSized (AnyDomain tm) where
  weakS e (Choice syn val) = Choice (weakS e syn) (weak e val)

public export covering
(WeakSized (tm Syntax), Vars (tm Value), Psh tm) => Vars (AnyDomain tm) where
  here = promote {tm = tm} here

public export
(EvalSized (over Value) (tm Syntax) (tm Value), Quote (tm Value) (tm Syntax))
  => EvalSized (AnyDomain over) (AnyDomain tm) (AnyDomain tm) where
  evalS env (Choice syn val) = let ev = delay (evalS (mapSub (force . (.val)) env) syn) in Choice (quote ev) ev
  
public export
(Relabel (tm Value), Relabel (tm Syntax)) => Relabel (AnyDomain tm) where
  relabel r (Choice syn val) = Choice (relabel r syn) (relabel r val)
  
public export
(Thin (tm Value), Thin (tm Syntax)) => Thin (AnyDomain tm) where
  thin r (Choice syn val) = Choice (thin r syn) (thin r val)
  
-- Atom binders
namespace AtomBinder
  public export
  0 AtomBinder : Reducibility -> Ident -> Ctx -> Type
  AtomBinder r = BinderShape r Atom
  
  public export covering
  promoteBinder : Size ns => {d : Domain} -> Binder r d n ns -> AtomBinder r n ns
  promoteBinder = mapBinder (\t => promote t)

-- Atom bodies
namespace AtomBody
  -- The atom version of a closure.
  public export
  AtomBody : Ident -> Ctx -> Type
  AtomBody n = AnyDomain (\d => Body d n)

  -- Turn a body into a term in an extended context.
  public export covering
  (.open) : Size ns => AtomBody n ns -> Atom (ns :< n')
  (.open) (Choice (Delayed s) (Closure env v)) = Choice (relabel (Change _ Id) s) (eval (lift env) v)

  public export covering
  close : Sub ns Atom ns -> Atom (ns :< n) -> AtomBody n ns
  close env t = Choice (Delayed t.syn) (Closure (mapSub (force . (.val)) env) t.syn)

  -- Promote a syntactical body to an `AtomBody`.
  public export covering
  promoteBody : Size ns
    => {d : Domain}
    -> Body d n ns
    -> AtomBody n ns
  promoteBody b = promote {tm = \d => Body d n} b
  
  -- Apply a body to an argument
  public export covering
  apply : Size ns => AtomBody n ns -> Atom ns -> Atom ns
  apply (Choice syn (Closure env v)) arg = promote (eval {val = Val} (env :< arg.val) v)

-- An annotation is a type and a stage
public export
Annot : Ctx -> Type
Annot = AtomTy

public export
record Expr (ns : Ctx) where
  constructor MkExpr
  tm : Atom ns
  annot : Annot ns
  
public export
tmL : Lens (Expr ns) (Atom ns)
tmL = MkLens (.tm) (\x, u => { tm := x } u)
  
public export
annotL : Lens (Expr ns) (Annot ns)
annotL = MkLens (.annot) (\x, u => { annot := x } u)

-- Operations
public export
Op : Arity -> Ctx -> Type
Op ar ns = (Tel ar Annot ns, Annot (ns ::< ar))
  
public export covering
Relabel Expr where
  relabel r (MkExpr t a) = MkExpr (relabel r t) (relabel r a)

public export covering
Thin Expr where
  thin r (MkExpr t a) = MkExpr (thin r t) (thin r a)

public export covering
WeakSized Expr where
  weakS e (MkExpr t a) = MkExpr (weakS e t) (weakS e a)

public export covering
EvalSized Atom Expr Expr where
  evalS env (MkExpr tm a) = MkExpr (evalS env tm) (evalS env a)

public export covering
Relabel (Op ar) where
  relabel r (a, b) = (relabel r a, relabel (keepMany r) b)

public export covering
Thin (Op ar) where
  thin r (a, b) = (thin r a, thin {sms = sms + a.count} {sns = sns + a.count} (keepMany r) b)
  
export covering
Show (Term Syntax ns) => Show (Atom ns) where
  show a = show a.syn
  
export covering
Show (Spine ar (Term Syntax) ns) => Show (Spine ar Atom ns) where
  show a = show a.syn