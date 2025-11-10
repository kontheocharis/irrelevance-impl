-- Defining the primitives in the language
module Core.Primitives.Definitions

import Data.Singleton
import Common
import Core.Base
import Decidable.Equality
import Data.Maybe
import Data.DPair
import Data.Hashable
import Utils

-- Primitives are either neutral or normal.
--
-- Neutral primitives might still be applied to other arguments after being fully
-- applied to their arity. For example,
--
-- ifThenElse : (A : Type) -> Bool -> A -> A -> A
--
-- is a primitive of arity 4, but could be applied to more than 2 arguments,
-- for example if we instantiate A with a function type:
--
-- Conversely, normal primitives can never be applied to more arguments than their
-- arity.
public export
data PrimitiveClass = PrimNeu | PrimNorm

-- Whether a primitive is reducible or not.
--
-- If it is reducible, it might have some computation rules depending on its arguments.
public export
data PrimitiveReducibility = PrimReducible | PrimIrreducible

-- Whether a primitive is native or declared in the prelude file.
public export
data PrimitiveLevel = PrimNative | PrimDeclared

-- The theory of primitives.
--
-- Consists of a list of operators, each of a specified arity. Equations are
-- given separately later (they are the reduction rules). Will also be given
-- proper types later.
public export
data Primitive : PrimitiveClass -> PrimitiveReducibility -> PrimitiveLevel -> Arity -> Type where
  PrimTYPE : Primitive PrimNorm PrimIrreducible PrimNative []
  PrimUNIT : Primitive PrimNorm PrimIrreducible PrimNative []
  PrimTT : Primitive PrimNorm PrimIrreducible PrimNative []
  PrimFIX : Primitive PrimNeu PrimReducible PrimNative [((Implicit, Zero), "A"), ((Explicit, Unres), "a")]

  PrimSIGMA : Primitive PrimNorm PrimIrreducible PrimDeclared [((Explicit, Zero), "A"), ((Explicit, Zero), "B")]
  PrimPAIR : Primitive PrimNorm PrimIrreducible PrimDeclared
    [((Implicit, Zero), "A"), ((Implicit, Zero), "B"), ((Explicit, Unres), "a"), ((Explicit, Unres), "b")]

-- Can't be DecEq without writing out all cases smh
export
primEq : (a : Primitive k r na ar) -> (b : Primitive k' r' na' ar') -> Maybe (a ~=~ b)
primEq PrimTYPE PrimTYPE = Just Refl
primEq PrimTYPE _ = Nothing
primEq PrimUNIT PrimUNIT = Just Refl
primEq PrimUNIT _ = Nothing
primEq PrimTT PrimTT = Just Refl
primEq PrimTT _ = Nothing
primEq PrimFIX PrimFIX = Just Refl
primEq PrimFIX _ = Nothing
primEq PrimSIGMA PrimSIGMA = Just Refl
primEq PrimSIGMA _ = Nothing
primEq PrimPAIR PrimPAIR = Just Refl
primEq PrimPAIR _ = Nothing

public export
primName : Primitive k r na ar -> String
primName PrimTYPE = "TYPE"
primName PrimUNIT = "UNIT"
primName PrimTT = "TT"
primName PrimFIX = "FIX"
primName PrimSIGMA = "SIGMA"
primName PrimPAIR = "PAIR"

public export
Eq (Primitive k r na ar) where
  (==) p p' = isJust $ primEq p p'

public export
record PrimitiveAnyIrr where
  constructor MkPrimitiveAnyIrr
  {0 classif : PrimitiveClass}
  {0 reducibility : PrimitiveReducibility}
  {0 level : PrimitiveLevel}
  {0 arity : Arity}
  primitive : Primitive classif reducibility level arity

public export
record PrimitiveAny where
  constructor MkPrimitiveAny
  {classif : PrimitiveClass}
  {reducibility : PrimitiveReducibility}
  {level : PrimitiveLevel}
  {arity : Arity}
  primitive : Primitive classif reducibility level arity

public export
Eq PrimitiveAnyIrr where
  (==) p p' = isJust $ primEq p.primitive p'.primitive
  
congPrimitive : {0 a, b : PrimitiveAnyIrr} -> a.primitive ~=~ b.primitive -> a = b
congPrimitive {a = MkPrimitiveAnyIrr _} {b = MkPrimitiveAnyIrr _} Refl = Refl

public export
SemiDecEq PrimitiveAnyIrr where
  semiDecEq p p' = case (primEq p.primitive p'.primitive) of
    Just p => Just (congPrimitive p)
    Nothing => Nothing

public export
Hashable PrimitiveAnyIrr where
  -- @@Optim: use integers!
  hashWithSalt s p = hashWithSalt s (primName p.primitive)
  
public export
Show (Primitive k r na ar) where
  show p = primName p

public export
nameToPrim : String -> Maybe PrimitiveAny
nameToPrim "TYPE"    = Just $ MkPrimitiveAny PrimTYPE
nameToPrim "UNIT"    = Just $ MkPrimitiveAny PrimUNIT
nameToPrim "TT"      = Just $ MkPrimitiveAny PrimTT
nameToPrim "FIX"     = Just $ MkPrimitiveAny PrimFIX
nameToPrim "SIGMA"   = Just $ MkPrimitiveAny PrimSIGMA
nameToPrim "PAIR"    = Just $ MkPrimitiveAny PrimPAIR
nameToPrim _         = Nothing

public export
nameToPrimId : {p : _} -> nameToPrim (primName p) === Just (MkPrimitiveAny p)
nameToPrimId {p = PrimTYPE}         = Refl
nameToPrimId {p = PrimUNIT}         = Refl
nameToPrimId {p = PrimTT}           = Refl
nameToPrimId {p = PrimFIX}          = Refl
nameToPrimId {p = PrimSIGMA}        = Refl
nameToPrimId {p = PrimPAIR}         = Refl
