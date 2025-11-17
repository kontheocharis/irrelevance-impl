module Common

import Decidable.Equality
import Decidable.Decidable
import Utils

-- A bound variable is either from an explicit or an implicit pi.
--
-- We remember this in the context.
public export
data PiKind = Explicit | Implicit
            
public export
Show PiKind where
  show Explicit = "explicit"
  show Implicit = "implicit"

public export
DecEq PiKind where
  decEq Explicit Explicit = Yes Refl
  decEq Implicit Implicit = Yes Refl
  decEq Explicit Implicit = No (\Refl impossible)
  decEq Implicit Explicit = No (\Refl impossible)

public export
Eq PiKind where
  a == b = isYes $ decEq a b

public export
Name : Type
Name = String
  
public export
data Mode = Zero | Unres

public export
DecEq Mode where
  decEq Zero Zero = Yes Refl
  decEq Unres Unres = Yes Refl
  decEq Zero Unres = No (\Refl impossible)
  decEq Unres Zero = No (\Refl impossible)

public export
Eq Mode where
  a == b = isYes $ decEq a b
          
public export
Ord Mode where
  compare Zero Zero = EQ
  compare Zero Unres = LT
  compare Unres Zero = GT
  compare Unres Unres = EQ
  
public export
(*) : Mode -> Mode -> Mode
(*) Zero m = Zero
(*) Unres m = m

public export
Show Mode where
  show Zero = "0"
  show Unres = "ω"
  
public export
showMode : Mode -> String
showMode Zero = "0 "
showMode Unres = ""

public export
Idiom : Type
Idiom = (PiKind, Mode)

-- A name is a member of a 'context skeleton'
public export
Ident : Type
Ident = (Idiom, Name)

-- automatic decidable equality check
decEqIdent : DecEq Ident
decEqIdent = %search

public export
[showIdent] Show Ident where
  show ((Explicit, m), n) = showMode m ++ n
  show ((Implicit, m), n) = "[" ++ showMode m ++ n ++ "]"