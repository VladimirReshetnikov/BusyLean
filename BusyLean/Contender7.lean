import BusyLean.SystemF.Candidates
import BusyLean.SystemF.Church
import BusyLean.SystemF.Normalize
import BusyLean.Contender6

/-!
# Contender 7: impredicative polymorphism

```
contender_7 := F7 (F7 42)      where   F7 := reflectF finalFamily
```

`reflectF f n` exceeds `f n` and the value of every closed Church-style
System F program of enumeration depth `≤ n` that has the Church numeral type
`∀X. (X → X) → X → X`. Programs may use the oracle `orc : nat → nat`,
interpreted as `f`. A program's value is computed by erasing types,
normalizing (total because of `sn_of_typed`), and reading off the numeral.

The oracle is Contender 6's final family. System F programs can therefore
amplify it with the full strength of second-order arithmetic. The outer
application `F7 (F7 42)` runs System F at a syntax budget exceeding
Contender 6.

**Do not evaluate `contender_7`.**
-/

namespace BusyLean.F

open Ty

/-- Types of enumeration depth `≤ n` (type variables below `n`). -/
def tysUpTo : Nat → List Ty
  | 0 => []
  | n + 1 =>
      let ts := tysUpTo n
      (BigNumber.natsUpTo n).map tvar ++ ((BigNumber.cross ts ts).map (fun p => arr p.1 p.2) ++
        ts.map all)

/-- Church-style programs of enumeration depth `≤ n`. -/
def ctmsUpTo : Nat → List CTm
  | 0 => []
  | n + 1 =>
      let ts := tysUpTo n
      let es := ctmsUpTo n
      (BigNumber.natsUpTo n).map CTm.var ++
      ((BigNumber.cross ts es).map (fun p => CTm.lam p.1 p.2) ++
      ((BigNumber.cross es es).map (fun p => CTm.app p.1 p.2) ++
      (es.map CTm.tlam ++
      ((BigNumber.cross es ts).map (fun p => CTm.tapp p.1 p.2) ++
      [CTm.orc]))))

/-- A closed program of type `nat` is strongly normalizing after erasure. -/
theorem sn_erase {f : Nat → Nat} {t : CTm} (h : infer [] t = some Ty.nat) :
    SN f (erase t) :=
  sn_of_typed (infer_sound t h)

/-- The value of a program relative to the oracle `f`: the numeral its erasure
normalizes to, if it is a closed program of type `nat`; otherwise `0`. -/
def fvalue (f : Nat → Nat) (t : CTm) : Nat :=
  match h : infer [] t with
  | some A =>
      if hA : A = Ty.nat then
        decode (nf f ⟨erase t, sn_erase (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Reflection over System F with oracle `f`. -/
def reflectF (f : Nat → Nat) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (f n) (BigNumber.maximum (fvalue f) (ctmsUpTo n))

end BusyLean.F

namespace BusyLean

/-- System F reflection over Contender 6's family. -/
def F7 (n : Nat) : Nat := F.reflectF finalFamily n

/-- **Contender 7.** Never evaluate it. -/
def contender_7 : Nat := F7 (F7 42)

end BusyLean
