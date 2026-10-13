import BusyLean.SystemFw.Candidates
import BusyLean.SystemFw.Church
import BusyLean.Contender7

/-!
# Contender 8: type operators (System Fω)

```
contender_8 := F8 (F8 42)      where   F8 := reflectFw family7
```

`reflectFw f n` exceeds `f n` and the value of every closed Church-style
System Fω program of enumeration depth `≤ n` with the Church numeral type.
Type checking uses `n` steps of type normalization per conversion, and
programs may call the oracle `orc`, interpreted as `f`. Values are computed
by erasing, normalizing (total by `Fw.sn_of_typed`), and decoding.

The oracle is Contender 7's family `family7 n = F7 (F7 n)` (so that
`family7 42` is Contender 7). Fω, with the strength of higher-order
arithmetic, can amplify System F's output.

**Do not evaluate `contender_8`.**
-/

namespace BusyLean.Fw

open Ty

/-- Kinds of enumeration depth `≤ n`. -/
def kindsUpTo : Nat → List Kind
  | 0 => []
  | n + 1 =>
      let ks := kindsUpTo n
      Kind.star :: (BigNumber.cross ks ks).map (fun p => Kind.arr p.1 p.2)

/-- Type constructors of enumeration depth `≤ n`. -/
def tysUpTo : Nat → List Ty
  | 0 => []
  | n + 1 =>
      let ks := kindsUpTo n
      let ts := tysUpTo n
      (BigNumber.natsUpTo n).map tvar ++
      ((BigNumber.cross ts ts).map (fun p => arr p.1 p.2) ++
      ((BigNumber.cross ks ts).map (fun p => all p.1 p.2) ++
      ((BigNumber.cross ks ts).map (fun p => lam p.1 p.2) ++
      (BigNumber.cross ks (BigNumber.cross ts ts)).map (fun p => app p.1 p.2.1 p.2.2))))

/-- Church-style Fω programs of enumeration depth `≤ n`. -/
def ctmsUpTo : Nat → List CTm
  | 0 => []
  | n + 1 =>
      let ks := kindsUpTo n
      let ts := tysUpTo n
      let es := ctmsUpTo n
      (BigNumber.natsUpTo n).map CTm.var ++
      ((BigNumber.cross ts es).map (fun p => CTm.lam p.1 p.2) ++
      ((BigNumber.cross es es).map (fun p => CTm.app p.1 p.2) ++
      ((BigNumber.cross ks es).map (fun p => CTm.tlam p.1 p.2) ++
      ((BigNumber.cross es ts).map (fun p => CTm.tapp p.1 p.2) ++
      [CTm.orc]))))

theorem sn_erase {f : Nat → Nat} {fuel : Nat} {t : CTm}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of an Fω program (type checked with `fuel`) relative to the oracle `f`. -/
def fvalue (f : Nat → Nat) (fuel : Nat) (t : CTm) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Reflection over System Fω with oracle `f`; the syntax budget is also the fuel. -/
def reflectFw (f : Nat → Nat) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (f n) (BigNumber.maximum (fvalue f n) (ctmsUpTo n))

end BusyLean.Fw

namespace BusyLean

/-- Contender 7's construction as a function of its input: `family7 42 = contender_7`. -/
def family7 (n : Nat) : Nat := F7 (F7 n)

/-- System Fω reflection over Contender 7's family. -/
def F8 (n : Nat) : Nat := Fw.reflectFw family7 n

/-- **Contender 8.** Never evaluate it. -/
def contender_8 : Nat := F8 (F8 42)

end BusyLean
