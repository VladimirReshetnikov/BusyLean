import BusyLean.SystemFk.Candidates
import BusyLean.SystemFk.Church
import BusyLean.Contender9

/-!
# Contender 10: kind polymorphism

```
contender_10 := F10 (F10 42)      where   F10 := reflectFk family9
```

`reflectFk f n` exceeds `f n` and the value of every closed Church-style
program of **kind-polymorphic System Fω** of enumeration depth `≤ n` with the
Church numeral type. Programs may quantify over kinds, so a single program can
iterate through kinds of unbounded order chosen at run time. Values are
computed by erasing, normalizing (total by `Fk.sn_of_typed`), and decoding.

The oracle is Contender 9's family `family9 n = F9 (F9 n)`.

**Do not evaluate `contender_10`.**
-/

namespace BusyLean.Fk

open Ty

/-- Kinds of enumeration depth `≤ n` (kind variables below `n`). -/
def kindsUpTo : Nat → List Kind
  | 0 => []
  | n + 1 =>
      let ks := kindsUpTo n
      Kind.star :: ((BigNumber.cross ks ks).map (fun p => Kind.arr p.1 p.2) ++
        (BigNumber.natsUpTo n).map Kind.kvar)

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
      ((BigNumber.cross ks (BigNumber.cross ts ts)).map (fun p => app p.1 p.2.1 p.2.2) ++
      ts.map kall))))

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
      (es.map CTm.klam ++
      ((BigNumber.cross es ks).map (fun p => CTm.kapp p.1 p.2) ++
      [CTm.orc]))))))

theorem sn_erase {f : Nat → Nat} {fuel : Nat} {t : CTm}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a program (type checked with `fuel`) relative to the oracle `f`. -/
def fvalue (f : Nat → Nat) (fuel : Nat) (t : CTm) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Reflection over kind-polymorphic System Fω with oracle `f`; the syntax
budget is also the fuel. -/
def reflectFk (f : Nat → Nat) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (f n) (BigNumber.maximum (fvalue f n) (ctmsUpTo n))

end BusyLean.Fk

namespace BusyLean

/-- Contender 9's construction as a function of its input: `family9 42 = contender_9`. -/
def family9 (n : Nat) : Nat := F9 (F9 n)

/-- Kind-polymorphic Fω reflection over Contender 9's family. -/
def F10 (n : Nat) : Nat := Fk.reflectFk family9 n

/-- **Contender 10.** Never evaluate it. -/
def contender_10 : Nat := F10 (F10 42)

end BusyLean
