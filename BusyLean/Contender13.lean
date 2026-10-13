import BusyLean.SystemFd.Candidates
import BusyLean.SystemFd.Church
import BusyLean.Contender12

/-!
# Contender 13: a predicative universe of operators

```
contender_13 := F13 (F13 42)      where   F13 := reflectFd family12
```

`reflectFd f n` exceeds `f n` and the value of every closed program of
**dynamic-kind System Fω** of enumeration depth `≤ n` with the Church
numeral type. The language extends kind-polymorphic Fω with a kind `dyn` of
operators of every dyn-free kind (`Σ k, Sem k`), type-level `pack` and
`unpack`, and kind quantification at two levels. Level-1 kind variables range
over kinds built from `dyn`, so programs can climb `dyn, dyn → ★, …` at run
time. Values are computed by erasing, normalizing (total by
`Fd.sn_of_typed`), and decoding.

The oracle is Contender 12's family `family12 n = F12 (F12 n)`.

**Do not evaluate `contender_13`.**
-/

namespace BusyLean.Fd

open Ty

/-- Kinds of enumeration depth `≤ n` (kind variables below `n`). -/
def kindsUpTo : Nat → List Kind
  | 0 => []
  | n + 1 =>
      let ks := kindsUpTo n
      Kind.star :: (Kind.dyn :: ((BigNumber.cross ks ks).map (fun p => Kind.arr p.1 p.2) ++
        ((BigNumber.natsUpTo n).map Kind.kvar ++ (BigNumber.natsUpTo n).map Kind.dvar)))

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
      (ts.map kall0 ++ (ts.map kall1 ++
      ((BigNumber.cross ks ts).map (fun p => pack p.1 p.2) ++
      (BigNumber.cross ks ts).map (fun p => unpack p.1 p.2))))))))

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
      (es.map CTm.klam0 ++
      ((BigNumber.cross es ks).map (fun p => CTm.kapp0 p.1 p.2) ++
      (es.map CTm.klam1 ++
      ((BigNumber.cross es ks).map (fun p => CTm.kapp1 p.1 p.2) ++
      [CTm.orc]))))))))

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

/-- Reflection over dynamic-kind System Fω with oracle `f`; the syntax budget
is also the fuel. -/
def reflectFd (f : Nat → Nat) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (f n) (BigNumber.maximum (fvalue f n) (ctmsUpTo n))

end BusyLean.Fd

namespace BusyLean

/-- Contender 12's construction as a function of its input: `family12 42 = contender_12`. -/
def family12 (n : Nat) : Nat := F12 (F12 n)

/-- Dynamic-kind Fω reflection over Contender 12's family. -/
def F13 (n : Nat) : Nat := Fd.reflectFd family12 n

/-- **Contender 13.** Never evaluate it. -/
def contender_13 : Nat := F13 (F13 42)

end BusyLean
