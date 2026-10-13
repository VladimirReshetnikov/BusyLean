import BusyLean.SystemFL.Ladder
import BusyLean.SystemFL.Church
import BusyLean.Contender13

/-!
# Contender 14: the ladder of universes

```
contender_14 := F14 (F14 42)      where   F14 := reflectFL family13
```

`reflectFL f n` exceeds `f n` and the value of every closed program of the
**level-`n` ladder language** of enumeration depth `≤ n` with the Church
numeral type. The level-`ℓ` language is dynamic-kind Fω (Contender 13) with
`ℓ` extra atomic kinds `dyn₀, …, dyn_{ℓ-1}`. Atom `dyn_i` denotes the `dyn` of
the level-`i` language, and `apack`/`aunpack` move operators into and out of an
atom from the base kinds below it. All levels are strongly normalizing by
`FL.sn_of_typed (FL.Univ f ℓ)`, a single theorem for every universe. So the
reflection diagonalizes over the levels as well as the programs: no fixed
level keeps up with `F14`.

The oracle is Contender 13's family `family13 n = F13 (F13 n)`.

**Do not evaluate `contender_14`.**
-/

namespace BusyLean.FL

open Ty

variable {α : Type}

/-- Kinds of enumeration depth `≤ n` over the atoms `as`. -/
def kindsUpTo (as : List α) : Nat → List (Kind α)
  | 0 => []
  | n + 1 =>
      let ks := kindsUpTo as n
      Kind.star :: (Kind.dyn :: ((BigNumber.cross ks ks).map (fun p => Kind.arr p.1 p.2) ++
        ((BigNumber.natsUpTo n).map Kind.kvar ++ ((BigNumber.natsUpTo n).map Kind.dvar ++
        as.map Kind.atom))))

/-- Type constructors of enumeration depth `≤ n` over the atoms `as`. -/
def tysUpTo (as : List α) : Nat → List (Ty α)
  | 0 => []
  | n + 1 =>
      let ks := kindsUpTo as n
      let ts := tysUpTo as n
      (BigNumber.natsUpTo n).map tvar ++
      ((BigNumber.cross ts ts).map (fun p => arr p.1 p.2) ++
      ((BigNumber.cross ks ts).map (fun p => all p.1 p.2) ++
      ((BigNumber.cross ks ts).map (fun p => lam p.1 p.2) ++
      ((BigNumber.cross ks (BigNumber.cross ts ts)).map (fun p => app p.1 p.2.1 p.2.2) ++
      (ts.map kall0 ++ (ts.map kall1 ++
      ((BigNumber.cross ks ts).map (fun p => pack p.1 p.2) ++
      ((BigNumber.cross ks ts).map (fun p => unpack p.1 p.2) ++
      ((BigNumber.cross as (BigNumber.cross ks ts)).map (fun p => apack p.1 p.2.1 p.2.2) ++
      (BigNumber.cross as (BigNumber.cross ks ts)).map (fun p => aunpack p.1 p.2.1 p.2.2))))))))))

/-- Church-style programs of enumeration depth `≤ n` over the atoms `as`. -/
def ctmsUpTo (as : List α) : Nat → List (CTm α)
  | 0 => []
  | n + 1 =>
      let ks := kindsUpTo as n
      let ts := tysUpTo as n
      let es := ctmsUpTo as n
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

theorem sn_erase {f : Nat → Nat} (ℓ : Nat) {fuel : Nat} {t : CTm (Atom ℓ)}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (Univ f ℓ) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a level-`ℓ` program (type checked with `fuel`) relative to the oracle `f`. -/
def fvalue (ℓ : Nat) (f : Nat → Nat) (fuel : Nat) (t : CTm (Atom ℓ)) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase ℓ (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Level-`n` programs of depth `≤ n`. -/
def ladderUpTo (n : Nat) : List (CTm (Atom n)) := ctmsUpTo (Atom.all n) n

/-- Reflection over the ladder with oracle `f`; the syntax budget is also the
fuel and the level. -/
def reflectFL (f : Nat → Nat) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (f n) (BigNumber.maximum (fvalue n f n) (ladderUpTo n))

end BusyLean.FL

namespace BusyLean

/-- Contender 13's construction as a function of its input: `family13 42 = contender_13`. -/
def family13 (n : Nat) : Nat := F13 (F13 n)

/-- Ladder reflection over Contender 13's family. -/
def F14 (n : Nat) : Nat := FL.reflectFL family13 n

/-- **Contender 14.** Never evaluate it. -/
def contender_14 : Nat := F14 (F14 42)

end BusyLean
