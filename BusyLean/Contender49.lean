import BusyLean.Contender48
import BusyLean.ReflectionFacts

/-!
# Contender 49: impredicative reflection over the tree

```
contender_49 := F49 (F49 42)
F49 n        := hier (treeReflect family48 T) T N
                where N = family48 n, T = levelIterTree N
```

Since Contender 38 the trees have been turned into numbers by `hier`, one
fixed fast-growing hierarchy. System FT2 offers a much stronger reading.
Its programs of type `nat` see the tree as the oracle tree and recurse over it
into every type, impredicatively. Such programs can implement `hier` itself,
and also iterate along the tree at higher types, build impredicative
encodings over it, and diagonalize.

`treeReflect g T m` is `m + 1` plus the largest of `g m` and the values of all
FT2 programs of type `nat` and depth `<= m` with oracles `g` (numbers) and `T`
(the tree). Contender 49 runs `hier` along Contender 48's tree with this
reflection as its base.

**Do not evaluate `contender_49`.**
-/

namespace BusyLean.FT2

open Ordinal

/-- A closed program of type `nat` is strongly normalizing after erasure, for every oracle. -/
theorem sn_erase_nat {f : Orc} {t : CTm} (h : infer [] t = some Ty.nat) : SN f (erase t) :=
  sn_of_typed (infer_sound t h)

/-- The value of an FT2 program relative to the oracles `f`: the numeral its erasure
normalizes to, if it is a closed program of type `nat`; otherwise `0`. -/
def natValue (f : Orc) (t : CTm) : Nat :=
  match h : infer [] t with
  | some A =>
      if hA : A = Ty.nat then
        decode (nf f ⟨erase t, sn_erase_nat (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

end BusyLean.FT2

namespace BusyLean

/-- Reflection over System FT2 with the number oracle `g` and the oracle tree `T`. -/
def treeReflect (g : Nat → Nat) (T : Ordinal.CTree) (m : Nat) : Nat :=
  m + 1 + BigNumber.maxN (g m) (BigNumber.maximum (FT2.natValue ⟨g, T⟩) (FT2.ctmsUpTo m))

/-- Contender 48's construction as a function of its input: `family48 42 = contender_48`. -/
def family48 (n : Nat) : Nat := F48 (F48 n)

/-- The hierarchy along Contender 48's tree, based on FT2 reflection over that tree. -/
def F49 (n : Nat) : Nat :=
  Ordinal.hier (treeReflect family48 (levelIterTree (family48 n)))
    (levelIterTree (family48 n)) (family48 n)

/-- **Contender 49.** Never evaluate it. -/
def contender_49 : Nat := F49 (F49 42)

end BusyLean
