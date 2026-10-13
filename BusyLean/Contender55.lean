import BusyLean.Contender54

/-!
# Contender 55: number languages stacked along the tree

```
contender_55 := F55 (F55 42)
F55 n        := hier (numStack prims54 (primEnv54 N family54) T family54) T N
                where N = family54 n, T = stackTree N
```

Contender 54 closes a number oracle under every program over its primitives
(including reflection over program-built trees) once. Here those closures are
stacked along a tree, as `ptlStack` stacks the tree languages:

* `numLift P σ g` is `g` closed under every closed `nat` program over the
  primitives plus `g`;
* `numStack P σ (a+1)` is the closure for the language whose primitives also
  include level `a`'s closure as a first-class
  `lift : (nat → nat) → nat → nat`;
* limits take the maximum over the first `m+1` branches.

The stack runs along Contender 54's tree, and `hier` reads the tree with it.

**Do not evaluate `contender_55`.**
-/
namespace BusyLean.Ordinal

/-- The closure of a number function `g` under every closed `nat` program over the primitives
plus `g`: `m + 1` plus the largest of `g m` and those programs' values (size `≤ m`). -/
def numLift (P : List TL.Ty) (σ : TL.Env P) (g : Nat → Nat) (m : Nat) : Nat :=
  m + 1 + BigNumber.maxN (g m) (BigNumber.maximum id (PTL.natsUpTo (.arr .nat .nat :: P) (g, σ) m))

/-- The type of a closure operator on number functions, `(nat → nat) → nat → nat`. -/
def liftNTy : TL.Ty := .arr (.arr .nat .nat) (.arr .nat .nat)

/-- Number languages stacked along a tree: each successor level adds the previous level's
closure as a first-class primitive; limits take maxima over the first branches. -/
def numStack (P : List TL.Ty) (σ : TL.Env P) : CTree → (Nat → Nat) → Nat → Nat
  | .zero => numLift P σ
  | .succ a => numLift (liftNTy :: P) (numStack P σ a, σ)
  | .lim f => fun g m => maxUpTo (fun i => numStack P σ (f i) g m) m
  | .supL _ => numLift P σ
  | .supH _ => numLift P σ

end BusyLean.Ordinal

namespace BusyLean

/-- Contender 54's construction as a function of its input: `family54 42 = contender_54`. -/
def family54 (n : Nat) : Nat := F54 (F54 n)

/-- The hierarchy along Contender 52's stacked tree, based on number languages stacked along it. -/
def F55 (n : Nat) : Nat :=
  Ordinal.hier
    (Ordinal.numStack prims54 (primEnv54 (family54 n) family54) (stackTree (family54 n)) family54)
    (stackTree (family54 n)) (family54 n)

/-- **Contender 55.** Never evaluate it. -/
def contender_55 : Nat := F55 (F55 42)

end BusyLean
