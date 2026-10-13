import BusyLean.Contender51

/-!
# Contender 52: languages over the iteration operators, stacked

```
contender_52 := F52 (F52 42)
F52 n        := hier (ladderReflect family51 T) T N
                where N = family51 n, T = stackTree N
```

`Ordinal.ptlLift P σ b t` closes an operator `b` under every program of the
language over the primitives `P` (plus `b`), applied to `t`. `ptlStack`
stacks these languages along a tree. Each successor level adds the previous
level's closure as a first-class primitive `lift : (tree → tree) → tree → tree`,
and limits are pointwise. With Contender 51's primitives (the seed, the
meta-jump, the universe-collapsing closure, and the iteration operators), the
stack runs to the height of Contender 51's tree, over the meta-jump.

**Do not evaluate `contender_52`.**
-/

namespace BusyLean

open Ordinal (CTree)

/-- Contender 51's construction as a function of its input: `family51 42 = contender_51`. -/
def family51 (n : Nat) : Nat := F51 (F51 n)

/-- Contender 51's tree, with languages over the iteration operators stacked to its height. -/
def stackTree (N : Nat) : CTree :=
  .lim fun i => if i = 0 then primTree N
    else Ordinal.ptlStack prims51 (primEnv51 N) (primTree N) (metaJump N) (primTree N)

/-- The hierarchy along the stacked tree, based on ladder reflection over it. -/
def F52 (n : Nat) : Nat :=
  Ordinal.hier (ladderReflect family51 (stackTree (family51 n))) (stackTree (family51 n)) (family51 n)

/-- **Contender 52.** Never evaluate it. -/
def contender_52 : Nat := F52 (F52 42)

end BusyLean
