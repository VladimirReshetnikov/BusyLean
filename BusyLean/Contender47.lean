import BusyLean.Contender46

/-!
# Contender 47: iterating the self-based iteration

```
contender_47 := F47 (F47 42)
F47 n        := hier family46 (psiTree (family46 n)) (family46 n)
```

Contender 45's `Θ` starts from the meta-jump and makes each stage the base of
the next. `thetaFrom B` is the same iteration started from an arbitrary base
`B`, with Contender 46's universe-collapsing closure. The whole iteration is
again an operator on trees, so it can be iterated:

  `Ψ_0 = metaJump`, `Ψ_{a+1}(t) = thetaFrom Ψ_a t t`, limits pointwise.

`Ψ_{a+1}` iterates `Θ` along its argument, starting from the whole `Ψ_a`.
`Ψ` is iterated along Contender 46's tree.

**Do not evaluate `contender_47`.**
-/

namespace BusyLean

/-- Contender 46's construction as a function of its input: `family46 42 = contender_46`. -/
def family46 (n : Nat) : Nat := F46 (F46 n)

/-- Contender 46's self-based iteration, started from the base `B`. -/
def thetaFrom (N : Nat) (B : Ordinal.CTree → Ordinal.CTree) :
    Ordinal.CTree → Ordinal.CTree → Ordinal.CTree
  | .zero => B
  | .succ a => fun t => Ordinal.metaBoostC (closeU N) t (thetaFrom N B a) t
  | .lim f => fun t => .lim fun i => thetaFrom N B (f i) t
  | .supL _ => B
  | .supH _ => B

/-- The iteration of iterations. -/
def psi (N : Nat) : Ordinal.CTree → Ordinal.CTree → Ordinal.CTree
  | .zero => metaJump N
  | .succ a => fun t => thetaFrom N (psi N a) t t
  | .lim f => fun t => .lim fun i => psi N (f i) t
  | .supL _ => metaJump N
  | .supH _ => metaJump N

/-- Contender 46's tree, with `Ψ` iterated to its height. -/
def psiTree (N : Nat) : Ordinal.CTree :=
  .lim fun i => if i = 0 then univTree46 N else psi N (univTree46 N) (univTree46 N)

/-- The hierarchy along the tree, based on Contender 46's family. -/
def F47 (n : Nat) : Nat := Ordinal.hier family46 (psiTree (family46 n)) (family46 n)

/-- **Contender 47.** Never evaluate it. -/
def contender_47 : Nat := F47 (F47 42)

end BusyLean
