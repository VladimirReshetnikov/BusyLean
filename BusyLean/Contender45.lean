import BusyLean.Contender44

/-!
# Contender 45: the construction as its own jump

```
contender_45 := F45 (F45 42)
F45 n        := hier family44 (thetaTree (family44 n)) (family44 n)
```

Contenders 40-44 build trees with operators over a **fixed** base, the
meta-jump. But each construction is itself an operator on trees:

  `Θ_{a+1}(t) = metaBoostC (closeL N) t Θ_a t`

stacks collapsing metalanguages to height `t` with base `Θ_a` and applies them
to `t`. So the whole previous construction is the base primitive of the next
one. `Θ_0` is the meta-jump, and limits are pointwise. `Θ` is iterated along
Contender 44's tree and applied to it.

**Do not evaluate `contender_45`.**
-/

namespace BusyLean

/-- Contender 44's construction as a function of its input: `family44 42 = contender_44`. -/
def family44 (n : Nat) : Nat := F44 (F44 n)

/-- The construction iterated along a tree, each stage the base of the next. -/
def theta (N : Nat) : Ordinal.CTree → Ordinal.CTree → Ordinal.CTree
  | .zero => metaJump N
  | .succ a => fun t => Ordinal.metaBoostC (closeL N) t (theta N a) t
  | .lim f => fun t => .lim fun i => theta N (f i) t
  | .supL _ => metaJump N
  | .supH _ => metaJump N

/-- Contender 44's tree, with the self-based construction iterated to its height. -/
def thetaTree (N : Nat) : Ordinal.CTree :=
  .lim fun i => if i = 0 then levelTree44 N else theta N (levelTree44 N) (levelTree44 N)

/-- The hierarchy along the tree, based on Contender 44's family. -/
def F45 (n : Nat) : Nat := Ordinal.hier family44 (thetaTree (family44 n)) (family44 n)

/-- **Contender 45.** Never evaluate it. -/
def contender_45 : Nat := F45 (F45 42)

end BusyLean
