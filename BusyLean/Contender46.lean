import BusyLean.Ordinal.RelUniverses
import BusyLean.Contender45

/-!
# Contender 46: universes of codes collapsed relative to the closure's operator

```
contender_46 := F46 (F46 42)
F46 n        := hier family45 (univTree46 (family45 n)) (family45 n)
```

Contenders 27-31 build universes of level codes, universe operators and
closure functionals of transfinite type. Until now they entered only through
`boost31`, which collapses with fixed ε-steps. `Ordinal.boost31J J Λ` collapses
the same universe **relative to `J`** (`U2.DNJ`). The first-class closure of the
metalanguages becomes

  `closeU N J t = lim (closeL N J t, boost31J J t, boost31J J (relLevelRounds J N t))`,

so programs can collapse universes relative to operators they build. The
self-based iteration `Θ` of Contender 45 is rerun with this closure, along
Contender 45's tree.

**Do not evaluate `contender_46`.**
-/

namespace BusyLean

/-- Contender 45's construction as a function of its input: `family45 42 = contender_45`. -/
def family45 (n : Nat) : Nat := F45 (F45 n)

/-- Contender 44's closure, plus universes collapsed relative to the operator. -/
def closeU (N : Nat) (J : Ordinal.CTree → Ordinal.CTree) (t : Ordinal.CTree) : Ordinal.CTree :=
  .lim fun i =>
    if i = 0 then closeL N J t
    else if i = 1 then Ordinal.boost31J J t
    else Ordinal.boost31J J (Ordinal.relLevelRounds J N t)

/-- Contender 45's self-based iteration, with the universe-collapsing closure. -/
def thetaU (N : Nat) : Ordinal.CTree → Ordinal.CTree → Ordinal.CTree
  | .zero => metaJump N
  | .succ a => fun t => Ordinal.metaBoostC (closeU N) t (thetaU N a) t
  | .lim f => fun t => .lim fun i => thetaU N (f i) t
  | .supL _ => metaJump N
  | .supH _ => metaJump N

/-- Contender 45's tree, with the universe-collapsing iteration to its height. -/
def univTree46 (N : Nat) : Ordinal.CTree :=
  .lim fun i => if i = 0 then thetaTree N else thetaU N (thetaTree N) (thetaTree N)

/-- The hierarchy along the tree, based on Contender 45's family. -/
def F46 (n : Nat) : Nat := Ordinal.hier family45 (univTree46 (family45 n)) (family45 n)

/-- **Contender 46.** Never evaluate it. -/
def contender_46 : Nat := F46 (F46 42)

end BusyLean
