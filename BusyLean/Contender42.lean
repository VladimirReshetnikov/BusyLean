import BusyLean.Ordinal.RelCollapse
import BusyLean.Contender41

/-!
# Contender 42: collapsing relative to the meta-jump

```
contender_42 := F42 (F42 42)
F42 n        := hier family41 (collapseTree (family41 n)) (family41 n)
```

Contenders 40 and 41 iterate the impredicative jumps with languages over
*countable* trees (System T over trees and P27's metalanguages). Predicative
collapse (`boost31`) entered only from outside, and never saw how the jump is
iterated. Here the collapse is relative to the strongest operator built so far,
the **meta-jump**

  `metaJump N t = lim (base41 N t, metaBoostT t (base41 N) t)`

(the ladder and System F jumps, under metalanguages stacked to the height of
`t`). `Ordinal.DJ` is Contender 25's Buchholz-style collapse with this
operator as its level-0 successor step. Every diagonal step of the collapse
re-enters level 0 and applies the meta-jump again. The argument is the
ε-iterates above `Ω_ω + T` for Contender 41's tree `T`.

**Do not evaluate `contender_42`.**
-/

namespace BusyLean

/-- Contender 41's construction as a function of its input: `family41 42 = contender_41`. -/
def family41 (n : Nat) : Nat := F41 (F41 n)

/-- The meta-jump: Contender 41's base, and metalanguages over it stacked to the height of `t`. -/
def metaJump (N : Nat) (t : Ordinal.CTree) : Ordinal.CTree :=
  .lim fun i => if i = 0 then base41 N t else Ordinal.metaBoostT t (base41 N) t

/-- Contender 41's tree, joined with its collapse relative to the meta-jump. -/
def collapseTree (N : Nat) : Ordinal.CTree :=
  .lim fun i => if i = 0 then readerTree N
    else Ordinal.relCollapse (metaJump N) N (readerTree N)

/-- The hierarchy along the collapsed tree, based on Contender 41's family. -/
def F42 (n : Nat) : Nat := Ordinal.hier family41 (collapseTree (family41 n)) (family41 n)

/-- **Contender 42.** Never evaluate it. -/
def contender_42 : Nat := F42 (F42 42)

end BusyLean
