import BusyLean.Contender47

/-!
# Contender 48: a tree-indexed hierarchy of iteration levels

```
contender_48 := F48 (F48 42)
F48 n        := hier family47 (levelIterTree (family47 n)) (family47 n)
```

Contender 45's `Θ` (`thetaFrom`, a base turned into an iteration along a tree)
and Contender 47's `Ψ` are the first two levels of a pattern. For any `Φ` that
turns a base into an iteration,

  `iterOf Φ B 0 = B`, `iterOf Φ B (a+1) t = Φ (iterOf Φ B a) t t`, limits pointwise,

iterates "run `Φ` from the previous stage". So `Ψ = iterOf thetaFrom metaJump`.
`iterLevel k` indexes these levels by a tree: level `0` is `thetaFrom`, level
`k+1` is `iterOf` of level `k`, and limit levels are pointwise limits. This is
a Veblen-style hierarchy of iteration operators. The level index, the
iteration height, and the argument are all Contender 47's tree.

**Do not evaluate `contender_48`.**
-/

namespace BusyLean

/-- Contender 47's construction as a function of its input: `family47 42 = contender_47`. -/
def family47 (n : Nat) : Nat := F47 (F47 n)

/-- Iterate "run `Φ` from the previous stage", starting from the base `B`. -/
def iterOf (Φ : (Ordinal.CTree → Ordinal.CTree) → Ordinal.CTree → Ordinal.CTree → Ordinal.CTree)
    (B : Ordinal.CTree → Ordinal.CTree) : Ordinal.CTree → Ordinal.CTree → Ordinal.CTree
  | .zero => B
  | .succ a => fun t => Φ (iterOf Φ B a) t t
  | .lim f => fun t => .lim fun i => iterOf Φ B (f i) t
  | .supL _ => B
  | .supH _ => B

/-- Iteration levels indexed by a tree: `thetaFrom`, then `iterOf` of the previous level. -/
def iterLevel (N : Nat) : Ordinal.CTree →
    (Ordinal.CTree → Ordinal.CTree) → Ordinal.CTree → Ordinal.CTree → Ordinal.CTree
  | .zero => thetaFrom N
  | .succ k => iterOf (iterLevel N k)
  | .lim f => fun B a t => .lim fun i => iterLevel N (f i) B a t
  | .supL _ => thetaFrom N
  | .supH _ => thetaFrom N

/-- Contender 47's tree, with the iteration hierarchy at level, height and argument equal to it. -/
def levelIterTree (N : Nat) : Ordinal.CTree :=
  .lim fun i => if i = 0 then psiTree N
    else iterLevel N (psiTree N) (metaJump N) (psiTree N) (psiTree N)

/-- The hierarchy along the tree, based on Contender 47's family. -/
def F48 (n : Nat) : Nat := Ordinal.hier family47 (levelIterTree (family47 n)) (family47 n)

/-- **Contender 48.** Never evaluate it. -/
def contender_48 : Nat := F48 (F48 42)

end BusyLean
