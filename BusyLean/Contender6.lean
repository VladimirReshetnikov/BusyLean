import BusyLean.Reflection

/-!
# Contender 6

```
contender_6 := stage p5Family index 42
```

* `stage` is forest reflection over P5's W-language (`BusyLean/Reflection.lean`).
* `index` is the join of **every tree `W ℕ` that a closed program of the
  W-language defines**: its `k`-th child joins, in enumeration order, the trees
  denoted by all programs of enumeration depth `≤ k`. The reflection hierarchy
  then runs along the language's *own* ordinals, rather than along an
  explicit notation system as in P1–P4.
* `p5Family` is the family of P5's proposed number (`BigNumber.iterate
  BigNumber.diagonal n n`). With it as seed, the comparison with P5 is a theorem
  (`p5_lt_contender_6`) and not only an ordinal estimate.

Informal size: with |L| ≈ ψ(Ω_ω) the W-language's ordinal, P5 is about
f_{|L|+ω²}(42), while `contender_6` is about f_{|L|·|L|}(42). See the README.

**Do not evaluate `contender_6`.**
-/

namespace BusyLean

open BigNumber (Term WTree)
open BusyLean.W

/-- The `W ℕ` tree denoted by a closed program (`leaf` if it denotes no tree;
the conversion is P5's own cast). -/
def defTree (t : Term) : WTree Nat :=
  BigNumber.castValue (.wt .nat) (BigNumber.interpret [] t).2

/-- The `i`-th list element, or a default value. -/
def nthD {α : Type} : List α → Nat → α → α
  | [], _, d => d
  | x :: _, 0, _ => x
  | _ :: xs, i + 1, d => nthD xs i d

/-- Join of the trees defined by all programs of enumeration depth `≤ k`. -/
def treesOfDepth (k : Nat) : WTree Nat :=
  .node fun i => defTree (nthD (BigNumber.allTerms k) i .zero)

/-- Join of all trees the W-language defines. -/
def index : WTree Nat := .node treesOfDepth

/-- The seed family: P5's proposed number, as a function of its input. -/
def p5Family : Family := fun _ n => BigNumber.iterate BigNumber.diagonal n n

/-- The reflection hierarchy along `index`. -/
def finalFamily (n : Nat) : Nat := stage p5Family index n

/-- **Contender 6.** Never evaluate it. -/
def contender_6 : Nat := finalFamily 42

end BusyLean
