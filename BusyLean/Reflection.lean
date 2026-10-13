import BigNumber.Proofs

/-!
# Reflection over the W-language

The object language is proposal P5's (`BigNumber`): raw terms of System T
extended with W-types `W A` over *every* finite type `A` (so `W ℕ`, `W (W ℕ)`,
`W (ℕ → W ℕ)`, …), each with a recursor into every type. It is the strongest
object language among the five proposals.

This file adds three things on top of that language.

1. **Relativization to an oracle family.** P5's interpreter resolves variables
   by *oldest-first levels*. Evaluating a program in the one-element
   environment `[⟨ℕ → ℕ → ℕ, fs⟩]` therefore turns `var 0` into the oracle
   family `fs` inside every program, under any number of binders. The
   language and its enumeration stay unchanged.
2. **Reflection** `reflect fs n`: a strict upper bound for every oracle value
   `fs i n` with `i ≤ n` and for every program of enumeration depth `≤ n`
   evaluated with the oracle (the finite-maximum idea of Contender 5).
3. **Forest reflection along W-trees** `stage seed a`, by structural recursion
   on a tree `a : W ℕ`. At a node, the oracle family *is* the family of child
   stages. A program can therefore call any child at a dynamically computed
   index, and no information is lost by taking a pointwise maximum.

The index used by Contender 6 is in `BusyLean/Contender6.lean`.
-/

namespace BusyLean.W

open BigNumber (Ty Term Value Env WTree)

/-- A countable family of unary functions, presented as a binary function. -/
abbrev Family := Nat → Nat → Nat

/-- The object-language type of an oracle family. -/
def oracleTy : Ty := .arr .nat (.arr .nat .nat)

/-- The environment that binds the oracle family as the outermost variable. -/
def oracleEnv (fs : Family) : Env := [⟨oracleTy, fs⟩]

/-- Numerical value of a program relative to an oracle family. -/
def evalWith (fs : Family) (t : Term) : Nat :=
  match BigNumber.interpret (oracleEnv fs) t with
  | ⟨.nat, n⟩ => n
  | ⟨.arr _ _, _⟩ => 0
  | ⟨.wt _, _⟩ => 0

/-- `prefixMax g k = max (g 0, …, g k)`. -/
def prefixMax (g : Nat → Nat) : Nat → Nat
  | 0 => g 0
  | k + 1 => BigNumber.maxN (prefixMax g k) (g (k + 1))

/-- One reflection step: exceed every visible oracle value and every program of
enumeration depth `≤ n` that is run with the oracle. -/
def reflect (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (evalWith fs) (BigNumber.allTerms n))

/-- Forest reflection along a well-founded `ℕ`-branching tree. Leaves reflect
over `seed`; a node reflects over the family of its children's stages. -/
def stage (seed : Family) : WTree Nat → Nat → Nat
  | .leaf => reflect seed
  | .node f => reflect (fun i => stage seed (f i))

/-! ## Basic inequalities -/

theorem le_prefixMax (g : Nat → Nat) : ∀ {i k : Nat}, i ≤ k → g i ≤ prefixMax g k
  | _, 0, h => by rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | i, k + 1, h => by
      cases Nat.lt_or_eq_of_le h with
      | inl hlt =>
          exact Nat.le_trans (le_prefixMax g (Nat.le_of_lt_succ hlt))
            (BigNumber.le_maxN_left _ _)
      | inr heq => rw [heq]; exact BigNumber.le_maxN_right _ _

theorem le_maximum {α : Type} (f : α → Nat) {x : α} :
    ∀ {l : List α}, x ∈ l → f x ≤ BigNumber.maximum f l
  | _ :: _, .head _ => BigNumber.le_maxN_left _ _
  | y :: _, .tail _ h => Nat.le_trans (le_maximum f h) (BigNumber.le_maxN_right (f y) _)

/-- The core of reflection: a bound `m` on the reflected maximum is exceeded. -/
theorem lt_reflect {fs : Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN (prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (evalWith fs) (BigNumber.allTerms n))) :
    m < reflect fs n := by
  unfold reflect
  omega

/-- Every visible oracle value is exceeded. -/
theorem oracle_lt_reflect (fs : Family) {i n : Nat} (hi : i ≤ n) : fs i n < reflect fs n :=
  lt_reflect (Nat.le_trans (le_prefixMax (fun j => fs j n) hi) (BigNumber.le_maxN_left _ _))

/-- Every program of depth `≤ n`, run with the oracle, is exceeded. -/
theorem evalWith_lt_reflect (fs : Family) {n : Nat} {t : Term}
    (ht : t ∈ BigNumber.allTerms n) : evalWith fs t < reflect fs n :=
  lt_reflect (Nat.le_trans (le_maximum (evalWith fs) ht) (BigNumber.le_maxN_right _ _))

/-- The input itself is exceeded. -/
theorem input_lt_reflect (fs : Family) (n : Nat) : n < reflect fs n :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_add_right _ _)

/-- Each visible child stage is strictly exceeded by its parent. -/
theorem stage_child_lt (seed : Family) (f : Nat → WTree Nat) {i n : Nat} (hi : i ≤ n) :
    stage seed (f i) n < stage seed (.node f) n :=
  oracle_lt_reflect (fun j => stage seed (f j)) hi

/-- Every visible seed value is strictly exceeded at a leaf. -/
theorem seed_lt_stage_leaf (seed : Family) {i n : Nat} (hi : i ≤ n) :
    seed i n < stage seed .leaf n :=
  oracle_lt_reflect seed hi

end BusyLean.W
