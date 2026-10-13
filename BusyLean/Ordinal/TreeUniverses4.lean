import BusyLean.Ordinal.TreeUniverses3

/-!
# Closure functionals of all finite types

`TreeUniverses3` iterates universe operators `Univ → Univ` and takes closure
points `Φ F`. Here the closure operation is lifted to all finite types:

* `A 0 = Univ`, `A (k+1) = A k → A k`, with pointwise unions at every type;
* `closure k f a = ⋃_m f^m a` for `f : A (k+1)`. So `closure 0` is `Φ`,
  `closure 1` closes `Φ`-like functionals under iteration, and so on;
* the chain `closure n (closure (n-1) (⋯ (closure 1 F₀)))` is applied to the
  base universe, where `F₀ = ΦT Λ` is Contender 29's tree-indexed operator.

Heuristically each type level adds a further layer of closure points: a
hierarchy of inaccessible-like universes of higher and higher type. Everything is
plain recursion in `Type 1`, with no axioms.
-/

namespace BusyLean.Ordinal

namespace U2

/-- Finite types over universes. -/
def A : Nat → Type 1
  | 0 => Univ
  | k + 1 => A k → A k

/-- Pointwise unions at every type. -/
def unionA : (k : Nat) → (Nat → A k) → A k
  | 0, s => Univ.union s
  | k + 1, s => fun a => unionA k fun m => s m a

/-- Iterates. -/
def iter {α : Type 1} (f : α → α) : Nat → α → α
  | 0, a => a
  | m + 1, a => f (iter f m a)

/-- Closure points at type `k+1`: the union of all iterates. -/
def closureA (k : Nat) (f : A (k + 1)) : A (k + 1) :=
  fun a => unionA k fun m => iter f m a

/-- The closure functionals: `W F₀ 0 = F₀`, `W F₀ (k+1) = closureA k`. -/
def W (F₀ : A 1) : (k : Nat) → A (k + 1)
  | 0 => F₀
  | k + 1 => closureA k

/-- Apply a type-`(k+1)` functional to the chain below it, down to type 1. -/
def applyDown (F₀ : A 1) : (k : Nat) → A (k + 1) → A 1
  | 0, x => x
  | k + 1, x => applyDown F₀ k (x (W F₀ k))

/-- The universe of type level `n` above the operator `F₀`. -/
def typeLevelUniv (F₀ : A 1) (n : Nat) : Univ := applyDown F₀ n (W F₀ n) Univ.base

end U2

/-- The tree of input `n`: collapse in the universe after the type-`n` closure chain
over Contender 29's operator `ΦT (operatorTree n)`. -/
def typeLevelTree (n : Nat) : CTree :=
  U2.universeTree (U2.typeLevelUniv (U2.ΦT (operatorTree n)) (n + 1))

end BusyLean.Ordinal
