import BusyLean.Independent.EpsilonHardy

/-!
# Independent tower, rung 3: the Hardy hierarchy along Buchholz's collapse

This rung is an **ordinal-notation hierarchy** built on Buchholz's functions
`ψ_ν`, written as tree ordinals.

*Trees of level `m`.* `T m` is the type of trees with countable limits
`lim f` and limits `sup μ f` of cofinality `Ω_{μ+1}`. In `T (m + 1)`, a `sup`
branches over `T m`; the level `μ ≤ m` of the node is recorded, and only the
branches at (lifts of) trees of level `μ` matter. `T 0` has no meaningful
`sup`. Lifting `T m → T (m + 1)` and projecting back are one structural map
`cmap` (`lift`, `proj`).

*Buchholz's collapse.* For a tree `α` of level `n + 1`, `psiAll n α ν` is
`ψ_ν(α)` as a tree of level `n`, for every `ν` at once, by Buchholz's
fundamental sequences:

* `ψ_ν(0) = Ω_ν` (with `Ω_0 = 1`);
* `ψ_ν(α + 1) = lim_k ψ_ν(α) · k`;
* `ψ_ν(lim f) = lim_k ψ_ν(f k)`;
* `ψ_ν(sup μ f) = sup_ξ ψ_ν(f ξ)` if `μ < ν`;
* `ψ_ν(sup μ f) = lim_k ψ_ν(f g_k)` if `μ ≥ ν`, where `g_0 = Ω_μ` and
  `g_{k+1} = ψ_μ(f g_k)`.

*The rung.* With `K = 42` levels, `ε_{Ω_K+1} = lim (Ω_1, Ω_K^{Ω_1},
Ω_K^{Ω_K^{Ω_1}}, …)`, `θ = ψ_0(ε_{Ω_K+1})`, and `F3 n = H_θ(n)`.

**Do not evaluate `contender_3`.**
-/

namespace BusyLean.Indep.Buch

open BusyLean.Indep.Eps (BTree hardy)

/-- Trees with countable limits and limits `sup μ f` (cofinality `Ω_{μ+1}`)
branching over `A`. -/
inductive Tr (A : Type) where
  | zero : Tr A
  | succ : Tr A → Tr A
  | lim : (Nat → Tr A) → Tr A
  | sup : Nat → (A → Tr A) → Tr A

/-- The branching type of level `m`. -/
@[reducible] def P : Nat → Type
  | 0 => Nat
  | m + 1 => Tr (P m)

/-- Trees of level `m`. -/
abbrev T (m : Nat) : Type := Tr (P m)

namespace Tr

variable {A B : Type}

/-- Rebuild a tree over a new branching type, keeping the `sup`s of level
`< thr` and replacing the others by `0`. -/
def cmap (thr : Nat) (h : B → A) : Tr A → Tr B
  | zero => zero
  | succ a => succ (cmap thr h a)
  | lim f => lim fun i => cmap thr h (f i)
  | sup μ f => if μ < thr then sup μ fun y => cmap thr h (f (h y)) else zero

/-- `a + b`, by recursion on `b`. -/
def add (a : Tr A) : Tr A → Tr A
  | zero => a
  | succ b => succ (add a b)
  | lim f => lim fun i => add a (f i)
  | sup μ f => sup μ fun x => add a (f x)

/-- `a · b`, by recursion on `b`. -/
def mul (a : Tr A) : Tr A → Tr A
  | zero => zero
  | succ b => add (mul a b) a
  | lim f => lim fun i => mul a (f i)
  | sup μ f => sup μ fun x => mul a (f x)

/-- `a · k` for a number `k`. -/
def mulNat (a : Tr A) : Nat → Tr A
  | 0 => zero
  | k + 1 => add (mulNat a k) a

/-- The Brouwer tree of a tree of level `0` (`sup`s become `0`). -/
def toB : Tr A → BTree
  | zero => .zero
  | succ a => .succ (toB a)
  | lim f => .lim fun i => toB (f i)
  | sup _ _ => .zero

end Tr

/-- Lifting `T m → T (m + 1)` and projecting `T (m + 1) → T m`. -/
def lp : (m : Nat) → (T m → T (m + 1)) × (T (m + 1) → T m)
  | 0 => (Tr.cmap 0 (fun _ => (0 : Nat)), Tr.cmap 0 (fun _ => .zero))
  | m + 1 => (Tr.cmap (m + 1) (lp m).2, Tr.cmap (m + 1) (lp m).1)

def lift (m : Nat) : T m → T (m + 1) := (lp m).1

def proj (m : Nat) : T (m + 1) → T m := (lp m).2

/-- Branches of a tree of level `n` as trees of level `n`. -/
def down : (n : Nat) → P n → T n
  | 0 => fun _ => .zero
  | n + 1 => lift n

/-- `Ω_ν` as a tree of level `n` (`Ω_0 = 1`). -/
def omega (n : Nat) : Nat → T n
  | 0 => .succ .zero
  | ν + 1 => .sup ν fun y => down n y

/-- `g` iterated `k` times. -/
def iterate {α : Type} (g : α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => g (iterate g k x)

/-- **Buchholz's collapse**: `psiAll n α ν = ψ_ν(α)` for `α` of level `n + 1`. -/
def psiAll (n : Nat) : T (n + 1) → Nat → T n
  | .zero => omega n
  | .succ a => fun ν => .lim fun k => Tr.mulNat (psiAll n a ν) k
  | .lim f => fun ν => .lim fun k => psiAll n (f k) ν
  | .sup μ f => fun ν =>
      if μ < ν then .sup μ fun y => psiAll n (f (down n y)) ν
      else .lim fun k => psiAll n (f (iterate (fun g => psiAll n (f g) μ) k (omega n μ))) ν

/-- `Ω_{n+1}` at the top level. -/
def OmegaTop (n : Nat) : T (n + 1) := .sup n fun y => lift n y

/-- `Ω_{n+1}^a` at the top level. -/
def opowTop (n : Nat) : T (n + 1) → T (n + 1)
  | .zero => .succ .zero
  | .succ a => .sup n fun b => Tr.mul (opowTop n a) (lift n b)
  | .lim f => .lim fun i => opowTop n (f i)
  | .sup μ f => .sup μ fun x => opowTop n (f x)

/-- `Ω_1, Ω_{n+1}^{Ω_1}, Ω_{n+1}^{Ω_{n+1}^{Ω_1}}, …` -/
def towerTop (n : Nat) : Nat → T (n + 1)
  | 0 => lift n (omega n 1)
  | k + 1 => opowTop n (towerTop n k)

/-- `ε_{Ω_{n+1}+1}`. -/
def epsTop (n : Nat) : T (n + 1) := .lim (towerTop n)

/-- `ψ_0(ε_{Ω_{n+1}+1})` as a Brouwer tree. -/
def theta (n : Nat) : BTree := Tr.toB (psiAll n (epsTop n) 0)

end BusyLean.Indep.Buch

namespace BusyLean.Indep

/-- The Hardy hierarchy at Buchholz's `ψ_0(ε_{Ω_42+1})`. -/
def F3 (n : Nat) : Nat := Eps.hardy (Buch.theta 41) n

/-- **The ordinal rung**: `H_θ(H_θ(42))` for `θ = ψ_0(ε_{Ω_42+1})`. Never evaluate it. -/
def contender_3 : Nat := F3 (F3 42)

end BusyLean.Indep
