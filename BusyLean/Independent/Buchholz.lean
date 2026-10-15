import BusyLean.Independent.EpsilonHardy

/-!
# Independent tower, rung 3: the Hardy hierarchy at the Takeuti–Feferman–Buchholz ordinal

This rung is an **ordinal-notation hierarchy** built on Buchholz's functions
`ψ_ν`, written as tree ordinals.

*Trees of level `m`.* `T m` is the type of trees with countable limits
`lim f` and limits `sup μ f` of cofinality `Ω_{μ+1}`. In `T (m + 1)`, a `sup`
branches over `T m`; the level `μ ≤ m` of the node is recorded, and only the
branches at (lifts of) trees of level `μ` matter. `T 0` has no meaningful
`sup`. Conversions between any two levels are one structural map `cmap` each
(`convFrom`, `convInto`).

*Trees of level `ω`.* A `sup μ m f` node of `TW` has cofinality `Ω_{μ+1}` and
branches over the trees of level `m`. `Ω_{n+1}` is the limit of all trees of
level `n` (`OmegaW n`), and `Ω_ω = lim_n Ω_{n+1}`.

*Buchholz's collapse.* `psiW α ν e = ψ_ν(α)`, computed at any level `e`, by
Buchholz's fundamental sequences:

* `ψ_ν(0) = Ω_ν` (with `Ω_0 = 1`);
* `ψ_ν(α + 1) = lim_k ψ_ν(α) · k`;
* `ψ_ν(lim f) = lim_k ψ_ν(f k)`;
* `ψ_ν(sup μ f) = sup_ξ ψ_ν(f ξ)` if `μ < ν`;
* `ψ_ν(sup μ f) = lim_k ψ_ν(f g_k)` if `μ ≥ ν`, where `g_0 = Ω_μ` and
  `g_{k+1} = ψ_μ(f g_k)`, computed at the level of the branches.

*The rung.* `ε_{Ω_ω+1} = lim (Ω_1, Ω_ω^{Ω_1}, Ω_ω^{Ω_ω^{Ω_1}}, …)`, and the
**Takeuti–Feferman–Buchholz ordinal** `θ = ψ_0(ε_{Ω_ω+1})` is the
proof-theoretic ordinal of `Π¹₁-CA + BI` and of `ID_ω`. `F3 n = H_θ(n)`.

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

/-- `g` iterated `k` times. -/
def iterate {α : Type} (g : α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => g (iterate g k x)

/-! ## The Takeuti–Feferman–Buchholz ordinal `ψ_0(ε_{Ω_ω+1})`

The collapse `psiW α ν e = ψ_ν(α)` lands in any level `e ≥ ν`. Its `sup` case
keeps the node when `μ < ν`, converting the branches from level `e - 1` to
level `m` (`supVia`), and otherwise diagonalizes with `g_0 = Ω_μ`,
`g_{k+1} = ψ_μ(α[g_k])`, computed at level `m`. -/

mutual

/-- From level `m` to level `j`: keep the `sup`s valid at level `j`. -/
def convFrom : (m j : Nat) → T m → T j
  | 0, 0 => Tr.cmap 0 (fun (n : Nat) => n)
  | 0, j + 1 => Tr.cmap 0 (fun (_ : T j) => (0 : Nat))
  | m + 1, 0 => Tr.cmap 0 (fun (_ : Nat) => (Tr.zero : T m))
  | m + 1, j + 1 => Tr.cmap (j + 1) (convInto m j)

/-- Into level `m` from level `j`. -/
def convInto : (m j : Nat) → T j → T m
  | 0, 0 => Tr.cmap 0 (fun (n : Nat) => n)
  | 0, j + 1 => Tr.cmap 0 (fun (_ : Nat) => (Tr.zero : T j))
  | m + 1, 0 => Tr.cmap 0 (fun (_ : T m) => (0 : Nat))
  | m + 1, j + 1 => Tr.cmap (m + 1) (convFrom m j)

end

/-- A `sup` with tag `μ` at level `e`, with branches given on level `j`. -/
def supVia : (e : Nat) → Nat → (j : Nat) → (T j → T e) → T e
  | 0, μ, _, _ => Tr.sup μ (fun _ => Tr.zero)
  | e + 1, μ, j, h => Tr.sup μ (fun y => h (convFrom e j y))

/-- `Ω_ν` at level `e`. -/
def omegaIn (e : Nat) : Nat → T e
  | 0 => .succ .zero
  | ν + 1 => supVia e ν e (fun x => x)

/-- Trees of level `ω`. -/
inductive TW where
  | zero : TW
  | succ : TW → TW
  | lim : (Nat → TW) → TW
  | sup : Nat → (m : Nat) → (T m → TW) → TW

/-- **Buchholz's collapse at level `ω`**: `psiW α ν e = ψ_ν(α)`, at level `e`. -/
def psiW : TW → Nat → (e : Nat) → T e
  | .zero => fun ν e => omegaIn e ν
  | .succ a => fun ν e => .lim fun k => Tr.mulNat (psiW a ν e) k
  | .lim f => fun ν e => .lim fun k => psiW (f k) ν e
  | .sup μ m f => fun ν e =>
      if μ < ν then supVia e μ m (fun x => psiW (f x) ν e)
      else .lim fun k => psiW (f (iterate (fun g => psiW (f g) μ m) k (omegaIn m μ))) ν e

/-- A `sup` of level `ω` whose branches are the branches of a tree of level `m`. -/
def supOfLevel : (m : Nat) → Nat → (P m → TW) → TW
  | 0, _, _ => .zero
  | m + 1, μ, h => .sup μ m h

/-- Trees of level `m` as trees of level `ω`. -/
def embW (m : Nat) : T m → TW
  | .zero => .zero
  | .succ a => .succ (embW m a)
  | .lim f => .lim fun i => embW m (f i)
  | .sup μ g => supOfLevel m μ fun z => embW m (g z)

namespace TW

def add (a : TW) : TW → TW
  | zero => a
  | succ b => succ (add a b)
  | lim f => lim fun i => add a (f i)
  | sup μ m f => sup μ m fun x => add a (f x)

def mul (a : TW) : TW → TW
  | zero => zero
  | succ b => add (mul a b) a
  | lim f => lim fun i => mul a (f i)
  | sup μ m f => sup μ m fun x => mul a (f x)

end TW

/-- `Ω_{n+1}`, the limit of all trees of level `n`. -/
def OmegaW (n : Nat) : TW := .sup n n (embW n)

/-- `Ω_ω = lim_n Ω_{n+1}`. -/
def OmegaOmega : TW := .lim OmegaW

/-- `Ω_ω^a`. -/
def opowW : TW → TW
  | .zero => .succ .zero
  | .succ a => TW.mul (opowW a) OmegaOmega
  | .lim f => .lim fun i => opowW (f i)
  | .sup μ m f => .sup μ m fun x => opowW (f x)

/-- `Ω_1, Ω_ω^{Ω_1}, Ω_ω^{Ω_ω^{Ω_1}}, …` -/
def towerW : Nat → TW
  | 0 => OmegaW 0
  | k + 1 => opowW (towerW k)

/-- `ε_{Ω_ω+1}`. -/
def epsW : TW := .lim towerW

/-- **The Takeuti–Feferman–Buchholz ordinal** `ψ_0(ε_{Ω_ω+1})`, as a Brouwer tree. -/
def thetaTFB : BTree := Tr.toB (psiW epsW 0 0)

end BusyLean.Indep.Buch

namespace BusyLean.Indep

/-- The Hardy hierarchy at the Takeuti–Feferman–Buchholz ordinal `ψ_0(ε_{Ω_ω+1})`. -/
def F3 (n : Nat) : Nat := Eps.hardy Buch.thetaTFB n

/-- **The ordinal rung**: `H_θ(H_θ(42))` for `θ = ψ_0(ε_{Ω_ω+1})`. Never evaluate it. -/
def contender_3 : Nat := F3 (F3 42)

end BusyLean.Indep
