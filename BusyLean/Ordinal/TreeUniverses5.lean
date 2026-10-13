import BusyLean.Ordinal.TreeUniverses4

/-!
# Closure functionals of transfinite type

`TreeUniverses4` lifts closure points to the finite types `A k`. Here the
types are indexed by countable tree ordinals:

* `AT 0 = Univ`, `AT (a+1) = AT a → AT a`, `AT (lim f) = (i : ℕ) → AT (f i)`;
* unions are pointwise, and `closureT a g x = ⋃_m g^m x` at successor types;
* `step a : AT (a+1)` is a canonical functional: `step 0 = F₀`,
  `step (b+1) = closureT b`, and componentwise at limits;
* `evalDown a : AT a → Univ` applies a functional to the canonical chain below
  it, down to a universe.

The type level is itself a collapsed tree: at input `n` it is Contender 30's
`typeLevelTree n`. Everything is structural recursion, with no axioms.
-/

namespace BusyLean.Ordinal

namespace U2

/-- Types over universes indexed by tree ordinals. -/
def AT : CTree → Type 1
  | .zero => Univ
  | .succ a => AT a → AT a
  | .lim f => (i : Nat) → AT (f i)
  | .supL _ => Univ
  | .supH _ => Univ

/-- Pointwise unions at every type. -/
def unionAT : (a : CTree) → (Nat → AT a) → AT a
  | .zero, s => Univ.union s
  | .succ a, s => fun x => unionAT a fun m => s m x
  | .lim f, s => fun i => unionAT (f i) fun m => s m i
  | .supL _, s => Univ.union s
  | .supH _, s => Univ.union s

/-- Closure points at a successor type. -/
def closureT (a : CTree) (g : AT (.succ a)) : AT (.succ a) :=
  fun x => unionAT a fun m => iter g m x

/-- Canonical functionals: `step 0 = F₀`, `step (b+1) = closureT b`, componentwise at limits. -/
def step (F₀ : Univ → Univ) : (a : CTree) → AT (.succ a)
  | .zero => F₀
  | .succ b => closureT b
  | .lim f => fun h i => step F₀ (f i) (h i)
  | .supL _ => F₀
  | .supH _ => F₀

/-- Canonical elements of every type. -/
def canon (F₀ : Univ → Univ) : (a : CTree) → AT a
  | .zero => Univ.base
  | .succ a => step F₀ a
  | .lim f => fun i => canon F₀ (f i)
  | .supL _ => Univ.base
  | .supH _ => Univ.base

/-- Evaluate down to a universe along the canonical chain. -/
def evalDown (F₀ : Univ → Univ) : (a : CTree) → AT a → Univ
  | .zero, U => U
  | .succ a, g => evalDown F₀ a (g (canon F₀ a))
  | .lim f, h => Univ.union fun i => evalDown F₀ (f i) (h i)
  | .supL _, U => U
  | .supH _, U => U

/-- The universe of transfinite type level `T+1` above the operator `F₀`. -/
def transTypeUniv (F₀ : Univ → Univ) (T : CTree) : Univ := evalDown F₀ (.succ T) (step F₀ T)

end U2

/-- The tree of input `n`: collapse after the closure chain of type level
`typeLevelTree n`, over Contender 29's operator. -/
def transTypeTree (n : Nat) : CTree :=
  U2.universeTree (U2.transTypeUniv (U2.ΦT (operatorTree n)) (typeLevelTree n))

end BusyLean.Ordinal
