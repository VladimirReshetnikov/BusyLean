import BusyLean.Ordinal.TreeCollapse

/-!
# Collapsing with transfinitely many levels

Levels are now countable tree ordinals. `Low a` lumps all levels below `a`,
by structural recursion on the level tree:

* `Low 0 = ∅`;
* `Low (a+1) = Low a ⊕ Lev a`;
* `Low (lim f) = Σ i, Low (f i) ⊕ Lev (f i)`.

Here `Lev a = Tre (Low a) Empty`: level-`a` trees have suprema over everything
below level `a`.

Arguments live in `LTop`, whose suprema carry their level:
`supAt (c : CTree) (g : Low c → LTop)`. So collapsing never needs to *decide*
an order between levels. `D a : LTop → Lev a` pattern-matches on the shape of
`c`:

* `c = c'+1` (cofinality `Ω_{c'+1}`): Buchholz's diagonal
  `x₀ = Ω_{c'}`, `x_{k+1} = D c' (g x_k)`, giving `lim_k D a (g x_k)`;
* `c = lim f`: the limit over `i` of the successor case at `f i`;
* zero, successor and limit arguments as in `TreeCollapse`.

Everything is structural recursion; no axioms.

`ladderTree n` iterates `Λ ↦ D 0 (ε_{Ω_Λ+1})` starting from Contender 25's
`bigTree n`. Heuristically this climbs toward the fixed points of
`α ↦ ψ₀(Ω_α)`.
-/

namespace BusyLean.Ordinal

/-- All levels below the level `a`. -/
def Low : CTree → Type
  | .zero => Empty
  | .succ a => Low a ⊕ Tre (Low a) Empty
  | .lim f => Σ i, (Low (f i) ⊕ Tre (Low (f i)) Empty)
  | .supL _ => Empty
  | .supH _ => Empty

/-- Level-`a` tree ordinals. -/
abbrev Lev (a : CTree) : Type := Tre (Low a) Empty

/-- One level up, extending suprema by zero. -/
def upSucc (a : CTree) : Lev a → Lev (.succ a) :=
  Tre.embed (fun h => .supL fun c => match c with | .inl b => h b | .inr _ => .zero) (fun h => .supH h)

/-- Into a limit level, extending suprema by zero. -/
def upLim (f : Nat → CTree) (i : Nat) : Lev (f i) → Lev (.lim f) :=
  Tre.embed (fun h => .supL fun p =>
      if hj : p.1 = i then
        match (hj ▸ p.2 : Low (f i) ⊕ Tre (Low (f i)) Empty) with
        | .inl b => h b
        | .inr _ => .zero
      else .zero)
    (fun h => .supH h)

/-- An element below level `a`, as an element of level `a`. -/
def embedLow : (a : CTree) → Low a → Lev a
  | .zero, b => b.elim
  | .succ a, .inl b => upSucc a (embedLow a b)
  | .succ a, .inr e => upSucc a e
  | .lim f, ⟨i, .inl b⟩ => upLim f i (embedLow (f i) b)
  | .lim f, ⟨i, .inr e⟩ => upLim f i e
  | .supL _, b => b.elim
  | .supH _, b => b.elim

/-- `Ω_a`: the supremum of everything below level `a` (plus `ω`). -/
def OmegaAt (a : CTree) : Lev a :=
  .lim fun m => if m = 0 then .supL (embedLow a) else Tre.nat m

/-- Arguments of the collapsing functions; suprema carry their level. -/
inductive LTop where
  | zero : LTop
  | succ : LTop → LTop
  | lim : (Nat → LTop) → LTop
  | supAt : (c : CTree) → (Low c → LTop) → LTop

namespace LTop

def nat : Nat → LTop
  | 0 => .zero
  | n + 1 => .succ (nat n)

def add (a : LTop) : LTop → LTop
  | .zero => a
  | .succ t => .succ (add a t)
  | .lim f => .lim fun n => add a (f n)
  | .supAt c g => .supAt c fun x => add a (g x)

def mul (a : LTop) : LTop → LTop
  | .zero => .zero
  | .succ t => add (mul a t) a
  | .lim f => .lim fun n => mul a (f n)
  | .supAt c g => .supAt c fun x => mul a (g x)

def expo : LTop → LTop
  | .zero => .succ .zero
  | .succ t => .lim fun n => mul (expo t) (nat n)
  | .lim f => .lim fun n => expo (f n)
  | .supAt c g => .supAt c fun x => expo (g x)

def tower : Nat → LTop → LTop
  | 0, x => x
  | k + 1, x => expo (tower k x)

/-- The next ε-number above `x`. -/
def epsNext (x : LTop) : LTop := .lim fun k => tower k (.succ x)

end LTop

/-- Level-`a` trees as arguments. -/
def toTopAt (a : CTree) : Lev a → LTop
  | .zero => .zero
  | .succ t => .succ (toTopAt a t)
  | .lim f => .lim fun n => toTopAt a (f n)
  | .supL h => .supAt a fun b => toTopAt a (h b)
  | .supH _ => .zero

/-- `Ω_a` as an argument. -/
def OmegaTop (a : CTree) : LTop := toTopAt a (OmegaAt a)

/-- **Collapsing with tree-indexed levels**, by structural recursion. -/
def DL : (a : CTree) → LTop → Lev a
  | a, .zero => OmegaAt a
  | a, .succ t => Tre.epsNext (DL a t)
  | a, .lim f => .lim fun n => DL a (f n)
  | a, .supAt c g =>
      match c, g with
      | .succ c', g =>
          let seq : Nat → Lev c' := fun k =>
            Nat.rec (motive := fun _ => Lev c') (OmegaAt c') (fun _ x => DL c' (g (.inr x))) k
          .lim fun k => DL a (g (.inr (seq k)))
      | .lim f, g =>
          .lim fun i =>
            let seq : Nat → Lev (f i) := fun k =>
              Nat.rec (motive := fun _ => Lev (f i)) (OmegaAt (f i))
                (fun _ x => DL (f i) (g ⟨i, .inr x⟩)) k
            .lim fun k => DL a (g ⟨i, .inr (seq k)⟩)
      | _, _ => OmegaAt a

/-- One more round: collapse `ε_{Ω_Λ+1}` to a countable tree. -/
def nextLevelTree (Λ : CTree) : CTree := DL .zero (LTop.epsNext (.succ (OmegaTop Λ)))

/-- `k` rounds above Contender 25's `bigTree n`. -/
def levelRounds (n : Nat) : Nat → CTree
  | 0 => bigTree n
  | k + 1 => nextLevelTree (levelRounds n k)

/-- The tree of input `n`: `n` rounds of transfinite-level collapsing. -/
def ladderTree (n : Nat) : CTree := levelRounds n (n + 1)

end BusyLean.Ordinal
