import BusyLean.Ordinal.TreeLevels

/-!
# Collapsing with tree-indexed levels, relative to a jump

`DL a` (Contender 26) collapses with levels indexed by countable trees.
`DLJ J a` is the same, with the level-0 successor step replaced by an operator
`J` on countable trees, as in `RelCollapse`: `DLJ J 0 (t+1) = lim (ε⁺ x, J (ε⁺ x))`.
Buchholz's diagonal at every supremum re-enters lower levels and ends at
level 0, so `J` is applied throughout.

`relLevelRounds J k Λ` iterates `Λ ↦ ψ^J₀(ε_{Ω_Λ+1})` `k` times, starting from
`Λ`. It climbs toward the fixed points of `α ↦ ψ^J₀(Ω_α)` relative to `J`, while
`relCollapse` stays below `ψ^J₀(Ω_{ω+1})`-like levels.
-/

namespace BusyLean.Ordinal

/-- The successor step at level `a`: `J` after ε⁺ at level 0, ε⁺ above it. -/
def jStepL (J : CTree → CTree) : (a : CTree) → Lev a → Lev a
  | .zero, x => Tre.lim fun i => if i = 0 then Tre.epsNext x else J (Tre.epsNext x)
  | _, x => Tre.epsNext x

/-- **Collapsing with tree-indexed levels relative to `J`**, by structural recursion. -/
def DLJ (J : CTree → CTree) : (a : CTree) → LTop → Lev a
  | a, .zero => OmegaAt a
  | a, .succ t => jStepL J a (DLJ J a t)
  | a, .lim f => .lim fun n => DLJ J a (f n)
  | a, .supAt c g =>
      match c, g with
      | .succ c', g =>
          let seq : Nat → Lev c' := fun k =>
            Nat.rec (motive := fun _ => Lev c') (OmegaAt c') (fun _ x => DLJ J c' (g (.inr x))) k
          .lim fun k => DLJ J a (g (.inr (seq k)))
      | .lim f, g =>
          .lim fun i =>
            let seq : Nat → Lev (f i) := fun k =>
              Nat.rec (motive := fun _ => Lev (f i)) (OmegaAt (f i))
                (fun _ x => DLJ J (f i) (g ⟨i, .inr x⟩)) k
            .lim fun k => DLJ J a (g ⟨i, .inr (seq k)⟩)
      | _, _ => OmegaAt a

/-- One round relative to `J`: collapse `ε_{Ω_Λ+1}` to a countable tree. -/
def relNextLevel (J : CTree → CTree) (Λ : CTree) : CTree :=
  DLJ J .zero (LTop.epsNext (.succ (OmegaTop Λ)))

/-- `k` rounds relative to `J`, starting from `Λ`; each round is joined with the previous tree. -/
def relLevelRounds (J : CTree → CTree) : Nat → CTree → CTree
  | 0, Λ => Λ
  | k + 1, Λ =>
      let prev := relLevelRounds J k Λ
      .lim fun i => if i = 0 then prev else relNextLevel J prev

end BusyLean.Ordinal
