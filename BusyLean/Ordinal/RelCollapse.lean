import BusyLean.Ordinal.TreeCollapse

/-!
# Collapsing relative to a jump

`D v` (Contender 25) is a Buchholz-style family of collapsing functions on tree
ordinals whose successor step is "the next ε-number". `DJ J v` is the same
family with the level-0 successor step replaced by an arbitrary operator `J`
on countable trees: `DJ J 0 (t+1) = lim (ε⁺(x), J (ε⁺(x)))` with
`x = DJ J 0 t`. Higher levels are unchanged.

Buchholz's diagonal at a supremum, `x₀ = Ω_j`, `x_{k+1} = D j (g x_k)`, feeds
every level back into level 0. So `J` is applied at every stage of the
collapse, not only to its result. Collapsing a large argument relative to `J`
thus yields closure points of `J` that iteration by a language over countable
trees does not reach. The definition is structural recursion, like `D`.
-/

namespace BusyLean.Ordinal

/-- The successor step at level `v`: `J` after ε⁺ at level 0, ε⁺ above it. -/
def LevT.jStep (J : CTree → CTree) : (v : Nat) → LevT v → LevT v
  | 0, x => Tre.lim fun i => if i = 0 then Tre.epsNext x else J (Tre.epsNext x)
  | _ + 1, x => Tre.epsNext x

/-- **Collapsing functions relative to `J`**, by structural recursion on the argument. -/
def DJ (J : CTree → CTree) : (v : Nat) → TopT → LevT v
  | v, .zero => LevT.Omega v
  | v, .succ t => LevT.jStep J v (DJ J v t)
  | v, .lim f => LevT.lim v fun n => DJ J v (f n)
  | v, .supL _ => LevT.zero v
  | v, .supH g =>
      let seq : (j : Nat) → Nat → LevT j := fun j n =>
        Nat.rec (motive := fun _ => LevT j) (LevT.Omega j) (fun _ acc => DJ J j (g ⟨j, acc⟩)) n
      LevT.lim v fun m =>
        match m with
        | 0 => LevT.supLow v fun p => if p.1 < v then DJ J v (g p) else LevT.zero v
        | i + 1 => LevT.lim v fun n => DJ J v (g ⟨v + i, seq (v + i) n⟩)

/-- The collapse of `ε`-iterates above `Ω_ω + T`, relative to `J`: heuristically
`ψ^J_0(ε_{Ω_ω+T+k})`. -/
def relCollapse (J : CTree → CTree) (k : Nat) (T : CTree) : CTree :=
  DJ J 0 (epsIter (k + 1) (Tre.add OmegaOmega (toTop 0 T)))

end BusyLean.Ordinal
