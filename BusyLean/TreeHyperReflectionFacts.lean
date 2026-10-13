import BusyLean.TreeHyperReflection
import BusyLean.HyperReflectionFacts

/-!
# Growth theorems for W-ranked diagonal hyperreflection

The arguments deliberately avoid monotonicity in oracle families.  Reflection
is not monotone because programs may inspect and branch on oracle values.
Every inequality is instead witnessed by an explicit child, splice coordinate,
or occurrence of the base transformer.

Adopted unchanged from proposal P22 (`proposals/P22-w-ranked-hyperreflection`,
"W-ranked diagonal hyperreflection").
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Splicing lifts preserves progressivity when every component lift does. -/
theorem spliceLifts_preservesProgressive {lifts : Nat → TransformerLift}
    (hlifts : ∀ i, PreservesProgressive (lifts i)) :
    PreservesProgressive (spliceLifts lifts) := by
  intro base hbase
  exact spliceTransformers_progressive (fun i => hlifts i base hbase)

/-- Splicing strictly inflationary lifts is strictly inflationary.

The requested output coordinate selects the corresponding component lift, so
no monotonicity or comparison between distinct components is needed.
-/
theorem spliceLifts_strictlyInflationary {lifts : Nat → TransformerLift}
    (hlifts : ∀ i, StrictlyInflationary (lifts i)) :
    StrictlyInflationary (spliceLifts lifts) := by
  intro base hbase seed i o n hi
  exact hlifts o base hbase seed i 0 n hi

/-- Every W-rank preserves progressivity. -/
theorem wDiagonalLift_preservesProgressive (schedule : WTree Nat) :
    (rank : WTree Nat) → PreservesProgressive (wDiagonalLift schedule rank)
  | .leaf => liftTransformer_preservesProgressive
  | .node f => by
      let lower : TransformerLift :=
        spliceLifts (fun i => wDiagonalLift schedule (f i))
      have hlower : PreservesProgressive lower := by
        apply spliceLifts_preservesProgressive
        intro i
        exact wDiagonalLift_preservesProgressive schedule (f i)
      intro base hbase
      change Progressive (stageLift lower (lower base) schedule)
      exact stageLift_progressive lower hlower
        (lower base) (hlower base hbase) schedule

/-- Every W-rank strictly exceeds its original base transformer. -/
theorem wDiagonalLift_strictlyInflationary (schedule : WTree Nat) :
    (rank : WTree Nat) → StrictlyInflationary (wDiagonalLift schedule rank)
  | .leaf => liftTransformer_strictlyInflationary
  | .node f => by
      let lower : TransformerLift :=
        spliceLifts (fun i => wDiagonalLift schedule (f i))
      have hlowerPres : PreservesProgressive lower := by
        apply spliceLifts_preservesProgressive
        intro i
        exact wDiagonalLift_preservesProgressive schedule (f i)
      have hlowerStrict : StrictlyInflationary lower := by
        apply spliceLifts_strictlyInflationary
        intro i
        exact wDiagonalLift_strictlyInflationary schedule (f i)
      intro base hbase seed i o n hi
      change base seed i n <
        stageLift lower (lower base) schedule seed o n
      have hfirst : base seed i n < lower base seed i n :=
        hlowerStrict base hbase seed i i n hi
      have hbase' : Progressive (lower base) :=
        hlowerPres base hbase
      have hsecond : lower base seed i n <
          stageLift lower (lower base) schedule seed o n :=
        base_lt_stageLift lower hlowerPres hlowerStrict
          (lower base) hbase' schedule seed i o n hi
      exact Nat.lt_trans hfirst hsecond

/-- Every visible child rank is strictly below its parent rank.

Coordinate `i` of the spliced lower lift names child `i`; the parent stage then
strictly exceeds that lower lift.  This theorem is the formal content behind
treating `WTree Nat` as a transfinite rank notation rather than merely a data
parameter.
-/
theorem wDiagonalLift_child_lt (schedule : WTree Nat)
    (f : Nat → WTree Nat) (base : Transformer) (hbase : Progressive base)
    (seed : Family) {i o n : Nat} (hi : i ≤ n) :
    wDiagonalLift schedule (f i) base seed 0 n <
      wDiagonalLift schedule (.node f) base seed o n := by
  let lower : TransformerLift :=
    spliceLifts (fun j => wDiagonalLift schedule (f j))
  have hlowerPres : PreservesProgressive lower := by
    apply spliceLifts_preservesProgressive
    intro j
    exact wDiagonalLift_preservesProgressive schedule (f j)
  have hlowerStrict : StrictlyInflationary lower := by
    apply spliceLifts_strictlyInflationary
    intro j
    exact wDiagonalLift_strictlyInflationary schedule (f j)
  have hbase' : Progressive (lower base) :=
    hlowerPres base hbase
  change lower base seed i n <
    stageLift lower (lower base) schedule seed o n
  exact base_lt_stageLift lower hlowerPres hlowerStrict
    (lower base) hbase' schedule seed i o n hi

end BusyLean
