import Mirror.Compiler
import Lean

/-! Generic semantic correctness. All semantic inputs below are abstract:
proof checking never needs to normalize a contender or enumerate its programs. -/
namespace BusyLean.Mirror

open BigNumber (Ty Term WTree)
open BusyLean.W (Family)

@[simp] theorem wmap_id {A : Type} (t : WTree A) :
    BigNumber.wmap (fun x => x) t = t := by
  induction t with
  | leaf => rfl
  | node f ih =>
      change WTree.node (fun i => BigNumber.wmap (fun x => x) (f i)) = WTree.node f
      apply congrArg WTree.node
      funext i
      exact ih i

@[simp] theorem wmap_id_function {A : Type} :
    (BigNumber.wmap (fun x : A => x)) = (fun t : WTree A => t) :=
  funext wmap_id

@[simp] theorem eqb_self (a : Ty) : BigNumber.eqb a a = true := by
  induction a <;> simp [BigNumber.eqb, *]

@[simp] theorem castPair_self (a : Ty) :
    BigNumber.castPair a a =
      ((fun x : BigNumber.den a => x), (fun x : BigNumber.den a => x)) := by
  induction a with
  | nat => rfl
  | arr a b iha ihb => simp [BigNumber.castPair, iha, ihb]
  | wt a iha => simp [BigNumber.castPair, iha]

@[simp] theorem castValue_self {a : Ty} (x : BigNumber.den a) :
    BigNumber.castValue a x = x := by
  simp [BigNumber.castValue]

theorem interpret_indexProgram (h : Hierarchy) (g : Generator) (s : Family)
    (n : Nat) (a : Nat → Nat) (fs : Family) :
    BigNumber.interpret (environment h g s n a fs) indexProgram =
      ⟨treeTy, WTree.node (fun k => WTree.node (fun i => g k i))⟩ := by
  simp [indexProgram, environment, BigNumber.interpret,
    BigNumber.lookup, BigNumber.nth?]

theorem interpret_numberProgram (h : Hierarchy) (g : Generator) (s : Family)
    (n : Nat) (a : Nat → Nat) (fs : Family) :
    BigNumber.interpret (environment h g s n a fs) numberProgram =
      ⟨Ty.nat, h s (.node (fun k => .node (fun i => g k i))) n⟩ := by
  simp [numberProgram, indexProgram, environment, BigNumber.interpret,
    BigNumber.lookup, BigNumber.nth?]

theorem eval_boostProgram (h : Hierarchy) (g : Generator) (s : Family)
    (n : Nat) (a : Nat → Nat) (fs : Family) :
    numericValue (environment h g s n a fs) boostProgram =
      a (h s (.node (fun k => .node (fun i => g k i))) n) := by
  simp [numericValue, boostProgram, numberProgram, indexProgram, environment,
    BigNumber.interpret, BigNumber.lookup, BigNumber.nth?]

theorem score_boostProgram (m : Model) (fs : Family) (n : Nat) :
    score m fs n boostProgram = boost (number m n) := by
  simpa only [score, libraryEnv, number, rawIndex] using
    eval_boostProgram (walk m.reflection) m.trees BusyLean.p5Family n boost fs

/-- Original raw casts are extensionally identities on identical W-types,
not generally judgmental identities. This bridge uses that distinction. -/
theorem walk_original (s : Family) (t : Tree) :
    walk BusyLean.W.reflect s t = BusyLean.W.stage s t := by
  induction t with
  | leaf => rfl
  | node f ih =>
      change BusyLean.W.reflect (fun i => walk BusyLean.W.reflect s (f i)) =
        BusyLean.W.reflect (fun i => BusyLean.W.stage s (f i))
      apply congrArg BusyLean.W.reflect
      funext i
      exact ih i

theorem rawIndex_initial : rawIndex initialModel = BusyLean.index := rfl

theorem number_initial (n : Nat) : number initialModel n = BusyLean.finalFamily n := by
  change walk BusyLean.W.reflect BusyLean.p5Family (rawIndex initialModel) n = _
  rw [rawIndex_initial, walk_original]
  rfl

end BusyLean.Mirror
