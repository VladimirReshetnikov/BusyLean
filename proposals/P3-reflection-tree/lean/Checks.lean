import Baseline
import Oracle
import Trees
import Hierarchy

/-!
# Small, executable sanity checks

All `example` declarations below are kernel-checked by definitional reduction.
The `CHECK` records are supplementary executable checks parsed independently
by verification/verify.py. They never evaluate contender_5, contender_6, or
baseline at depth greater than 4. Counts are obtained by traversing the actual
enumerations, not by substituting their counting recurrences.
-/

namespace Biggest.Sanity

def numeral : Nat → Term
  | 0 => .zero
  | n + 1 => .app .succ (numeral n)

/-- Because lookup is reversed, 0 denotes the outer binder and 1 the inner. -/
def chooseOuter : Term :=
  .lam .nat (.arr .nat .nat) (.lam .nat .nat (.var 0))

def chooseInner : Term :=
  .lam .nat (.arr .nat .nat) (.lam .nat .nat (.var 1))

def applyTwo (f : Term) (a b : Nat) : Term :=
  .app (.app f (numeral a)) (numeral b)

/-- In the step's environment, index 1 selects the accumulator. -/
def incrementAccumulator : Term :=
  .lam .nat (.arr .nat .nat) (.lam .nat .nat (.app .succ (.var 1)))

def addByRecursion (base count : Nat) : Term :=
  .app (.app (.app (.natRec .nat) (numeral base)) incrementAccumulator)
    (numeral count)

def sampleTerms : List Term :=
  [.zero, .succ, .var 0, .app .succ .zero, .app .zero .succ,
    .app .succ .succ, applyTwo chooseOuter 5 7,
    applyTwo chooseInner 5 7, addByRecursion 5 3]

def sampleOracle (n : Nat) : Nat := 10 * n + 3

example : lookup [10, 11, 12] 0 = some 12 := rfl
example : lookup [10, 11, 12] 2 = some 10 := rfl
example : lookup [10, 11, 12] 3 = none := rfl
example : eval (.var 0) = 0 := rfl
example : eval (.app .zero .succ) = 0 := rfl
example : eval (.app .succ .succ) = 1 := rfl
example : eval (applyTwo chooseOuter 5 7) = 5 := rfl
example : eval (applyTwo chooseInner 5 7) = 7 := rfl
example : eval (addByRecursion 5 3) = 8 := rfl

theorem quote_preserves (f : Nat → Nat) (n : Nat) (t : Term) :
    evalExpr f n (.quote t) = eval t := rfl

example : evalExpr sampleOracle 7 .input = 7 := rfl
example : evalExpr sampleOracle 7 (.app .oracle .input) = 73 := rfl
example : evalExpr sampleOracle 7 (.app .oracle .succ) = 3 := rfl
example : evalExpr sampleOracle 7 (.app .zero .oracle) = 0 := rfl

/-- A quotation keeps the empty old environment, even beneath a new binder. -/
example : evalExpr sampleOracle 7
    (.app (.lam .nat .nat (.quote (.var 0))) (.app .succ .zero)) = 0 := rfl

example : treeIter Nat.succ 5 0 = 5 := rfl
example : stageAdd (stageNat 2) (stageNat 3) = stageNat 5 := rfl
example : stageMul (stageNat 2) (stageNat 3) = stageNat 6 := rfl
example : omegaPow .zero = stageNat 1 := rfl
example : hierarchy .zero 3 = 4 := rfl
example : hierarchy (.lim (fun _ => .zero)) 0 = 2 := rfl
example : hierarchy (.succ .zero) 0 = 4 := rfl
example : hierarchy (.succ .zero) 1 = 16 := rfl

#eval IO.println s!"CHECK type_counts = {(List.range 5).map (fun n => (typesUpTo n).length)}"
#eval IO.println s!"CHECK term_counts = {(List.range 5).map (fun n => (termsUpTo n).length)}"
#eval IO.println s!"CHECK baseline_values = {(List.range 5).map baseline}"
#eval IO.println s!"CHECK expression_counts = {(List.range 4).map (fun n => (exprsUpTo n).length)}"
#eval IO.println s!"CHECK raw_samples = {sampleTerms.map eval}"
#eval IO.println s!"CHECK quote_samples = {sampleTerms.map (fun t => evalExpr sampleOracle 7 (.quote t))}"
#eval IO.println s!"CHECK oracle_samples = {([Expr.input, .app .oracle .input, .app .oracle .succ, .app .zero .oracle]).map (evalExpr sampleOracle 7)}"
#eval IO.println s!"CHECK reflect_samples = {(List.range 3).map (reflect Nat.succ)}"
#eval IO.println s!"CHECK hierarchy_successor_samples = {(List.range 3).map (hierarchy (.succ .zero))}"

end Biggest.Sanity

#print axioms Biggest.Sanity.quote_preserves
