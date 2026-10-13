import BigNumber.BaselineDefs

namespace BigNumber.SemanticChecks
open Baseline

def numeral : Nat → Term
  | 0 => .zero
  | n + 1 => .app .succ (numeral n)

def doubleStep : Term :=
  .lam .nat (.arr (.arr .nat .nat) (.arr .nat .nat))
    (.lam (.arr .nat .nat) (.arr .nat .nat)
      (.lam .nat .nat (.app (.var 1) (.app (.var 1) (.var 2)))))

def higherRec : Term :=
  .app (.app (.app (.app (.natRec (.arr .nat .nat)) .succ) doubleStep)
    (numeral 3)) .zero

set_option maxRecDepth 8192 in
theorem higher_type_recursion : eval higherRec = 8 := rfl

end BigNumber.SemanticChecks
