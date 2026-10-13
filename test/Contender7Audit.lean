import BusyLean
import Lean

/-!
# Contender 7 audit

Run with `lake env lean test/Contender7Audit.lean`.
-/

open Lean Elab Command

/-- All constants reachable from `root` through declaration types and values. -/
def c7ConstClosure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := #[root]
  while stack.size > 0 do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    let body : Array Name := match ci with
      | .defnInfo v => v.value.getUsedConstants
      | .thmInfo v => v.value.getUsedConstants
      | .opaqueInfo v => v.value.getUsedConstants
      | _ => #[]
    stack := stack ++ ci.type.getUsedConstants ++ body
  return seen

/-- Fail if any listed constant occurs in the dependency closure. -/
elab "#c7_assert_not_in_closure " root:ident " : " bad:ident* : command => do
  let env <- getEnv
  let r <- liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := c7ConstClosure env r
  for b in bad do
    let n <- liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: closure of {cl.size} constants avoids all {bad.size} forbidden names"

#print axioms BusyLean.contender_7
#print axioms BusyLean.contender7_branch_step_lt
#print axioms BusyLean.contender7_branch_zero_lt_succ
#print axioms BusyLean.finalFamily_lt_contender7Branch42
#print axioms BusyLean.contender_6_lt_contender_7
#print axioms BusyLean.contender_5_lt_contender_7
#print axioms BusyLean.finalFamily_lt_contender7Family
#print axioms BusyLean.hyper41_lt_contender7Branch42
#print axioms BusyLean.hyper41_lt_contender_7

-- The definition is independent of the previous named values and comparison
-- theorems.  It may reuse structural machinery (`index`, `stage`, `p5Family`).
#c7_assert_not_in_closure BusyLean.contender_7 :
  BusyLean.contender_5 BusyLean.contender_6
  BusyLean.contender_5_lt_contender_6 BusyLean.contender_6_lt_contender_7
  BigNumber.contender_5 BigNumber.contender_6
  BusyLean.C5.largestOfDepth BusyLean.C5.maxBy

#check @BusyLean.contender_6_lt_contender_7
#check @BusyLean.hyper41_lt_contender_7

-- A feasible computability sanity check.  Never evaluate input 42.
#eval BusyLean.contender7Family 0
