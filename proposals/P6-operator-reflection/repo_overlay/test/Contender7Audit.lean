import BusyLean.Comparison7
import Lean

/-!
Run with:

    lake env lean test/Contender7Audit.lean

The expected axiom set is empty or a subset of `{propext, Quot.sound}`.
The dependency audit checks the transitive kernel-environment closure, not just
surface syntax.  Do not add `#eval BusyLean.contender_7`.
-/

open Lean Elab Command

/-- All constants reachable from `root` through declaration types and values. -/
def contender7ConstClosure (env : Environment) (root : Name) : NameSet := Id.run do
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

/-- Fail if any listed declaration occurs in the transitive closure of root. -/
elab "#assert_contender7_not_in_closure " root:ident " : " bad:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let closure := contender7ConstClosure env r
  for b in bad do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if closure.contains n then
      throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: closure of {closure.size} constants avoids all {bad.size} forbidden names"

#print axioms BusyLean.contender_7
#print axioms BusyLean.contender_6_lt_contender_7
#print axioms BusyLean.finalFamily_lt_autonomousFamily
#print axioms BusyLean.defined_operator_eventually_lt

#assert_contender7_not_in_closure BusyLean.contender_7 :
  BusyLean.contender_6 BusyLean.finalFamily BusyLean.contender_5
  BigNumber.contender_6 BigNumber.contender_5
  BusyLean.C5.largestOfDepth BusyLean.C5.maxBy
  BusyLean.C5.largestSTLCNatRecNatOfDepth

#check @BusyLean.contender_6_lt_contender_7
#check @BusyLean.contender_5_lt_contender_7
#check @BusyLean.p5_lt_contender_7
