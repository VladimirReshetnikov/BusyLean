import BusyLean.Comparison20
import Lean

/-!
Focused kernel audit for Contender 20.

Run after installation with:

  lake env lean test/Audit20.lean
-/

open Lean Elab Command

/-- All constants reachable from `root` through types and values. -/
def constClosure20 (env : Environment) (root : Name) : NameSet := Id.run do
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

/-- Fail if any listed constant is in the transitive closure of `root`. -/
elab "#assert_not_in_closure20 " root:ident " : " bad:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := constClosure20 env r
  for b in bad do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then
      throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: closure of {cl.size} constants avoids all {bad.size} forbidden names"

#print axioms BusyLean.spliceLifts_good
#print axioms BusyLean.promoteLift_good
#print axioms BusyLean.baseLift_lt_liftStage
#print axioms BusyLean.superIterate_good
#print axioms BusyLean.lift_lt_superIterate_succ
#print axioms BusyLean.contender_20
#print axioms BusyLean.diagonalLift_lt_lift20
#print axioms BusyLean.family19_lt_F20
#print axioms BusyLean.final_lvalue_lt_F20
#print axioms BusyLean.contender_19_lt_contender_20

#assert_not_in_closure20 BusyLean.contender_20 :
  BusyLean.contender_19 BusyLean.contender_18 BusyLean.contender_17
  BusyLean.contender_16 BusyLean.contender_15 BusyLean.contender_14
  BusyLean.contender_13 BusyLean.contender_12 BusyLean.contender_11
  BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8
  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

#check @BusyLean.contender_19_lt_contender_20
#check @BusyLean.diagonalLift_lt_lift20
#check @BusyLean.final_lvalue_lt_F20
