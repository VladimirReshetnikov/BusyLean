import BusyLean.Comparison14
import Lean

/-!
# Contender 14 audit

Run with `lake env lean test/Audit14.lean` after copying the two source modules
into the BusyLean repository.  It checks axioms and verifies that the new
number's definition does not depend on any earlier contender constant.
-/

open Lean Elab Command

/-- All constants reachable from `root` through declaration types and values. -/
def constClosure14 (env : Environment) (root : Name) : NameSet := Id.run do
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

/-- Fail if any listed constant belongs to the transitive closure of `root`. -/
elab "#assert_not_in_closure14 " root:ident " : " bad:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := constClosure14 env r
  for b in bad do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then
      throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: closure of {cl.size} constants avoids all forbidden names"

#print axioms BusyLean.contender_14
#print axioms BusyLean.contender_13_lt_contender_14
#print axioms BusyLean.family13_lt_F14
#print axioms BusyLean.family13_twice_lt_F14
#print axioms BusyLean.fvalue_lt_F14
#print axioms BusyLean.operatorPower_progressive
#print axioms BusyLean.operatorPower_step_lt

#assert_not_in_closure14 BusyLean.contender_14 :
  BusyLean.contender_13 BusyLean.contender_12 BusyLean.contender_11
  BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8
  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

#check @BusyLean.contender_13_lt_contender_14
#check @BusyLean.fvalue_lt_F14
#check @BusyLean.operatorPower_step_lt
