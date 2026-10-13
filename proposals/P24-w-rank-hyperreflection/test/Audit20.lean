import BusyLean.Comparison20
import Lean

/-! Focused audit for Contender 20. -/

open Lean Elab Command

/-- Constants reachable from a declaration through types and values. -/
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

/-- Fail if a forbidden declaration occurs in the closure of `root`. -/
elab "#assert_not_in_closure20 " root:ident " : " bad:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := constClosure20 env r
  for b in bad do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then
      throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: closure of {cl.size} constants avoids all {bad.size} forbidden names"

#print axioms BusyLean.contender_20
#print axioms BusyLean.contender_19_lt_contender_20
#print axioms BusyLean.family19_lt_F20
#print axioms BusyLean.lvalue_lt_F20
#print axioms BusyLean.seed_lt_runHyperLift
#print axioms BusyLean.treeDiagonalLift_good

#assert_not_in_closure20 BusyLean.contender_20 :
  BusyLean.contender_19 BusyLean.contender_18 BusyLean.contender_17
  BusyLean.contender_16 BusyLean.contender_15 BusyLean.contender_14
  BusyLean.contender_13 BusyLean.contender_12 BusyLean.contender_11
  BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8
  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

#check @BusyLean.contender_19_lt_contender_20
#check @BusyLean.family19_lt_F20
#check @BusyLean.lvalue_lt_F20
#check @BusyLean.seed_lt_treeDiagonalLift
