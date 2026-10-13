import BusyLean.Comparison14
import Lean

/-! Focused audit for Contender 14. -/

open Lean Elab Command

/-- All constants reachable from `root` through types and values. -/
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

/-- Fail if any forbidden constant is reachable from the root definition. -/
elab "#assert_not_in_closure14 " root:ident " : " bad:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := constClosure14 env r
  for b in bad do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then
      throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: closure of {cl.size} constants avoids all {bad.size} forbidden names"

#print axioms BusyLean.contender_14
#print axioms BusyLean.contender_13_lt_contender_14
#print axioms BusyLean.family13_lt_F14
#print axioms BusyLean.fvalue_lt_contender_14
#print axioms BusyLean.rankLift_preserves
#print axioms BusyLean.rankLift_step_lt
#print axioms BusyLean.fixed_rank_lt_diagonalRank14

#assert_not_in_closure14 BusyLean.contender_14 :
  BusyLean.contender_13 BusyLean.contender_12 BusyLean.contender_11
  BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8
  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

#check @BusyLean.contender_13_lt_contender_14
#check @BusyLean.family13_lt_F14
#check @BusyLean.fvalue_lt_contender_14
#check @BusyLean.rankLift_preserves
#check @BusyLean.rankLift_step_lt
#check @BusyLean.fixed_rank_lt_diagonalRank14
