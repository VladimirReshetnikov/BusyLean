import BusyLean7
import Lean

/-! Adapted from pinned BusyLean/test/Audit.lean. RUN, do not assume, this audit. -/
open Lean Elab Command

def constClosure (env : Environment) (root : Name) : NameSet := Id.run do
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

elab "#assert_not_in_closure " root:ident " : " bad:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := constClosure env r
  for b in bad do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: closure of {cl.size} constants avoids all {bad.size} forbidden names"

#print axioms BusyLean.contender_7
#print axioms BusyLean.contender_6_lt_contender_7
#print axioms BusyLean.contender_6_tower_lt_contender_7
#print axioms BusyLean7.no_eventual_self_majorant
#print axioms BusyLean7.ramify_index_eventually_dominates

#assert_not_in_closure BusyLean.contender_7 :
  BusyLean.contender_6 BusyLean.finalFamily BigNumber.contender_6

#check BusyLean.contender_6_lt_contender_7
#check BusyLean.contender_6_tower_lt_contender_7
#check BusyLean7.ramify_index_eventually_dominates
