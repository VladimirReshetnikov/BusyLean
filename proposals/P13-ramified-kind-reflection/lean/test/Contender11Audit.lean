import BusyLean.Comparison11
import Lean

/-!
Standalone audit fragment for Contender 11.

After integrating the two modules into BusyLean, run:

    lake env lean test/Contender11Audit.lean
-/

open Lean Elab Command

/-- All constants reachable from `root` through types and values. -/
def constClosure11 (env : Environment) (root : Name) : NameSet := Id.run do
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

elab "#assert_not_in_closure11 " root:ident " : " bad:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := constClosure11 env r
  for b in bad do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then
      throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: closure of {cl.size} constants avoids all forbidden names"

#print axioms BusyLean.contender_11
#print axioms BusyLean.contender_10_lt_contender_11
#print axioms BusyLean.family10_lt_F11
#print axioms BusyLean.fixed_rank_eventually_lt_F11
#print axioms BusyLean.fvalue_lt_F11
#print axioms BusyLean.RK.ramified_dominates
#print axioms BusyLean.RK.ramified_lt_of_lt

-- The construction may use the previous *family* `F10`, but not any previous
-- contender constant.
#assert_not_in_closure11 BusyLean.contender_11 :
  BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8
  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

#check @BusyLean.contender_10_lt_contender_11
#check @BusyLean.fixed_rank_eventually_lt_F11
#check @BusyLean.fvalue_lt_F11
#check @BusyLean.RK.ramified_level_lt
