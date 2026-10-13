import BusyLean.Comparison51
import Lean

open Lean Elab Command

def constClosure51 (env : Environment) (root : Name) : NameSet := Id.run do
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

elab "#assert_not_in_closure51 " root:ident " : " bad:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := constClosure51 env r
  for b in bad do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: closure of {cl.size} constants avoids all {bad.size} forbidden names"

#print axioms BusyLean.Ordinal.UTL.run
#print axioms BusyLean.Ordinal.UTL.denote
#print axioms BusyLean.Ordinal.universalLangLift
#print axioms BusyLean.Ordinal.universalBoostT
#print axioms BusyLean.iterLevel50
#print axioms BusyLean.base51
#print axioms BusyLean.universalTree51
#print axioms BusyLean.reader51
#print axioms BusyLean.contender_51
#print axioms BusyLean.family50_lt_F51
#print axioms BusyLean.official_tree_le_F51
#print axioms BusyLean.universal_stack_le_F51
#print axioms BusyLean.contender_50_lt_contender_51

#assert_not_in_closure51 BusyLean.contender_51 :
  BusyLean.contender_50 BusyLean.contender_49 BusyLean.contender_48
