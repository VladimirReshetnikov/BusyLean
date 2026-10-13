import BusyLean.Comparison42
import Lean

open Lean Elab Command

/-- Transitive constant closure, used to ensure that the new closed number uses
the previous *family* but not the previous closed contender constant. -/
def constClosure42 (env : Environment) (root : Name) : NameSet := Id.run do
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

elab "#assert_not_in_closure42 " root:ident " : " bad:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := constClosure42 env r
  for b in bad do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: closure of {cl.size} constants avoids all {bad.size} forbidden names"

#print axioms BusyLean.Ordinal.UTL.run
#print axioms BusyLean.Ordinal.UTL.denote
#print axioms BusyLean.Ordinal.universalLangLift
#print axioms BusyLean.Ordinal.universalBoostT
#print axioms BusyLean.universalTree
#print axioms BusyLean.contender_42
#print axioms BusyLean.family41_lt_F42
#print axioms BusyLean.universal_stack_le_F42
#print axioms BusyLean.contender_41_lt_contender_42

#assert_not_in_closure42 BusyLean.contender_42 :
  BusyLean.contender_41 BusyLean.contender_40 BusyLean.contender_39
