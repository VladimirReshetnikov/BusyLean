import BusyLean.Comparison14
import Lean

/-!
# Contender 14 audit

This file checks the axioms of the new definitions and theorems and verifies
that the new contender depends on Contender 13's construction, not on any
previous named contender constant.
-/

open Lean Elab Command

/-- All constants reachable from `root` through declaration types and values. -/
def contender14ConstClosure (env : Environment) (root : Name) : NameSet := Id.run do
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

/-- Fail if one of the forbidden constants occurs in the transitive closure. -/
elab "#contender14_assert_not_in_closure " root:ident " : " bad:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := contender14ConstClosure env r
  for b in bad do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: closure of {cl.size} constants avoids all {bad.size} forbidden names"

#print axioms BusyLean.reflect14
#print axioms BusyLean.metaTower14
#print axioms BusyLean.F14
#print axioms BusyLean.contender_14
#print axioms BusyLean.contender_13_lt_contender_14
#print axioms BusyLean.family13_lt_F14
#print axioms BusyLean.fvalue_lt_F14
#print axioms BusyLean.fvalue_lt_contender_14

#contender14_assert_not_in_closure BusyLean.contender_14 :
  BusyLean.contender_13 BusyLean.contender_12 BusyLean.contender_11
  BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8
  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

#check @BusyLean.fdTransformer14_progressive
#check @BusyLean.metaTower14_progressive
#check @BusyLean.transformer_lt_metaStep14
#check @BusyLean.coreStage_lt_metaStep14
#check @BusyLean.family13_lt_F14
#check @BusyLean.contender_13_lt_contender_14
#check @BusyLean.fvalue_lt_contender_14
