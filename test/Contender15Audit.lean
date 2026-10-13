import BusyLean.Comparison15
import Lean

/-!
# Contender 15 audit

This file checks the axiom footprint and verifies that the new definition uses
prior constructions rather than any prior named contender constant.
-/

open Lean Elab Command

/-- All constants reachable from `root` through declaration types and values. -/
def contender15ConstClosure (env : Environment) (root : Name) : NameSet := Id.run do
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

/-- Fail if any forbidden prior contender constant occurs transitively. -/
elab "#contender15_assert_not_in_closure " root:ident " : " bad:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := contender15ConstClosure env r
  for b in bad do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: closure of {cl.size} constants avoids all {bad.size} forbidden names"

#print axioms BusyLean.diagonalLift
#print axioms BusyLean.diagonalTransformer15
#print axioms BusyLean.metaTower15
#print axioms BusyLean.F15
#print axioms BusyLean.contender_15
#print axioms BusyLean.family14_lt_F15
#print axioms BusyLean.F14_lt_F15
#print axioms BusyLean.fvalue_lt_F15
#print axioms BusyLean.contender_14_lt_contender_15
#print axioms BusyLean.contender_13_lt_contender_15
#print axioms BusyLean.fvalue_lt_contender_15

#contender15_assert_not_in_closure BusyLean.contender_15 :
  BusyLean.contender_14 BusyLean.contender_13 BusyLean.contender_12
  BusyLean.contender_11 BusyLean.contender_10 BusyLean.contender_9
  BusyLean.contender_8 BusyLean.contender_7 BusyLean.contender_6
  BusyLean.contender_5

#check @BusyLean.diagonalTransformer15_progressive
#check @BusyLean.metaTower15_progressive
#check @BusyLean.transformer_lt_metaStep15
#check @BusyLean.coreStage_lt_crowned15
#check @BusyLean.family14_lt_F15
#check @BusyLean.F14_lt_F15
#check @BusyLean.fvalue_lt_F15
#check @BusyLean.contender_14_lt_contender_15
#check @BusyLean.contender_13_lt_contender_15
#check @BusyLean.fvalue_lt_contender_15
