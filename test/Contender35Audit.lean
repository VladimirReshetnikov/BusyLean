import BusyLean.Comparison35
import Lean

/-! Focused axiom and dependency audit for Contender 35. -/

open Lean Elab Command

/-- All constants reachable from a declaration through types and values. -/
def constClosure35 (env : Environment) (root : Name) : NameSet := Id.run do
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

elab "#assert_not_in_closure35 " root:ident " : " bad:ident* : command => do
  let env <- getEnv
  let r <- liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := constClosure35 env r
  for b in bad do
    let n <- liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then
      throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: closure of {cl.size} constants avoids all {bad.size} forbidden names"

#print axioms BusyLean.Ordinal.OML.Tm.eval
#print axioms BusyLean.Ordinal.operatorMetaLift
#print axioms BusyLean.Ordinal.operatorBoostT
#print axioms BusyLean.Ordinal.operatorStackedTree
#print axioms BusyLean.FL.sn_erase_ostree
#print axioms BusyLean.F35
#print axioms BusyLean.contender_35
#print axioms BusyLean.family34_lt_F35
#print axioms BusyLean.osvalue_lt_F35
#print axioms BusyLean.contender_34_lt_contender_35

#check BusyLean.contender_34_lt_contender_35
#check BusyLean.family34_lt_F35
#check BusyLean.osvalue_lt_F35

/-- Rule 5: the new definition uses the predecessor's family, never an earlier
contender constant itself. -/
#assert_not_in_closure35 BusyLean.contender_35 :
  BusyLean.contender_34 BusyLean.contender_33 BusyLean.contender_32
  BusyLean.contender_31 BusyLean.contender_30 BusyLean.contender_29
  BusyLean.contender_28 BusyLean.contender_27 BusyLean.contender_26
  BusyLean.contender_25 BusyLean.contender_24 BusyLean.contender_23
  BusyLean.contender_22 BusyLean.contender_21 BusyLean.contender_20
  BusyLean.contender_19 BusyLean.contender_18 BusyLean.contender_17
  BusyLean.contender_16 BusyLean.contender_15 BusyLean.contender_14
  BusyLean.contender_13 BusyLean.contender_12 BusyLean.contender_11
  BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8
  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5
