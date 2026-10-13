import BusyLean.Comparison26
import Lean

/-!
# Contender 26 audit

This focused audit checks the new definitions and comparison theorem, and
verifies that `contender_26` reuses Contender 25's constructions without
embedding any named predecessor contender constant.
-/

open Lean Elab Command

/-- All constants reachable from `root` through types and values. -/
def contender26ConstClosure (env : Environment) (root : Name) : NameSet := Id.run do
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

/-- Fail if any listed constant is in the closure of the first one. -/
elab "#contender26_assert_not_in_closure " root:ident " : " bad:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := contender26ConstClosure env r
  for b in bad do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: closure of {cl.size} constants avoids all {bad.size} forbidden names"

#print axioms BusyLean.budget26
#print axioms BusyLean.reflectAStarFamily
#print axioms BusyLean.aStarTransformer
#print axioms BusyLean.F26
#print axioms BusyLean.contender_26
#print axioms BusyLean.contender_25_lt_height26_42
#print axioms BusyLean.aStarValue_lt_F26
#print axioms BusyLean.contender_25_lt_contender_26

#contender26_assert_not_in_closure BusyLean.contender_26 :
  BusyLean.contender_25 BusyLean.contender_24 BusyLean.contender_23
  BusyLean.contender_22 BusyLean.contender_21 BusyLean.contender_20
  BusyLean.contender_19 BusyLean.contender_18 BusyLean.contender_17
  BusyLean.contender_16 BusyLean.contender_15 BusyLean.contender_14
  BusyLean.contender_13 BusyLean.contender_12 BusyLean.contender_11
  BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8
  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

#check @BusyLean.reflectAFamily_lt_budget26
#check @BusyLean.oracle_lt_budget26
#check @BusyLean.contender_25_lt_height26_42
#check @BusyLean.aStarValue_lt_F26
#check @BusyLean.contender_25_lt_selected_F26
#check @BusyLean.contender_25_lt_contender_26
