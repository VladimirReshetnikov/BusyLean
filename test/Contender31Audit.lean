import BusyLean.Comparison31
import Lean

/-!
# Contender 31 audit

This focused audit checks the new definitions and comparison theorem, and
verifies that `contender_31` reuses Contender 30's constructions without
embedding any named predecessor contender constant.
-/

open Lean Elab Command

/-- All constants reachable from `root` through types and values. -/
def contender31ConstClosure (env : Environment) (root : Name) : NameSet := Id.run do
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
elab "#contender31_assert_not_in_closure " root:ident " : " bad:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := contender31ConstClosure env r
  for b in bad do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: closure of {cl.size} constants avoids all {bad.size} forbidden names"

#print axioms BusyLean.budget31
#print axioms BusyLean.reflectTLStarFamily
#print axioms BusyLean.tlStarTransformer
#print axioms BusyLean.F31
#print axioms BusyLean.contender_31
#print axioms BusyLean.contender_30_lt_height31_42
#print axioms BusyLean.tlStarValue_lt_F31
#print axioms BusyLean.contender_30_lt_contender_31

#contender31_assert_not_in_closure BusyLean.contender_31 :
  BusyLean.contender_30 BusyLean.contender_29 BusyLean.contender_28
  BusyLean.contender_27 BusyLean.contender_26 BusyLean.contender_25
  BusyLean.contender_24 BusyLean.contender_23 BusyLean.contender_22
  BusyLean.contender_21 BusyLean.contender_20 BusyLean.contender_19
  BusyLean.contender_18 BusyLean.contender_17 BusyLean.contender_16
  BusyLean.contender_15 BusyLean.contender_14 BusyLean.contender_13
  BusyLean.contender_12 BusyLean.contender_11 BusyLean.contender_10
  BusyLean.contender_9 BusyLean.contender_8 BusyLean.contender_7
  BusyLean.contender_6 BusyLean.contender_5

#check @BusyLean.reflectTLFamily_lt_budget31
#check @BusyLean.oracle_lt_budget31
#check @BusyLean.contender_30_lt_height31_42
#check @BusyLean.tlStarValue_lt_F31
#check @BusyLean.contender_30_lt_selected_F31
#check @BusyLean.contender_30_lt_contender_31
