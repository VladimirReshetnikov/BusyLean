import BusyLean
import Lean

/-!
# Contender 7 kernel audit

Run with `lake env lean test/Contender7Audit.lean` after installing the overlay.
It prints axioms, proves that the new number's defining closure does not contain
any incumbent contender value, and records the comparison theorem signatures.
-/

open Lean Elab Command

/-- All constants reachable from `root` through declaration types and values. -/
def contender7ConstClosure (env : Environment) (root : Name) : NameSet := Id.run do
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

/-- Fail if any listed constant occurs in the closure of the first one. -/
elab "#assert_not_in_contender7_closure " root:ident " : " bad:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := contender7ConstClosure env r
  for b in bad do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: closure of {cl.size} constants avoids all {bad.size} forbidden names"

#print axioms BusyLean.contender_7
#print axioms BusyLean.contender_6_lt_contender_7
#print axioms BusyLean.contender_5_lt_contender_7
#print axioms BusyLean.p5_lt_contender_7
#print axioms BusyLean.stageOrder_indexDominates

-- The construction reuses the incumbent language and seed, but not any named
-- incumbent value as an iteration counter or hidden subterm.
#assert_not_in_contender7_closure BusyLean.contender_7 :
  BusyLean.contender_6 BusyLean.contender_5
  BigNumber.contender_6 BigNumber.contender_5

#check @BusyLean.contender_6_lt_contender_7
#check @BusyLean.contender_5_lt_contender_7
#check @BusyLean.p5_lt_contender_7
#check @BusyLean.stageOrder_step
#check @BusyLean.stageOrder_indexDominates
