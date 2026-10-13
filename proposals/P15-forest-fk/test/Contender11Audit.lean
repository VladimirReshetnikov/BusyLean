import BusyLean.Comparison11
import Lean

/-!
# Contender 11 audit

Run with:

```bash
lake env lean test/Contender11Audit.lean
```

This file prints axiom dependencies and checks that the new number does not
use any earlier contender constant.  It intentionally does not evaluate any
contender.
-/

open Lean Elab Command

/-- All constants reachable from `root` through declaration types and values. -/
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

/-- Fail if any listed constant lies in the transitive closure of `root`. -/
elab "#assert_not_in_closure11 " root:ident " : " bad:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := constClosure11 env r
  for b in bad do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: closure of {cl.size} constants avoids all {bad.size} forbidden names"

#print axioms BusyLean.contender_11
#print axioms BusyLean.contender_10_lt_contender_11
#print axioms BusyLean.family10_lt_F11
#print axioms BusyLean.defined_tree_eventually_lt11
#print axioms BusyLean.fvalue_lt_contender_11

#assert_not_in_closure11 BusyLean.contender_11 :
  BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8
  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5
  BigNumber.contender_6 BigNumber.contender_5

#check @BusyLean.contender_10_lt_contender_11
#check @BusyLean.family10_lt_F11
#check @BusyLean.defined_tree_eventually_lt11
#check @BusyLean.fvalue_lt_contender_11
