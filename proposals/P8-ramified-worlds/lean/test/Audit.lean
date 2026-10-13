import BusyLeanNext
import Lean

/-! Audit tooling only. Its command elaborators are not dependencies of the
number. Adapted from BusyLean/test/Audit.lean (MIT-0), pinned upstream commit.
Do not replace any of these checks with evaluation of a contender. -/
open Lean Elab Command

namespace BusyLeanNextAudit

def constClosure (env : Environment) (root : Name) : NameSet := Id.run do
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

elab "#audit_number " root:ident " avoids " bad:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := constClosure env r
  for b in bad do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then throwError m!"{r} depends on forbidden constant {n}"
  for c in cl.toList do
    let some ci := env.find? c | continue
    match ci with
    | .axiomInfo _ =>
        unless c == ``propext || c == ``Quot.sound do
          throwError m!"{r} depends on disallowed axiom {c}"
    | _ => pure ()
  logInfo m!"AUDIT PASS: {r}; {cl.size} reachable constants"

end BusyLeanNextAudit

#print axioms BusyLean.V7.contender_7
#print axioms BusyLean.V7.contender_6_lt_contender_7
#print axioms BusyLean.V7.towerOrbit_contender6_lt_contender7
#print axioms BusyLean.V7.no_lower_language_representation
#print axioms BusyLean.V7.no_programTree_eq_index

#audit_number BusyLean.V7.contender_7 avoids
  BusyLean.contender_6 BusyLean.finalFamily BusyLean.contender_5
  BigNumber.contender_5 BigNumber.contender_6

#audit_number BusyLean.V7.contender_6_lt_contender_7 avoids
#audit_number BusyLean.V7.towerOrbit_contender6_lt_contender7 avoids
#audit_number BusyLean.V7.no_lower_language_representation avoids
#audit_number BusyLean.V7.no_programTree_eq_index avoids
