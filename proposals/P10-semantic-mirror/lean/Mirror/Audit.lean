import Mirror.Comparison
import Lean

/-! These commands have NOT been executed in the artifact-generation environment.
They are adapted from the pinned repository's dependency-audit implementation. -/
open Lean Elab Command

namespace MirrorAudit

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

elab "#assert_not_in_closure " root:ident " : " bad:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := constClosure env r
  for b in bad do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: {cl.size} reachable constants; forbidden-name audit passed"

elab "#assert_allowed_axioms " root:ident : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := constClosure env r
  for n in cl.toList do
    match env.find? n with
    | some (.axiomInfo _) =>
        if n != ``propext && n != ``Quot.sound then
          throwError m!"{r} depends on forbidden axiom {n}"
    | _ => pure ()
  logInfo m!"{r}: axiom whitelist audit passed"

end MirrorAudit

#print axioms BusyLean.contender_7
#print axioms BusyLean.contender_6_lt_contender_7
#print axioms BusyLean.contender_7_tower_margin
#print axioms BusyLean.Mirror.no_finite_round_program_for_final
#print axioms BusyLean.Mirror.no_limit_program_for_final
#print axioms BusyLean.Mirror.castPair_self
#print axioms BusyLean.Mirror.mem_allTerms_of_rank

#assert_allowed_axioms BusyLean.contender_7
#assert_allowed_axioms BusyLean.contender_6_lt_contender_7
#assert_allowed_axioms BusyLean.contender_7_tower_margin
#assert_allowed_axioms BusyLean.Mirror.no_finite_round_program_for_final
#assert_allowed_axioms BusyLean.Mirror.no_limit_program_for_final

#assert_not_in_closure BusyLean.contender_7 :
  BusyLean.contender_6 BusyLean.finalFamily BusyLean.index
  BigNumber.contender_6 BusyLean.Mirror.boostProgram
  BusyLean.Mirror.numberProgram BusyLean.Mirror.indexProgram

#check @BusyLean.contender_6_lt_contender_7
#check @BusyLean.contender_7_tower_margin
#check @BusyLean.Mirror.iterated_boost_lt_final
