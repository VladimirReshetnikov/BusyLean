import BusyLean
import Lean

/-!
# Audit

Run with `lake env lean test/Audit.lean`. It:

1. prints the axioms of every submitted declaration (only `propext` is allowed);
2. checks that `contender_6`'s definition does not mention Contender 5's value
   or the old language's winner selection (`#assert_not_in_closure`);
3. lists every old-language constant that *does* appear in the closure, so
   that inherited guards are visible.
-/

open Lean Elab Command

/-- All constants reachable from `root` through types and values. -/
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

/-- Fail if any listed constant is in the closure of the first one. -/
elab "#assert_not_in_closure " root:ident " : " bad:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := constClosure env r
  for b in bad do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: closure of {cl.size} constants avoids all {bad.size} forbidden names"

/-- List closure members from the given namespaces. -/
elab "#closure_members " root:ident " in " nss:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := constClosure env r
  for ns in nss do
    let hits := cl.toList.filter (fun n => ns.getId.isPrefixOf n) |>.map toString
    logInfo m!"{r} uses {hits.length} constants under {ns.getId}: {hits.toArray.qsort (· < ·)}"

-- 1. Axioms.
#print axioms BusyLean.contender_5
#print axioms BusyLean.contender_6
#print axioms BusyLean.contender_5_lt_contender_6
#print axioms BusyLean.p5_lt_contender_6
#print axioms BusyLean.p5Family_lt_finalFamily
#print axioms BusyLean.defined_tree_eventually_lt
#print axioms BusyLean.program_lt_finalFamily
#print axioms BusyLean.PortAgreement.largest_eq_oldMaximum
#print axioms BusyLean.contender_7
#print axioms BusyLean.contender_6_lt_contender_7
#print axioms BusyLean.fvalue_lt_contender_7
#print axioms BusyLean.F.sn_of_typed

-- 2. The definition never mentions Contender 5, its winner selection, or the
--    contender constants of P5.
#assert_not_in_closure BusyLean.contender_6 :
  BusyLean.contender_5 BusyLean.C5.largestOfDepth BusyLean.C5.maxBy
  BusyLean.C5.largestSTLCNatRecNatOfDepth BigNumber.contender_5 BigNumber.contender_6

-- 3. Old-language material that is reachable: P5's seed contains the guard
--    `max (oldMaximum n) (wMaximum n)`, which is inherited here.
#closure_members BusyLean.contender_6 in BusyLean.C5 BusyLean.PortAgreement
#closure_members BusyLean.contender_6 in BigNumber.oldMaximum BigNumber.oldTerms

-- Contender 7's definition uses System F normalization and Contender 6's
-- family as its oracle, but never the constant `contender_6` itself.
#assert_not_in_closure BusyLean.contender_7 :
  BusyLean.contender_6 BusyLean.contender_5 BigNumber.contender_6

-- The statements, for the record.
#check @BusyLean.contender_5_lt_contender_6
#check @BusyLean.p5_lt_contender_6
#check @BusyLean.contender_6_lt_contender_7
#check @BusyLean.F.sn_of_typed

-- The final family is a genuine computable function (only input 0 is feasible).
#eval BusyLean.finalFamily 0
