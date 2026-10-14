import BusyLean.Independent.AckermannLtSystemT
import BusyLean.Independent.SystemTLtEps
import BusyLean.Independent.EpsLtLadder
import BusyLean.Independent.Tower
import Lean

/-!
# Audit of the independent tower

Run with `lake env lean test/IndependentAudit.lean`. It:

1. prints the axioms of every rung and comparison (only `propext` and
   `Quot.sound` are allowed);
2. lists, for every rung, the modules its definition depends on;
3. fails if a rung's definition reaches a lower rung's module, or any module
   of the main tower's contenders (`BusyLean.Contender*`, `BusyLean.Comparison*`),
   except that rung 2 *is* the ported Contender 5.
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

/-- The modules (outside Lean's own `Init`/`Lean`/`Std`) that define the
constants in the closure of `root`. -/
def closureModules (env : Environment) (root : Name) : Array Name := Id.run do
  let mut mods : Array Name := #[]
  for c in (constClosure env root).toList do
    if let some i := env.getModuleIdxFor? c then
      let m := env.header.moduleNames[i.toNat]!
      let top := m.getRoot
      if top != `Init && top != `Lean && top != `Std && !mods.contains m then
        mods := mods.push m
  return mods.qsort (fun a b => a.toString < b.toString)

/-- `#assert_independent root allowing m₁ … : f₁ …` lists the modules in the
closure of `root` and fails if one of them is a main-tower contender module
(other than the allowed ones) or one of the forbidden modules `fᵢ`. -/
elab "#assert_independent " root:ident " allowing " ok:ident* " forbidding " bad:ident* :
    command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let mods := closureModules env r
  let okN := ok.map (·.getId)
  let badN := bad.map (·.getId)
  for m in mods do
    let s := m.toString
    let contest := s.startsWith "BusyLean.Contender" || s.startsWith "BusyLean.Comparison"
    if (contest && !okN.contains m) || badN.contains m then
      throwError m!"{r} depends on module {m}"
  logInfo m!"{r} depends only on the modules {mods}"

-- 1. Axioms.
#print axioms BusyLean.Indep.contender_1
#print axioms BusyLean.Indep.contender_2
#print axioms BusyLean.Indep.contender_3
#print axioms BusyLean.Indep.contender_4
#print axioms BusyLean.Indep.contender_1_lt_contender_2
#print axioms BusyLean.Indep.contender_2_lt_contender_3
#print axioms BusyLean.Indep.contender_3_lt_contender_4
#print axioms BusyLean.Indep.contender_2_lt_contender_4
#print axioms BusyLean.Indep.independent_tower
#print axioms BusyLean.F.nf_eq_of_steps
#print axioms BusyLean.Indep.Inf.value_le_hardy
#print axioms BusyLean.Indep.Inf.elimAll_spec
#print axioms BusyLean.Indep.eval_le_hardy_eps
#print axioms BusyLean.Indep.TT.eval_bhProgram
#print axioms BusyLean.Indep.Feps_le_F3
#print axioms BusyLean.Indep.TT.utrT_steps

-- 2–3. Independence of the definitions.
#assert_independent BusyLean.Indep.contender_1 allowing forbidding
  BusyLean.Contender5 BusyLean.Independent.SystemT BusyLean.Independent.EpsilonHardy
  BusyLean.Independent.Bachmann BusyLean.Independent.Ladder
#assert_independent BusyLean.Indep.contender_2 allowing BusyLean.Contender5 forbidding
  BusyLean.Independent.Ackermann BusyLean.Independent.EpsilonHardy BusyLean.Independent.Bachmann
  BusyLean.Independent.Ladder
#assert_independent BusyLean.Indep.contender_3 allowing forbidding
  BusyLean.Contender5 BusyLean.Independent.Ackermann BusyLean.Independent.SystemT
  BusyLean.Independent.Ladder
#assert_independent BusyLean.Indep.contender_4 allowing forbidding
  BusyLean.Contender5 BusyLean.Independent.Ackermann BusyLean.Independent.SystemT
  BusyLean.Independent.SystemTFacts BusyLean.Independent.TEmbedding BusyLean.Independent.TTyped
  BusyLean.Independent.EpsilonHardy BusyLean.Independent.Bachmann BusyLean.Independent.TreeLang

-- 4. The statements.
#check @BusyLean.Indep.contender_1_lt_contender_2
#check @BusyLean.Indep.contender_2_lt_contender_3
#check @BusyLean.Indep.contender_3_lt_contender_4
