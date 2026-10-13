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
#print axioms BusyLean.contender_8
#print axioms BusyLean.contender_7_lt_contender_8
#print axioms BusyLean.fvalue_lt_contender_8
#print axioms BusyLean.Fw.sn_of_typed
#print axioms BusyLean.Fw.infer_sound
#print axioms BusyLean.contender_9
#print axioms BusyLean.contender_8_lt_contender_9
#print axioms BusyLean.defined_tree_eventually_lt9
#print axioms BusyLean.unpair2_code
#print axioms BusyLean.contender_10
#print axioms BusyLean.contender_9_lt_contender_10
#print axioms BusyLean.fvalue_lt_contender_10
#print axioms BusyLean.Fk.sn_of_typed
#print axioms BusyLean.Fk.infer_sound
#print axioms BusyLean.contender_11
#print axioms BusyLean.contender_10_lt_contender_11
#print axioms BusyLean.defined_tree_eventually_lt11
#print axioms BusyLean.contender_12
#print axioms BusyLean.contender_11_lt_contender_12
#print axioms BusyLean.family11_lt_F12
#print axioms BusyLean.contender_13
#print axioms BusyLean.contender_12_lt_contender_13
#print axioms BusyLean.fvalue_lt_contender_13
#print axioms BusyLean.Fd.sn_of_typed
#print axioms BusyLean.Fd.infer_sound
#print axioms BusyLean.contender_14
#print axioms BusyLean.contender_13_lt_contender_14
#print axioms BusyLean.fvalue_lt_contender_14
#print axioms BusyLean.FL.sn_of_typed
#print axioms BusyLean.FL.infer_sound
#print axioms BusyLean.FL.Univ
#print axioms BusyLean.contender_15
#print axioms BusyLean.contender_14_lt_contender_15
#print axioms BusyLean.fvalue_lt_F15
#print axioms BusyLean.diagonalLift_strictlyInflationary
#print axioms BusyLean.contender_16
#print axioms BusyLean.contender_15_lt_contender_16
#print axioms BusyLean.tvalue_lt_F16
#print axioms BusyLean.FL.wfUniv
#print axioms BusyLean.Ordinal.wf_sorted
#print axioms BusyLean.Ordinal.omegaPow_wf
#print axioms BusyLean.contender_17
#print axioms BusyLean.contender_16_lt_contender_17
#print axioms BusyLean.evalue_lt_F17
#print axioms BusyLean.Ordinal.epsilon0_wf
#print axioms BusyLean.contender_18
#print axioms BusyLean.contender_17_lt_contender_18
#print axioms BusyLean.gvalue_lt_F18
#print axioms BusyLean.Ordinal.gamma0_wf
#print axioms BusyLean.Ordinal.Veblen.acc_phi
#print axioms BusyLean.contender_19
#print axioms BusyLean.contender_18_lt_contender_19
#print axioms BusyLean.lvalue_lt_F19
#print axioms BusyLean.Ordinal.largeVeblen_wf
#print axioms BusyLean.Ordinal.LVeblen.acc_phi
#print axioms BusyLean.Ordinal.accQ_sorted
#print axioms BusyLean.contender_20
#print axioms BusyLean.contender_19_lt_contender_20
#print axioms BusyLean.bvalue_lt_F20
#print axioms BusyLean.Ordinal.bachmannHoward_wf
#print axioms BusyLean.Ordinal.BH.accD0
#print axioms BusyLean.contender_21
#print axioms BusyLean.contender_20_lt_contender_21
#print axioms BusyLean.zvalue_lt_F21
#print axioms BusyLean.Ordinal.buchholz_wf
#print axioms BusyLean.Ordinal.Buch.stepR
#print axioms BusyLean.contender_22
#print axioms BusyLean.contender_21_lt_contender_22
#print axioms BusyLean.tvalue22_lt_F22
#print axioms BusyLean.Ordinal.tower_wf
#print axioms BusyLean.Ordinal.BuchB.stepR
#print axioms BusyLean.contender_23
#print axioms BusyLean.contender_22_lt_contender_23
#print axioms BusyLean.tvalue22_lt_F23
#print axioms BusyLean.wDiagonalLift_strictlyInflationary
#print axioms BusyLean.contender_24
#print axioms BusyLean.contender_23_lt_contender_24
#print axioms BusyLean.rvalue_lt_F24
#print axioms BusyLean.Ordinal.roundTower_wf

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

-- Contender 8's definition uses System F-omega normalization and Contender 7's
-- family as its oracle, but never the constant `contender_7` itself.
#assert_not_in_closure BusyLean.contender_8 :
  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

-- Contender 9's definition reflects F-omega along Contender 6's index, seeded
-- with Contender 8's family; the earlier contender constants never occur.
#assert_not_in_closure BusyLean.contender_9 :
  BusyLean.contender_8 BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

-- Contender 10's definition uses kind-polymorphic F-omega normalization and
-- Contender 9's family as its oracle; the earlier contender constants never occur.
#assert_not_in_closure BusyLean.contender_10 :
  BusyLean.contender_9 BusyLean.contender_8 BusyLean.contender_7 BusyLean.contender_6
  BusyLean.contender_5

#assert_not_in_closure BusyLean.contender_11 :
  BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8 BusyLean.contender_7
  BusyLean.contender_6 BusyLean.contender_5

#assert_not_in_closure BusyLean.contender_12 :
  BusyLean.contender_11 BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8
  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

#assert_not_in_closure BusyLean.contender_13 :
  BusyLean.contender_12 BusyLean.contender_11 BusyLean.contender_10 BusyLean.contender_9
  BusyLean.contender_8 BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

#assert_not_in_closure BusyLean.contender_14 :
  BusyLean.contender_13 BusyLean.contender_12 BusyLean.contender_11 BusyLean.contender_10
  BusyLean.contender_9 BusyLean.contender_8 BusyLean.contender_7 BusyLean.contender_6
  BusyLean.contender_5

#assert_not_in_closure BusyLean.contender_15 :
  BusyLean.contender_14 BusyLean.contender_13 BusyLean.contender_12 BusyLean.contender_11
  BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8 BusyLean.contender_7
  BusyLean.contender_6 BusyLean.contender_5

#assert_not_in_closure BusyLean.contender_16 :
  BusyLean.contender_15 BusyLean.contender_14 BusyLean.contender_13 BusyLean.contender_12
  BusyLean.contender_11 BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8
  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

#assert_not_in_closure BusyLean.contender_17 :
  BusyLean.contender_16 BusyLean.contender_15 BusyLean.contender_14 BusyLean.contender_13
  BusyLean.contender_12 BusyLean.contender_11 BusyLean.contender_10 BusyLean.contender_9
  BusyLean.contender_8 BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

#assert_not_in_closure BusyLean.contender_18 :
  BusyLean.contender_17 BusyLean.contender_16 BusyLean.contender_15 BusyLean.contender_14
  BusyLean.contender_13 BusyLean.contender_12 BusyLean.contender_11 BusyLean.contender_10
  BusyLean.contender_9 BusyLean.contender_8 BusyLean.contender_7 BusyLean.contender_6
  BusyLean.contender_5

#assert_not_in_closure BusyLean.contender_19 :
  BusyLean.contender_18 BusyLean.contender_17 BusyLean.contender_16 BusyLean.contender_15
  BusyLean.contender_14 BusyLean.contender_13 BusyLean.contender_12 BusyLean.contender_11
  BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8 BusyLean.contender_7
  BusyLean.contender_6 BusyLean.contender_5

#assert_not_in_closure BusyLean.contender_20 :
  BusyLean.contender_19 BusyLean.contender_18 BusyLean.contender_17 BusyLean.contender_16
  BusyLean.contender_15 BusyLean.contender_14 BusyLean.contender_13 BusyLean.contender_12
  BusyLean.contender_11 BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8
  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

#assert_not_in_closure BusyLean.contender_21 :
  BusyLean.contender_20 BusyLean.contender_19 BusyLean.contender_18 BusyLean.contender_17
  BusyLean.contender_16 BusyLean.contender_15 BusyLean.contender_14 BusyLean.contender_13
  BusyLean.contender_12 BusyLean.contender_11 BusyLean.contender_10 BusyLean.contender_9
  BusyLean.contender_8 BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

#assert_not_in_closure BusyLean.contender_22 :
  BusyLean.contender_21 BusyLean.contender_20 BusyLean.contender_19 BusyLean.contender_18
  BusyLean.contender_17 BusyLean.contender_16 BusyLean.contender_15 BusyLean.contender_14
  BusyLean.contender_13 BusyLean.contender_12 BusyLean.contender_11 BusyLean.contender_10
  BusyLean.contender_9 BusyLean.contender_8 BusyLean.contender_7 BusyLean.contender_6
  BusyLean.contender_5

#assert_not_in_closure BusyLean.contender_23 :
  BusyLean.contender_22 BusyLean.contender_21 BusyLean.contender_20 BusyLean.contender_19
  BusyLean.contender_18 BusyLean.contender_17 BusyLean.contender_16 BusyLean.contender_15
  BusyLean.contender_14 BusyLean.contender_13 BusyLean.contender_12 BusyLean.contender_11
  BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8 BusyLean.contender_7
  BusyLean.contender_6 BusyLean.contender_5

#assert_not_in_closure BusyLean.contender_24 :
  BusyLean.contender_23 BusyLean.contender_22 BusyLean.contender_21 BusyLean.contender_20
  BusyLean.contender_19 BusyLean.contender_18 BusyLean.contender_17 BusyLean.contender_16
  BusyLean.contender_15 BusyLean.contender_14 BusyLean.contender_13 BusyLean.contender_12
  BusyLean.contender_11 BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8
  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

-- The statements, for the record.
#check @BusyLean.contender_5_lt_contender_6
#check @BusyLean.p5_lt_contender_6
#check @BusyLean.contender_6_lt_contender_7
#check @BusyLean.F.sn_of_typed
#check @BusyLean.contender_7_lt_contender_8
#check @BusyLean.Fw.sn_of_typed
#check @BusyLean.contender_8_lt_contender_9
#check @BusyLean.contender_9_lt_contender_10
#check @BusyLean.contender_10_lt_contender_11
#check @BusyLean.contender_11_lt_contender_12
#check @BusyLean.contender_12_lt_contender_13
#check @BusyLean.Fd.sn_of_typed
#check @BusyLean.contender_13_lt_contender_14
#check @BusyLean.FL.sn_of_typed
#check @BusyLean.contender_14_lt_contender_15
#check @BusyLean.contender_15_lt_contender_16
#check @BusyLean.contender_16_lt_contender_17
#check @BusyLean.contender_17_lt_contender_18
#check @BusyLean.contender_18_lt_contender_19
#check @BusyLean.contender_19_lt_contender_20
#check @BusyLean.contender_20_lt_contender_21
#check @BusyLean.contender_21_lt_contender_22
#check @BusyLean.contender_22_lt_contender_23
#check @BusyLean.contender_23_lt_contender_24
#check @BusyLean.Ordinal.roundTower_wf
#check @BusyLean.Ordinal.tower_wf
#check @BusyLean.Ordinal.buchholz_wf
#check @BusyLean.Ordinal.bachmannHoward_wf
#check @BusyLean.Ordinal.largeVeblen_wf
#check @BusyLean.Ordinal.gamma0_wf
#check @BusyLean.Ordinal.epsilon0_wf
#check @BusyLean.FL.wfUniv
#check @BusyLean.Ordinal.wf_sorted
#check @BusyLean.Fk.sn_of_typed

-- The final family is a genuine computable function (only input 0 is feasible).
#eval BusyLean.finalFamily 0
