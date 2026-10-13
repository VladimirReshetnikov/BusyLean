import BusyLean.Comparison15
import Lean

/-! # Universal-envelope Contender 15 audit -/

open Lean Elab Command

/-- All constants reachable from a declaration through types and values. -/
def contender15ConstClosure (env : Environment) (root : Name) : NameSet := Id.run do
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

elab "#contender15_assert_not_in_closure " root:ident " : " bad:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := contender15ConstClosure env r
  for b in bad do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: closure of {cl.size} constants avoids all {bad.size} forbidden names"

#print axioms BusyLean.incoming14Envelope
#print axioms BusyLean.family14
#print axioms BusyLean.diagonalTransformer15
#print axioms BusyLean.metaTower15
#print axioms BusyLean.F15
#print axioms BusyLean.contender_15
#print axioms BusyLean.contender_14_lt_contender_15
#print axioms BusyLean.diagonalOperatorTower14_lt_contender_15
#print axioms BusyLean.rdor14_lt_contender_15
#print axioms BusyLean.rankDiagonal14_lt_contender_15
#print axioms BusyLean.contender_13_lt_contender_15
#print axioms BusyLean.fvalue_lt_contender_15

#contender15_assert_not_in_closure BusyLean.contender_15 :
  BusyLean.contender_14
  BusyLean.Incoming14.DiagonalOperatorTower.contender_14
  BusyLean.Incoming14.RDOR.contender_14
  BusyLean.Incoming14.RankDiagonal.contender_14
  BusyLean.contender_13 BusyLean.contender_12 BusyLean.contender_11
  BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8
  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

#check @BusyLean.family14_lt_F15
#check @BusyLean.contender_14_lt_contender_15
#check @BusyLean.diagonalOperatorTower14_lt_contender_15
#check @BusyLean.rdor14_lt_contender_15
#check @BusyLean.rankDiagonal14_lt_contender_15
#check @BusyLean.contender_13_lt_contender_15
#check @BusyLean.fvalue_lt_contender_15
