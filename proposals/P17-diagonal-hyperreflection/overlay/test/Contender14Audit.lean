import BusyLean.Comparison14
import Lean

open Lean Elab Command

/-- All constants reachable from a declaration through its type and value. -/
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

/-- Fail when one of the listed constants occurs in the transitive closure. -/
elab "#assert_not_in_closure " root:ident " : " bad:ident* : command => do
  let env ← getEnv
  let r ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo root
  let cl := constClosure env r
  for b in bad do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
    if cl.contains n then throwError m!"{r} depends on forbidden constant {n}"
  logInfo m!"{r}: closure of {cl.size} constants avoids all {bad.size} forbidden names"

-- Axiom audit: only the contest-permitted axioms may appear.
#print axioms BusyLean.contender_14
#print axioms BusyLean.contender_13_lt_contender_14
#print axioms BusyLean.family13_lt_F14
#print axioms BusyLean.fvalue_lt_F14
#print axioms BusyLean.diagonalLift_rank_lt_succ

-- No earlier contender value is used as a hidden seed.  The construction uses
-- the earlier families and languages, as the contest rules permit.
#assert_not_in_closure BusyLean.contender_14 :
  BusyLean.contender_13 BusyLean.contender_12 BusyLean.contender_11
  BusyLean.contender_10 BusyLean.contender_9 BusyLean.contender_8
  BusyLean.contender_7 BusyLean.contender_6 BusyLean.contender_5

#check @BusyLean.contender_13_lt_contender_14
#check @BusyLean.fdDiagonal_rank_lt_succ
#check @BusyLean.fvalue_lt_F14

-- A small executable witness for the generic machinery only.  It does not
-- unfold any contender.
def tinySeed : BusyLean.W.Family := fun i n => i + n

def tinyProgressive : BusyLean.Transformer := fun seed _ n => seed 0 n + n + 1

#eval (BusyLean.stageLift BusyLean.liftTransformer tinyProgressive .leaf tinySeed 0 0)
