import Original
import Arboreal
import Forest

/-!
Small semantic regression tests. These tests are kernel-checked equalities,
not trusted native-decide certificates. The final contender and Rw are never
evaluated. In particular the tree tests exercise the *object-language*
recursor, including function-valued and tree-valued elimination.
-/

namespace Smoke

theorem reversedLookup0 : Original.lookup [10, 11, 12] 0 = some 12 := rfl
theorem reversedLookup1 : Original.lookup [10, 11, 12] 1 = some 11 := rfl
theorem reversedLookup2 : Original.lookup [10, 11, 12] 2 = some 10 := rfl
theorem reversedLookup3 : Original.lookup [10, 11, 12] 3 = none := rfl

theorem originalUnbound : Original.eval (.var 42) = 0 := rfl
theorem originalApplyNumber : Original.eval (.app .zero .succ) = 0 := rfl
theorem originalBadArgument : Original.eval (.app .succ .succ) = 1 := rfl

theorem originalBadArrowCast :
    Original.cast (src := .nat) (.arr .nat .nat) (7 : Nat) (9 : Nat) = (0 : Nat) := rfl

theorem originalBadNatCast :
    Original.cast (src := .arr .nat .nat) .nat Nat.succ = (0 : Nat) := rfl

def originalNumeral : Nat → Original.Term
  | 0 => .zero
  | k + 1 => .app .succ (originalNumeral k)

theorem originalOutermostBinder :
    Original.eval
      (.app (.app (.lam .nat (.arr .nat .nat) (.lam .nat .nat (.var 0)))
        (originalNumeral 2)) (originalNumeral 3)) = 2 := rfl

theorem originalInnermostBinder :
    Original.eval
      (.app (.app (.lam .nat (.arr .nat .nat) (.lam .nat .nat (.var 1)))
        (originalNumeral 2)) (originalNumeral 3)) = 3 := rfl

def numeral : Nat → Arboreal.Term
  | 0 => .zero
  | k + 1 => .app .succ (numeral k)

def treeTwo : Arboreal.Term := .app .treeSucc (.app .treeSucc .treeZero)

def treeLimit : Arboreal.Term := .app .treeLim (.lam .nat .tree treeTwo)

def treeSuccNat : Arboreal.Term :=
  .lam .tree (.arr .nat .nat) (.lam .nat .nat (.app .succ (.var 1)))

def treeLimitNat : Arboreal.Term :=
  .lam (.arr .nat .tree) (.arr (.arr .nat .nat) .nat)
    (.lam (.arr .nat .nat) .nat (.app (.var 1) .zero))

def treeToNat (t : Arboreal.Term) : Arboreal.Term :=
  .app (.app (.app (.app (.treeRec .nat) .zero) treeSuccNat) treeLimitNat) t

theorem treeRecNatSuccessor : Arboreal.eval Nat.succ 0 (treeToNat treeTwo) = 2 := rfl
theorem treeRecNatLimit : Arboreal.eval Nat.succ 0 (treeToNat treeLimit) = 2 := rfl

def fnTy : Arboreal.Ty := .arr .nat .nat

def treeSuccFn : Arboreal.Term :=
  .lam .tree (.arr fnTy fnTy)
    (.lam fnTy fnTy
      (.lam .nat .nat (.app .succ (.app (.var 1) (.var 2)))))

def treeLimitFn : Arboreal.Term :=
  .lam (.arr .nat .tree) (.arr (.arr .nat fnTy) fnTy)
    (.lam (.arr .nat fnTy) fnTy (.app (.var 1) .zero))

def treeToFn (t : Arboreal.Term) : Arboreal.Term :=
  .app (.app (.app (.app (.treeRec fnTy) (.lam .nat .nat (.var 0)))
    treeSuccFn) treeLimitFn) t

theorem treeRecFunctionSuccessor :
    Arboreal.eval Nat.succ 0 (.app (treeToFn treeTwo) (numeral 3)) = 5 := rfl

theorem treeRecFunctionLimit :
    Arboreal.eval Nat.succ 0 (.app (treeToFn treeLimit) (numeral 3)) = 5 := rfl

def treeSuccTree : Arboreal.Term :=
  .lam .tree (.arr .tree .tree) (.lam .tree .tree (.app .treeSucc (.var 1)))

def treeLimitTree : Arboreal.Term :=
  .lam (.arr .nat .tree) (.arr (.arr .nat .tree) .tree)
    (.lam (.arr .nat .tree) .tree (.app .treeLim (.var 1)))

def treeToTree (t : Arboreal.Term) : Arboreal.Term :=
  .app (.app (.app (.app (.treeRec .tree) .treeZero) treeSuccTree) treeLimitTree) t

theorem treeRecTreeSuccessor :
    Arboreal.interp Nat.succ 0 [] (treeToTree treeTwo) =
      ⟨.tree, BTree.succ (BTree.succ BTree.zero)⟩ := rfl

theorem treeRecTreeLimit :
    Arboreal.interp Nat.succ 0 [] (treeToTree treeLimit) =
      ⟨.tree, BTree.lim (fun _ => BTree.succ (BTree.succ BTree.zero))⟩ := rfl

theorem arborealApplyTree : Arboreal.eval Nat.succ 0 (.app .treeZero .zero) = 0 := rfl

theorem arborealOldIsClosed :
    Arboreal.eval Nat.succ 0
      (.app (.lam .nat .nat (.old (.var 0))) (numeral 3)) = 0 := rfl

def indexedOracles (i m : Nat) : Nat := 10 * i + m

/-- The computed index is n+1, beyond the explicitly joined prefix 0,...,n. -/
def dynamicFamilyCall : Forest.Expr :=
  .app (.app .family (.app (.base .succ) (.base .input))) (.base .input)

theorem familySelectsBeyondPrefix :
    Forest.eval indexedOracles 2 dynamicFamilyCall = 32 := rfl

def familyUnderLambda : Forest.Expr :=
  .app (.lam .nat .nat
      (.app (.app .family (.base (.var 0))) (.base .input)))
    (.base (numeral 3))

theorem familyReceivesBaseVariable :
    Forest.eval indexedOracles 2 familyUnderLambda = 32 := rfl

/-- Each recursive value selects the next oracle, inside the recursor branch. -/
def forestSuccessor : Forest.Expr :=
  .lam .tree (.arr .nat .nat)
    (.lam .nat .nat
      (.app (.app .family (.base (.var 1))) (.base .input)))

def forestTreeRec (t : Arboreal.Term) : Forest.Expr :=
  .app (.app (.app (.app (.base (.treeRec .nat)) (.base .zero))
    forestSuccessor) (.base treeLimitNat)) (.base t)

theorem familyWithinTreeRecSuccessor :
    Forest.eval indexedOracles 2 (forestTreeRec treeTwo) = 22 := rfl

theorem familyWithinTreeRecLimit :
    Forest.eval indexedOracles 2 (forestTreeRec treeLimit) = 22 := rfl

theorem forestSemanticChecks :
    Forest.eval indexedOracles 2 dynamicFamilyCall = 32 ∧
    Forest.eval indexedOracles 2 familyUnderLambda = 32 ∧
    Forest.eval indexedOracles 2 (forestTreeRec treeTwo) = 22 ∧
    Forest.eval indexedOracles 2 (forestTreeRec treeLimit) = 22 :=
  ⟨familySelectsBeyondPrefix, familyReceivesBaseVariable,
    familyWithinTreeRecSuccessor, familyWithinTreeRecLimit⟩

/-- Core evaluation regressions; the remaining assertions are audited below. -/
theorem semanticChecks :
    Original.lookup [10, 11, 12] 0 = some 12 ∧
    Original.lookup [10, 11, 12] 1 = some 11 ∧
    Original.lookup [10, 11, 12] 2 = some 10 ∧
    Original.lookup [10, 11, 12] 3 = none ∧
    Original.eval (.var 42) = 0 ∧
    Original.eval (.app .zero .succ) = 0 ∧
    Original.eval (.app .succ .succ) = 1 ∧
    Arboreal.eval Nat.succ 0 (treeToNat treeTwo) = 2 ∧
    Arboreal.eval Nat.succ 0 (treeToNat treeLimit) = 2 ∧
    Arboreal.eval Nat.succ 0 (.app (treeToFn treeTwo) (numeral 3)) = 5 ∧
    Arboreal.eval Nat.succ 0 (.app (treeToFn treeLimit) (numeral 3)) = 5 ∧
    Arboreal.interp Nat.succ 0 [] (treeToTree treeTwo) =
      ⟨.tree, BTree.succ (BTree.succ BTree.zero)⟩ ∧
    Arboreal.interp Nat.succ 0 [] (treeToTree treeLimit) =
      ⟨.tree, BTree.lim (fun _ => BTree.succ (BTree.succ BTree.zero))⟩ :=
  ⟨reversedLookup0, reversedLookup1, reversedLookup2, reversedLookup3,
    originalUnbound, originalApplyNumber, originalBadArgument,
    treeRecNatSuccessor, treeRecNatLimit, treeRecFunctionSuccessor, treeRecFunctionLimit,
    treeRecTreeSuccessor, treeRecTreeLimit⟩

#print axioms Smoke.semanticChecks
#print axioms Smoke.originalBadArrowCast
#print axioms Smoke.originalBadNatCast
#print axioms Smoke.originalOutermostBinder
#print axioms Smoke.originalInnermostBinder
#print axioms Smoke.arborealApplyTree
#print axioms Smoke.arborealOldIsClosed
#print axioms Smoke.forestSemanticChecks

end Smoke
