import BusyLean.Contender12
import BusyLean.SystemFL.Transfinite

/-!
# A ramified universe hierarchy indexed by a language-generated W-tree

The earlier transfinite contenders use explicit, linearly ordered ordinal
notations as atoms.  This module instead uses *addresses in a fixed
countably-branching well-founded tree*.  A level is a finite path from the
root; a level lies immediately below its parent exactly when that path is
valid in the tree.  Well-foundedness is inherited directly from structural
well-foundedness of `WTree`.

The particular tree `autonomousUniverseTree` contains `tree12` as branch zero
and, on the remaining branches, every finite autonomous hyper-closure above
`tree12`.  Thus the object language receives a genuinely ramified hierarchy
whose index is built from the W-language's own language-generated tree, rather
than from a fixed explicit notation system.
-/

namespace BusyLean.Ordinal

open BigNumber (WTree)

/-- A finite address in a countably branching tree.  The constructor is
"snoc-like": `child p i` appends branch `i` to the path `p`. -/
inductive TreePath : Type where
  | root : TreePath
  | child : TreePath → Nat → TreePath
  deriving DecidableEq, Repr

namespace TreePath

/-- Follow a finite address.  Invalid addresses return `none`. -/
def follow (t : WTree Nat) : TreePath → Option (WTree Nat)
  | .root => some t
  | .child p i =>
      match follow t p with
      | some (.node f) => some (f i)
      | _ => none

/-- Boolean validity of an address in a tree. -/
def valid (t : WTree Nat) (p : TreePath) : Bool :=
  match follow t p with
  | some _ => true
  | none => false

/-- `childLt t b a` says that `b` is a valid immediate child of `a` in `t`. -/
def childLt (t : WTree Nat) : TreePath → TreePath → Bool
  | .root, _ => false
  | .child p i, a => decide (p = a) && valid t (.child p i)

/-- Accessibility of a valid address, proved by structural recursion on the
subtree reached by that address. -/
theorem acc_follow (root : WTree Nat) :
    ∀ (cur : WTree Nat) (p : TreePath),
      follow root p = some cur →
      Acc (fun b a => childLt root b a = true) p
  | .leaf, p, hp => by
      refine Acc.intro p ?_
      intro b hb
      cases b with
      | root =>
          simp [childLt] at hb
      | child q i =>
          simp only [childLt, Bool.and_eq_true] at hb
          have hq : q = p := of_decide_eq_true hb.1
          subst q
          have hv : valid root (.child p i) = true := hb.2
          simp [valid, follow, hp] at hv
  | .node f, p, hp => by
      refine Acc.intro p ?_
      intro b hb
      cases b with
      | root =>
          simp [childLt] at hb
      | child q i =>
          simp only [childLt, Bool.and_eq_true] at hb
          have hq : q = p := of_decide_eq_true hb.1
          subst q
          exact acc_follow root (f i) (.child p i) (by
            simp [follow, hp])

/-- The immediate-valid-child relation is well-founded for every `WTree`. -/
theorem childLt_wf (root : WTree Nat) :
    WellFounded (fun b a => childLt root b a = true) := by
  refine ⟨fun p => ?_⟩
  cases hp : follow root p with
  | none =>
      refine Acc.intro p ?_
      intro b hb
      cases b with
      | root =>
          simp [childLt] at hb
      | child q i =>
          simp only [childLt, Bool.and_eq_true] at hb
          have hq : q = p := of_decide_eq_true hb.1
          subst q
          have hv : valid root (.child p i) = true := hb.2
          simp [valid, follow, hp] at hv
  | some cur =>
      exact acc_follow root cur p hp

/-- A simple increasing finite enumeration of paths.  Every finite path occurs
at some stage; duplicates are harmless for finite maxima. -/
def pathsUpTo : Nat → List TreePath
  | 0 => [.root]
  | n + 1 =>
      let ps := pathsUpTo n
      ps ++ ps.flatMap (fun p =>
        (List.range (n + 1)).map (fun i => .child p i))

end TreePath

/-- A fixed countable join containing `tree12` and all finite autonomous
hyper-closures above it.  Branch zero is exactly `tree12`. -/
def autonomousUniverseTree : WTree Nat :=
  .node fun k =>
    match k with
    | 0 => tree12
    | n + 1 =>
        Autonomous.realize
          (Autonomous.hyper n (Autonomous.encode tree12))

/-- Atoms for the ramified W-tree universe hierarchy. -/
abbrev WLevel := TreePath

instance : FL.AtomOrder WLevel where
  lt := TreePath.childLt autonomousUniverseTree

/-- Structural well-foundedness of the W-tree universe hierarchy. -/
theorem wLevel_wf : WellFounded (FL.ALt (α := WLevel)) :=
  TreePath.childLt_wf autonomousUniverseTree

/-- Valid W-tree levels of enumeration depth `n`. -/
def wLevelsUpTo (n : Nat) : List WLevel :=
  (TreePath.pathsUpTo n).filter
    (TreePath.valid autonomousUniverseTree)

/-- The old language-generated index is visibly present at branch zero. -/
theorem follow_tree12 :
    TreePath.follow autonomousUniverseTree (.child .root 0) = some tree12 := rfl

end BusyLean.Ordinal
