import BusyLean.SystemFL.Transfinite

/-!
# Ladders indexed by addresses in a tree ordinal

Idea from proposal P25 (`proposals/P25-autonomous-wtree-universes`): atoms are
finite *addresses* in a computable well-founded tree. Here the trees are tree
ordinals (`Tre`: zero, successor, countable limits, and two kinds of higher
suprema used by collapsing functions), and the order is **strict descendant**:
`b < a` when the valid address `b` extends `a`.

* The order is decidable: compare addresses and follow `b` in the tree.
* It is well-founded *structurally*, by recursion on the subtree reached by
  `a`. No ordinal-notation theory is needed.

So the ladder of universes over `Addr t` has the length of the rank of `t`,
for any countable tree ordinal `t` Lean can define.
-/

namespace BusyLean.Ordinal

/-- Tree ordinals with countable limits and suprema indexed by `X` and `Y`. -/
inductive Tre (X Y : Type) where
  | zero : Tre X Y
  | succ : Tre X Y → Tre X Y
  | lim : (Nat → Tre X Y) → Tre X Y
  | supL : (X → Tre X Y) → Tre X Y
  | supH : (Y → Tre X Y) → Tre X Y

/-- Countable tree ordinals (only countable branching). -/
abbrev CTree := Tre Empty Empty

/-- Finite addresses. -/
inductive TreePath where
  | root : TreePath
  | child : TreePath → Nat → TreePath
  deriving DecidableEq

namespace TreePath

/-- Children of a countable tree: `succ t` has the single child `t` (at every
index), `lim f` has the children `f i`. -/
def childOf : CTree → Nat → Option CTree
  | .succ t, _ => some t
  | .lim f, i => some (f i)
  | _, _ => none

def follow (t : CTree) : TreePath → Option CTree
  | .root => some t
  | .child p i =>
      match follow t p with
      | some s => childOf s i
      | none => none

def valid (t : CTree) (p : TreePath) : Bool := (follow t p).isSome

/-- `b` strictly extends `a`. -/
def isDesc : TreePath → TreePath → Bool
  | .root, _ => false
  | .child p _, a => decide (p = a) || isDesc p a

/-- The descendant order on valid addresses. -/
def lt (t : CTree) (b a : TreePath) : Bool := isDesc b a && valid t b

theorem isDesc_split : ∀ {b : TreePath} {a : TreePath}, isDesc b a = true →
    ∃ j, b = .child a j ∨ isDesc b (.child a j) = true
  | .root, _, h => by simp [isDesc] at h
  | .child p i, a, h => by
      simp only [isDesc, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with rfl | h
      · exact ⟨i, Or.inl rfl⟩
      · obtain ⟨j, hj⟩ := isDesc_split h
        refine ⟨j, Or.inr ?_⟩
        rcases hj with rfl | hj
        · simp [isDesc]
        · simp [isDesc, hj]

theorem follow_none_desc (t : CTree) : ∀ {b a : TreePath}, follow t a = none →
    isDesc b a = true → follow t b = none
  | .root, _, _, h => by simp [isDesc] at h
  | .child p i, a, ha, h => by
      simp only [isDesc, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with rfl | h
      · simp [follow, ha]
      · simp [follow, follow_none_desc t ha h]

theorem follow_leafish_desc (t : CTree) {a : TreePath} {s : CTree} (ha : follow t a = some s)
    (hs : ∀ i, childOf s i = none) : ∀ {b : TreePath}, isDesc b a = true → follow t b = none := by
  intro b hb
  obtain ⟨j, hj⟩ := isDesc_split hb
  have hc : follow t (.child a j) = none := by simp [follow, ha, hs j]
  rcases hj with rfl | hj
  · exact hc
  · exact follow_none_desc t hc hj

/-- Accessibility of an address, by structural recursion on the subtree it reaches. -/
theorem acc_follow (t : CTree) : ∀ (s : CTree) (a : TreePath), follow t a = some s →
    Acc (fun b a => lt t b a = true) a
  | .lim f, a, ha => by
      refine Acc.intro a fun b hb => ?_
      simp only [lt, Bool.and_eq_true] at hb
      obtain ⟨j, hj⟩ := isDesc_split hb.1
      have hc : follow t (.child a j) = some (f j) := by simp [follow, ha, childOf]
      have hacc := acc_follow t (f j) (.child a j) hc
      rcases hj with rfl | hj
      · exact hacc
      · exact hacc.inv (by simp only [lt, hj, hb.2, Bool.and_self])
  | .succ s, a, ha => by
      refine Acc.intro a fun b hb => ?_
      simp only [lt, Bool.and_eq_true] at hb
      obtain ⟨j, hj⟩ := isDesc_split hb.1
      have hc : follow t (.child a j) = some s := by simp [follow, ha, childOf]
      have hacc := acc_follow t s (.child a j) hc
      rcases hj with rfl | hj
      · exact hacc
      · exact hacc.inv (by simp only [lt, hj, hb.2, Bool.and_self])
  | .zero, a, ha => Acc.intro a fun b hb => by
      simp only [lt, Bool.and_eq_true, valid] at hb
      rw [follow_leafish_desc t ha (fun _ => rfl) hb.1] at hb; simp at hb
  | .supL g, a, ha => Acc.intro a fun b hb => by
      simp only [lt, Bool.and_eq_true, valid] at hb
      rw [follow_leafish_desc t ha (fun _ => rfl) hb.1] at hb; simp at hb
  | .supH g, a, ha => Acc.intro a fun b hb => by
      simp only [lt, Bool.and_eq_true, valid] at hb
      rw [follow_leafish_desc t ha (fun _ => rfl) hb.1] at hb; simp at hb

theorem lt_wf (t : CTree) : WellFounded (fun b a => lt t b a = true) := by
  refine ⟨fun a => ?_⟩
  cases ha : follow t a with
  | some s => exact acc_follow t s a ha
  | none =>
    exact Acc.intro a fun b hb => by
      simp only [lt, Bool.and_eq_true, valid] at hb
      rw [follow_none_desc t ha hb.1] at hb; simp at hb

theorem isDesc_trans : ∀ {c b a : TreePath}, isDesc c b = true → isDesc b a = true →
    isDesc c a = true
  | .root, _, _, h, _ => by simp [isDesc] at h
  | .child p _, b, a, h1, h2 => by
      simp only [isDesc, Bool.or_eq_true, decide_eq_true_eq] at h1 ⊢
      rcases h1 with rfl | h1
      · exact Or.inr h2
      · exact Or.inr (isDesc_trans h1 h2)

/-- The descendant order is transitive. -/
theorem lt_trans (t : CTree) {c b a : TreePath} (h1 : lt t c b = true) (h2 : lt t b a = true) :
    lt t c a = true := by
  simp only [lt, Bool.and_eq_true] at h1 h2 ⊢
  exact ⟨isDesc_trans h1.1 h2.1, h1.2⟩

/-- Addresses with at most `n` steps and indices below `n`. -/
def upTo : Nat → List TreePath
  | 0 => [.root]
  | n + 1 =>
      let ps := upTo n
      ps ++ ps.flatMap fun p => (List.range (n + 1)).map fun i => .child p i

end TreePath

/-- Addresses in the tree `t`, as atoms of a ladder. -/
def Addr (_t : CTree) : Type := TreePath

instance (t : CTree) : DecidableEq (Addr t) := inferInstanceAs (DecidableEq TreePath)

instance (t : CTree) : FL.AtomOrder (Addr t) := ⟨TreePath.lt t⟩

theorem addr_wf (t : CTree) : WellFounded (FL.ALt (α := Addr t)) := TreePath.lt_wf t

/-- Valid addresses of enumeration depth `n`. -/
def addrUpTo (t : CTree) (n : Nat) : List (Addr t) :=
  (TreePath.upTo n).filter (TreePath.valid t)

end BusyLean.Ordinal
