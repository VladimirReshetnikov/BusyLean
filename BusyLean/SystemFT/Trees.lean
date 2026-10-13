import BusyLean.SystemFT.Candidates
import BusyLean.SystemFT.Church
import BusyLean.SystemFT.Normalize
import BusyLean.Ordinal.TreeAddress
import BigNumber.Definitions

/-!
# Reading off the trees that System F programs denote

A closed program of type `tree` is in `WT` (`wt_of_typed`). `toTree` reads its
tree off its normal form:

* `con 1 b` gives `succ (toTree b)`,
* `con 2 g` gives `lim (k ↦ toTree (g k̄))`,
* anything else gives `zero`.

The recursion is well-founded because `WT` is inductive: the *child* relation
(reduce, then take a constructor argument) is accessible from every `WT` term.
Like `nf`, `toTree` uses `termination_by` on a bundled type, so it is compiled
as ordinary code and depends only on `propext` and `Quot.sound`.

The trees can be enormous. Polymorphic Church trees `∀X. X → (X → X) →
((nat → X) → X) → X` can be instantiated at `X = tree`, so every tree that
System F defines through its impredicative encodings becomes a real `CTree`.
-/

namespace BusyLean.FT

open Tm Ordinal

/-- Reflexive-transitive closure of `Step`. -/
inductive Reach (f : Nat → Nat) : Tm → Tm → Prop where
  | refl (t : Tm) : Reach f t t
  | step {t u v : Tm} : Step f t u → Reach f u v → Reach f t v

theorem WT.reach {t v : Tm} (h : WT f t) (r : Reach f t v) : WT f v := by
  induction r with
  | refl => exact h
  | step s _ ih => exact ih (h.step s)

/-- `nf` is reached from the term by reduction. -/
theorem nf_reach (f : Nat → Nat) (x : SNTm f) : Reach f x.term (nf f x) := by
  obtain ⟨t, h⟩ := x
  induction h with
  | intro t hacc ih =>
      rw [nf]
      split
      · exact Reach.refl _
      · next u hu => exact Reach.step (nstep_sound hu) (ih u (nstep_sound hu))

/-- `x` is a child of `t`: some reduct of `t` is a constructor application
with argument `x` (successor), or `x = g k̄` for the argument `g` (limit). -/
def Child (f : Nat → Nat) (x t : Tm) : Prop :=
  ∃ v, Reach f t v ∧ (v = app (con 1) x ∨ ∃ g k, v = app (con 2) g ∧ x = app g (num k))

theorem acc_child {t : Tm} (h : WT f t) : Acc (Child f) t := by
  induction h with
  | @mk t _ _ _ _ ihs ih1 ih2 =>
      refine Acc.intro t fun x ⟨v, r, hv⟩ => ?_
      cases r with
      | refl =>
          rcases hv with rfl | ⟨g, k, rfl, rfl⟩
          · exact ih1 x rfl
          · exact ih2 g rfl k
      | step s r => exact Acc.inv (ihs _ s) ⟨v, r, hv⟩

/-- A term bundled with a proof that it denotes a well-founded tree. -/
structure WTTm (f : Nat → Nat) where
  term : Tm
  wt : WT f term

instance (priority := high) wtRel (f : Nat → Nat) : WellFoundedRelation (WTTm f) where
  rel x y := Child f x.term y.term
  wf := ⟨fun ⟨t, h⟩ => by
    have a := acc_child h
    induction a with
    | intro t _ ih => exact Acc.intro _ fun ⟨u, hu⟩ c => ih u c hu⟩

theorem WT.succ_arg {t b : Tm} (h : WT f t) (e : t = app (con 1) b) : WT f b := by
  cases h with
  | mk _ _ h1 _ => exact h1 b e

theorem WT.lim_arg {t g : Tm} (h : WT f t) (e : t = app (con 2) g) (k : Nat) :
    WT f (app g (num k)) := by
  cases h with
  | mk _ _ _ h2 => exact h2 g e k

/-- The tree denoted by a `WT` term. -/
def toTree (f : Nat → Nat) (x : WTTm f) : CTree :=
  match h : nf f ⟨x.term, x.wt.sn⟩ with
  | app (con 1) b =>
      .succ (toTree f ⟨b, (x.wt.reach (nf_reach f ⟨x.term, x.wt.sn⟩)).succ_arg h⟩)
  | app (con 2) g =>
      .lim fun k => toTree f ⟨app g (num k),
        (x.wt.reach (nf_reach f ⟨x.term, x.wt.sn⟩)).lim_arg h k⟩
  | _ => .zero
termination_by x
decreasing_by
  · exact ⟨_, nf_reach f ⟨x.term, x.wt.sn⟩, Or.inl h⟩
  · exact ⟨_, nf_reach f ⟨x.term, x.wt.sn⟩, Or.inr ⟨g, k, h, rfl⟩⟩

/-! ## Enumeration -/

open Ty

/-- Types of enumeration depth `≤ n`, including `tree`. -/
def tysUpTo : Nat → List Ty
  | 0 => []
  | n + 1 =>
      let ts := tysUpTo n
      Ty.tree :: ((BigNumber.natsUpTo n).map tvar ++
        ((BigNumber.cross ts ts).map (fun p => arr p.1 p.2) ++ ts.map all))

/-- Church-style programs of enumeration depth `≤ n`, with tree constructors. -/
def ctmsUpTo : Nat → List CTm
  | 0 => []
  | n + 1 =>
      let ts := tysUpTo n
      let es := ctmsUpTo n
      (BigNumber.natsUpTo n).map CTm.var ++
      ((BigNumber.cross ts es).map (fun p => CTm.lam p.1 p.2) ++
      ((BigNumber.cross es es).map (fun p => CTm.app p.1 p.2) ++
      (es.map CTm.tlam ++
      ((BigNumber.cross es ts).map (fun p => CTm.tapp p.1 p.2) ++
      [CTm.orc, CTm.con 0, CTm.con 1, CTm.con 2]))))

/-- The tree a program denotes relative to the oracle `f`, if it is a closed
program of type `tree`; otherwise `zero`. -/
def progTree (f : Nat → Nat) (t : CTm) : CTree :=
  match h : infer [] t with
  | some A =>
      if hA : A = Ty.tree then
        toTree f ⟨erase t, wt_of_typed (infer_sound t (h.trans (congrArg some hA)))⟩
      else .zero
  | none => .zero

/-- The supremum of a base tree and the trees of all programs of depth `≤ n`. -/
def progSup (f : Nat → Nat) (base : CTree) (n : Nat) : CTree :=
  .lim fun i => if i = 0 then base else ((ctmsUpTo n).map (progTree f)).getD (i - 1) .zero

end BusyLean.FT
