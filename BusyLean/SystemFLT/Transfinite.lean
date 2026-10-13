import BusyLean.SystemFLT.Candidates

/-!
# Transfinite ladders: a universe for every well-founded atom order

Contender 14 built its universes by recursion on a finite tower of atoms.
Here the construction is generic: for any type of atoms whose order
`AtomOrder.lt` is well-founded, `wfUniv f wf` is a `Universe`. The domain of an
atom `a` is defined by well-founded recursion. It is the type of operators of
every base kind that *fits* `a`, i.e. whose atoms all lie strictly below `a`:

`El a = Σ (k : BaseKind α) (_ : k.Fits a), Sem k`   (atoms below `a` read via `El`).

Packing stores the kind with the operator; reading compares kinds (decidable)
and returns the stored operator, so the law `rd (pk v) = v` holds. The only
non-definitional step is the unfolding equation `WellFounded.fix_eq`, which
is used through casts.

So the ladder language normalizes for ladders of any well-founded length.
-/

namespace BusyLean.FLT

open BusyLean.FL

open BusyLean.FT (Cand snCand)

variable {α : Type} [DecidableEq α] [AtomOrder α] (f : Nat → Nat)

/-- The order on atoms, as a relation. -/
def ALt (b a : α) : Prop := AtomOrder.lt b a = true

/-- Semantics of base kinds fitting `a`, given the domains of the atoms below `a`. -/
def SemR (a : α) (E : (b : α) → ALt b a → Type) : (k : BaseKind α) → k.Fits a → Type
  | .star, _ => Cand f
  | .arr x y, h => SemR a E x h.1 → SemR a E y h.2
  | .atom b, h => E b h

/-- The domain of `a`, from the domains of the atoms below it. -/
structure Body (a : α) (E : (b : α) → ALt b a → Type) where
  kind : BaseKind α
  fits : kind.Fits a
  val : SemR f a E kind fits

variable (wf : WellFounded (ALt (α := α)))

/-- The domains of all atoms, by well-founded recursion. -/
def wfEl : α → Type := wf.fix (fun a E => Body f a E)

omit [DecidableEq α] in
theorem wfEl_eq (a : α) : wfEl f wf a = Body f a (fun b _ => wfEl f wf b) :=
  WellFounded.fix_eq wf _ a

omit [DecidableEq α] in
/-- Fitting kinds have the same semantics read through `wfEl`. -/
theorem semB_semR (a : α) :
    ∀ (k : BaseKind α) (h : k.Fits a), SemB f (wfEl f wf) k = SemR f a (fun b _ => wfEl f wf b) k h
  | .star, _ => rfl
  | .arr x y, h => by
      show (SemB f (wfEl f wf) x → SemB f (wfEl f wf) y) = (SemR f a _ x h.1 → SemR f a _ y h.2)
      rw [semB_semR a x h.1, semB_semR a y h.2]
  | .atom _, _ => rfl

def wfPk (a : α) (k : BaseKind α) (h : k.Fits a) (v : SemB f (wfEl f wf) k) : wfEl f wf a :=
  cast (wfEl_eq f wf a).symm
    (⟨k, h, cast (semB_semR f wf a k h) v⟩ : Body f a (fun b _ => wfEl f wf b))

def wfD (a : α) : wfEl f wf a := wfPk f wf a .star trivial (snCand f)

/-- Default operators of every base kind. -/
def wfDflt : (k : BaseKind α) → SemB f (wfEl f wf) k
  | .star => snCand f
  | .arr _ y => fun _ => wfDflt y
  | .atom a => wfD f wf a

/-- Reading a body at a requested kind. -/
def readBody (a : α) (k : BaseKind α) (x : Body f a (fun b _ => wfEl f wf b)) :
    SemB f (wfEl f wf) k :=
  if hk : x.kind = k then
    cast (by subst hk; exact (semB_semR f wf a x.kind x.fits).symm) x.val
  else wfDflt f wf k

def wfRd (a : α) (k : BaseKind α) (e : wfEl f wf a) : SemB f (wfEl f wf) k :=
  readBody f wf a k (cast (wfEl_eq f wf a) e)

theorem cast_cast_id {A B : Type} (e₁ : A = B) (e₂ : B = A) (x : A) :
    cast e₂ (cast e₁ x) = x := by subst e₁; rfl

theorem readBody_mk (a : α) (k : BaseKind α) (h : k.Fits a) (v : SemB f (wfEl f wf) k) :
    readBody f wf a k ⟨k, h, cast (semB_semR f wf a k h) v⟩ = v := by
  unfold readBody
  rw [dite_eq_left rfl]
  exact cast_cast_id _ _ v

theorem wfRd_wfPk (a : α) (k : BaseKind α) (h : k.Fits a) (v : SemB f (wfEl f wf) k) :
    wfRd f wf a k (wfPk f wf a k h v) = v := by
  unfold wfRd wfPk
  rw [cast_cast_id]
  exact readBody_mk f wf a k h v

/-- **The universe of a well-founded atom order.** -/
def wfUniv : Universe f α where
  El := wfEl f wf
  d := wfD f wf
  pk := wfPk f wf
  rd := wfRd f wf
  rd_pk := wfRd_wfPk f wf

end BusyLean.FLT
