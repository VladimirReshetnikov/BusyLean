import BusyLean.SystemFL.Candidates

/-!
# The ladder of universes

Atoms of level `ℓ`: `Atom 0 = Empty` and `Atom (ℓ+1) = Option (Atom ℓ)`. At
level `ℓ+1`, the new atom `none` denotes the previous level's `dyn`, the
universe of operators of all level-`ℓ` base kinds. The older atoms `some a`
keep their meaning. Older atoms lie below newer ones, so an operator whose
kind mentions only older atoms can be packed into a newer atom.

`Univ f ℓ` is the resulting `Universe`. The read-back law at level `ℓ+1`
reduces to the law at level `ℓ` through `lower`, which recognizes level-`ℓ+1`
base kinds that avoid the new atom.
-/

namespace BusyLean.FL

open BusyLean.F (Cand snCand)

def Atom : Nat → Type
  | 0 => Empty
  | ℓ + 1 => Option (Atom ℓ)

def Atom.decEq : (ℓ : Nat) → DecidableEq (Atom ℓ)
  | 0 => fun a => a.elim
  | ℓ + 1 => letI := Atom.decEq ℓ; inferInstanceAs (DecidableEq (Option (Atom ℓ)))

instance (ℓ : Nat) : DecidableEq (Atom ℓ) := Atom.decEq ℓ

/-- `lt b a`: atom `b` is older than atom `a`. -/
def Atom.lt : (ℓ : Nat) → Atom ℓ → Atom ℓ → Bool
  | 0, a, _ => a.elim
  | _ + 1, some _, none => true
  | _ + 1, none, _ => false
  | ℓ + 1, some b, some a => Atom.lt ℓ b a

instance (ℓ : Nat) : AtomOrder (Atom ℓ) := ⟨Atom.lt ℓ⟩

/-- All atoms of level `ℓ`, newest first. -/
def Atom.all : (ℓ : Nat) → List (Atom ℓ)
  | 0 => []
  | ℓ + 1 => none :: (Atom.all ℓ).map some

/-! ## Lowering base kinds that avoid the newest atom -/

section Lower

variable {β : Type}

def lower : BaseKind (Option β) → Option (BaseKind β)
  | .star => some .star
  | .arr x y =>
      match lower x, lower y with
      | some a, some b => some (.arr a b)
      | _, _ => none
  | .atom none => none
  | .atom (some b) => some (.atom b)

/-- Domains of `Option` atoms, from domains of the older atoms and of the new one. -/
def extEl (El : β → Type) (E₀ : Type) : Option β → Type
  | none => E₀
  | some b => El b

theorem semB_lower {f : Nat → Nat} (El : β → Type) (E₀ : Type) :
    ∀ {k : BaseKind (Option β)} {k₀ : BaseKind β}, lower k = some k₀ →
      SemB f (extEl El E₀) k = SemB f El k₀
  | .star, k₀, h => by cases h; rfl
  | .arr x y, k₀, h => by
      simp only [lower] at h
      cases hx : lower x with
      | none => rw [hx] at h; cases h
      | some a =>
          cases hy : lower y with
          | none => rw [hx, hy] at h; cases h
          | some b =>
              rw [hx, hy] at h
              cases h
              show (SemB f _ x → SemB f _ y) = (SemB f El a → SemB f El b)
              rw [semB_lower El E₀ hx, semB_lower El E₀ hy]
  | .atom none, _, h => nomatch h
  | .atom (some _), k₀, h => by cases h; rfl

end Lower

/-! ## Fitting kinds lower -/

/-- The newest atom of level `ℓ+1`: the previous level's `dyn`. -/
abbrev Atom.new (ℓ : Nat) : Atom (ℓ + 1) := none

/-- An older atom, seen at level `ℓ+1`. -/
abbrev Atom.old {ℓ : Nat} (a : Atom ℓ) : Atom (ℓ + 1) := some a

theorem lower_isSome_of_fits_new {ℓ : Nat} :
    ∀ {k : BaseKind (Atom (ℓ + 1))}, k.Fits (Atom.new ℓ) → (lower k).isSome = true
  | .star, _ => rfl
  | .arr x y, h => by
      have hx := lower_isSome_of_fits_new h.1
      have hy := lower_isSome_of_fits_new h.2
      cases ex : lower x with
      | none => rw [ex] at hx; cases hx
      | some a =>
          cases ey : lower y with
          | none => rw [ey] at hy; cases hy
          | some b => simp only [lower, ex, ey, Option.isSome_some]
  | .atom none, h => nomatch h
  | .atom (some _), _ => rfl

theorem lower_isSome_of_fits_old {ℓ : Nat} {a : Atom ℓ} :
    ∀ {k : BaseKind (Atom (ℓ + 1))}, k.Fits (Atom.old a) → (lower k).isSome = true
  | .star, _ => rfl
  | .arr x y, h => by
      have hx := lower_isSome_of_fits_old h.1
      have hy := lower_isSome_of_fits_old h.2
      cases ex : lower x with
      | none => rw [ex] at hx; cases hx
      | some a =>
          cases ey : lower y with
          | none => rw [ey] at hy; cases hy
          | some b => simp only [lower, ex, ey, Option.isSome_some]
  | .atom none, h => nomatch h
  | .atom (some _), _ => rfl

theorem fits_lower_of_fits_old {ℓ : Nat} {a : Atom ℓ} :
    ∀ {k : BaseKind (Atom (ℓ + 1))} {k₀ : BaseKind (Atom ℓ)},
      k.Fits (Atom.old a) → lower k = some k₀ → k₀.Fits a
  | .star, k₀, _, hl => by cases hl; trivial
  | .arr x y, k₀, h, hl => by
      cases ex : lower x with
      | none => simp only [lower, ex] at hl; cases hl
      | some p =>
          cases ey : lower y with
          | none => simp only [lower, ex, ey] at hl; cases hl
          | some q =>
              simp only [lower, ex, ey] at hl
              cases hl
              exact ⟨fits_lower_of_fits_old h.1 ex, fits_lower_of_fits_old h.2 ey⟩
  | .atom none, _, h, _ => nomatch h
  | .atom (some _), k₀, h, hl => by cases hl; exact h

theorem cast_cast_self {A B : Type} (e₁ : A = B) (e₂ : B = A) (x : A) :
    cast e₂ (cast e₁ x) = x := by subst e₁; rfl

/-! ## The universes -/

variable (f : Nat → Nat)

/-- Default elements of base kinds, given default elements of the atoms. -/
def dfltE {β : Type} (El : β → Type) (d : (a : β) → El a) : (k : BaseKind β) → SemB f El k
  | .star => snCand f
  | .arr _ y => fun _ => dfltE El d y
  | .atom a => d a

section Next

variable {ℓ : Nat} (U : Universe f (Atom ℓ))

/-- The domains of level `ℓ+1`. -/
abbrev nextEl : Atom (ℓ + 1) → Type := extEl U.El (BVal U)

def nextD : (a : Atom (ℓ + 1)) → nextEl f U a
  | none => ⟨.star, snCand f⟩
  | some a => U.d a

/-- Reading a level-`ℓ+1` base kind out of an element, through `lower`. -/
def readVia {E : Type} (g : (k₀ : BaseKind (Atom ℓ)) → E → SemB f U.El k₀)
    (k : BaseKind (Atom (ℓ + 1))) (e : E) : SemB f (nextEl f U) k :=
  match hl : lower k with
  | some k₀ => cast (semB_lower U.El (BVal U) hl).symm (g k₀ e)
  | none => dfltE f (nextEl f U) (nextD f U) k

theorem readVia_of {E : Type} (g : (k₀ : BaseKind (Atom ℓ)) → E → SemB f U.El k₀)
    {k : BaseKind (Atom (ℓ + 1))} {k₀ : BaseKind (Atom ℓ)} (hl : lower k = some k₀) (e : E) :
    readVia f U g k e = cast (semB_lower U.El (BVal U) hl).symm (g k₀ e) := by
  unfold readVia
  split
  · next k₁ h₁ =>
      rw [h₁] at hl
      cases hl
      rfl
  · next h₁ => rw [h₁] at hl; cases hl

/-- The lowered kind of a fitting kind. -/
def lowerGet {k : BaseKind (Atom (ℓ + 1))} (hs : (lower k).isSome = true) : BaseKind (Atom ℓ) :=
  (lower k).get hs

theorem lower_eq_get {k : BaseKind (Atom (ℓ + 1))} (hs : (lower k).isSome = true) :
    lower k = some (lowerGet hs) := (Option.some_get hs).symm

def nextPk : (a : Atom (ℓ + 1)) → (k : BaseKind (Atom (ℓ + 1))) → k.Fits a →
    SemB f (nextEl f U) k → nextEl f U a
  | none, _, h, v =>
      let hs := lower_isSome_of_fits_new h
      (⟨lowerGet hs, cast (semB_lower U.El (BVal U) (lower_eq_get hs)) v⟩ : BVal U)
  | some a, _, h, v =>
      let hs := lower_isSome_of_fits_old h
      U.pk a (lowerGet hs) (fits_lower_of_fits_old h (lower_eq_get hs))
        (cast (semB_lower U.El (BVal U) (lower_eq_get hs)) v)

def nextRd : (a : Atom (ℓ + 1)) → (k : BaseKind (Atom (ℓ + 1))) → nextEl f U a →
    SemB f (nextEl f U) k
  | none, k, e => readVia f U (fun k₀ (x : BVal U) => x.get k₀) k e
  | some a, k, e => readVia f U (U.rd a) k e

theorem nextRd_nextPk_new (k : BaseKind (Atom (ℓ + 1))) (h : k.Fits (Atom.new ℓ))
    (v : SemB f (nextEl f U) k) : nextRd f U (Atom.new ℓ) k (nextPk f U (Atom.new ℓ) k h v) = v := by
  have hs := lower_isSome_of_fits_new h
  show readVia f U (fun k₀ (x : BVal U) => x.get k₀) k
    (⟨lowerGet hs, cast (semB_lower U.El (BVal U) (lower_eq_get hs)) v⟩ : BVal U) = v
  rw [readVia_of f U _ (lower_eq_get hs), BVal.get_self]
  exact cast_cast_self _ _ _

theorem nextRd_nextPk_old (a : Atom ℓ) (k : BaseKind (Atom (ℓ + 1))) (h : k.Fits (Atom.old a))
    (v : SemB f (nextEl f U) k) : nextRd f U (Atom.old a) k (nextPk f U (Atom.old a) k h v) = v := by
  have hs := lower_isSome_of_fits_old h
  show readVia f U (U.rd a) k
    (U.pk a (lowerGet hs) (fits_lower_of_fits_old h (lower_eq_get hs))
      (cast (semB_lower U.El (BVal U) (lower_eq_get hs)) v)) = v
  rw [readVia_of f U _ (lower_eq_get hs), U.rd_pk]
  exact cast_cast_self _ _ _

theorem nextRd_nextPk (a : Atom (ℓ + 1)) (k : BaseKind (Atom (ℓ + 1))) (h : k.Fits a)
    (v : SemB f (nextEl f U) k) : nextRd f U a k (nextPk f U a k h v) = v := by
  cases a with
  | none => exact nextRd_nextPk_new f U k h v
  | some a => exact nextRd_nextPk_old f U a k h v

/-- The next universe: the new atom denotes the previous level's `dyn`. -/
def nextUniv : Universe f (Atom (ℓ + 1)) where
  El := nextEl f U
  d := nextD f U
  pk := nextPk f U
  rd := nextRd f U
  rd_pk := nextRd_nextPk f U

end Next

/-- The ground universe has no atoms. -/
def univ0 : Universe f (Atom 0) where
  El a := a.elim
  d a := a.elim
  pk a := a.elim
  rd a := a.elim
  rd_pk a := a.elim

/-- The universe of level `ℓ`: atoms `dyn₀, …, dyn_{ℓ-1}`. -/
def Univ : (ℓ : Nat) → Universe f (Atom ℓ)
  | 0 => univ0 f
  | ℓ + 1 => nextUniv f (Univ ℓ)

end BusyLean.FL
