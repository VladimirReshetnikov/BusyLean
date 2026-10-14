import BusyLean.Independent.TTyped
import BusyLean.Independent.SystemT

/-!
# Rung 2 < rung 3: System T embeds into the ladder

Every raw System T term `w` of depth `≤ 42` (in particular the winner that
defines rung 2) is translated into a Church-style ladder program `trC [] w`.
The pieces proved elsewhere are:

* `infer_trC`: the program type checks, with type `nat` when `w` has static
  type `nat`;
* `erase_trC` and `utr_steps`: it erases to a term that β-reduces to the
  Church numeral of `w`'s Contender 5 value, under any oracle;
* `nf_eq_of_steps` (confluence): the normalizer finds that numeral.

This file bounds the program's depth (`cdepth_trC`, at most `2·42 + 42 + 60`),
shows that programs of small depth are enumerated (`mem_ctmsUpTo`), and checks
that `F3 42` already exceeds that bound: a translated System T program of
depth `≤ 42` computes `2^10`.

No step uses rung 2 in the definition of rung 3. The comparison is a
simulation: the stronger language runs the weaker one's programs.
-/

namespace BusyLean.Indep.Emb

open BusyLean.FL
open BusyLean.Indep.Ladder (kindsUpTo tysUpTo ctmsUpTo cross natsUpTo listMax fvalue
  ladderUpTo ladderMax stage)

variable {α : Type} [DecidableEq α] [AtomOrder α]

/-! ## Depth of System F fragment programs -/

def tdepth : Ty α → Nat
  | .tvar n => n + 2
  | .arr A B => max (tdepth A) (tdepth B) + 1
  | .all _ A => tdepth A + 1
  | .lam _ _ | .app _ _ _ | .kall0 _ | .kall1 _ | .pack _ _ | .unpack _ _ | .apack _ _ _
  | .aunpack _ _ _ => 0

/-- Types of the System F fragment: variables, arrows, `∀` over `★`. -/
def IsF : Ty α → Prop
  | .tvar _ => True
  | .arr A B => IsF A ∧ IsF B
  | .all k A => k = .star ∧ IsF A
  | .lam _ _ | .app _ _ _ | .kall0 _ | .kall1 _ | .pack _ _ | .unpack _ _ | .apack _ _ _
  | .aunpack _ _ _ => False

def cdepth : CTm α → Nat
  | .var n => n + 2
  | .lam A e => max (tdepth A) (cdepth e) + 1
  | .app t u => max (cdepth t) (cdepth u) + 1
  | .tlam _ e => cdepth e + 1
  | .tapp e A => max (cdepth e) (tdepth A) + 1
  | .klam0 _ | .kapp0 _ _ | .klam1 _ | .kapp1 _ _ | .orc => 0

/-- Programs of the System F fragment. -/
def IsFC : CTm α → Prop
  | .var _ => True
  | .lam A e => IsF A ∧ IsFC e
  | .app t u => IsFC t ∧ IsFC u
  | .tlam k e => k = .star ∧ IsFC e
  | .tapp e A => IsFC e ∧ IsF A
  | .klam0 _ | .kapp0 _ _ | .klam1 _ | .kapp1 _ _ | .orc => False

/-! ## Enumeration -/

omit [DecidableEq α] [AtomOrder α] in
theorem mem_cross {A B : Type} {x : A} {y : B} {xs : List A} {ys : List B} (hx : x ∈ xs)
    (hy : y ∈ ys) : (x, y) ∈ cross xs ys :=
  List.mem_flatMap.mpr ⟨x, hx, List.mem_map_of_mem hy⟩

theorem mem_natsUpTo : ∀ {m n : Nat}, n < m → n ∈ natsUpTo m
  | m + 1, n, h => by
      by_cases e : n = m
      · subst e; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_natsUpTo (by omega))

omit [DecidableEq α] [AtomOrder α] in
theorem star_mem_kindsUpTo (as : List α) : ∀ {m : Nat}, 0 < m → Kind.star ∈ kindsUpTo as m
  | _ + 1, _ => List.mem_cons_self

omit [DecidableEq α] [AtomOrder α] in
theorem pos_of_mem_tysUpTo {as : List α} {A : Ty α} : ∀ {m : Nat}, A ∈ tysUpTo as m → 0 < m
  | _ + 1, _ => Nat.succ_pos _

omit [DecidableEq α] [AtomOrder α] in
theorem pos_of_mem_ctmsUpTo {as : List α} {e : CTm α} : ∀ {m : Nat}, e ∈ ctmsUpTo as m → 0 < m
  | _ + 1, _ => Nat.succ_pos _

omit [DecidableEq α] [AtomOrder α] in
theorem mem_tysUpTo (as : List α) : ∀ (A : Ty α) {m : Nat}, IsF A → tdepth A ≤ m →
    A ∈ tysUpTo as m
  | .tvar n, m + 1, _, h =>
      List.mem_append_left _ (List.mem_map_of_mem (mem_natsUpTo (by simp only [tdepth] at h; omega)))
  | .arr A B, m + 1, hF, h => by
      simp only [tdepth] at h
      refine List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem
        (f := fun p : Ty α × Ty α => Ty.arr p.1 p.2) (mem_cross ?_ ?_)))
      · exact mem_tysUpTo as A hF.1 (by omega)
      · exact mem_tysUpTo as B hF.2 (by omega)
  | .all k A, m + 1, hF, h => by
      simp only [tdepth] at h
      obtain ⟨hk, hA⟩ := hF
      subst hk
      have hA' := mem_tysUpTo as A hA (m := m) (by omega)
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
        (List.mem_map_of_mem (f := fun p : Kind α × Ty α => Ty.all p.1 p.2)
          (mem_cross (star_mem_kindsUpTo as (pos_of_mem_tysUpTo hA')) hA'))))
  | .tvar _, 0, _, h => absurd h (Nat.not_succ_le_zero _)
  | .arr _ _, 0, _, h => absurd h (Nat.not_succ_le_zero _)
  | .all _ _, 0, _, h => absurd h (Nat.not_succ_le_zero _)
  | .lam _ _, _, hF, _ | .app _ _ _, _, hF, _ | .kall0 _, _, hF, _ | .kall1 _, _, hF, _
  | .pack _ _, _, hF, _ | .unpack _ _, _, hF, _ | .apack _ _ _, _, hF, _
  | .aunpack _ _ _, _, hF, _ => hF.elim

omit [DecidableEq α] [AtomOrder α] in
theorem mem_ctmsUpTo (as : List α) : ∀ (e : CTm α) {m : Nat}, IsFC e → cdepth e ≤ m →
    e ∈ ctmsUpTo as m
  | .var n, m + 1, _, h =>
      List.mem_append_left _ (List.mem_map_of_mem (mem_natsUpTo (by simp only [cdepth] at h; omega)))
  | .lam A e, m + 1, hF, h => by
      simp only [cdepth] at h
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem
        (f := fun p : Ty α × CTm α => CTm.lam p.1 p.2)
        (mem_cross (mem_tysUpTo as A hF.1 (by omega)) (mem_ctmsUpTo as e hF.2 (by omega)))))
  | .app t u, m + 1, hF, h => by
      simp only [cdepth] at h
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
        (List.mem_map_of_mem (f := fun p : CTm α × CTm α => CTm.app p.1 p.2)
        (mem_cross (mem_ctmsUpTo as t hF.1 (by omega)) (mem_ctmsUpTo as u hF.2 (by omega))))))
  | .tlam k e, m + 1, hF, h => by
      simp only [cdepth] at h
      obtain ⟨hk, he⟩ := hF
      subst hk
      have he' := mem_ctmsUpTo as e he (m := m) (by omega)
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ (List.mem_map_of_mem (f := fun p : Kind α × CTm α => CTm.tlam p.1 p.2)
          (mem_cross (star_mem_kindsUpTo as (pos_of_mem_ctmsUpTo he')) he')))))
  | .tapp e A, m + 1, hF, h => by
      simp only [cdepth] at h
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _
          (List.mem_map_of_mem (f := fun p : CTm α × Ty α => CTm.tapp p.1 p.2)
          (mem_cross (mem_ctmsUpTo as e hF.1 (by omega)) (mem_tysUpTo as A hF.2 (by omega))))))))
  | .var _, 0, _, h => absurd h (Nat.not_succ_le_zero _)
  | .lam _ _, 0, _, h => absurd h (Nat.not_succ_le_zero _)
  | .app _ _, 0, _, h => absurd h (Nat.not_succ_le_zero _)
  | .tlam _ _, 0, _, h => absurd h (Nat.not_succ_le_zero _)
  | .tapp _ _, 0, _, h => absurd h (Nat.not_succ_le_zero _)
  | .klam0 _, _, hF, _ | .kapp0 _ _, _, hF, _ | .klam1 _, _, hF, _ | .kapp1 _ _, _, hF, _
  | .orc, _, hF, _ => hF.elim

/-! ## The translation stays in the System F fragment -/

omit [DecidableEq α] [AtomOrder α] in
theorem isF_tyT : ∀ a : C5.Ty, IsF (tyT a : Ty α)
  | .nat => ⟨rfl, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩
  | .arr a b => ⟨isF_tyT a, isF_tyT b⟩

omit [DecidableEq α] [AtomOrder α] in
theorem tdepth_tyT : ∀ a : C5.Ty, tdepth (tyT a : Ty α) = tyDepth a + 4
  | .nat => rfl
  | .arr a b => by
      show max (tdepth (tyT a : Ty α)) (tdepth (tyT b : Ty α)) + 1 = _
      rw [tdepth_tyT a, tdepth_tyT b]
      simp only [tyDepth]
      omega

omit [DecidableEq α] [AtomOrder α] in
theorem isFC_recC {R : Ty α} (hR : IsF R) : IsFC (recC R) := by
  simp only [IsFC, recC, stepC, pairC, fstC, sndC, succC, zeroC, pairTyC, IsF, Ty.nat, hR,
    and_self]

section
omit [DecidableEq α] [AtomOrder α]
theorem tdepth_nat : tdepth (Ty.nat : Ty α) = 5 := rfl

theorem tdepth_pairTyC (R : Ty α) : tdepth (pairTyC Ty.nat R) ≤ tdepth R + 8 := by
  unfold pairTyC; simp only [tdepth, tdepth_nat]; omega

theorem cdepth_pairC (R : Ty α) : cdepth (pairC Ty.nat R) ≤ tdepth R + 12 := by
  unfold pairC; simp only [cdepth, tdepth, tdepth_nat]; omega

theorem cdepth_fstC (R : Ty α) (p : CTm α) :
    cdepth (fstC Ty.nat R p) ≤ max (cdepth p) (tdepth R + 8) + 2 := by
  unfold fstC; simp only [cdepth, tdepth_nat]; omega

theorem cdepth_sndC (R : Ty α) (p : CTm α) :
    cdepth (sndC Ty.nat R p) ≤ max (cdepth p) (tdepth R + 8) + 2 := by
  unfold sndC; simp only [cdepth, tdepth_nat]; omega

theorem cdepth_succC : cdepth (succC : CTm α) = 12 := rfl
theorem cdepth_zeroC : cdepth (zeroC : CTm α) = 5 := rfl

theorem cdepth_stepC (R : Ty α) : cdepth (stepC R) ≤ tdepth R + 25 := by
  have h1 := cdepth_pairC R
  have h2 := cdepth_fstC R (.var 0)
  have h3 := cdepth_sndC R (.var 0)
  have h4 := tdepth_pairTyC R
  unfold stepC; simp only [cdepth, tdepth, tdepth_nat, cdepth_succC] at h2 h3 ⊢; omega

theorem cdepth_recC (R : Ty α) : cdepth (recC R) ≤ tdepth R + 45 := by
  have h1 := cdepth_pairC R
  have h4 := tdepth_pairTyC R
  have h5 := cdepth_stepC R
  unfold recC
  generalize hq : (CTm.app (.app (.tapp (.var 0) (pairTyC Ty.nat R)) (.app (stepC R) (.var 1)))
      (.app (.app (pairC Ty.nat R) zeroC) (.var 2)) : CTm α) = q
  have h3 := cdepth_sndC R q
  have hq' : cdepth q ≤ tdepth R + 30 := by
    subst hq; simp only [cdepth, cdepth_zeroC]; omega
  simp only [cdepth, tdepth, tdepth_nat]; omega
end


omit [DecidableEq α] [AtomOrder α] in
theorem isFC_errC : ∀ a : C5.Ty, IsFC (errC a : CTm α)
  | .nat => ⟨rfl, ⟨trivial, trivial⟩, trivial, trivial⟩
  | .arr a b => ⟨isF_tyT a, isFC_errC b⟩

omit [DecidableEq α] [AtomOrder α] in
theorem cdepth_errC : ∀ a : C5.Ty, cdepth (errC a : CTm α) ≤ tyDepth a + 5
  | .nat => by show 5 ≤ 6; omega
  | .arr a b => by
      have ih := cdepth_errC b
      show max (tdepth (tyT a : Ty α)) (cdepth (errC b : CTm α)) + 1 ≤ _
      rw [tdepth_tyT]
      simp only [tyDepth]
      omega

omit [DecidableEq α] [AtomOrder α] in
theorem isFC_castC (src dst : C5.Ty) {u : CTm α} (hu : IsFC u) : IsFC (castC src dst u) := by
  unfold castC
  cases C5.typeEqb src dst
  · exact isFC_errC dst
  · exact hu

omit [DecidableEq α] [AtomOrder α] in
theorem cdepth_castC (src dst : C5.Ty) (u : CTm α) :
    cdepth (castC src dst u) ≤ max (cdepth u) (tyDepth dst + 5) := by
  unfold castC
  cases C5.typeEqb src dst
  · exact Nat.le_trans (cdepth_errC dst) (Nat.le_max_right _ _)
  · exact Nat.le_max_left _ _

omit [DecidableEq α] [AtomOrder α] in
theorem isFC_trC : ∀ (Γ : List C5.Ty) (t : C5.Term), IsFC (trC Γ t : CTm α)
  | Γ, .var x => by
      show IsFC (match C5.lookup Γ x with
        | some _ => (CTm.var (Γ.length - (x + 1)) : CTm α)
        | none => zeroC)
      cases C5.lookup Γ x
      · exact isFC_errC .nat
      · trivial
  | Γ, .lam a b t => ⟨isF_tyT a, isFC_castC _ b (isFC_trC (a :: Γ) t)⟩
  | Γ, .app t u => by
      show IsFC (match stype Γ t with
        | .nat => (zeroC : CTm α)
        | .arr a _ => .app (trC Γ t) (castC (stype Γ u) a (trC Γ u)))
      cases stype Γ t with
      | nat => exact isFC_errC .nat
      | arr a _ => exact ⟨isFC_trC Γ t, isFC_castC _ a (isFC_trC Γ u)⟩
  | _, .zero => isFC_errC .nat
  | _, .succ => by
      show IsFC (succC : CTm α)
      simp only [IsFC, succC, IsF, Ty.nat, and_self]
  | _, .natRec r => isFC_recC (isF_tyT r)

/-! ## Depth bounds -/

theorem mem_of_nthError {β : Type} {a : β} : ∀ {Γ : List β} {n : Nat},
    C5.nthError Γ n = some a → a ∈ Γ
  | _ :: _, 0, h => by cases h; exact List.mem_cons_self
  | _ :: _, _ + 1, h => List.mem_cons_of_mem _ (mem_of_nthError h)

theorem mem_of_lookup {β : Type} {Γ : List β} {x : Nat} {a : β} (h : C5.lookup Γ x = some a) :
    a ∈ Γ := mem_of_nthError (lookup_some h)

theorem tyDepth_stype (K : Nat) : ∀ (Γ : List C5.Ty) (t : C5.Term),
    (∀ a ∈ Γ, tyDepth a ≤ K) → depth t ≤ K + 1 → tyDepth (stype Γ t) ≤ K + 4
  | Γ, .var x, hΓ, _ => by
      show tyDepth (match C5.lookup Γ x with
        | some a => a
        | none => .nat) ≤ _
      cases hl : C5.lookup Γ x with
      | none => show 1 ≤ _; omega
      | some a => exact Nat.le_trans (hΓ a (mem_of_lookup hl)) (by omega)
  | _, .lam a b t, _, h => by
      simp only [depth] at h
      show max (tyDepth a) (tyDepth b) + 1 ≤ _
      omega
  | Γ, .app t u, hΓ, h => by
      simp only [depth] at h
      have ih := tyDepth_stype K Γ t hΓ (by omega)
      show tyDepth (match stype Γ t with
        | .nat => .nat
        | .arr _ b => b) ≤ _
      revert ih
      cases stype Γ t with
      | nat => intro _; show 1 ≤ K + 4; omega
      | arr a b =>
          intro ih
          show tyDepth b ≤ K + 4
          simp only [tyDepth] at ih
          omega
  | _, .zero, _, _ => by show 1 ≤ K + 4; omega
  | _, .succ, _, _ => by show 2 ≤ K + 4; omega
  | _, .natRec r, _, h => by
      simp only [depth] at h
      show tyDepth (C5.Ty.arr r (.arr (.arr .nat (.arr r r)) (.arr .nat r))) ≤ K + 4
      simp only [tyDepth]
      omega

omit [DecidableEq α] [AtomOrder α] in
theorem cdepth_trC (K : Nat) : ∀ (Γ : List C5.Ty) (t : C5.Term),
    (∀ a ∈ Γ, tyDepth a ≤ K) → depth t ≤ K →
    cdepth (trC Γ t : CTm α) ≤ 2 * depth t + Γ.length + K + 60
  | Γ, .var x, _, _ => by
      show cdepth (match C5.lookup Γ x with
        | some _ => (CTm.var (Γ.length - (x + 1)) : CTm α)
        | none => zeroC) ≤ _
      cases C5.lookup Γ x
      · show 5 ≤ _; omega
      · show Γ.length - (x + 1) + 2 ≤ _; omega
  | Γ, .lam a b t, hΓ, h => by
      simp only [depth] at h ⊢
      have hΓ' : ∀ c ∈ a :: Γ, tyDepth c ≤ K := by
        intro c hc
        cases hc with
        | head => omega
        | tail _ hc => exact hΓ c hc
      have ih := cdepth_trC K (a :: Γ) t hΓ' (by omega)
      have hc := cdepth_castC (α := α) (stype (a :: Γ) t) b (trC (a :: Γ) t)
      show max (tdepth (tyT a : Ty α)) (cdepth (castC _ b (trC (a :: Γ) t : CTm α))) + 1 ≤ _
      rw [tdepth_tyT]
      simp only [List.length_cons] at ih
      omega
  | Γ, .app t u, hΓ, h => by
      simp only [depth] at h ⊢
      have iht := cdepth_trC K Γ t hΓ (by omega)
      have ihu := cdepth_trC K Γ u hΓ (by omega)
      have hs := tyDepth_stype K Γ t hΓ (by omega)
      show cdepth (match stype Γ t with
        | .nat => (zeroC : CTm α)
        | .arr a _ => .app (trC Γ t) (castC (stype Γ u) a (trC Γ u))) ≤ _
      revert hs
      cases stype Γ t with
      | nat => intro _; show 5 ≤ _; omega
      | arr a b =>
          intro hs
          simp only [tyDepth] at hs
          have hc := cdepth_castC (α := α) (stype Γ u) a (trC Γ u)
          show max (cdepth (trC Γ t : CTm α)) (cdepth (castC (stype Γ u) a (trC Γ u : CTm α))) + 1
            ≤ _
          omega
  | _, .zero, _, _ => by show 5 ≤ _; omega
  | _, .succ, _, _ => by show 12 ≤ _; omega
  | Γ, .natRec r, _, h => by
      simp only [depth] at h ⊢
      have := cdepth_recC (tyT r : Ty α)
      rw [tdepth_tyT] at this
      exact Nat.le_trans this (by omega)

end BusyLean.Indep.Emb

namespace BusyLean.Indep

open BusyLean.FL
open BusyLean.Indep.Emb
open BusyLean.Indep.Ladder (fvalue ladderUpTo ladderMax stage listMax)

/-! ## Values of translated programs -/

theorem fvalue_eq {ℓ fuel n : Nat} {g : Nat → Nat} {t : CTm (Atom ℓ)}
    (h : infer fuel [] [] t = some Ty.nat) (hs : F.Steps g (erase t) (F.Tm.num n)) :
    fvalue ℓ g fuel t = n := by
  unfold fvalue
  split
  · next A hA =>
      have e : A = Ty.nat := by rw [h] at hA; cases hA; rfl
      subst e
      rw [dite_eq_left rfl]
      exact F.decode_nf_of_steps _ hs
  · next hA => rw [h] at hA; cases hA

theorem le_listMax {A : Type} (score : A → Nat) {x : A} :
    ∀ {l : List A}, x ∈ l → score x ≤ listMax score l
  | _ :: _, .head _ => Nat.le_max_left _ _
  | _ :: _, .tail _ h => Nat.le_trans (le_listMax score h) (Nat.le_max_right _ _)

/-- A System T term of static type `nat` whose translation fits the budget `m`
has a value below `ladderMax g m`, for every oracle `g`. -/
theorem eval_le_listMax (g : Nat → Nat) (m : Nat) {w : C5.Term} (hs : stype [] w = .nat)
    (hd : cdepth (trC [] w : CTm (Atom m)) ≤ m) :
    C5.eval w ≤ listMax (fvalue m g m) (ladderUpTo m) := by
  have hmem : (trC [] w : CTm (Atom m)) ∈ ladderUpTo m :=
    mem_ctmsUpTo _ _ (isFC_trC [] w) hd
  have hty : infer m [] [] (trC [] w : CTm (Atom m)) = some Ty.nat := by
    have h := infer_trC (α := Atom m) (fuel := m) [] [] w
    rw [hs] at h
    exact h
  have hsteps : F.Steps g (erase (trC [] w : CTm (Atom m))) (F.Tm.num (C5.eval w)) := by
    rw [erase_trC]
    exact utr_steps hs
  have hv := fvalue_eq (ℓ := m) hty hsteps
  have hle := le_listMax (fvalue m g m) hmem
  rw [hv] at hle
  exact hle

theorem eval_lt_ladderMax (g : Nat → Nat) (m : Nat) {w : C5.Term} (hs : stype [] w = .nat)
    (hd : cdepth (trC [] w : CTm (Atom m)) ≤ m) : C5.eval w < ladderMax g m := by
  have h := eval_le_listMax g m hs hd
  unfold ladderMax
  generalize listMax (fvalue m g m) (ladderUpTo m) = L at h
  omega

theorem F3_eq (n : Nat) : F3 n = ladderMax (stage n) n := rfl

/-! ## `F3 42` is already large -/

/-- `natRec (succ) (λ _ g x. g (g x)) 10 0 = 2^10`, in Contender 5's syntax. -/
def pow2Program : C5.Term :=
  .app (.app (.app (.app (.natRec N2)  .succ)
    (.lam N (.arr N2 N2) (.lam N2 N2 (.lam N N (.app (.var 1) (.app (.var 1) (.var 2)))))))
    (numT 10)) .zero

theorem stype_pow2Program : stype [] pow2Program = .nat := rfl

theorem recursion_double (s : Nat → (Nat → Nat) → Nat → Nat)
    (hs : ∀ k g x, s k g x = g (g x)) : ∀ k x, C5.recursion Nat.succ s k x = x + 2 ^ k
  | 0, x => rfl
  | k + 1, x => by
      show s k (C5.recursion Nat.succ s k) x = _
      rw [hs, recursion_double s hs k, recursion_double s hs k, Nat.pow_succ]
      omega

theorem eval_pow2Program : C5.eval pow2Program = 1024 := by
  have h1 : C5.interp [] (.natRec N2) =
      (⟨.arr N2 (.arr (.arr N (.arr N2 N2)) (.arr N N2)), C5.recursion⟩ : C5.Value) := rfl
  have h2 := interp_app h1 (interp_succ [])
  have hstep : C5.interp [] (.lam N (.arr N2 N2) (.lam N2 N2 (.lam N N
      (.app (.var 1) (.app (.var 1) (.var 2)))))) =
      (⟨.arr N (.arr N2 N2), (C5.interp [] (.lam N (.arr N2 N2) (.lam N2 N2 (.lam N N
        (.app (.var 1) (.app (.var 1) (.var 2))))))).2⟩ : C5.Value) := rfl
  have h3 := interp_app h2 hstep
  have h4 := interp_app h3 (interp_numT [] 10)
  have h5 := interp_app h4 (rfl : C5.interp [] .zero = (⟨.nat, (0 : Nat)⟩ : C5.Value))
  have h := eval_of_interp (h5 :)
  have hs : ∀ k g x, ((C5.interp [] (.lam N (.arr N2 N2) (.lam N2 N2 (.lam N N
      (.app (.var 1) (.app (.var 1) (.var 2))))))).2 : Nat → (Nat → Nat) → Nat → Nat) k g x =
      g (g x) := fun _ _ _ => rfl
  unfold pow2Program
  rw [h]
  exact recursion_double _ hs 10 0

theorem cdepth_pow2Program : cdepth (trC [] pow2Program : CTm (Atom 42)) ≤ 42 :=
  Nat.le_of_ble_eq_true rfl

theorem add_le_ladderMax (g : Nat → Nat) (m : Nat) {x : Nat}
    (h : x ≤ listMax (fvalue m g m) (ladderUpTo m)) : m + 1 + x ≤ ladderMax g m :=
  Nat.add_le_add_left h _

theorem F3_42_ge : 1067 ≤ F3 42 := by
  have h := eval_le_listMax (stage 42) 42 stype_pow2Program cdepth_pow2Program
  rw [eval_pow2Program] at h
  rw [F3_eq]
  exact add_le_ladderMax (stage 42) 42 h

/-! ## The comparison -/

/-- Every System T value of depth `≤ 42` is below `F3 m` once `m ≥ F3 42`. -/
theorem eval_lt_F3 {w : C5.Term} (hw : depth w ≤ 42) {m : Nat} (hm : F3 42 ≤ m) :
    C5.eval w < F3 m := by
  rw [F3_eq]
  cases hs : stype [] w with
  | arr a b =>
      have h0 : C5.eval w = 0 := by
        have ht := interp_fst w []
        unfold C5.eval
        revert ht
        generalize C5.interp [] w = v
        obtain ⟨T, x⟩ := v
        intro ht
        have hT : T = .arr a b := ht.trans hs
        subst hT
        rfl
      rw [h0]
      unfold ladderMax
      generalize listMax (fvalue m (stage m) m) (ladderUpTo m) = L
      omega
  | nat =>
      refine eval_lt_ladderMax _ _ hs ?_
      have h := cdepth_trC (α := Atom m) 42 [] w (fun _ h => nomatch h) hw
      have h42 := F3_42_ge
      simp only [List.length_nil] at h
      generalize F3 42 = M at h42 hm
      generalize cdepth (trC [] w : CTm (Atom m)) = D at h
      omega

/-- **Rung 2 < rung 3.** -/
theorem contender_2_lt_contender_3 : contender_2 < contender_3 := by
  unfold contender_2 contender_3 C5.largestSTLCNatRecNatOfDepth C5.largestOfDepth
  have hw : depth (C5.maxBy C5.eval 0 .zero (C5.termsUpTo 42)) ≤ 42 := by
    cases maxBy_mem C5.eval (C5.termsUpTo 42) 0 .zero with
    | inl h => exact depth_of_mem h
    | inr h => rw [h]; decide
  exact eval_lt_F3 hw (Nat.le_refl _)

end BusyLean.Indep
