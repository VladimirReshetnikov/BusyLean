import BusyLean.Independent.TtoInfBounds
import BusyLean.Independent.SystemT

/-!
# System T < the Hardy hierarchy at `ε₀`: an ordinal analysis

Every raw System T term `w` of depth `≤ 42` with static type `nat` is
translated into an infinitary term `P` (Tait's case trees for recursion) with
the same value (`value_progOf`). All of `P`'s redexes have level `< 47`, and its
height is at most `ω³ + 94` (`TtoInfBounds.lean`). Forty-seven rounds of cut
elimination remove the redexes. Each round costs one `ω`-exponential
(`elimAll_spec`), and the bounding lemma reads the value off the redex-free term
(`value_le_hardy`):

  `eval w ≤ H_{ω^{ω^{⋯^{ω³+94}}}}(y) ≤ H_{ω_{49}}(y) ≤ H_{ε₀}(y)`  for `y ≥ 200`.

The comparisons between trees use the structural order `Le 200`, which is sound
for the Hardy functions at arguments `≥ 200` (`Le.hardy_le`).
-/

namespace BusyLean.Indep

-- The linter would normalize hypotheses about `elimAll 47 …` (47 rounds of cut elimination).
set_option linter.constructorNameAsVariable false

open BusyLean.Indep.Inf
open BusyLean.Indep.Eps
open BusyLean.Indep.Eps.BTree (add opow mulNat omega tower epsilon0)
open BusyLean.Indep.Emb (stype)

theorem cast_ht_rank {ρ : Nat} : ∀ {T : C5.Ty} (tt : Tm [] T) (hs : T = .nat),
    ht (hs ▸ tt) = ht tt ∧ (RankLt ρ tt → RankLt ρ (hs ▸ tt))
  | _, _, rfl => ⟨rfl, id⟩

theorem opow_opowIter : ∀ (k : Nat) (a : BTree), opow (opowIter k a) = opowIter k (opow a)
  | 0, _ => rfl
  | k + 1, a => opow_opowIter k (opow a)

theorem opowIter_tower : ∀ (k j : Nat), opowIter k (tower j) = tower (j + k)
  | 0, _ => rfl
  | k + 1, j => by
      show opowIter k (tower (j + 1)) = tower (j + (k + 1))
      rw [opowIter_tower k (j + 1)]
      congr 1
      omega

-- From here on, `elimAll 47 …` and `opowIter 47 …` are used only through lemmas.
attribute [local irreducible] elimAll opowIter

theorem rankLt_progOf {w : C5.Term} (hw : depth w ≤ 42) (hs : stype [] w = .nat) :
    RankLt 47 (progOf w hs) :=
  (cast_ht_rank (ρ := 47) (trI [] w) hs).2 (rankLt_trI 42 [] w (fun _ h => nomatch h) hw)

theorem ht_progOf {w : C5.Term} (hw : depth w ≤ 42) (hs : stype [] w = .nat) :
    Le 200 (ht (progOf w hs)) (add W (fin 94)) := by
  unfold progOf
  rw [(cast_ht_rank (ρ := 47) (trI [] w) hs).1]
  exact (ht_trI 42 (by omega) [] w (fun _ h => nomatch h) hw).trans (addW_mono (by omega))

theorem opow_iter_le_epsilon0 (X : BTree) (h : Le 200 X (add W (fin 94))) :
    Le 200 (opow (opowIter 47 X)) epsilon0 := by
  have h4 : Le 200 (add W (fin 94)) (opow (fin 4)) := by
    have hW : Le 200 (fin 94) W :=
      (fin_le_omega (by omega)).trans (opow_mono (a := fin 1) (b := fin 3) (by omega)
        (fin_mono (by omega)))
    exact (add_mono_right W hW).trans (opow_add_self_le (by omega) (fin 3))
  have h5 : Le 200 (opow (fin 4)) (tower 1) := opow_mono (by omega) (fin_le_omega (by omega))
  have := opow_mono (by omega) (opowIter_mono (by omega) 47 ((h.trans h4).trans h5))
  rw [opowIter_tower] at this
  exact this.trans (.limR 49 (by omega) (Le.refl 200 _))

/-- **The ordinal bound for System T at depth 42.** -/
theorem eval_le_hardy_eps {w : C5.Term} (hw : depth w ≤ 42) (hs : stype [] w = .nat) {y : Nat}
    (hy : 200 ≤ y) : C5.eval w ≤ hardy epsilon0 y := by
  have hy2 : 2 ≤ y := Nat.le_trans (by decide) hy
  -- (no `omega` below: it would inspect hypotheses about `elimAll 47 …`)
  obtain ⟨hr0, hht, hev⟩ := elimAll_spec 47 (progOf w hs) (rankLt_progOf hw hs)
  have h1 : C5.eval w = value (elimAll 47 (progOf w hs)) := by
    rw [← value_progOf w hs]; exact (hev env0).symm
  have h2 : value (elimAll 47 (progOf w hs)) ≤ hardy (opow (ht (elimAll 47 (progOf w hs)))) y :=
    value_le_hardy _ hr0 hy2
  have h3 : hardy (opow (ht (elimAll 47 (progOf w hs)))) y ≤
      hardy (opow (opowIter 47 (ht (progOf w hs)))) y :=
    (opow_mono (by decide) hht).hardy_le hy2
  have h4 : hardy (opow (opowIter 47 (ht (progOf w hs)))) y ≤ hardy epsilon0 y :=
    (opow_iter_le_epsilon0 _ (ht_progOf hw hs)).hardy_le hy
  rw [h1]
  exact Nat.le_trans h2 (Nat.le_trans h3 h4)

/-! ## The comparison -/

theorem le_epsilon0_three : Le 3 (mulNat omega 3) epsilon0 :=
  .limR 1 (by omega) (.limR 2 (by omega) (by
    show Le 3 (mulNat omega 3) (opow (mulNat (.succ .zero) 2))
    rw [mulNat_one]
    exact .limR 3 (Nat.le_refl 3) (Le.refl 3 _)))

theorem maxUpTo_of_mono {g : Nat → Nat} (hg : ∀ i j, i ≤ j → g i ≤ g j) : ∀ y, maxUpTo g y = g y
  | 0 => rfl
  | y + 1 => by
      show max (maxUpTo g y) (g (y + 1)) = g (y + 1)
      rw [maxUpTo_of_mono hg y]
      exact Nat.max_eq_right (hg _ _ (Nat.le_succ y))

theorem hardy_fin : ∀ (i y : Nat), hardy (fin i) y = y + i
  | 0, _ => rfl
  | i + 1, y => by
      show hardy (fin i) (y + 1) = y + (i + 1)
      rw [hardy_fin i (y + 1)]
      omega

theorem hardy_omega (y : Nat) : hardy omega y = y + y := by
  show maxUpTo (fun i => hardy (mulNat (.succ .zero) i) y) y = y + y
  simp only [mulNat_one, hardy_fin]
  exact maxUpTo_of_mono (fun i j h => by omega) y

theorem hardy_omega_three : hardy (mulNat omega 3) 42 = 336 := by
  show hardy (add (add (add .zero omega) omega) omega) 42 = 336
  rw [hardy_add, hardy_add, hardy_add, hardy_omega, hardy_omega, hardy_omega]
  rfl

theorem Feps_42_ge : 336 ≤ Feps 42 := by
  have h := le_epsilon0_three.hardy_le (y := 42) (by decide)
  rw [hardy_omega_three] at h
  exact h

theorem eval_eq_zero_of_arr {w : C5.Term} {a b : C5.Ty} (hs : stype [] w = .arr a b) :
    C5.eval w = 0 := by
  have ht := BusyLean.Indep.Emb.interp_fst w []
  unfold C5.eval
  revert ht
  generalize C5.interp [] w = v
  obtain ⟨T, x⟩ := v
  intro ht
  have hT : T = .arr a b := ht.trans hs
  subst hT
  rfl

theorem Feps_mono {a b : Nat} (h : a ≤ b) : Feps a ≤ Feps b := hardy_mono epsilon0 h

theorem Feps_succ (a : Nat) : Feps a + 1 ≤ Feps (a + 1) := hardy_lt_succ epsilon0 a

theorem eval_le_Feps {w : C5.Term} (hw : depth w ≤ 42) (hs : stype [] w = .nat) :
    C5.eval w ≤ Feps 200 :=
  eval_le_hardy_eps hw hs (Nat.le_refl 200)

/-- **System T < the Hardy hierarchy at `ε₀`.** -/
theorem contender_2_lt_contenderEps : contender_2 < contenderEps := by
  unfold contender_2 contenderEps C5.largestSTLCNatRecNatOfDepth C5.largestOfDepth
  have hw : depth (C5.maxBy C5.eval 0 .zero (C5.termsUpTo 42)) ≤ 42 := by
    cases maxBy_mem C5.eval (C5.termsUpTo 42) 0 .zero with
    | inl h => exact depth_of_mem h
    | inr h => rw [h]; decide
  generalize C5.maxBy C5.eval 0 .zero (C5.termsUpTo 42) = w at hw ⊢
  have hlt : Feps 200 < Feps (Feps 42) := by
    have h1 := Feps_succ 200
    have h2 : Feps 201 ≤ Feps (Feps 42) := Feps_mono (by
      have hF := Feps_42_ge
      generalize Feps 42 = M at hF ⊢
      omega)
    generalize Feps 200 = a at h1 ⊢
    generalize Feps 201 = b at h1 h2
    generalize Feps (Feps 42) = c at h2 ⊢
    omega
  cases hs : stype [] w with
  | nat => exact Nat.lt_of_le_of_lt (eval_le_Feps hw hs) hlt
  | arr a b =>
      have h0 := eval_eq_zero_of_arr hs
      -- (no `rw` here: its closing `rfl` would try to evaluate `Feps (Feps 42)`)
      exact Nat.lt_of_le_of_lt (Nat.le_of_eq h0) (Nat.lt_of_le_of_lt (Nat.zero_le (Feps 200)) hlt)

end BusyLean.Indep
