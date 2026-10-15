import BusyLean.Independent.TtoInfBounds
import BusyLean.Independent.SystemT
import BusyLean.Independent.Buchholz

/-!
# Rung 2 < rung 3: System T < the Hardy hierarchy at `θ` (an ordinal analysis)

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

Finally `ε₀` sits inside Buchholz's `θ = ψ_0(Ω_ω)`: the branch `0` of `θ` is
`ψ_0(ε_{Ω_2+1})`, whose branch `0` is `ψ_0(Ω_1)`, the limit of `1, ω, ω^ω, …`.
Its Brouwer tree is exactly `ε₀` (`toB_branch0`). So `H_{ε₀}(y) ≤ H_θ(y)`
(`Feps_le_F3`).
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

/-! ## `ε₀` inside `θ` -/

namespace Buch

/-- A tree without `sup` nodes. -/
def SF {A : Type} : Tr A → Prop
  | .zero => True
  | .succ a => SF a
  | .lim f => ∀ i, SF (f i)
  | .sup _ _ => False

theorem cmap_sf {A B : Type} (thr : Nat) (h : B → A) : ∀ x : Tr A, SF x →
    SF (Tr.cmap thr h x) ∧ Tr.toB (Tr.cmap thr h x) = Tr.toB x
  | .zero, _ => ⟨trivial, rfl⟩
  | .succ a, hx => ⟨(cmap_sf thr h a hx).1, congrArg BTree.succ (cmap_sf thr h a hx).2⟩
  | .lim f, hx => ⟨fun i => (cmap_sf thr h (f i) (hx i)).1,
      congrArg BTree.lim (funext fun i => (cmap_sf thr h (f i) (hx i)).2)⟩
  | .sup _ _, hx => hx.elim

theorem lift_sf (m : Nat) (x : T m) (hx : SF x) :
    SF (lift m x) ∧ Tr.toB (lift m x) = Tr.toB x := by
  cases m with
  | zero => exact cmap_sf _ _ x hx
  | succ m => exact cmap_sf _ _ x hx

theorem proj_sf (m : Nat) (x : T (m + 1)) (hx : SF x) :
    SF (proj m x) ∧ Tr.toB (proj m x) = Tr.toB x := by
  cases m with
  | zero => exact cmap_sf _ _ x hx
  | succ m => exact cmap_sf _ _ x hx

theorem add_sf {A : Type} (a : Tr A) (ha : SF a) : ∀ b : Tr A, SF b →
    SF (Tr.add a b) ∧ Tr.toB (Tr.add a b) = BTree.add (Tr.toB a) (Tr.toB b)
  | .zero, _ => ⟨ha, rfl⟩
  | .succ b, hb => ⟨(add_sf a ha b hb).1, congrArg BTree.succ (add_sf a ha b hb).2⟩
  | .lim f, hb => ⟨fun i => (add_sf a ha (f i) (hb i)).1,
      congrArg BTree.lim (funext fun i => (add_sf a ha (f i) (hb i)).2)⟩
  | .sup _ _, hb => hb.elim

theorem mulNat_sf {A : Type} (a : Tr A) (ha : SF a) : ∀ k : Nat,
    SF (Tr.mulNat a k) ∧ Tr.toB (Tr.mulNat a k) = BTree.mulNat (Tr.toB a) k
  | 0 => ⟨trivial, rfl⟩
  | k + 1 => by
      have ih := mulNat_sf a ha k
      have h := add_sf (Tr.mulNat a k) ih.1 a ha
      refine ⟨h.1, ?_⟩
      show Tr.toB (Tr.add (Tr.mulNat a k) a) = BTree.add (BTree.mulNat (Tr.toB a) k) (Tr.toB a)
      rw [h.2, ih.2]

/-- On trees without `sup`s, `ψ_0` is `ω^·`. -/
theorem psi0_sf {A : Type} (dn : A → Tr A) : ∀ z : Tr (Tr A), SF z →
    SF (psiG dn z 0) ∧ Tr.toB (psiG dn z 0) = BTree.opow (Tr.toB z)
  | .zero, _ => ⟨trivial, rfl⟩
  | .succ a, hz => by
      have ih := psi0_sf dn a hz
      refine ⟨fun k => (mulNat_sf _ ih.1 k).1, ?_⟩
      show BTree.lim (fun k => Tr.toB (Tr.mulNat (psiG dn a 0) k)) =
        BTree.lim fun k => BTree.mulNat (BTree.opow (Tr.toB a)) k
      congr 1; funext k; rw [(mulNat_sf _ ih.1 k).2, ih.2]
  | .lim f, hz => ⟨fun k => (psi0_sf dn (f k) (hz k)).1,
      congrArg BTree.lim (funext fun k => (psi0_sf dn (f k) (hz k)).2)⟩
  | .sup _ _, hz => hz.elim

theorem iterate_opow_tower : ∀ i, iterate BTree.opow (i + 1) (.succ .zero) = tower i
  | 0 => rfl
  | i + 1 => congrArg BTree.opow (iterate_opow_tower i)

/-- The branch `0` of `ψ_0(ε_{Ω_{n+2}+1})` is `ψ_0(Ω_1)`, the limit of `1, ω, ω^ω, …`:
its Brouwer tree is exactly `ε₀`. -/
theorem toB_branch0 (n : Nat) :
    Tr.toB (psiG (down (n + 1)) (towerG (n + 1) (lift (n + 1)) (down (n + 1)) 0) 0) =
      epsilon0 := by
  let F : T (n + 1) → T (n + 2) := fun y => lift (n + 1) (lift n (proj n y))
  have hF : ∀ x, SF x → SF (F x) ∧ Tr.toB (F x) = Tr.toB x := fun x hx => by
    have h1 := proj_sf n x hx
    have h2 := lift_sf n _ h1.1
    have h3 := lift_sf (n + 1) _ h2.1
    exact ⟨h3.1, h3.2.trans (h2.2.trans h1.2)⟩
  have e : towerG (n + 1) (lift (n + 1)) (down (n + 1)) 0 = .sup 0 F := by
    show Tr.cmap (n + 1) (proj n) (.sup 0 fun y => lift n y) = _
    simp only [Tr.cmap, Nat.zero_lt_succ, ite_true]
    rfl
  have hg : ∀ k, SF (iterate (fun g => psiG (down (n + 1)) (F g) 0) k (omegaG (down (n + 1)) 0)) ∧
      Tr.toB (iterate (fun g => psiG (down (n + 1)) (F g) 0) k (omegaG (down (n + 1)) 0)) =
        iterate BTree.opow k (.succ .zero) := by
    intro k
    induction k with
    | zero => exact ⟨trivial, rfl⟩
    | succ k ih =>
        have h1 := hF _ ih.1
        have h2 := psi0_sf (down (n + 1)) _ h1.1
        refine ⟨h2.1, ?_⟩
        show Tr.toB (psiG (down (n + 1)) (F _) 0) = BTree.opow (iterate BTree.opow k (.succ .zero))
        rw [h2.2, h1.2, ih.2]
  rw [e]
  show BTree.lim (fun k => Tr.toB (psiG (down (n + 1))
    (F (iterate (fun g => psiG (down (n + 1)) (F g) 0) k (omegaG (down (n + 1)) 0))) 0)) =
      BTree.lim tower
  congr 1
  funext k
  have h1 := hF _ (hg k).1
  rw [(psi0_sf (down (n + 1)) _ h1.1).2, h1.2, (hg k).2]
  exact iterate_opow_tower k

/-- On trees of level `0` without `sup`s, embedded at level `ω`, `ψ_0` is `ω^·`. -/
theorem psiW_emb0 : ∀ x : T 0, SF x →
    SF (psiW (embW 0 x) 0 0) ∧ Tr.toB (psiW (embW 0 x) 0 0) = BTree.opow (Tr.toB x)
  | .zero, _ => ⟨trivial, rfl⟩
  | .succ a, hx => by
      have ih := psiW_emb0 a hx
      refine ⟨fun k => (mulNat_sf _ ih.1 k).1, ?_⟩
      show BTree.lim (fun k => Tr.toB (Tr.mulNat (psiW (embW 0 a) 0 0) k)) =
        BTree.lim fun k => BTree.mulNat (BTree.opow (Tr.toB a)) k
      congr 1; funext k; rw [(mulNat_sf _ ih.1 k).2, ih.2]
  | .lim f, hx => ⟨fun k => (psiW_emb0 (f k) (hx k)).1,
      congrArg BTree.lim (funext fun k => (psiW_emb0 (f k) (hx k)).2)⟩
  | .sup _ _, hx => hx.elim

/-- The branch `0` of `ψ_0(ε_{Ω_ω+1})` is `ψ_0(Ω_1)`: its Brouwer tree is exactly `ε₀`. -/
theorem toB_branch0W : Tr.toB (psiW (towerW 0) 0 0) = epsilon0 := by
  have hg : ∀ k, SF (iterate (fun g => psiW (embW 0 g) 0 0) k (omegaIn 0 0)) ∧
      Tr.toB (iterate (fun g => psiW (embW 0 g) 0 0) k (omegaIn 0 0)) =
        iterate BTree.opow k (.succ .zero) := by
    intro k
    induction k with
    | zero => exact ⟨trivial, rfl⟩
    | succ k ih =>
        have h := psiW_emb0 _ ih.1
        refine ⟨h.1, ?_⟩
        show Tr.toB (psiW (embW 0 _) 0 0) = BTree.opow (iterate BTree.opow k (.succ .zero))
        rw [h.2, ih.2]
  show BTree.lim (fun k => Tr.toB (psiW (embW 0
    (iterate (fun g => psiW (embW 0 g) 0 0) k (omegaIn 0 0))) 0 0)) = BTree.lim tower
  congr 1
  funext k
  rw [(psiW_emb0 _ (hg k).1).2, (hg k).2]
  exact iterate_opow_tower k

end Buch

/-- `H_{ε₀} ≤ H_θ` for the Takeuti–Feferman–Buchholz tree `θ`. -/
theorem Feps_le_TFB (y : Nat) : Feps y ≤ hardy Buch.thetaTFB y := by
  have h : Feps y ≤ hardy (Buch.Tr.toB (Buch.psiW (Buch.towerW 0) 0 0)) y := by
    rw [Buch.toB_branch0W]; exact Nat.le_refl _
  exact Nat.le_trans h (le_maxUpTo (fun k => hardy (Buch.Tr.toB (Buch.psiW (Buch.towerW k) 0 0)) y)
    (Nat.zero_le y))

/-- `H_{ε₀} ≤ H_θ`: the branch `0` of `θ = ψ_0(Ω_ω)` is `ψ_0(ε_{Ω_2+1})`, whose branch `0`
is `ε₀`. -/
theorem Feps_le_F3 (y : Nat) : Feps y ≤ F3 y := by
  have h : Feps y ≤ hardy (Buch.theta 1) y := by
    have e := Buch.toB_branch0 0
    have h1 : Feps y ≤ hardy (Buch.Tr.toB (Buch.psiG (Buch.down 1)
        (Buch.towerG 1 (Buch.lift 1) (Buch.down 1) 0) 0)) y := by
      rw [e]; exact Nat.le_refl _
    exact Nat.le_trans h1 (le_maxUpTo (fun k => hardy (Buch.Tr.toB (Buch.psiG (Buch.down 1)
      (Buch.towerG 1 (Buch.lift 1) (Buch.down 1) k) 0)) y) (Nat.zero_le y))
  exact Nat.le_trans h (le_maxUpTo (fun K => hardy (Buch.theta (K + 1)) y) (Nat.zero_le y))

theorem F3_42_ge : 336 ≤ F3 42 := Nat.le_trans Feps_42_ge (Feps_le_F3 42)

theorem F3_mono {a b : Nat} (h : a ≤ b) : F3 a ≤ F3 b := hardy_mono _ h

theorem F3_succ (a : Nat) : F3 a + 1 ≤ F3 (a + 1) := hardy_lt_succ _ a

/-- **Rung 2 < rung 3**: System T < the Hardy hierarchy at Buchholz's `θ`. -/
theorem contender_2_lt_contender_3 : contender_2 < contender_3 := by
  unfold contender_2 contender_3 C5.largestSTLCNatRecNatOfDepth C5.largestOfDepth
  have hw : depth (C5.maxBy C5.eval 0 .zero (C5.termsUpTo 42)) ≤ 42 := by
    cases maxBy_mem C5.eval (C5.termsUpTo 42) 0 .zero with
    | inl h => exact depth_of_mem h
    | inr h => rw [h]; decide
  generalize C5.maxBy C5.eval 0 .zero (C5.termsUpTo 42) = w at hw ⊢
  have hlt : Feps 200 < F3 (F3 42) := by
    have h0 := Feps_le_F3 200
    have h1 := F3_succ 200
    have h2 : F3 201 ≤ F3 (F3 42) := F3_mono (by
      have hF := F3_42_ge
      generalize F3 42 = M at hF ⊢
      omega)
    generalize Feps 200 = a at h0 ⊢
    generalize F3 200 = b at h0 h1
    generalize F3 201 = c at h1 h2
    generalize F3 (F3 42) = d at h2 ⊢
    omega
  cases hs : stype [] w with
  | nat => exact Nat.lt_of_le_of_lt (eval_le_Feps hw hs) hlt
  | arr a b =>
      have h0 := eval_eq_zero_of_arr hs
      -- (no `rw` here: its closing `rfl` would try to evaluate `F3 (F3 42)`)
      exact Nat.lt_of_le_of_lt (Nat.le_of_eq h0) (Nat.lt_of_le_of_lt (Nat.zero_le (Feps 200)) hlt)

end BusyLean.Indep
