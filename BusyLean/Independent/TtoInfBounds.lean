import BusyLean.Independent.TtoInf

/-!
# Ranks and heights of translated System T terms

* `rankLt_trI`: in the translation of a term of depth `≤ K` (in an environment
  of types of depth `≤ K`), every redex has level `< K + 5`. Redexes come only
  from the source's applications, and a type's level is below its depth.
* `ht_trI`: the height of the translation is at most `ω³ + (depth + K + 10)`,
  at index level `200`. The recursor's case tree has branch `k` of height
  `≤ 3k`, and `lim_k 3k ⊑ ω² + ω² ⊑ ω³`.
-/

namespace BusyLean.Indep.Inf

open BusyLean.C5 (Ty Term lookup)
open BusyLean.Indep.Emb (stype tyDepth_stype)
open BusyLean.Indep.Eps
open BusyLean.Indep.Eps.BTree (add opow mulNat omega)

/-! ## Levels and ranks -/

theorem lev_lt_tyDepth : ∀ σ : Ty, lev σ < tyDepth σ
  | .nat => Nat.zero_lt_one
  | .arr a b => by
      have ha := lev_lt_tyDepth a
      have hb := lev_lt_tyDepth b
      simp only [lev, tyDepth]
      omega

theorem rankLt_errT {ρ : Nat} {Γ : List Ty} : ∀ σ : Ty, RankLt ρ (errT σ : Tm Γ σ)
  | .nat => trivial
  | .arr _ b => rankLt_errT (Γ := _ :: Γ) b

theorem rankLt_castT {ρ : Nat} {Γ : List Ty} (src dst : Ty) {t : Tm Γ src} (h : RankLt ρ t) :
    RankLt ρ (castT src dst t) := by
  unfold castT
  split
  · next he =>
      have e := typeEqb_eq' he
      subst e
      exact h
  · exact rankLt_errT dst
where
  typeEqb_eq' {a b : Ty} (h : C5.typeEqb a b = true) : a = b := BusyLean.Indep.Emb.typeEqb_eq h

theorem rankLt_numT {ρ : Nat} {Γ : List Ty} : ∀ k, RankLt ρ (numT k : Tm Γ .nat)
  | 0 => trivial
  | k + 1 => rankLt_numT k

theorem not_isLam_iterT {Γ : List Ty} {r : Ty} {a : Tm Γ r} {f : Tm Γ (.arr .nat (.arr r r))}
    (ha : ¬ IsLam a) : ∀ k, ¬ IsLam (iterT a f k)
  | 0 => ha
  | _ + 1 => fun h => h.elim

theorem rankLt_iterT {ρ : Nat} {Γ : List Ty} {r : Ty} {a : Tm Γ r}
    {f : Tm Γ (.arr .nat (.arr r r))} (ha : RankLt ρ a) (hf : RankLt ρ f) (hfl : ¬ IsLam f) :
    ∀ k, RankLt ρ (iterT a f k)
  | 0 => ha
  | k + 1 => ⟨⟨hf, rankLt_numT k, fun h => absurd h hfl⟩, rankLt_iterT ha hf hfl k, fun h => h.elim⟩

theorem rankLt_caseAt {ρ : Nat} : ∀ {Γ : List Ty} (r : Ty) {n : Tm Γ .nat} {g : Nat → Tm Γ r},
    RankLt ρ n → (∀ k, RankLt ρ (g k)) → (∀ k, ¬ IsLam (g k)) → RankLt ρ (caseAt r n g)
  | _, .nat, _, _, hn, hg, _ => ⟨hn, hg⟩
  | _, .arr _ β, _, _, hn, hg, hgl =>
      rankLt_caseAt β (rankLt_rename ρ _ _ hn)
        (fun k => ⟨rankLt_rename ρ _ _ (hg k), trivial, fun h => absurd (isLam_rename _ _ h) (hgl k)⟩)
        (fun _ h => h.elim)

theorem rankLt_recT {ρ : Nat} {Γ : List Ty} (r : Ty) : RankLt ρ (recT r : Tm Γ _) :=
  rankLt_caseAt r trivial (rankLt_iterT trivial trivial (fun h => h.elim))
    (not_isLam_iterT (fun h => h.elim))

theorem rankLt_trVarAux {ρ : Nat} {Γ : List Ty} (x : Nat) :
    ∀ (o : Option Ty) (h : lookup Γ x = o), RankLt ρ (trVarAux x o h)
  | some _, _ => trivial
  | none, _ => trivial

theorem rankLt_trApp {R : Nat} {Γ : List Ty} : ∀ (T : Ty) {tt : Tm Γ T} (U : Ty) {uu : Tm Γ U},
    RankLt R tt → RankLt R uu → lev T < R → RankLt R (trApp T tt U uu)
  | .nat, _, _, _, _, _, _ => trivial
  | .arr a _, _, U, _, ht, hu, hl => ⟨ht, rankLt_castT U a hu, fun _ => hl⟩

theorem rankLt_trI (K : Nat) : ∀ (Γ : List Ty) (w : Term),
    (∀ a ∈ Γ, tyDepth a ≤ K) → depth w ≤ K → RankLt (K + 5) (trI Γ w)
  | Γ, .var x, _, _ => rankLt_trVarAux x (lookup Γ x) rfl
  | Γ, .lam a b t, hΓ, h => by
      simp only [depth] at h
      have hΓ' : ∀ c ∈ a :: Γ, tyDepth c ≤ K := by
        intro c hc
        cases hc with
        | head => omega
        | tail _ hc => exact hΓ c hc
      exact rankLt_castT _ b (rankLt_trI K (a :: Γ) t hΓ' (by omega))
  | Γ, .app t u, hΓ, h => by
      simp only [depth] at h
      have hs := tyDepth_stype K Γ t hΓ (by omega)
      have hl := lev_lt_tyDepth (stype Γ t)
      exact rankLt_trApp _ _ (rankLt_trI K Γ t hΓ (by omega)) (rankLt_trI K Γ u hΓ (by omega))
        (by omega)
  | _, .zero, _, _ => trivial
  | _, .succ, _, _ => trivial
  | _, .natRec r, _, _ => rankLt_recT r

/-! ## Finite trees -/

/-- The finite tree `n`. -/
def fin : Nat → BTree
  | 0 => .zero
  | n + 1 => .succ (fin n)

theorem fin_mono {n : Nat} : ∀ {a b : Nat}, a ≤ b → Le n (fin a) (fin b)
  | 0, _, _ => .zero _
  | _ + 1, _ + 1, h => .succ (fin_mono (Nat.le_of_succ_le_succ h))

theorem add_fin (a : BTree) : ∀ b, add a (fin b) = Nat.rec a (fun _ x => .succ x) b
  | 0 => rfl
  | b + 1 => congrArg BTree.succ (add_fin a b)

theorem add_fin_fin (a : Nat) : ∀ b, add (fin a) (fin b) = fin (a + b)
  | 0 => rfl
  | b + 1 => congrArg BTree.succ (add_fin_fin a b)

theorem join_fin_le {n : Nat} (a b : Nat) : Le n (join (fin a) (fin b)) (fin (max a b)) :=
  join_le (fin_mono (Nat.le_max_left a b)) (fin_mono (Nat.le_max_right a b))

theorem mulNat_one : ∀ k, mulNat (.succ .zero) k = fin k
  | 0 => rfl
  | k + 1 => by
      show add (mulNat (.succ .zero) k) (.succ .zero) = fin (k + 1)
      rw [mulNat_one k]; rfl

theorem fin_le_omega {n k : Nat} (hk : k ≤ n) : Le n (fin k) omega :=
  .limR k hk (by rw [mulNat_one]; exact Le.refl n _)

theorem omega_eq : omega = opow (.succ .zero) := rfl

theorem fin_le_opow2 {n e : Nat} (he : e ≤ n) (hn : 1 ≤ n) : Le n (fin e) (opow (fin 2)) :=
  (fin_le_omega he).trans (.limR 1 hn (le_add_left .zero _))

theorem fin_mul3_le {n : Nat} (hn : 3 ≤ n) : ∀ k, Le n (fin (3 * k)) (mulNat omega k)
  | 0 => Le.refl n _
  | k + 1 => by
      rw [show 3 * (k + 1) = 3 * k + 3 by omega, ← add_fin_fin]
      exact add_mono (fin_mul3_le hn k) (fin_le_omega hn)

/-- `ω³`. -/
def W : BTree := opow (fin 3)

theorem lim_le_W {n e : Nat} (hn : 3 ≤ n) (he : e ≤ n) {h : Nat → BTree}
    (hh : ∀ k, Le n (h k) (fin (3 * k + e))) : Le n (.lim h) W := by
  have h1 : Le n (.lim h) (add (opow (fin 2)) (opow (fin 2))) := .lim fun k => by
    refine (hh k).trans ?_
    rw [show 3 * k + e = e + 3 * k by omega, ← add_fin_fin]
    exact add_mono (fin_le_opow2 he (by omega)) (fin_mul3_le hn k)
  exact h1.trans (opow_add_self_le (by omega) (fin 2))

/-! ## Heights of the combinators -/

/-- The number of arguments of a type. -/
def arity : Ty → Nat
  | .nat => 0
  | .arr _ b => arity b + 1

theorem arity_lt_tyDepth : ∀ σ : Ty, arity σ < tyDepth σ
  | .nat => Nat.zero_lt_one
  | .arr a b => by
      have := arity_lt_tyDepth b
      simp only [arity, tyDepth]
      omega

theorem ht_errT {Γ : List Ty} : ∀ σ : Ty, ht (errT σ : Tm Γ σ) = fin (arity σ)
  | .nat => rfl
  | .arr _ b => congrArg BTree.succ (ht_errT (Γ := _ :: Γ) b)

theorem ht_numT {Γ : List Ty} : ∀ k, ht (numT k : Tm Γ .nat) = fin k
  | 0 => rfl
  | k + 1 => congrArg BTree.succ (ht_numT k)

theorem ht_iterT {n : Nat} (hn : 1 ≤ n) {Γ : List Ty} {r : Ty} {a : Tm Γ r}
    {f : Tm Γ (.arr .nat (.arr r r))} (ha : ht a = .zero) (hf : ht f = .zero) :
    ∀ k, Le n (ht (iterT a f k)) (fin (3 * k))
  | 0 => by rw [show ht (iterT a f 0) = ht a from rfl, ha]; exact .zero _
  | k + 1 => by
      show Le n (.succ (join (.succ (join (ht f) (ht (numT k : Tm Γ .nat)))) (ht (iterT a f k)))) _
      rw [hf, ht_numT]
      have h1 : Le n (.succ (join .zero (fin k))) (fin (k + 1)) :=
        .succ (join_le (.zero _) (Le.refl n _))
      have h2 := join_mono h1 (ht_iterT hn ha hf k)
      have h3 := (h2.trans (join_fin_le (k + 1) (3 * k)))
      exact (Le.succ h3).trans (fin_mono (a := max (k + 1) (3 * k) + 1) (b := 3 * (k + 1)) (by omega))

theorem ht_caseAt {n : Nat} (hn : 3 ≤ n) : ∀ {Γ : List Ty} (r : Ty) {m : Tm Γ .nat}
    {g : Nat → Tm Γ r} (e : Nat), ht m = .zero → (∀ k, Le n (ht (g k)) (fin (3 * k + e))) →
    e + arity r ≤ n → Le n (ht (caseAt r m g)) (add W (fin (arity r + 1)))
  | _, .nat, m, g, e, hm, hg, he => by
      show Le n (.succ (join (.lim fun k => ht (g k)) (ht m))) (.succ (add W .zero))
      rw [hm]
      exact .succ (join_le (lim_le_W hn (by simp only [arity] at he; omega) hg) (.zero _))
  | _, .arr α β, m, g, e, hm, hg, he => by
      have hm' : ht (weaken (τ := α) m) = .zero := by unfold weaken; rw [ht_rename]; exact hm
      have hg' : ∀ k, Le n (ht (Tm.app (weaken (g k)) (.var .here))) (fin (3 * k + (e + 1))) := by
        intro k
        show Le n (.succ (join (ht (weaken (g k))) .zero)) _
        unfold weaken
        rw [ht_rename]
        exact .succ (join_le (hg k) (.zero _))
      have ih := ht_caseAt hn β (e + 1) hm' hg' (by simp only [arity] at he; omega)
      exact .succ ih

theorem ht_recT {n : Nat} (hn : 3 ≤ n) {Γ : List Ty} (r : Ty) (hr : arity r ≤ n) :
    Le n (ht (recT r : Tm Γ _)) (add W (fin (arity r + 4))) :=
  .succ (.succ (.succ (ht_caseAt hn r 0 rfl
    (fun k => (ht_iterT (by omega) rfl rfl k).trans (fin_mono (by omega))) (by omega))))

theorem fin_le_addW {n a b : Nat} (h : a ≤ b) : Le n (fin a) (add W (fin b)) :=
  (fin_mono h).trans (le_add_left W (fin b))

theorem addW_mono {n a b : Nat} (h : a ≤ b) : Le n (add W (fin a)) (add W (fin b)) :=
  add_mono_right W (fin_mono h)

theorem ht_castT {n : Nat} {Γ : List Ty} (src dst : Ty) (t : Tm Γ src) {m : Nat}
    (ht_t : Le n (ht t) (add W (fin m))) (hd : arity dst ≤ m) :
    Le n (ht (castT src dst t)) (add W (fin m)) := by
  unfold castT
  split
  · next he =>
      have e := BusyLean.Indep.Emb.typeEqb_eq he
      subst e
      exact ht_t
  · rw [ht_errT]; exact fin_le_addW hd

theorem ht_trVarAux {n : Nat} {Γ : List Ty} (x : Nat) (m : Nat) :
    ∀ (o : Option Ty) (h : lookup Γ x = o), Le n (ht (trVarAux x o h)) (add W (fin m))
  | some _, _ => .zero _
  | none, _ => .zero _

theorem ht_trApp {n : Nat} {Γ : List Ty} : ∀ (T : Ty) (tt : Tm Γ T) (U : Ty) (uu : Tm Γ U) {m : Nat},
    Le n (ht tt) (add W (fin m)) → Le n (ht uu) (add W (fin m)) → tyDepth T ≤ m →
    Le n (ht (trApp T tt U uu)) (add W (fin (m + 1)))
  | .nat, _, _, _, _, _, _, _ => .zero _
  | .arr a b, tt, U, uu, m, h1, h2, hm => by
      show Le n (.succ (join (ht tt) (ht (castT U a uu)))) (.succ (add W (fin m)))
      have := arity_lt_tyDepth a
      have hc := ht_castT U a uu h2 (by simp only [tyDepth] at hm; omega)
      exact .succ (join_le h1 hc)

/-- **Heights of translated terms.** -/
theorem ht_trI (K : Nat) (hK : K + 10 ≤ 200) : ∀ (Γ : List Ty) (w : Term),
    (∀ a ∈ Γ, tyDepth a ≤ K) → depth w ≤ K →
    Le 200 (ht (trI Γ w)) (add W (fin (depth w + K + 10)))
  | Γ, .var x, _, _ => ht_trVarAux x _ (lookup Γ x) rfl
  | Γ, .lam a b t, hΓ, h => by
      simp only [depth] at h ⊢
      have hΓ' : ∀ c ∈ a :: Γ, tyDepth c ≤ K := by
        intro c hc
        cases hc with
        | head => omega
        | tail _ hc => exact hΓ c hc
      have ih := ht_trI K hK (a :: Γ) t hΓ' (by omega)
      have hb := arity_lt_tyDepth b
      have hc := ht_castT (n := 200) _ b (trI (a :: Γ) t) (m := depth t + K + 10) ih (by omega)
      show Le 200 (.succ (ht (castT _ b (trI (a :: Γ) t)))) _
      exact (Le.succ (hc.trans (addW_mono (b := max (max (tyDepth a) (tyDepth b)) (depth t) + K + 10)
        (by omega)))).trans (addW_mono (n := 200)
          (a := max (max (tyDepth a) (tyDepth b)) (depth t) + K + 10 + 1)
          (b := max (max (tyDepth a) (tyDepth b)) (depth t) + 1 + K + 10) (by omega))
  | Γ, .app t u, hΓ, h => by
      simp only [depth] at h ⊢
      have hs := tyDepth_stype K Γ t hΓ (by omega)
      have ha := arity_lt_tyDepth (stype Γ t)
      have iht := (ht_trI K hK Γ t hΓ (by omega)).trans
        (addW_mono (b := max (depth t) (depth u) + K + 10) (by omega))
      have ihu := (ht_trI K hK Γ u hΓ (by omega)).trans
        (addW_mono (b := max (depth t) (depth u) + K + 10) (by omega))
      exact (ht_trApp _ _ _ _ (m := max (depth t) (depth u) + K + 10) iht ihu (by omega)).trans
        (addW_mono (by omega))
  | _, .zero, _, _ => .zero _
  | _, .succ, _, _ => fin_le_addW (n := 200) (a := 2) (by simp only [depth]; omega)
  | _, .natRec r, _, h => by
      simp only [depth] at h ⊢
      have := arity_lt_tyDepth r
      exact (ht_recT (by omega) r (by omega)).trans (addW_mono (by omega))

end BusyLean.Indep.Inf
