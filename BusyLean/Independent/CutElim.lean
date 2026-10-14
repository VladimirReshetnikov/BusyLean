import BusyLean.Independent.InfTerms

/-!
# Cut elimination with height bounds, and the bounding lemma

A *redex* is an application whose function is a λ. Its *level* is the level of
the λ's type. `cutElim ρ` contracts every redex of level `ρ`, innermost first.
Contracting a redex of level `ρ` substitutes a term whose type has level `< ρ`,
so it creates only redexes of smaller level (Tait). Hence, if all redexes have
level `≤ ρ`, all redexes of the result have level `< ρ` (`rankLt_cutElim`).

Heights grow by one exponential per round: `ht (cutElim ρ t) ⊑ ω^{ht t}`
(`ht_cutElim`). Meaning is preserved (`eval_cutElim`).

When no redex is left, a closed term of type `nat` is built from `zero`,
`succ` and `case`, and its value is bounded by the Hardy function of
`ω^{ht t}` (`eval_le_hardy`). Reading off a case branch `k` is paid for by the
limit at index `k`, which the Hardy function reaches at arguments `≥ k`.
-/

namespace BusyLean.Indep.Inf

open BusyLean.C5 (Ty den)
open BusyLean.Indep.Eps
open BusyLean.Indep.Eps.BTree (add opow)

/-- The level of a type. -/
def lev : Ty → Nat
  | .nat => 0
  | .arr a b => max (lev a + 1) (lev b)

/-- Is the term a λ? -/
def IsLam : {Γ : List Ty} → {σ : Ty} → Tm Γ σ → Prop
  | _, _, .lam _ => True
  | _, _, _ => False

/-- All redexes have level `< ρ`. -/
def RankLt (ρ : Nat) : {Γ : List Ty} → {σ : Ty} → Tm Γ σ → Prop
  | _, _, .var _ => True
  | _, _, .lam b => RankLt ρ b
  | _, _, @Tm.app _ σ τ s u => RankLt ρ s ∧ RankLt ρ u ∧ (IsLam s → lev (.arr σ τ) < ρ)
  | _, _, .zero => True
  | _, _, .succ t => RankLt ρ t
  | _, _, .case n br => RankLt ρ n ∧ ∀ k, RankLt ρ (br k)

/-- Contract a redex of level `ρ` at the root, if there is one. -/
def appRed (ρ : Nat) {Γ : List Ty} {σ τ : Ty} : Tm Γ (.arr σ τ) → Tm Γ σ → Tm Γ τ
  | .lam b, u => if lev (.arr σ τ) = ρ then subst1 b u else .app (.lam b) u
  | s, u => .app s u

/-- Contract all redexes of level `ρ`, innermost first. -/
def cutElim (ρ : Nat) : {Γ : List Ty} → {σ : Ty} → Tm Γ σ → Tm Γ σ
  | _, _, .var v => .var v
  | _, _, .lam b => .lam (cutElim ρ b)
  | _, _, .app s u => appRed ρ (cutElim ρ s) (cutElim ρ u)
  | _, _, .zero => .zero
  | _, _, .succ t => .succ (cutElim ρ t)
  | _, _, .case n br => .case (cutElim ρ n) fun k => cutElim ρ (br k)

/-! ## Meaning is preserved -/

theorem eval_appRed (ρ : Nat) {Γ : List Ty} {σ τ : Ty} (s : Tm Γ (.arr σ τ)) (u : Tm Γ σ)
    (e : Env Γ) : eval (appRed ρ s u) e = eval s e (eval u e) := by
  cases s with
  | lam b =>
      show eval (if lev (.arr σ τ) = ρ then subst1 b u else .app (.lam b) u) e = _
      split
      · rw [eval_subst1]; rfl
      · rfl
  | var _ => rfl
  | app _ _ => rfl

theorem eval_cutElim (ρ : Nat) : ∀ {Γ : List Ty} {σ : Ty} (t : Tm Γ σ) (e : Env Γ),
    eval (cutElim ρ t) e = eval t e
  | _, _, .var _, _ => rfl
  | _, _, .lam b, e => by
      funext x
      exact eval_cutElim ρ b (Env.cons x e)
  | _, _, .app s u, e => by
      show eval (appRed ρ (cutElim ρ s) (cutElim ρ u)) e = _
      rw [eval_appRed, eval_cutElim ρ s, eval_cutElim ρ u]; rfl
  | _, _, .zero, _ => rfl
  | _, _, .succ t, e => by
      show Nat.succ (eval (cutElim ρ t) e) = _
      rw [eval_cutElim ρ t]; rfl
  | _, _, .case n br, e => by
      show eval (cutElim ρ (br (eval (cutElim ρ n) e))) e = _
      rw [eval_cutElim ρ n, eval_cutElim ρ]; rfl

/-! ## Heights -/

theorem join_opow_le {n : Nat} (hn : 1 ≤ n) (a b : BTree) :
    Le n (join (opow a) (opow b)) (opow (join a b)) :=
  join_le (opow_mono hn (le_join_left a b)) (opow_mono hn (le_join_right hn a b))

theorem join_comm_le {n : Nat} (hn : 1 ≤ n) (a b : BTree) : Le n (join a b) (join b a) :=
  join_le (le_join_right hn b a) (le_join_left b a)

/-- The bound for an application node. -/
theorem app_bound {n : Nat} (hn : 2 ≤ n) {x y a b : BTree} (hx : Le n x (opow a))
    (hy : Le n y (opow b)) : Le n (.succ (join x y)) (opow (.succ (join a b))) :=
  (Le.succ ((join_mono hx hy).trans (join_opow_le (by omega) a b))).trans (succ_opow_le hn _)

theorem ht_appRed (ρ : Nat) {Γ : List Ty} {σ τ : Ty} (s : Tm Γ (.arr σ τ)) (u : Tm Γ σ)
    {a b : BTree} (hs : Le 2 (ht s) (opow a)) (hu : Le 2 (ht u) (opow b)) :
    Le 2 (ht (appRed ρ s u)) (opow (.succ (join a b))) := by
  cases s with
  | lam c =>
      show Le 2 (ht (if lev (.arr σ τ) = ρ then subst1 c u else .app (.lam c) u)) _
      split
      · have hc : Le 2 (ht c) (opow a) := (Le.succR (Le.refl 2 _)).trans hs
        refine (ht_subst1 c u).trans ?_
        refine (add_mono hu hc).trans ?_
        exact (opow_add_opow_le (Nat.le_refl 2) b a).trans
          (opow_mono (by omega) (Le.succ (join_comm_le (by omega) b a)))
      · exact app_bound (Nat.le_refl 2) hs hu
  | var _ => exact app_bound (Nat.le_refl 2) hs hu
  | app _ _ => exact app_bound (Nat.le_refl 2) hs hu

theorem ht_cutElim (ρ : Nat) : ∀ {Γ : List Ty} {σ : Ty} (t : Tm Γ σ),
    Le 2 (ht (cutElim ρ t)) (opow (ht t))
  | _, _, .var _ => .zero _
  | _, _, .lam b =>
      (Le.succ (ht_cutElim ρ b)).trans (succ_opow_le (Nat.le_refl 2) _)
  | _, _, .app s u => ht_appRed ρ _ _ (ht_cutElim ρ s) (ht_cutElim ρ u)
  | _, _, .zero => .zero _
  | _, _, .succ t =>
      (Le.succ (ht_cutElim ρ t)).trans (succ_opow_le (Nat.le_refl 2) _)
  | _, _, .case n br =>
      app_bound (Nat.le_refl 2) (a := .lim fun k => ht (br k)) (.lim fun k => ht_cutElim ρ (br k))
        (ht_cutElim ρ n)

/-! ## Ranks -/

theorem isLam_rename : ∀ {Γ Δ : List Ty} {σ : Ty} (r : Ren Γ Δ) (t : Tm Γ σ),
    IsLam (rename r t) → IsLam t
  | _, _, _, _, .lam _, _ => trivial
  | _, _, _, _, .var _, h => h.elim
  | _, _, _, _, .app _ _, h => h.elim
  | _, _, _, _, .zero, h => h.elim
  | _, _, _, _, .succ _, h => h.elim
  | _, _, _, _, .case _ _, h => h.elim

theorem rankLt_rename (ρ : Nat) : ∀ {Γ Δ : List Ty} {σ : Ty} (r : Ren Γ Δ) (t : Tm Γ σ),
    RankLt ρ t → RankLt ρ (rename r t)
  | _, _, _, _, .var _, _ => trivial
  | _, _, _, r, .lam b, h => rankLt_rename ρ r.lift b h
  | _, _, _, r, .app s u, h =>
      ⟨rankLt_rename ρ r s h.1, rankLt_rename ρ r u h.2.1, fun hl => h.2.2 (isLam_rename r s hl)⟩
  | _, _, _, _, .zero, _ => trivial
  | _, _, _, r, .succ t, h => rankLt_rename ρ r t h
  | _, _, _, r, .case n br, h => ⟨rankLt_rename ρ r n h.1, fun k => rankLt_rename ρ r (br k) (h.2 k)⟩

/-- A substitution whose terms have small rank, and which replaces only variables
of small level by λs. -/
def SubOK (ρ : Nat) {Γ Δ : List Ty} (s : Sub Γ Δ) : Prop :=
  ∀ τ v, RankLt ρ (s τ v) ∧ (IsLam (s τ v) → lev τ < ρ)

theorem SubOK.lift {ρ : Nat} {Γ Δ : List Ty} {s : Sub Γ Δ} (h : SubOK ρ s) (α : Ty) :
    SubOK ρ (Sub.lift (τ := α) s) := fun τ v => by
  cases v with
  | here => exact ⟨trivial, fun hl => hl.elim⟩
  | there v =>
      exact ⟨rankLt_rename ρ _ _ (h τ v).1, fun hl => (h τ v).2 (isLam_rename _ _ hl)⟩

theorem rankLt_subst (ρ : Nat) : ∀ {Γ Δ : List Ty} {σ : Ty} (s : Sub Γ Δ), SubOK ρ s →
    ∀ t : Tm Γ σ, RankLt ρ t → RankLt ρ (subst s t)
  | _, _, _, s, hs, .var v, _ => (hs _ v).1
  | _, _, .arr α _, s, hs, .lam b, h => rankLt_subst ρ _ (hs.lift α) b h
  | _, _, _, s, hs, .app t u, h => by
      refine ⟨rankLt_subst ρ s hs t h.1, rankLt_subst ρ s hs u h.2.1, ?_⟩
      cases t with
      | var v => exact (hs _ v).2
      | lam _ => exact fun _ => h.2.2 trivial
      | app _ _ => exact fun hl => hl.elim
  | _, _, _, _, _, .zero, _ => trivial
  | _, _, _, s, hs, .succ t, h => rankLt_subst ρ s hs t h
  | _, _, _, s, hs, .case n br, h =>
      ⟨rankLt_subst ρ s hs n h.1, fun k => rankLt_subst ρ s hs (br k) (h.2 k)⟩

theorem lev_lt_of_arr {σ τ : Ty} {ρ : Nat} (h : lev (.arr σ τ) = ρ) : lev σ < ρ := by
  have : lev σ + 1 ≤ lev (.arr σ τ) := Nat.le_max_left _ _
  omega

theorem lev_cod_le {σ τ : Ty} : lev τ ≤ lev (.arr σ τ) := Nat.le_max_right _ _

/-- One round lowers the rank, and a λ can appear only at a small type. -/
theorem rankLt_cutElim (ρ : Nat) : ∀ {Γ : List Ty} {σ : Ty} (t : Tm Γ σ), RankLt (ρ + 1) t →
    RankLt ρ (cutElim ρ t) ∧ (IsLam (cutElim ρ t) → IsLam t ∨ lev σ ≤ ρ)
  | _, _, .var _, _ => ⟨trivial, fun h => h.elim⟩
  | _, _, .lam b, h => ⟨(rankLt_cutElim ρ b h).1, fun _ => Or.inl trivial⟩
  | _, _, @Tm.app _ σ' τ s u, h => by
      obtain ⟨hs, hsl⟩ := rankLt_cutElim ρ s h.1
      have hu := (rankLt_cutElim ρ u h.2.1).1
      show RankLt ρ (appRed ρ (cutElim ρ s) (cutElim ρ u)) ∧
        (IsLam (appRed ρ (cutElim ρ s) (cutElim ρ u)) → IsLam (Tm.app s u) ∨ lev τ ≤ ρ)
      revert hs hsl
      generalize cutElim ρ s = s'
      intro hs hsl
      cases s' with
      | lam b =>
          show RankLt ρ (if lev (.arr σ' τ) = ρ then subst1 b (cutElim ρ u) else
              .app (.lam b) (cutElim ρ u)) ∧
            (IsLam (if lev (.arr σ' τ) = ρ then subst1 b (cutElim ρ u) else
              .app (.lam b) (cutElim ρ u)) → IsLam (Tm.app s u) ∨ lev τ ≤ ρ)
          split
          · next he =>
              refine ⟨rankLt_subst ρ _ ?_ b hs, fun _ => Or.inr (he ▸ lev_cod_le)⟩
              intro τ' v
              cases v with
              | here => exact ⟨hu, fun _ => lev_lt_of_arr he⟩
              | there v => exact ⟨trivial, fun hl => hl.elim⟩
          · next he =>
              refine ⟨⟨hs, hu, fun _ => ?_⟩, fun hl => hl.elim⟩
              have hle : lev (.arr σ' τ) ≤ ρ := by
                rcases hsl trivial with hl | hl
                · exact Nat.le_of_lt_succ (h.2.2 hl)
                · exact hl
              omega
      | var _ => exact ⟨⟨hs, hu, fun hl => hl.elim⟩, fun hl => hl.elim⟩
      | app _ _ => exact ⟨⟨hs, hu, fun hl => hl.elim⟩, fun hl => hl.elim⟩
  | _, _, .zero, _ => ⟨trivial, fun h => h.elim⟩
  | _, _, .succ t, h => ⟨(rankLt_cutElim ρ t h).1, fun h => h.elim⟩
  | _, _, .case n br, h =>
      ⟨⟨(rankLt_cutElim ρ n h.1).1, fun k => (rankLt_cutElim ρ (br k) (h.2 k)).1⟩, fun h => h.elim⟩

/-! ## All rounds -/

/-- Eliminate the levels `k-1, …, 1, 0`, in this order. -/
def elimAll : Nat → {Γ : List Ty} → {σ : Ty} → Tm Γ σ → Tm Γ σ
  | 0, _, _, t => t
  | k + 1, _, _, t => elimAll k (cutElim k t)

/-- `k`-fold `ω`-exponentiation. -/
def opowIter : Nat → BTree → BTree
  | 0, a => a
  | k + 1, a => opowIter k (opow a)

theorem opowIter_mono {n : Nat} (hn : 1 ≤ n) : ∀ (k : Nat) {a b : BTree}, Le n a b →
    Le n (opowIter k a) (opowIter k b)
  | 0, _, _, h => h
  | k + 1, _, _, h => opowIter_mono hn k (opow_mono hn h)

theorem elimAll_spec : ∀ (k : Nat) {Γ : List Ty} {σ : Ty} (t : Tm Γ σ), RankLt k t →
    RankLt 0 (elimAll k t) ∧ Le 2 (ht (elimAll k t)) (opowIter k (ht t)) ∧
      ∀ e, eval (elimAll k t) e = eval t e
  | 0, _, _, t, h => ⟨h, Le.refl 2 _, fun _ => rfl⟩
  | k + 1, _, _, t, h => by
      obtain ⟨hr, hh, he⟩ := elimAll_spec k (cutElim k t) (rankLt_cutElim k t h).1
      refine ⟨hr, hh.trans (opowIter_mono (by omega) k (ht_cutElim k t)), fun e => ?_⟩
      rw [show elimAll (k + 1) t = elimAll k (cutElim k t) from rfl, he, eval_cutElim]

/-! ## The bounding lemma -/

/-- The empty environment. -/
def env0 : Env [] := fun _ v => nomatch v

/-- The value of a closed term of type `nat`. -/
def value (t : Tm [] .nat) : Nat := eval t env0

theorem closed_isLam : ∀ {σ τ : Ty} (t : Tm [] (.arr σ τ)), RankLt 0 t → IsLam t
  | _, _, .lam _, _ => trivial
  | _, _, .var v, _ => nomatch v
  | _, _, .app s _, h => absurd (h.2.2 (closed_isLam s h.1)) (Nat.not_lt_zero _)

/-- A value of a type known to be `nat`, as a number. -/
def natVal {σ : Ty} (h : σ = .nat) (x : den σ) : Nat := by subst h; exact x

theorem bound_aux {Γ : List Ty} {σ : Ty} (t : Tm Γ σ) : ∀ (_ : Γ = []) (hσ : σ = .nat)
    (e : Env Γ), RankLt 0 t → ∀ y, 2 ≤ y → natVal hσ (eval t e) ≤ hardy (opow (ht t)) y := by
  induction t with
  | var v => intro hΓ; subst hΓ; nomatch v
  | lam _ _ => intro _ hσ; cases hσ
  | @app Γ' α β s u _ _ =>
      intro hΓ hσ _ h; subst hΓ
      exact absurd (h.2.2 (closed_isLam s h.1)) (Nat.not_lt_zero _)
  | zero => intro _ _ _ _ _ _; exact Nat.zero_le _
  | succ t ih =>
      intro hΓ hσ e h y hy
      have ih' := ih hΓ rfl e h y hy
      show natVal rfl (eval t e) + 1 ≤ hardy (opow (.succ (ht t))) y
      have h1 : hardy (opow (ht t)) y + 1 ≤ hardy (.succ (opow (ht t))) y :=
        hardy_lt_succ (opow (ht t)) y
      have h2 := (succ_opow_le (Nat.le_refl 2) (ht t)).hardy_le hy
      omega
  | case n br ihn ihbr =>
      intro hΓ hσ e h y hy
      show natVal rfl (eval (br (natVal rfl (eval n e))) e) ≤
        hardy (opow (.succ (join (.lim fun k => ht (br k)) (ht n)))) y
      generalize hk : natVal rfl (eval n e) = k
      have hnk : k ≤ hardy (opow (ht n)) y := hk ▸ ihn hΓ rfl e h.1 y hy
      generalize hz : hardy (opow (ht n)) y = z at hnk
      have hz2 : 2 ≤ z := hz ▸ Nat.le_trans hy (le_hardy _ y)
      have hb := ihbr k hΓ rfl e (h.2 k) z hz2
      have h1 : hardy (opow (ht (br k))) z ≤ hardy (opow (.lim fun k => ht (br k))) z :=
        (Le.limR (g := fun j => opow (ht (br j))) k (Nat.le_refl k) (Le.refl k _)).hardy_le hnk
      have h2 : hardy (opow (.lim fun k => ht (br k))) z ≤
          hardy (opow (join (.lim fun k => ht (br k)) (ht n))) z :=
        (opow_mono (by omega) (le_join_left _ (ht n))).hardy_le hz2
      have h3 : hardy (opow (join (.lim fun k => ht (br k)) (ht n))) z ≤
          hardy (opow (join (.lim fun k => ht (br k)) (ht n)))
            (hardy (opow (join (.lim fun k => ht (br k)) (ht n))) y) := by
        rw [← hz]
        exact hardy_mono _ ((opow_mono (by omega) (le_join_right (by omega) _ (ht n))).hardy_le hy)
      have h4 := (opow_add_self_le (Nat.le_refl 2) (join (.lim fun k => ht (br k)) (ht n))).hardy_le hy
      rw [hardy_add] at h4
      omega

/-- **Bounding lemma.** A closed term of type `nat` without redexes has a value
below `H_{ω^{ht t}}(y)` for every `y ≥ 2`. -/
theorem value_le_hardy (t : Tm [] .nat) (h : RankLt 0 t) {y : Nat} (hy : 2 ≤ y) :
    value t ≤ hardy (opow (ht t)) y :=
  bound_aux t rfl rfl env0 h y hy

end BusyLean.Indep.Inf
