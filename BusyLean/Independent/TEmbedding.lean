import BusyLean.Independent.SystemTFacts
import BusyLean.Independent.Confluence

/-!
# System T inside the untyped λ-calculus: a logical relation

Every raw Contender 5 term `t` (ill-typed ones included) is translated into an
untyped λ-term `utr Γ t` over Church numerals. The translation is guided by
the *static type* `stype Γ t`, which is the type tag that Contender 5's
interpreter will attach to the value of `t` in any environment of types `Γ`.
Contender 5's quirks become static decisions:

* a cast between different types is replaced by the default (`error`) value;
* an application whose function has type `nat` becomes the numeral `0`;
* an unbound variable becomes the numeral `0`.

Natural recursion is compiled to iteration over pairs, in the usual way.

The relation `Rel a u x` says that the term `u` computes the value `x : den a`
(at `nat`: `u` reduces to the Church numeral `x`). The fundamental lemma
`rel_utr` shows that every term's translation computes its value; with
confluence this gives `utr_steps`: a closed term of static type `nat` reduces to
the Church numeral of its Contender 5 value.
-/

namespace BusyLean.Indep.Emb

open BusyLean.C5
open BusyLean.F (Steps Tm)
open BusyLean.F.Tm

variable {f : Nat → Nat}

/-! ## Static types -/

theorem typeEqb_eq : ∀ {a b : Ty}, typeEqb a b = true → a = b
  | .nat, .nat, _ => rfl
  | .arr a b, .arr c d, h => by
      simp only [typeEqb, Bool.and_eq_true] at h
      rw [typeEqb_eq h.1, typeEqb_eq h.2]
  | .nat, .arr _ _, h => nomatch h
  | .arr _ _, .nat, h => nomatch h

/-- The type tag of the value of `t` in an environment of types `Γ`. -/
def stype (Γ : List Ty) : Term → Ty
  | .var x =>
      match lookup Γ x with
      | some a => a
      | none => .nat
  | .lam a b _ => .arr a b
  | .app t _ =>
      match stype Γ t with
      | .nat => .nat
      | .arr _ b => b
  | .zero => .nat
  | .succ => .arr .nat .nat
  | .natRec r => .arr r (.arr (.arr .nat (.arr r r)) (.arr .nat r))

theorem nthError_map {α β : Type} (g : α → β) : ∀ (l : List α) (n : Nat),
    nthError (l.map g) n = (nthError l n).map g
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => nthError_map g l n

theorem lookup_map {α β : Type} (g : α → β) (l : List α) (n : Nat) :
    lookup (l.map g) n = (lookup l n).map g := by
  show (match Nat.ble (l.map g).length n with
      | true => none
      | false => nthError (l.map g) ((l.map g).length - (n + 1))) =
    Option.map g (match Nat.ble l.length n with
      | true => none
      | false => nthError l (l.length - (n + 1)))
  rw [List.length_map]
  cases Nat.ble l.length n
  · exact nthError_map g l _
  · rfl

/-- Types of an environment. -/
abbrev tys (e : List Value) : List Ty := e.map Sigma.fst

theorem interp_fst : ∀ (t : Term) (e : List Value), (interp e t).1 = stype (tys e) t
  | .var x, e => by
      show (match lookup e x with
          | some r => r
          | none => (⟨.nat, error .nat⟩ : Value)).1 = (match lookup (tys e) x with
          | some a => a
          | none => .nat)
      rw [lookup_map]
      cases lookup e x <;> rfl
  | .lam a b _, _ => rfl
  | .app t u, e => by
      have ih := interp_fst t e
      show (match interp e t, interp e u with
          | ⟨.nat, _⟩, _ => (⟨.nat, error .nat⟩ : Value)
          | ⟨.arr a _, r₁⟩, ⟨_, r₂⟩ => ⟨_, r₁ (cast a r₂)⟩).1 = (match stype (tys e) t with
          | .nat => .nat
          | .arr _ b => b)
      rw [← ih]
      generalize interp e t = v
      obtain ⟨T, x⟩ := v
      cases T <;> rfl
  | .zero, _ => rfl
  | .succ, _ => rfl
  | .natRec _, _ => rfl

/-! ## Combinators -/

/-- Default values: `0` and constant functions. -/
def errTm : Ty → Tm
  | .nat => num 0
  | .arr _ b => lam (errTm b)

theorem subst_errTm (σ : Nat → Tm) : ∀ a, subst σ (errTm a) = errTm a
  | .nat => subst_num σ 0
  | .arr _ b => by
      show lam (subst (up σ) (errTm b)) = lam (errTm b)
      rw [subst_errTm _ b]

/-- A cast: the identity between equal types, the default value otherwise. -/
def castTm (src dst : Ty) (u : Tm) : Tm := if typeEqb src dst then u else errTm dst

theorem subst_castTm (σ : Nat → Tm) (src dst : Ty) (u : Tm) :
    subst σ (castTm src dst u) = castTm src dst (subst σ u) := by
  unfold castTm
  cases typeEqb src dst
  · exact subst_errTm σ dst
  · rfl

/-- Church successor `λn s z. s (n s z)`. -/
def succTm : Tm := lam (lam (lam (app (var 1) (app (app (var 2) (var 1)) (var 0)))))

/-- `λx y k. k x y`. -/
def pairTm : Tm := lam (lam (lam (app (app (var 0) (var 2)) (var 1))))

/-- `p (λx y. x)`. -/
def fstTm (p : Tm) : Tm := app p (lam (lam (var 1)))

/-- `p (λx y. y)`. -/
def sndTm (p : Tm) : Tm := app p (lam (lam (var 0)))

/-- The iteration step `λf p. ⟨succ (fst p), f (fst p) (snd p)⟩`. -/
def stepTm : Tm :=
  lam (lam (app (app pairTm (app succTm (fstTm (var 0))))
    (app (app (var 1) (fstTm (var 0))) (sndTm (var 0)))))

/-- Natural recursion `λa f n. snd (n (step f) ⟨0, a⟩)`. -/
def recTm : Tm :=
  lam (lam (lam (sndTm (app (app (var 0) (app stepTm (var 1))) (app (app pairTm (num 0)) (var 2))))))

/-! ## The translation -/

/-- Translation of a raw term in an environment of types `Γ` (innermost first). -/
def utr (Γ : List Ty) : Term → Tm
  | .var x =>
      match lookup Γ x with
      | some _ => var (Γ.length - (x + 1))
      | none => num 0
  | .lam a b t => lam (castTm (stype (a :: Γ) t) b (utr (a :: Γ) t))
  | .app t u =>
      match stype Γ t with
      | .nat => num 0
      | .arr a _ => app (utr Γ t) (castTm (stype Γ u) a (utr Γ u))
  | .zero => num 0
  | .succ => succTm
  | .natRec _ => recTm

/-! ## Reduction lemmas -/

theorem subst_up_up_beta (b x y : Tm) (σ : Nat → Tm) :
    subst (cons y (cons x var)) (subst (up (up σ)) b) = subst (cons y (cons x σ)) b := by
  rw [subst_subst]
  congr 1
  funext n
  match n with
  | 0 => rfl
  | 1 => rfl
  | n + 2 =>
      show subst (cons y (cons x var)) (ren Nat.succ (ren Nat.succ (σ n))) = σ n
      rw [ren_ren, subst_ren]
      exact subst_var (σ n)

theorem steps_beta2 (b x y : Tm) :
    Steps f (app (app (lam (lam b)) x) y) (subst (cons y (cons x var)) b) := by
  have h₁ : Steps f (app (app (lam (lam b)) x) y)
      (app (lam (subst (up (cons x var)) b)) y) := Steps.appL y (Steps.beta _ _)
  refine h₁.trans ?_
  have h₂ := Steps.beta (f := f) (subst (up (cons x var)) b) y
  rwa [subst_beta] at h₂

theorem steps_beta3 (b x y z : Tm) :
    Steps f (app (app (app (lam (lam (lam b))) x) y) z)
      (subst (cons z (cons y (cons x var))) b) := by
  have h₁ : Steps f (app (app (app (lam (lam (lam b))) x) y) z)
      (app (app (lam (lam (subst (up (up (cons x var))) b))) y) z) :=
    Steps.appL z (Steps.appL y (Steps.beta _ _))
  refine h₁.trans ?_
  have h₂ := steps_beta2 (f := f) (subst (up (up (cons x var))) b) y z
  rwa [subst_up_up_beta] at h₂

/-- `F (F (… (F X)))`. -/
def iterTm (F X : Tm) : Nat → Tm
  | 0 => X
  | n + 1 => app F (iterTm F X n)

theorem subst_iterApp_eq (σ : Nat → Tm) : ∀ n, subst σ (iterApp n) = iterTm (σ 1) (σ 0) n
  | 0 => rfl
  | n + 1 => by
      show app (σ 1) (subst σ (iterApp n)) = _
      rw [subst_iterApp_eq σ n]
      rfl

theorem steps_num_app (n : Nat) (F X : Tm) :
    Steps f (app (app (num n) F) X) (iterTm F X n) := by
  have h := steps_beta2 (f := f) (iterApp n) F X
  rwa [subst_iterApp_eq] at h

theorem iterTm_vars : ∀ n, iterTm (var 1) (var 0) n = iterApp n
  | 0 => rfl
  | n + 1 => by
      show app (var 1) (iterTm (var 1) (var 0) n) = app (var 1) (iterApp n)
      rw [iterTm_vars n]

theorem steps_fst (x y : Tm) : Steps f (fstTm (app (app pairTm x) y)) x := by
  have h₁ : Steps f (fstTm (app (app pairTm x) y))
      (app (lam (app (app (var 0) (ren Nat.succ x)) (ren Nat.succ y))) (lam (lam (var 1)))) := by
    have := Steps.appL (f := f) (lam (lam (var 1))) (steps_beta2 (f := f)
      (lam (app (app (var 0) (var 2)) (var 1))) x y)
    exact this
  refine h₁.trans ((Steps.beta _ _).trans ?_)
  show Steps f (app (app (lam (lam (var 1)))
    (subst (cons (lam (lam (var 1))) var) (ren Nat.succ x)))
    (subst (cons (lam (lam (var 1))) var) (ren Nat.succ y))) x
  rw [subst_ren, subst_ren]
  show Steps f (app (app (lam (lam (var 1))) (subst var x)) (subst var y)) x
  rw [subst_var, subst_var]
  have h := steps_beta2 (f := f) (var 1) x y
  exact h

theorem steps_snd (x y : Tm) : Steps f (sndTm (app (app pairTm x) y)) y := by
  have h₁ : Steps f (sndTm (app (app pairTm x) y))
      (app (lam (app (app (var 0) (ren Nat.succ x)) (ren Nat.succ y))) (lam (lam (var 0)))) := by
    have := Steps.appL (f := f) (lam (lam (var 0))) (steps_beta2 (f := f)
      (lam (app (app (var 0) (var 2)) (var 1))) x y)
    exact this
  refine h₁.trans ((Steps.beta _ _).trans ?_)
  show Steps f (app (app (lam (lam (var 0)))
    (subst (cons (lam (lam (var 0))) var) (ren Nat.succ x)))
    (subst (cons (lam (lam (var 0))) var) (ren Nat.succ y))) y
  rw [subst_ren, subst_ren]
  show Steps f (app (app (lam (lam (var 0))) (subst var x)) (subst var y)) y
  rw [subst_var, subst_var]
  have h := steps_beta2 (f := f) (var 0) x y
  exact h

/-! ## The logical relation -/

/-- `Rel a u x`: the term `u` computes the value `x`. -/
def Rel (f : Nat → Nat) : (a : Ty) → Tm → den a → Prop
  | .nat, u, n => Steps f u (num n)
  | .arr a b, u, g => ∀ w x, Rel f a w x → Rel f b (app u w) (g x)

theorem Rel.expand : ∀ {a : Ty} {u u' : Tm} {x : den a}, Steps f u u' → Rel f a u' x → Rel f a u x
  | .nat, _, _, _, h, hr => h.trans hr
  | .arr _ _, _, _, _, h, hr => fun w y hw => Rel.expand (Steps.appL w h) (hr w y hw)

theorem rel_error : ∀ a : Ty, Rel f a (errTm a) (error a)
  | .nat => Steps.refl _
  | .arr _ b => fun w _ _ => by
      have h := Steps.beta (f := f) (errTm b) w
      rw [subst_errTm] at h
      exact Rel.expand h (rel_error b)

theorem castImpl_ne : ∀ {a b : Ty}, typeEqb a b = false → ∀ x, (castImpl a b).1 x = error b
  | .nat, .nat, h, _ => nomatch h
  | .nat, .arr _ _, _, _ => rfl
  | .arr _ _, .nat, _, _ => rfl
  | .arr a b, .arr c d, h, x => by
      simp only [typeEqb] at h
      show (match typeEqb a c && typeEqb b d with
        | true => _
        | false => castError (.arr a b) (.arr c d)).1 x = _
      rw [h]
      rfl

theorem rel_cast {src dst : Ty} {u : Tm} {x : den src} (h : Rel f src u x) :
    Rel f dst (castTm src dst u) (C5.cast dst x) := by
  unfold castTm C5.cast
  cases he : typeEqb src dst with
  | false =>
      rw [castImpl_ne he]
      exact rel_error dst
  | true =>
      have e := typeEqb_eq he
      subst e
      rw [(castImpl_same src).1]
      exact h

theorem rel_succ : Rel f (.arr .nat .nat) succTm Nat.succ := by
  intro w (n : Nat) (hw : Steps f w (num n))
  have h₁ : Steps f (app succTm w)
      (lam (lam (app (var 1) (app (app (ren Nat.succ (ren Nat.succ w)) (var 1)) (var 0))))) :=
    Steps.beta _ _
  refine h₁.trans (Steps.lam (Steps.lam (Steps.appR _ ?_)))
  have hw' : Steps f (ren Nat.succ (ren Nat.succ w)) (num n) := by
    have := (hw.ren Nat.succ).ren Nat.succ
    rwa [BusyLean.F.ren_num, BusyLean.F.ren_num] at this
  refine (Steps.appL (var 0) (Steps.appL (var 1) hw')).trans ?_
  have := steps_num_app (f := f) n (var 1) (var 0)
  rwa [iterTm_vars] at this

/-- One iteration step applied to a pair. -/
theorem steps_step (g x y : Tm) :
    Steps f (app (app stepTm g) (app (app pairTm x) y))
      (app (app pairTm (app succTm (fstTm (app (app pairTm x) y))))
        (app (app g (fstTm (app (app pairTm x) y))) (sndTm (app (app pairTm x) y)))) := by
  have h := steps_beta2 (f := f)
    (app (app pairTm (app succTm (fstTm (var 0))))
      (app (app (var 1) (fstTm (var 0))) (sndTm (var 0)))) g (app (app pairTm x) y)
  exact h

theorem rel_iter {r : Ty} {g : Tm} {z : Tm} {g' : Nat → den r → den r} {z' : den r}
    (hz : Rel f r z z') (hg : Rel f (.arr .nat (.arr r r)) g g') :
    ∀ j, ∃ x y, Steps f (iterTm (app stepTm g) (app (app pairTm (num 0)) z) j)
      (app (app pairTm x) y) ∧ Rel f .nat x j ∧ Rel f r y (recursion z' g' j)
  | 0 => ⟨num 0, z, Steps.refl _, Steps.refl _, hz⟩
  | j + 1 => by
      obtain ⟨x, y, hs, hx, hy⟩ := rel_iter hz hg j
      refine ⟨_, _, (Steps.appR _ hs).trans (steps_step g x y), ?_, ?_⟩
      · exact rel_succ _ j (Rel.expand (steps_fst x y) hx)
      · exact hg _ j (Rel.expand (steps_fst x y) hx) _ _ (Rel.expand (steps_snd x y) hy)

theorem rel_rec (r : Ty) :
    Rel f (.arr r (.arr (.arr .nat (.arr r r)) (.arr .nat r))) recTm recursion := by
  intro z z' hz g g' hg w n hw
  have h₁ : Steps f (app (app (app recTm z) g) w)
      (sndTm (app (app w (app stepTm g)) (app (app pairTm (num 0)) z))) := by
    have h := steps_beta3 (f := f)
      (sndTm (app (app (var 0) (app stepTm (var 1))) (app (app pairTm (num 0)) (var 2)))) z g w
    have e : subst (cons w (cons g (cons z var)))
        (sndTm (app (app (var 0) (app stepTm (var 1))) (app (app pairTm (num 0)) (var 2)))) =
        sndTm (app (app w (app (subst (cons w (cons g (cons z var))) stepTm) g))
          (app (app (subst (cons w (cons g (cons z var))) pairTm)
            (subst (cons w (cons g (cons z var))) (num 0))) z)) := rfl
    have hs : ∀ σ : Nat → Tm, subst σ stepTm = stepTm := fun σ => rfl
    have hp : ∀ σ : Nat → Tm, subst σ pairTm = pairTm := fun σ => rfl
    rw [e, hs, hp, subst_num] at h
    exact h
  refine Rel.expand h₁ ?_
  obtain ⟨x, y, hs, _, hy⟩ := rel_iter hz hg n
  refine Rel.expand (Steps.appL _ ((Steps.appL _ (Steps.appL _ hw)).trans
    (steps_num_app n _ _))) ?_
  exact Rel.expand ((Steps.appL _ hs).trans (steps_snd x y)) hy

/-! ## The fundamental lemma -/

/-- A substitution computes an environment. -/
def EnvRel (f : Nat → Nat) (σ : Nat → Tm) (e : List Value) : Prop :=
  ∀ i v, nthError e i = some v → Rel f v.1 (σ i) v.2

theorem EnvRel.cons {σ : Nat → Tm} {e : List Value} (h : EnvRel f σ e) {a : Ty} {w : Tm}
    {x : den a} (hw : Rel f a w x) : EnvRel f (cons w σ) (⟨a, x⟩ :: e) := fun i v hv => by
  cases i with
  | zero => cases hv; exact hw
  | succ i => exact h i v hv

theorem lookup_some {α : Type} {e : List α} {x : Nat} {v : α} (h : lookup e x = some v) :
    nthError e (e.length - (x + 1)) = some v := by
  change (match Nat.ble e.length x with
    | true => none
    | false => nthError e (e.length - (x + 1))) = some v at h
  cases hb : Nat.ble e.length x with
  | true => rw [hb] at h; cases h
  | false => rw [hb] at h; exact h

/-! ## Depth of static types -/

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

/-- **Fundamental lemma.** -/
theorem rel_utr : ∀ (t : Term) {e : List Value} {σ : Nat → Tm}, EnvRel f σ e →
    Rel f (interp e t).1 (subst σ (utr (tys e) t)) (interp e t).2
  | .var x, e, σ, hσ => by
      show Rel f (match lookup e x with
          | some r => r
          | none => (⟨.nat, error .nat⟩ : Value)).1
        (subst σ (match lookup (tys e) x with
          | some _ => var ((tys e).length - (x + 1))
          | none => num 0))
        (match lookup e x with
          | some r => r
          | none => (⟨.nat, error .nat⟩ : Value)).2
      rw [lookup_map]
      cases hl : lookup e x with
      | none => exact Steps.refl _
      | some v =>
          show Rel f v.1 (σ ((tys e).length - (x + 1))) v.2
          rw [List.length_map]
          exact hσ _ v (lookup_some hl)
  | .lam a b t, e, σ, hσ => by
      intro w x hw
      have h₁ : Steps f (app (subst σ (utr (tys e) (.lam a b t))) w)
          (subst (cons w σ) (castTm (stype (a :: tys e) t) b (utr (a :: tys e) t))) := by
        have h := Steps.beta (f := f)
          (subst (up σ) (castTm (stype (a :: tys e) t) b (utr (a :: tys e) t))) w
        rw [subst_beta] at h
        exact h
      refine Rel.expand h₁ ?_
      rw [subst_castTm]
      have ih := rel_utr t (e := ⟨a, x⟩ :: e) (hσ.cons hw)
      have ht := interp_fst t (⟨a, x⟩ :: e)
      revert ih
      show Rel f (interp (⟨a, x⟩ :: e) t).1 (subst (cons w σ) (utr (a :: tys e) t))
          (interp (⟨a, x⟩ :: e) t).2 →
        Rel f b (castTm (stype (a :: tys e) t) b (subst (cons w σ) (utr (a :: tys e) t)))
          (cast b (interp (⟨a, x⟩ :: e) t).2)
      rw [← show stype (tys (⟨a, x⟩ :: e)) t = stype (a :: tys e) t from rfl, ← ht]
      exact rel_cast
  | .app t u, e, σ, hσ => by
      have iht := rel_utr t hσ
      have ihu := rel_utr u hσ
      have ht := interp_fst t e
      have hu := interp_fst u e
      show Rel f (match interp e t, interp e u with
          | ⟨.nat, _⟩, _ => (⟨.nat, error .nat⟩ : Value)
          | ⟨.arr a _, r₁⟩, ⟨_, r₂⟩ => ⟨_, r₁ (cast a r₂)⟩).1
        (subst σ (match stype (tys e) t with
          | .nat => num 0
          | .arr a _ => app (utr (tys e) t) (castTm (stype (tys e) u) a (utr (tys e) u))))
        (match interp e t, interp e u with
          | ⟨.nat, _⟩, _ => (⟨.nat, error .nat⟩ : Value)
          | ⟨.arr a _, r₁⟩, ⟨_, r₂⟩ => ⟨_, r₁ (cast a r₂)⟩).2
      rw [← ht, ← hu]
      revert iht ihu
      generalize interp e t = vt
      generalize interp e u = vu
      intro iht ihu
      obtain ⟨T, xt⟩ := vt
      obtain ⟨U, xu⟩ := vu
      cases T with
      | nat => exact Steps.refl _
      | arr a b =>
          show Rel f b (app (subst σ (utr (tys e) t))
            (subst σ (castTm U a (utr (tys e) u)))) (xt (cast a xu))
          rw [subst_castTm]
          exact iht _ _ (rel_cast ihu)
  | .zero, _, _, _ => Steps.refl _
  | .succ, _, _, _ => rel_succ
  | .natRec r, _, _, _ => rel_rec r

/-- A closed term of static type `nat` reduces to the numeral of its value. -/
theorem utr_steps {t : Term} (h : stype [] t = .nat) : Steps f (utr [] t) (num (eval t)) := by
  have hr := rel_utr (f := f) t (e := []) (σ := var) (fun _ _ hv => nomatch hv)
  rw [subst_var] at hr
  have ht := interp_fst t []
  revert hr
  unfold eval
  generalize interp [] t = v at ht ⊢
  obtain ⟨T, x⟩ := v
  have hT : T = .nat := ht.trans h
  subst hT
  exact id

end BusyLean.Indep.Emb
