import BusyLean.Independent.TFBProg

/-!
# The Takeuti–Feferman–Buchholz program computes `ψ_0(ε_{Ω_ω+1})` (proof infrastructure)

The erased program is built from the erasures `…U = eraseF …W` of the closed
combinators of `TFBProg.lean`. Each is `λx₁ … xₙ. b` where `b` applies closed
terms and variables only, so one β-lemma (`steps_lams`) describes it.

* **Evidence** for the branching type `P m` behaves like the numeral `m`
  (`RelEv`): `ev0 = 0̄` and the step is the Church successor.
* **Induction over the levels** (`rel_indL`): for any family of relations `RC m`
  closed under expansion, `indL ev s b` is related at the level of `ev`.
-/

namespace BusyLean.Indep.TFB

open BusyLean.Indep.FW
open BusyLean.F (Steps)
open BusyLean.F.Tm (var app lam subst cons up ren num)
open BusyLean.Indep.Emb (succTm pairTm fstTm sndTm iterTm steps_fst steps_snd steps_num_app)

variable {f : Nat → Nat}

/-! ## n-ary β-reduction -/

/-- `λ … λ. b` with `n` binders. -/
def lamsU : Nat → F.Tm → F.Tm
  | 0, b => b
  | n + 1, b => lam (lamsU n b)

/-- `h a₁ … aₙ`. -/
def appsU (h : F.Tm) : List F.Tm → F.Tm
  | [] => h
  | a :: as => appsU (app h a) as

/-- The substitution of `a₁ … aₙ` for the variables `n - 1, …, 0` over `σ`. -/
def envU (σ : Nat → F.Tm) : List F.Tm → Nat → F.Tm
  | [] => σ
  | a :: as => envU (cons a σ) as

theorem steps_appsU {h h' : F.Tm} (e : Steps f h h') : ∀ as, Steps f (appsU h as) (appsU h' as)
  | [] => e
  | a :: as => steps_appsU (Steps.appL a e) as

theorem steps_lamsU : ∀ (as : List F.Tm) (σ : Nat → F.Tm) (b : F.Tm),
    Steps f (appsU (subst σ (lamsU as.length b)) as) (subst (envU σ as) b)
  | [], _, _ => Steps.refl _
  | a :: as, σ, b => by
      have h1 : Steps f (app (lam (subst (up σ) (lamsU as.length b))) a)
          (subst (cons a σ) (lamsU as.length b)) := by
        have h := Steps.beta (f := f) (subst (up σ) (lamsU as.length b)) a
        rwa [F.Tm.subst_beta] at h
      exact (steps_appsU h1 as).trans (steps_lamsU as (cons a σ) b)

/-- **β-reduction of `λx₁ … xₙ. b` applied to `a₁ … aₙ`.** -/
theorem steps_lams (as : List F.Tm) (b : F.Tm) :
    Steps f (appsU (lamsU as.length b) as) (subst (envU var as) b) := by
  have h := steps_lamsU (f := f) as var b
  rwa [F.Tm.subst_var] at h

/-- `⟨x, y⟩`. -/
abbrev pairU (x y : F.Tm) : F.Tm := app (app pairTm x) y

/-! ## Evidence -/

/-- The evidence for the branching type of level `m` behaves like the numeral `m`. -/
def RelEv (f : Nat → Nat) (m : Nat) (u : F.Tm) : Prop := Steps f u (num m)

theorem RelEv.expand {m : Nat} {u u' : F.Tm} (h : Steps f u u') (h' : RelEv f m u') :
    RelEv f m u := h.trans h'

theorem relEv_succ {m : Nat} {u : F.Tm} (h : RelEv f m u) : RelEv f (m + 1) (app succTm u) :=
  TT.rel_succ (f := f) u m h

/-- `iterTm succ 0 m` reduces to the numeral `m`. -/
theorem steps_iter_succ : ∀ m, Steps f (iterTm succTm (num 0) m) (num m)
  | 0 => Steps.refl _
  | m + 1 => TT.rel_succ (f := f) _ m (steps_iter_succ m)

def EV0U : F.Tm := eraseF ev0W

theorem EV0U_eq : EV0U = num 0 := rfl

theorem relEv0 : RelEv f 0 EV0U := Steps.refl _

def EVSTEPU : F.Tm := eraseF evStepW

theorem EVSTEPU_eq : EVSTEPU = succTm := rfl

/-! ## Induction over the levels -/

def STEPLU : F.Tm := eraseF stepLW

theorem steps_stepL (s p : F.Tm) : Steps f (app (app STEPLU s) p)
    (pairU (app succTm (fstTm p)) (app (app s (fstTm p)) (sndTm p))) :=
  steps_lams [s, p] (pairU (app succTm (fstTm (var 0))) (app (app (var 1) (fstTm (var 0))) (sndTm (var 0))))

def INDLU : F.Tm := eraseF indLW

theorem steps_indL_beta (ev s b : F.Tm) : Steps f (app (app (app INDLU ev) s) b)
    (sndTm (app (app ev (app STEPLU s)) (pairU (num 0) b))) :=
  steps_lams [ev, s, b] (sndTm (app (app (var 2) (app STEPLU (var 1))) (pairU (num 0) (var 0))))

/-- **Induction over the levels.** -/
theorem rel_indL {RC : Nat → F.Tm → Prop} (hexp : ∀ {m u u'}, Steps f u u' → RC m u' → RC m u)
    {s b : F.Tm} (hb : RC 0 b)
    (hs : ∀ m e c, RelEv f m e → RC m c → RC (m + 1) (app (app s e) c)) :
    ∀ {m ev}, RelEv f m ev → RC m (app (app (app INDLU ev) s) b) := by
  have inv : ∀ m, ∃ e c, Steps f (iterTm (app STEPLU s) (pairU (num 0) b) m) (pairU e c) ∧
      RelEv f m e ∧ RC m c := by
    intro m
    induction m with
    | zero => exact ⟨num 0, b, Steps.refl _, Steps.refl _, hb⟩
    | succ m ih =>
      obtain ⟨e, c, hst, he, hc⟩ := ih
      refine ⟨app succTm (fstTm (pairU e c)), app (app s (fstTm (pairU e c))) (sndTm (pairU e c)),
        (Steps.appR _ hst).trans (steps_stepL s (pairU e c)), relEv_succ ((steps_fst e c).trans he), ?_⟩
      exact hexp ((Steps.appL _ (Steps.appR _ (steps_fst e c))).trans (Steps.appR _ (steps_snd e c)))
        (hs m e c he hc)
  intro m ev hev
  obtain ⟨e, c, hst, _, hc⟩ := inv m
  have h1 : Steps f (app (app ev (app STEPLU s)) (pairU (num 0) b))
      (iterTm (app STEPLU s) (pairU (num 0) b) m) :=
    (Steps.appL _ (Steps.appL _ hev)).trans (steps_num_app m _ _)
  exact hexp ((steps_indL_beta ev s b).trans ((Steps.appL _ (h1.trans hst)).trans (steps_snd e c))) hc

def LVLOFU : F.Tm := eraseF lvlOfW

/-- The level of the evidence, as a numeral. -/
theorem steps_lvlOf {m : Nat} {ev : F.Tm} (h : RelEv f m ev) : Steps f (app LVLOFU ev) (num m) := by
  have h1 : Steps f (app LVLOFU ev) (app (app ev succTm) (num 0)) :=
    steps_lams [ev] (app (app (var 0) succTm) (num 0))
  exact h1.trans ((Steps.appL _ (Steps.appL _ h)).trans ((steps_num_app m _ _).trans (steps_iter_succ m)))

/-! ## Pieces translated from `TT`

Each is the translation of a closed `TT` term whose untyped form does not
depend on the levels, so the logical relation of `TT` applies at every level. -/

open BusyLean.Indep.TT (Rel)
open BusyLean.Indep.TT (rel_utrT0)

def RAISEU : F.Tm := eraseF raiseW

theorem RAISEU_eq (j : Nat) : RAISEU = TT.utrT (TT.raiseT j (Γ := [])) :=
  eraseF_trTL (lv4 T0W (.tvar 0) (treeSW (.tvar 0)) (treeSW (.tvar 0)))
    (lv4 natW natW (.tvar 0) (.tvar 0)) (TT.raiseT 2 (Γ := []))

theorem rel_raise (j : Nat) (h : Buch.P j → Nat) :
    Rel f (.arr (.lev 0) (.lev j)) RAISEU (Buch.Tr.cmap 0 h) := by
  rw [RAISEU_eq j, ← TT.eval_raiseT j TT.env0 h]
  exact rel_utrT0 _

def DROPU : F.Tm := eraseF dropW

theorem DROPU_eq (a : Nat) : DROPU = TT.utrT (TT.dropT a (Γ := [])) :=
  eraseF_trTL (lv4 T0W (.tvar 0) (treeSW (.tvar 0)) (treeSW (.tvar 0)))
    (lv4 natW natW (.tvar 0) (.tvar 0)) (TT.dropT 1 (Γ := []))

theorem rel_drop : ∀ (j : Nat) (h : Nat → Buch.P j),
    Rel f (.arr (.lev j) (.lev 0)) DROPU (Buch.Tr.cmap 0 h)
  | 0, h => by
      rw [show DROPU = TT.utrT (TT.raiseT 0 (Γ := [])) from DROPU_eq 0,
        ← TT.eval_raiseT 0 TT.env0 h]
      exact rel_utrT0 _
  | a + 1, h => by
      rw [DROPU_eq a, ← TT.eval_dropT a TT.env0 h]
      exact rel_utrT0 _

def CMAPU : F.Tm := eraseF cmapW

theorem rel_cmap (a b : Nat) :
    Rel f (.arr .nat (.arr (.arr (.lev b) (.lev a)) (.arr (.lev (a + 1)) (.lev (b + 1)))))
      CMAPU (fun thr h => Buch.Tr.cmap thr h) := by
  have e : CMAPU = TT.utrT (TT.cmapT a b (Γ := [])) :=
    eraseF_trTL (lv4 (treeSW (.tvar 1)) (treeSW (treeSW (.tvar 1))) (treeSW (.tvar 0))
      (treeSW (treeSW (.tvar 0)))) (lv4 (.tvar 1) (treeSW (.tvar 1)) (.tvar 0) (treeSW (.tvar 0)))
      (TT.cmapT 0 2 (Γ := []))
  have h := rel_utrT0 (f := f) (TT.cmapT a b (Γ := []))
  rw [← e] at h
  have ev : TT.eval (TT.cmapT a b (Γ := [])) TT.env0 = fun thr h => Buch.Tr.cmap thr h :=
    funext fun thr => funext fun h => TT.eval_cmapT a b TT.env0 thr h
  rw [ev] at h
  exact h

def SUPV0U : F.Tm := eraseF supV0W

theorem rel_supV0 : Rel f (.arr .nat (.lev 0)) SUPV0U (fun μ => Buch.Tr.sup μ (fun _ => Buch.Tr.zero)) :=
  rel_utrT0 (TT.supVia0T (Γ := []))

def MULNATU : F.Tm := eraseF mulNatW

theorem rel_mulNat : ∀ m : Nat, Rel f (.arr (.lev m) (.arr .nat (.lev m))) MULNATU Buch.Tr.mulNat
  | 0 => by
      have e : MULNATU = TT.utrT (TT.mulNat0T (Γ := [])) :=
        eraseF_trTL (lv4 (.tvar 0) (treeSW (.tvar 0)) (.tvar 0) (.tvar 0))
          (lv4 (.tvar 0) (.tvar 0) (.tvar 0) (.tvar 0)) (TT.mulNatL 0 (Γ := []))
      have h := rel_utrT0 (f := f) (TT.mulNat0T (Γ := []))
      rw [← e] at h
      have ev : TT.eval (TT.mulNat0T (Γ := [])) TT.env0 = Buch.Tr.mulNat :=
        funext fun a => funext fun k => TT.eval_mulNat0T TT.env0 a k
      rw [ev] at h
      exact h
  | m + 1 => by
      have e : MULNATU = TT.utrT (TT.mulNatL m (Γ := [])) :=
        eraseF_trTL (lv4 (.tvar 0) (treeSW (.tvar 0)) (.tvar 0) (.tvar 0))
          (lv4 (.tvar 0) (.tvar 0) (.tvar 0) (.tvar 0)) (TT.mulNatL 0 (Γ := []))
      have h := rel_utrT0 (f := f) (TT.mulNatL m (Γ := []))
      rw [← e] at h
      have ev : TT.eval (TT.mulNatL m (Γ := [])) TT.env0 = Buch.Tr.mulNat :=
        funext fun a => funext fun k => TT.eval_mulNatL m TT.env0 a k
      rw [ev] at h
      exact h

def IFLTU : F.Tm := eraseF ifLtW

theorem rel_ifLt (m : Nat) :
    Rel f (.arr .nat (.arr .nat (.arr (.lev m) (.arr (.lev m) (.lev m))))) IFLTU
      (fun μ c a b => if μ < c then a else b) := by
  have e : IFLTU = TT.utrT (TT.ifLtC (r := .lev m) (Γ := [])) :=
    eraseF_trTL (lv4 (treeSW (.tvar 0)) (treeSW (.tvar 0)) (treeSW (.tvar 0)) (treeSW (.tvar 0)))
      (lv4 (.tvar 0) (.tvar 0) (.tvar 0) (.tvar 0)) (TT.ifLtC (r := .lev 0) (Γ := []))
  have h := rel_utrT0 (f := f) (TT.ifLtC (r := .lev m) (Γ := []))
  rw [← e] at h
  have ev : TT.eval (TT.ifLtC (r := .lev m) (Γ := [])) TT.env0 =
      fun (μ c : Nat) (a b : Buch.T m) => if μ < c then a else b :=
    funext fun μ => funext fun c => funext fun a => funext fun b => TT.eval_ifLtC TT.env0 μ c a b
  rw [ev] at h
  exact h

def TOB0U : F.Tm := eraseF toB0W

theorem rel_toB0 : Rel f (.arr (.lev 0) .tree) TOB0U Buch.Tr.toB := by
  have h := rel_utrT0 (f := f) (TT.toB0T (Γ := []))
  rw [TT.eval_toB0T] at h
  exact h

/-! ## Conversions between levels -/

/-- `c` gives the conversions between level `m` and every level. -/
def RConv (f : Nat → Nat) (m : Nat) (c : F.Tm) : Prop :=
  ∀ j e, RelEv f j e → Rel f (.arr (.lev m) (.lev j)) (fstTm (app c e)) (Buch.convFrom m j) ∧
    Rel f (.arr (.lev j) (.lev m)) (sndTm (app c e)) (Buch.convInto m j)

theorem RConv.expand {m : Nat} {c c' : F.Tm} (h : Steps f c c') (h' : RConv f m c') : RConv f m c :=
  fun j e he => ⟨Rel.expand (Steps.appL _ (Steps.appL _ h)) (h' j e he).1,
    Rel.expand (Steps.appL _ (Steps.appL _ h)) (h' j e he).2⟩

def CONVBASEU : F.Tm := eraseF convBaseW
def CBASEDU : F.Tm := eraseF cBaseDW
def CSTEPDU : F.Tm := eraseF cStepDW
def CONVSTEPU : F.Tm := eraseF convStepW
def CONVU : F.Tm := eraseF convW

theorem rel_convBase : RConv f 0 CONVBASEU := by
  intro j e _
  have h1 : Steps f (app CONVBASEU e) (pairU RAISEU DROPU) := steps_lams [e] (pairU RAISEU DROPU)
  constructor
  · refine Rel.expand ((Steps.appL _ h1).trans (steps_fst _ _)) ?_
    cases j with
    | zero => exact rel_raise 0 (fun n => n)
    | succ j => exact rel_raise (j + 1) (fun _ => 0)
  · refine Rel.expand ((Steps.appL _ h1).trans (steps_snd _ _)) ?_
    cases j with
    | zero => exact rel_drop 0 (fun n => n)
    | succ j => exact rel_drop (j + 1) (fun _ => Buch.Tr.zero)

theorem steps_cStepD (e c e₂ c₂ : F.Tm) : Steps f (app (app (app (app CSTEPDU e) c) e₂) c₂)
    (pairU (app (app CMAPU (app succTm (app LVLOFU e₂))) (sndTm (app c e₂)))
      (app (app CMAPU (app succTm (app LVLOFU e))) (fstTm (app c e₂)))) :=
  steps_lams [e, c, e₂, c₂]
    (pairU (app (app CMAPU (app succTm (app LVLOFU (var 1)))) (sndTm (app (var 2) (var 1))))
      (app (app CMAPU (app succTm (app LVLOFU (var 3)))) (fstTm (app (var 2) (var 1)))))

theorem rel_convStep {m : Nat} {e c : F.Tm} (he : RelEv f m e) (hc : RConv f m c) :
    RConv f (m + 1) (app (app CONVSTEPU e) c) := by
  intro j e₂ he₂
  have h1 : Steps f (app (app (app CONVSTEPU e) c) e₂)
      (app (app (app INDLU e₂) (app (app CSTEPDU e) c)) CBASEDU) :=
    steps_lams [e, c, e₂] (app (app (app INDLU (var 0)) (app (app CSTEPDU (var 2)) (var 1))) CBASEDU)
  let RC : Nat → F.Tm → Prop := fun j c₂ =>
    Rel f (.arr (.lev (m + 1)) (.lev j)) (fstTm c₂) (Buch.convFrom (m + 1) j) ∧
      Rel f (.arr (.lev j) (.lev (m + 1))) (sndTm c₂) (Buch.convInto (m + 1) j)
  have hexp : ∀ {j u u'}, Steps f u u' → RC j u' → RC j u := fun h h' =>
    ⟨Rel.expand (Steps.appL _ h) h'.1, Rel.expand (Steps.appL _ h) h'.2⟩
  have hb : RC 0 CBASEDU :=
    ⟨Rel.expand (steps_fst _ _) (rel_drop (m + 1) (fun _ => Buch.Tr.zero)),
      Rel.expand (steps_snd _ _) (rel_raise (m + 1) (fun _ => 0))⟩
  have hs : ∀ j e₃ c₃, RelEv f j e₃ → RC j c₃ →
      RC (j + 1) (app (app (app (app CSTEPDU e) c) e₃) c₃) := by
    intro j e₃ c₃ he₃ _
    have h2 := steps_cStepD (f := f) e c e₃ c₃
    obtain ⟨hF, hI⟩ := hc j e₃ he₃
    constructor
    · refine Rel.expand ((Steps.appL _ h2).trans (steps_fst _ _)) ?_
      exact rel_cmap m j _ _ (relEv_succ (steps_lvlOf he₃)) _ _ hI
    · refine Rel.expand ((Steps.appL _ h2).trans (steps_snd _ _)) ?_
      exact rel_cmap j m _ _ (relEv_succ (steps_lvlOf he)) _ _ hF
  have h3 := rel_indL (RC := RC) hexp hb hs he₂
  exact ⟨Rel.expand (Steps.appL _ h1) h3.1, Rel.expand (Steps.appL _ h1) h3.2⟩

/-- **Conversions between any two levels.** -/
theorem rel_conv {m : Nat} {ev : F.Tm} (h : RelEv f m ev) : RConv f m (app CONVU ev) := by
  have h1 : Steps f (app CONVU ev) (app (app (app INDLU ev) CONVSTEPU) CONVBASEU) :=
    steps_lams [ev] (app (app (app INDLU (var 0)) CONVSTEPU) CONVBASEU)
  exact RConv.expand h1 (rel_indL (RC := RConv f) (fun h h' => RConv.expand h h') rel_convBase
    (fun _ _ _ he hc => rel_convStep he hc) h)

/-! ## `sup`s with branches given on another level -/

/-- `c` builds the `sup`s of level `m` with branches given on any level. -/
def RSV (f : Nat → Nat) (m : Nat) (c : F.Tm) : Prop :=
  ∀ t μ, Steps f t (num μ) → ∀ j e, RelEv f j e → ∀ h (hv : Buch.T j → Buch.T m),
    Rel f (.arr (.lev j) (.lev m)) h hv →
    Rel f (.lev m) (app (app (app c t) e) h) (Buch.supVia m μ j hv)

theorem RSV.expand {m : Nat} {c c' : F.Tm} (h : Steps f c c') (h' : RSV f m c') : RSV f m c :=
  fun t μ ht j e he hh hv hr =>
    Rel.expand (Steps.appL _ (Steps.appL _ (Steps.appL _ h))) (h' t μ ht j e he hh hv hr)

def COMPOSEU : F.Tm := eraseF composeW

theorem rel_compose {a b c : TT.Ty} {g : F.Tm} {gv : TT.den b → TT.den c} {h : F.Tm}
    {hv : TT.den a → TT.den b} (hg : Rel f (.arr b c) g gv) (hh : Rel f (.arr a b) h hv) :
    Rel f (.arr a c) (app (app COMPOSEU g) h) (fun x => gv (hv x)) := fun w x hw =>
  Rel.expand (steps_lams [g, h, w] (app (var 2) (app (var 1) (var 0)))) (hg _ _ (hh w x hw))

def SVBASEU : F.Tm := eraseF svBaseW
def SVSTEPU : F.Tm := eraseF svStepW
def SUPVIAU : F.Tm := eraseF supViaW

theorem rel_svBase : RSV f 0 SVBASEU := fun t μ ht _ e _ h _ _ =>
  Rel.expand (steps_lams [t, e, h] (app SUPV0U (var 2))) (rel_supV0 t μ ht)

theorem rel_svStep {m : Nat} {e c : F.Tm} (he : RelEv f m e) :
    RSV f (m + 1) (app (app SVSTEPU e) c) := by
  intro t μ ht j e₂ he₂ h hv hh
  have h1 : Steps f (app (app (app (app (app SVSTEPU e) c) t) e₂) h)
      (app (app TT.osupTm t) (app (app COMPOSEU h) (fstTm (app (app CONVU e) e₂)))) :=
    steps_lams [e, c, t, e₂, h]
      (app (app TT.osupTm (var 2)) (app (app COMPOSEU (var 0)) (fstTm (app (app CONVU (var 4)) (var 1)))))
  exact Rel.expand h1 (TT.rel_lsup m t μ ht _ _ (rel_compose hh ((rel_conv he) j e₂ he₂).1))

/-- **`supVia` at every level.** -/
theorem rel_supVia {m : Nat} {ev : F.Tm} (h : RelEv f m ev) : RSV f m (app SUPVIAU ev) := by
  have h1 : Steps f (app SUPVIAU ev) (app (app (app INDLU ev) SVSTEPU) SVBASEU) :=
    steps_lams [ev] (app (app (app INDLU (var 0)) SVSTEPU) SVBASEU)
  exact RSV.expand h1 (rel_indL (RC := RSV f) (fun h h' => RSV.expand h h') rel_svBase
    (fun _ _ _ he _ => rel_svStep he) h)

/-! ## Folds over level trees, into any relation -/

open BusyLean.Indep.TT (app4 limArg4 steps_limArg4 RelLS RelP)

theorem rel_lfoldG {A β : Type} {R : F.Tm → A → Prop} {RX : F.Tm → β → Prop}
    (hexp : ∀ {u u' x}, Steps f u u' → RX u' x → RX u x)
    {z s l p : F.Tm} {Fn : Buch.Tr A → β} {zv : β} {sv : β → β} {lv : (Nat → β) → β}
    {pv : Nat → (A → β) → β}
    (ez : Fn .zero = zv) (es : ∀ a, Fn (.succ a) = sv (Fn a))
    (el : ∀ g, Fn (.lim g) = lv (fun k => Fn (g k)))
    (ep : ∀ μ g, Fn (.sup μ g) = pv μ (fun x => Fn (g x)))
    (hz : RX z zv) (hs : ∀ w x, RX w x → RX (app s w) (sv x))
    (hl : ∀ g gv, (∀ n k, Steps f n (num k) → RX (app g n) (gv k)) → RX (app l g) (lv gv))
    (hp : ∀ t μ, Steps f t (num μ) → ∀ g (gv : A → β), (∀ w x, R w x → RX (app g w) (gv x)) →
      RX (app (app p t) g) (pv μ gv)) :
    ∀ (a : Buch.Tr A) (u : F.Tm), RelLS f R u a → RX (app4 u z s l p) (Fn a) := by
  intro a
  induction a with
  | zero => intro u hu; rw [ez]; exact hexp (hu z s l p) hz
  | succ a ih =>
      intro u hu
      obtain ⟨u', hu', hsu⟩ := hu
      rw [es]; exact hexp (hsu z s l p) (hs _ _ (ih u' hu'))
  | lim g ih =>
      intro u hu
      obtain ⟨g', hg', hsu⟩ := hu
      rw [el]
      exact hexp (hsu z s l p) (hl _ _ fun n k hn =>
        hexp (steps_limArg4 g' z s l p n) (ih k _ (hg' n k hn)))
  | sup μ g ih =>
      intro u hu
      obtain ⟨t, g', ht, hg', hsu⟩ := hu
      rw [ep]
      exact hexp (hsu z s l p) (hp t μ ht _ _ fun w x hw =>
        hexp (steps_limArg4 g' z s l p w) (ih x _ (hg' w x hw)))

/-! ## Trees of level `ω` -/

/-- `RelW u a`: the term `u` represents the tree `a` of level `ω`. -/
def RelW (f : Nat → Nat) (u : F.Tm) : Buch.TW → Prop
  | .zero => ∀ z s l p, Steps f (app4 u z s l p) z
  | .succ a => ∃ u', RelW f u' a ∧ ∀ z s l p, Steps f (app4 u z s l p) (app s (app4 u' z s l p))
  | .lim h => ∃ g, (∀ n k, Steps f n (num k) → RelW f (app g n) (h k)) ∧
      ∀ z s l p, Steps f (app4 u z s l p) (app l (limArg4 g z s l p))
  | .sup μ m h => ∃ t e g, Steps f t (num μ) ∧ RelEv f m e ∧
      (∀ w x, Rel f (.lev m) w x → RelW f (app g w) (h x)) ∧
      ∀ z s l p, Steps f (app4 u z s l p) (app (app (app p t) e) (limArg4 g z s l p))

theorem RelW.expand {u u' : F.Tm} (h : Steps f u u') : ∀ {a : Buch.TW}, RelW f u' a → RelW f u a
  | .zero, hr => fun z s l p => (TT.app4_steps h z s l p).trans (hr z s l p)
  | .succ _, ⟨u'', hr, hs⟩ => ⟨u'', hr, fun z s l p => (TT.app4_steps h z s l p).trans (hs z s l p)⟩
  | .lim _, ⟨g, hg, hs⟩ => ⟨g, hg, fun z s l p => (TT.app4_steps h z s l p).trans (hs z s l p)⟩
  | .sup _ _ _, ⟨t, e, g, ht, he, hg, hs⟩ =>
      ⟨t, e, g, ht, he, hg, fun z s l p => (TT.app4_steps h z s l p).trans (hs z s l p)⟩

theorem rel_foldW {β : Type} {RX : F.Tm → β → Prop}
    (hexp : ∀ {u u' x}, Steps f u u' → RX u' x → RX u x)
    {z s l p : F.Tm} {Fn : Buch.TW → β} {zv : β} {sv : β → β} {lv : (Nat → β) → β}
    {pv : Nat → (m : Nat) → (Buch.T m → β) → β}
    (ez : Fn .zero = zv) (es : ∀ a, Fn (.succ a) = sv (Fn a))
    (el : ∀ g, Fn (.lim g) = lv (fun k => Fn (g k)))
    (ep : ∀ μ m g, Fn (.sup μ m g) = pv μ m (fun x => Fn (g x)))
    (hz : RX z zv) (hs : ∀ w x, RX w x → RX (app s w) (sv x))
    (hl : ∀ g gv, (∀ n k, Steps f n (num k) → RX (app g n) (gv k)) → RX (app l g) (lv gv))
    (hp : ∀ t μ, Steps f t (num μ) → ∀ m e, RelEv f m e → ∀ g (gv : Buch.T m → β),
      (∀ w x, Rel f (.lev m) w x → RX (app g w) (gv x)) → RX (app (app (app p t) e) g) (pv μ m gv)) :
    ∀ (a : Buch.TW) (u : F.Tm), RelW f u a → RX (app4 u z s l p) (Fn a) := by
  intro a
  induction a with
  | zero => intro u hu; rw [ez]; exact hexp (hu z s l p) hz
  | succ a ih =>
      intro u hu
      obtain ⟨u', hu', hsu⟩ := hu
      rw [es]; exact hexp (hsu z s l p) (hs _ _ (ih u' hu'))
  | lim g ih =>
      intro u hu
      obtain ⟨g', hg', hsu⟩ := hu
      rw [el]
      exact hexp (hsu z s l p) (hl _ _ fun n k hn =>
        hexp (steps_limArg4 g' z s l p n) (ih k _ (hg' n k hn)))
  | sup μ m g ih =>
      intro u hu
      obtain ⟨t, e, g', ht, he, hg', hsu⟩ := hu
      rw [ep]
      exact hexp (hsu z s l p) (hp t μ ht m e he _ _ fun w x hw =>
        hexp (steps_limArg4 g' z s l p w) (ih x _ (hg' w x hw)))

def ZEROTWU : F.Tm := eraseF zeroTWW
def SUCCTWU : F.Tm := eraseF succTWW
def LIMTWU : F.Tm := eraseF limTWW
def SUPTWU : F.Tm := eraseF supTWW

theorem rel_zeroTW : RelW f ZEROTWU .zero := fun z s l p => steps_lams [z, s, l, p] (var 3)

theorem rel_succTW {a : F.Tm} {av : Buch.TW} (ha : RelW f a av) : RelW f (app SUCCTWU a) (.succ av) :=
  ⟨a, ha, fun z s l p =>
    steps_lams [a, z, s, l, p] (app (var 2) (app4 (var 4) (var 3) (var 2) (var 1) (var 0)))⟩

theorem rel_limTW {g : F.Tm} {gv : Nat → Buch.TW}
    (hg : ∀ n k, Steps f n (num k) → RelW f (app g n) (gv k)) : RelW f (app LIMTWU g) (.lim gv) :=
  ⟨g, hg, fun z s l p => steps_lams [g, z, s, l, p]
    (app (var 1) (lam (app4 (app (var 5) (var 0)) (var 4) (var 3) (var 2) (var 1))))⟩

theorem rel_supTW {t e g : F.Tm} {μ m : Nat} {gv : Buch.T m → Buch.TW} (ht : Steps f t (num μ))
    (he : RelEv f m e) (hg : ∀ w x, Rel f (.lev m) w x → RelW f (app g w) (gv x)) :
    RelW f (app (app (app SUPTWU t) e) g) (.sup μ m gv) :=
  ⟨t, e, g, ht, he, hg, fun z s l p => steps_lams [t, e, g, z, s, l, p]
    (app (app (app (var 0) (var 6)) (var 5))
      (lam (app4 (app (var 5) (var 0)) (var 4) (var 3) (var 2) (var 1))))⟩

/-! ## Trees of level `m` as trees of level `ω` -/

/-- `c` embeds the trees of level `m`. -/
def REmb (f : Nat → Nat) (m : Nat) (c : F.Tm) : Prop :=
  ∀ w a, Rel f (.lev m) w a → RelW f (app c w) (Buch.embW m a)

theorem REmb.expand {m : Nat} {c c' : F.Tm} (h : Steps f c c') (h' : REmb f m c') : REmb f m c :=
  fun w a hw => RelW.expand (Steps.appL _ h) (h' w a hw)

def EMBSUP0U : F.Tm := eraseF embSup0W
def EMBBASEU : F.Tm := eraseF embBaseW
def EMBHU : F.Tm := eraseF embHW
def EMBSTEPU : F.Tm := eraseF embStepW
def EMBU : F.Tm := eraseF embW

theorem rel_embBase : REmb f 0 EMBBASEU := by
  intro w a hw
  have h1 : Steps f (app EMBBASEU w) (app4 w ZEROTWU SUCCTWU LIMTWU EMBSUP0U) :=
    steps_lams [w] (app4 (var 0) ZEROTWU SUCCTWU LIMTWU EMBSUP0U)
  refine RelW.expand h1 ?_
  refine rel_lfoldG (R := RelP f 0) (RX := RelW f) (fun h h' => RelW.expand h h')
    (Fn := Buch.embW 0) rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) rel_zeroTW
    (fun _ _ h => rel_succTW h) (fun _ _ h => rel_limTW h) ?_ a w hw
  intro t μ _ g _ _
  exact RelW.expand (steps_lams [t, g] ZEROTWU) rel_zeroTW

theorem rel_embStep {m : Nat} {e c : F.Tm} (he : RelEv f m e) :
    REmb f (m + 1) (app (app EMBSTEPU e) c) := by
  intro w a hw
  have h1 : Steps f (app (app (app EMBSTEPU e) c) w) (app4 w ZEROTWU SUCCTWU LIMTWU (app EMBHU e)) :=
    steps_lams [e, c, w] (app4 (var 0) ZEROTWU SUCCTWU LIMTWU (app EMBHU (var 2)))
  refine RelW.expand h1 ?_
  refine rel_lfoldG (R := RelP f (m + 1)) (RX := RelW f) (fun h h' => RelW.expand h h')
    (Fn := Buch.embW (m + 1)) rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) rel_zeroTW
    (fun _ _ h => rel_succTW h) (fun _ _ h => rel_limTW h) ?_ a w hw
  intro t μ ht g gv hg
  exact RelW.expand (steps_lams [e, t, g] (app (app (app SUPTWU (var 1)) (var 2)) (var 0)))
    (rel_supTW ht he hg)

/-- **Trees of every level as trees of level `ω`.** -/
theorem rel_emb {m : Nat} {ev : F.Tm} (h : RelEv f m ev) : REmb f m (app EMBU ev) := by
  have h1 : Steps f (app EMBU ev) (app (app (app INDLU ev) EMBSTEPU) EMBBASEU) :=
    steps_lams [ev] (app (app (app INDLU (var 0)) EMBSTEPU) EMBBASEU)
  exact REmb.expand h1 (rel_indL (RC := REmb f) (fun h h' => REmb.expand h h') rel_embBase
    (fun _ _ _ he _ => rel_embStep he) h)

/-! ## Arithmetic of level `ω` -/

def ADDTWU : F.Tm := eraseF addTWW

theorem rel_addTW {a b : F.Tm} {av bv : Buch.TW} (ha : RelW f a av) (hb : RelW f b bv) :
    RelW f (app (app ADDTWU a) b) (Buch.TW.add av bv) := by
  have h1 : Steps f (app (app ADDTWU a) b) (app4 b a SUCCTWU LIMTWU SUPTWU) :=
    steps_lams [a, b] (app4 (var 0) (var 1) SUCCTWU LIMTWU SUPTWU)
  refine RelW.expand h1 ?_
  exact rel_foldW (RX := RelW f) (fun h h' => RelW.expand h h') (Fn := Buch.TW.add av)
    rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) ha (fun _ _ h => rel_succTW h)
    (fun _ _ h => rel_limTW h) (fun _ _ ht _ _ he _ _ hg => rel_supTW ht he hg) bv b hb

def FLIPADDU : F.Tm := eraseF flipAddW
def MULTWU : F.Tm := eraseF mulTWW

theorem rel_mulTW {a b : F.Tm} {av bv : Buch.TW} (ha : RelW f a av) (hb : RelW f b bv) :
    RelW f (app (app MULTWU a) b) (Buch.TW.mul av bv) := by
  have h1 : Steps f (app (app MULTWU a) b) (app4 b ZEROTWU (app FLIPADDU a) LIMTWU SUPTWU) :=
    steps_lams [a, b] (app4 (var 0) ZEROTWU (app FLIPADDU (var 1)) LIMTWU SUPTWU)
  refine RelW.expand h1 ?_
  refine rel_foldW (RX := RelW f) (fun h h' => RelW.expand h h') (Fn := Buch.TW.mul av)
    (sv := fun r => Buch.TW.add r av) rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) rel_zeroTW ?_
    (fun _ _ h => rel_limTW h) (fun _ _ ht _ _ he _ _ hg => rel_supTW ht he hg) bv b hb
  intro w x hw
  exact RelW.expand (steps_lams [a, w] (app (app ADDTWU (var 0)) (var 1))) (rel_addTW hw ha)

/-! ## `Ω_{n+1}`, `Ω_ω` and `ε_{Ω_ω+1}` -/

/-- `u` is (up to reduction) the package of the branching type of level `m`. -/
def RelPkg (f : Nat → Nat) (m : Nat) (u : F.Tm) : Prop :=
  ∀ k, ∃ e, RelEv f m e ∧ Steps f (app u k) (app k e)

def PKG0U : F.Tm := eraseF pkg0W
def KSTEPU : F.Tm := eraseF kStepW
def PKGSTEPU : F.Tm := eraseF pkgStepW
def LVLPKGU : F.Tm := eraseF lvlPkgW

theorem relPkg_iter : ∀ m, RelPkg f m (iterTm PKGSTEPU PKG0U m)
  | 0 => fun k => ⟨num 0, Steps.refl _, steps_lams [k] (app (var 0) (num 0))⟩
  | m + 1 => fun k => by
      obtain ⟨e, he, hs⟩ := relPkg_iter m (app KSTEPU k)
      refine ⟨app succTm e, relEv_succ he, ?_⟩
      have h1 : Steps f (app (app PKGSTEPU (iterTm PKGSTEPU PKG0U m)) k)
          (app (iterTm PKGSTEPU PKG0U m) (app KSTEPU k)) :=
        steps_lams [iterTm PKGSTEPU PKG0U m, k] (app (var 1) (app KSTEPU (var 0)))
      exact h1.trans (hs.trans (steps_lams [k, e] (app (var 1) (app succTm (var 0)))))

theorem relPkg_lvlPkg {t : F.Tm} {n : Nat} (ht : Steps f t (num n)) : RelPkg f n (app LVLPKGU t) := by
  intro k
  obtain ⟨e, he, hs⟩ := relPkg_iter (f := f) n k
  have h1 : Steps f (app LVLPKGU t) (iterTm PKGSTEPU PKG0U n) :=
    (steps_lams [t] (app (app (var 0) PKGSTEPU) PKG0U)).trans
      ((Steps.appL _ (Steps.appL _ ht)).trans (steps_num_app n _ _))
  exact ⟨e, he, (Steps.appL _ h1).trans hs⟩

def OMKU : F.Tm := eraseF omKW
def OMEGATWU : F.Tm := eraseF omegaTWW

/-- **`Ω_{n+1}`**, the limit of all trees of level `n`. -/
theorem rel_omegaTW {t : F.Tm} {n : Nat} (ht : Steps f t (num n)) :
    RelW f (app OMEGATWU t) (Buch.OmegaW n) := by
  obtain ⟨e, he, hs⟩ := relPkg_lvlPkg (f := f) ht (app OMKU t)
  have h1 : Steps f (app OMEGATWU t) (app (app (app SUPTWU t) e) (app EMBU e)) :=
    (steps_lams [t] (app (app LVLPKGU (var 0)) (app OMKU (var 0)))).trans
      (hs.trans (steps_lams [t, e] (app (app (app SUPTWU (var 1)) (var 0)) (app EMBU (var 0)))))
  exact RelW.expand h1 (rel_supTW ht he (rel_emb he))

def OMEGAOMEGAU : F.Tm := eraseF omegaOmegaW

theorem rel_omegaOmega : RelW f OMEGAOMEGAU Buch.OmegaOmega :=
  rel_limTW fun _ _ hn => rel_omegaTW hn

def MULOOU : F.Tm := eraseF mulOOW
def OPOWTWU : F.Tm := eraseF opowTWW

/-- **`Ω_ω^a`.** -/
theorem rel_opowTW {a : F.Tm} {av : Buch.TW} (ha : RelW f a av) :
    RelW f (app OPOWTWU a) (Buch.opowW av) := by
  have h1 : Steps f (app OPOWTWU a) (app4 a (app SUCCTWU ZEROTWU) MULOOU LIMTWU SUPTWU) :=
    steps_lams [a] (app4 (var 0) (app SUCCTWU ZEROTWU) MULOOU LIMTWU SUPTWU)
  refine RelW.expand h1 ?_
  refine rel_foldW (RX := RelW f) (fun h h' => RelW.expand h h') (Fn := Buch.opowW)
    (sv := fun r => Buch.TW.mul r Buch.OmegaOmega) rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) (rel_succTW rel_zeroTW) ?_
    (fun _ _ h => rel_limTW h) (fun _ _ ht _ _ he _ _ hg => rel_supTW ht he hg) av a ha
  intro w x hw
  exact RelW.expand (steps_lams [w] (app (app MULTWU (var 0)) OMEGAOMEGAU)) (rel_mulTW hw rel_omegaOmega)

def TOWERTWU : F.Tm := eraseF towerTWW

theorem rel_tower_iter : ∀ k, RelW f (iterTm OPOWTWU (app OMEGATWU (num 0)) k) (Buch.towerW k)
  | 0 => rel_omegaTW (Steps.refl _)
  | k + 1 => rel_opowTW (rel_tower_iter k)

theorem rel_towerTW {t : F.Tm} {k : Nat} (ht : Steps f t (num k)) :
    RelW f (app TOWERTWU t) (Buch.towerW k) :=
  RelW.expand ((steps_lams [t] (app (app (var 0) OPOWTWU) (app OMEGATWU (num 0)))).trans
    ((Steps.appL _ (Steps.appL _ ht)).trans (steps_num_app k _ _))) (rel_tower_iter k)

def EPSTWU : F.Tm := eraseF epsTWW

/-- **`ε_{Ω_ω+1}`.** -/
theorem rel_epsTW : RelW f EPSTWU Buch.epsW := rel_limTW fun _ _ hn => rel_towerTW hn

/-! ## The collapse -/

/-- `u` computes `φ ν e` at every level `e`, from the evidence for `e` and the numeral `ν`. -/
def RelR (f : Nat → Nat) (u : F.Tm) (φ : Nat → (e : Nat) → Buch.T e) : Prop :=
  ∀ e ev, RelEv f e ev → ∀ t ν, Steps f t (num ν) → Rel f (.lev e) (app (app u ev) t) (φ ν e)

theorem RelR.expand {u u' : F.Tm} {φ : Nat → (e : Nat) → Buch.T e} (h : Steps f u u')
    (h' : RelR f u' φ) : RelR f u φ :=
  fun e ev hev t ν ht => Rel.expand (Steps.appL _ (Steps.appL _ h)) (h' e ev hev t ν ht)

def IDU : F.Tm := eraseF idW

theorem rel_id (σ : TT.Ty) : Rel f (.arr σ σ) IDU (fun x => x) := fun w _ hw =>
  Rel.expand (steps_lams [w] (var 0)) hw

def OMSTEPU : F.Tm := eraseF omStepW
def OMEGAOFU : F.Tm := eraseF omegaOfW

theorem omegaIn_eq (e ν : Nat) :
    Buch.omegaIn e ν =
      TT.recursion (Buch.Tr.succ Buch.Tr.zero) (fun k _ => Buch.supVia e k e (fun x => x)) ν := by
  cases ν <;> rfl

/-- **`Ω_ν` at every level.** -/
theorem rel_omegaOf : RelR f OMEGAOFU (fun ν e => Buch.omegaIn e ν) := by
  intro e ev hev t ν ht
  have h1 : Steps f (app (app OMEGAOFU ev) t)
      (app (app (app Emb.recTm (app TT.osuccTm TT.ozeroTm)) (app OMSTEPU ev)) t) :=
    steps_lams [ev, t] (app (app (app Emb.recTm (app TT.osuccTm TT.ozeroTm)) (app OMSTEPU (var 1))) (var 0))
  refine Rel.expand h1 ?_
  show Rel f (.lev e) _ (Buch.omegaIn e ν)
  rw [omegaIn_eq]
  refine TT.rel_rec (f := f) (.lev e) _ _ (TT.rel_lsucc e _ _ (TT.rel_lzero e)) _ _ ?_ t ν ht
  intro w k hw w₂ x _
  exact Rel.expand (steps_lams [ev, w, w₂] (app (app (app (app SUPVIAU (var 2)) (var 1)) (var 2)) IDU))
    (rel_supVia hev w k hw e ev hev IDU (fun x => x) (rel_id (.lev e)))

def SPSIU : F.Tm := eraseF sPsiW

theorem rel_sPsi {r : F.Tm} {φ : Nat → (e : Nat) → Buch.T e} (hr : RelR f r φ) :
    RelR f (app SPSIU r) (fun ν e => Buch.Tr.lim fun k => Buch.Tr.mulNat (φ ν e) k) := by
  intro e ev hev t ν ht
  have h1 : Steps f (app (app (app SPSIU r) ev) t) (app TT.olimTm (app MULNATU (app (app r ev) t))) :=
    steps_lams [r, ev, t] (app TT.olimTm (app MULNATU (app (app (var 2) (var 1)) (var 0))))
  exact Rel.expand h1 (TT.rel_llim e _ _ (rel_mulNat e _ _ (hr e ev hev t ν ht)))

def LKU : F.Tm := eraseF lkW
def LPSIU : F.Tm := eraseF lPsiW

theorem rel_lPsi {g : F.Tm} {φ : Nat → Nat → (e : Nat) → Buch.T e}
    (hg : ∀ n k, Steps f n (num k) → RelR f (app g n) (φ k)) :
    RelR f (app LPSIU g) (fun ν e => Buch.Tr.lim fun k => φ k ν e) := by
  intro e ev hev t ν ht
  have h1 : Steps f (app (app (app LPSIU g) ev) t) (app TT.olimTm (app (app (app LKU g) ev) t)) :=
    steps_lams [g, ev, t] (app TT.olimTm (app (app (app LKU (var 2)) (var 1)) (var 0)))
  refine Rel.expand h1 (TT.rel_llim e _ _ ?_)
  intro n k hn
  exact Rel.expand (steps_lams [g, ev, t, n] (app (app (app (var 3) (var 0)) (var 2)) (var 1)))
    (hg n k hn e ev hev t ν ht)

def KKU : F.Tm := eraseF kkW
def DSTEPU : F.Tm := eraseF dStepW
def DKU : F.Tm := eraseF dkW
def PPSIU : F.Tm := eraseF pPsiW

/-- The `sup` case of the collapse: keep the node, or diagonalize. -/
def psiSup (μ m : Nat) (gv : Buch.T m → Nat → (e : Nat) → Buch.T e) : Nat → (e : Nat) → Buch.T e :=
  fun ν e => if μ < ν then Buch.supVia e μ m (fun x => gv x ν e)
    else .lim fun k => gv (Buch.iterate (fun g => gv g μ m) k (Buch.omegaIn m μ)) ν e

theorem rel_pPsi {t : F.Tm} {μ : Nat} (ht : Steps f t (num μ)) {m : Nat} {e : F.Tm}
    (he : RelEv f m e) {g : F.Tm} {gv : Buch.T m → Nat → (e : Nat) → Buch.T e}
    (hg : ∀ w x, Rel f (.lev m) w x → RelR f (app g w) (gv x)) :
    RelR f (app (app (app PPSIU t) e) g) (psiSup μ m gv) := by
  intro e₂ ev hev t₂ ν ht₂
  have h1 : Steps f (app (app (app (app (app PPSIU t) e) g) ev) t₂)
      (app (app (app (app IFLTU t) t₂)
          (app (app (app (app SUPVIAU ev) t) e) (app (app (app KKU g) ev) t₂)))
        (app TT.olimTm (app (app (app (app (app DKU t) e) g) ev) t₂))) :=
    steps_lams [t, e, g, ev, t₂]
      (app (app (app (app IFLTU (var 4)) (var 0))
          (app (app (app (app SUPVIAU (var 1)) (var 4)) (var 3)) (app (app (app KKU (var 2)) (var 1)) (var 0))))
        (app TT.olimTm (app (app (app (app (app DKU (var 4)) (var 3)) (var 2)) (var 1)) (var 0))))
  refine Rel.expand h1 (rel_ifLt e₂ t μ ht t₂ ν ht₂ _ _ ?_ _ _ ?_)
  · refine rel_supVia hev t μ ht m e he _ (fun x => gv x ν e₂) ?_
    intro w x hw
    exact Rel.expand (steps_lams [g, ev, t₂, w] (app (app (app (var 3) (var 0)) (var 2)) (var 1)))
      (hg w x hw e₂ ev hev t₂ ν ht₂)
  · refine TT.rel_llim e₂ _ _ ?_
    intro n k hn
    have hrec : Rel f (.lev m)
        (app (app (app Emb.recTm (app (app OMEGAOFU e) t)) (app (app (app DSTEPU t) e) g)) n)
        (Buch.iterate (fun g' => gv g' μ m) k (Buch.omegaIn m μ)) := by
      rw [← TT.recursion_iterate]
      refine TT.rel_rec (f := f) (.lev m) _ _ (rel_omegaOf m e he t μ ht) _ _ ?_ n k hn
      intro w₁ k₁ _ w₂ x hw₂
      exact Rel.expand (steps_lams [t, e, g, w₁, w₂] (app (app (app (var 2) (var 0)) (var 3)) (var 4)))
        (hg w₂ x hw₂ m e he t μ ht)
    have h2 : Steps f (app (app (app (app (app (app DKU t) e) g) ev) t₂) n)
        (app (app (app g (app (app (app Emb.recTm (app (app OMEGAOFU e) t))
          (app (app (app DSTEPU t) e) g)) n)) ev) t₂) :=
      steps_lams [t, e, g, ev, t₂, n]
        (app (app (app (var 3) (app (app (app Emb.recTm (app (app OMEGAOFU (var 4)) (var 5)))
          (app (app (app DSTEPU (var 5)) (var 4)) (var 3))) (var 0))) (var 2)) (var 1))
    exact Rel.expand h2 (hg _ _ hrec e₂ ev hev t₂ ν ht₂)

def PSIU : F.Tm := eraseF psiW

/-- **Buchholz's collapse at level `ω`, into every level.** -/
theorem rel_psi {a : F.Tm} {av : Buch.TW} (ha : RelW f a av) : RelR f (app PSIU a) (Buch.psiW av) := by
  have h1 : Steps f (app PSIU a) (app4 a OMEGAOFU SPSIU LPSIU PPSIU) :=
    steps_lams [a] (app4 (var 0) OMEGAOFU SPSIU LPSIU PPSIU)
  refine RelR.expand h1 ?_
  exact rel_foldW (RX := RelR f) (fun h h' => RelR.expand h h') (Fn := Buch.psiW)
    (sv := fun φ ν e => Buch.Tr.lim fun k => Buch.Tr.mulNat (φ ν e) k)
    (lv := fun φs ν e => Buch.Tr.lim fun k => φs k ν e) (pv := psiSup)
    rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) rel_omegaOf (fun _ _ h => rel_sPsi h)
    (fun _ _ h => rel_lPsi h) (fun _ _ ht _ _ he _ _ hg => rel_pPsi ht he hg) av a ha

/-- **The program computes the Takeuti–Feferman–Buchholz ordinal.** -/
theorem rel_thetaW : TT.RelT f (eraseF thetaW) Buch.thetaTFB := by
  have e : eraseF thetaW = app TOB0U (app (app (app PSIU EPSTWU) (num 0)) (num 0)) := rfl
  rw [e]
  exact rel_toB0 _ _ (rel_psi rel_epsTW 0 (num 0) (Steps.refl _) (num 0) 0 (Steps.refl _))

end BusyLean.Indep.TFB
