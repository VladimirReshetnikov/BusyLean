import BusyLean.Independent.TreeLang
import BusyLean.Independent.TEmbedding

/-!
# `TT` inside the untyped λ-calculus: Church-encoded trees

Numbers are Church numerals, natural recursion is iteration over pairs (as in
`TEmbedding.lean`), and a Brouwer tree is encoded by its iterator
`λz s l. …`, as in System F. The constructors become

* `tzero = λz s l. z`,
* `tsucc = λt z s l. s (t z s l)`,
* `tlim = λg z s l. l (λn. g n z s l)`,

and `fold = λz s l t. t z s l`.

The relation at the tree type is defined by recursion on the **tree value**
(`RelT`): a term represents `lim f` if, applied to `z s l`, it reduces to
`l (λn. g n z s l)` for a term `g` whose values represent `f`. This avoids the
impredicative quantification over all result types; the fold lemma
`rel_foldT` is proved by induction on the tree. `utrT_steps`: a closed `TT`
program of type `nat` reduces to the Church numeral of its value.
-/

namespace BusyLean.Indep.TT

open BusyLean.F (Steps)
open BusyLean.F.Tm
open BusyLean.Indep.Emb (steps_beta3 subst_up_up_beta steps_num_app iterTm iterTm_vars succTm
  pairTm fstTm sndTm stepTm recTm steps_fst steps_snd steps_step)

variable {f : Nat → Nat}

/-! ## Combinators -/

def app3 (u z s l : F.Tm) : F.Tm := .app (.app (.app u z) s) l

def tzeroTm : F.Tm := .lam (.lam (.lam (.var 2)))

def tsuccTm : F.Tm :=
  .lam (.lam (.lam (.lam (.app (.var 1) (app3 (.var 3) (.var 2) (.var 1) (.var 0))))))

def tlimTm : F.Tm :=
  .lam (.lam (.lam (.lam (.app (.var 0)
    (.lam (app3 (.app (.var 4) (.var 0)) (.var 3) (.var 2) (.var 1)))))))

def foldTm : F.Tm := .lam (.lam (.lam (.lam (app3 (.var 0) (.var 3) (.var 2) (.var 1)))))

/-- The function `λn. g n z s l`, shifted under its binder. -/
def limArg (g z s l : F.Tm) : F.Tm :=
  .lam (app3 (.app (ren Nat.succ g) (.var 0)) (ren Nat.succ z) (ren Nat.succ s) (ren Nat.succ l))

/-! ## Four β-steps -/

theorem subst_up3_beta (b x y z w : F.Tm) :
    subst (cons w (cons z (cons y var))) (subst (up (up (up (cons x var)))) b) =
      subst (cons w (cons z (cons y (cons x var)))) b := by
  rw [subst_subst]
  congr 1
  funext n
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => show subst _ (ren Nat.succ (ren Nat.succ (ren Nat.succ x))) = x
         rw [ren_ren, ren_ren, subst_ren]; exact subst_var x
  | n + 4 => rfl

theorem steps_beta4 (b x y z w : F.Tm) :
    Steps f (.app (.app (.app (.app (.lam (.lam (.lam (.lam b)))) x) y) z) w)
      (subst (cons w (cons z (cons y (cons x var)))) b) := by
  have h₁ : Steps f (.app (.app (.app (.app (.lam (.lam (.lam (.lam b)))) x) y) z) w)
      (.app (.app (.app (.lam (.lam (.lam (subst (up (up (up (cons x var)))) b)))) y) z) w) :=
    Steps.appL w (Steps.appL z (Steps.appL y (Steps.beta _ _)))
  refine h₁.trans ?_
  have h₂ := steps_beta3 (f := f) (subst (up (up (up (cons x var)))) b) y z w
  rwa [subst_up3_beta] at h₂

theorem steps_limArg (g z s l n : F.Tm) :
    Steps f (.app (limArg g z s l) n) (app3 (.app g n) z s l) := by
  have h := Steps.beta (f := f)
    (app3 (.app (ren Nat.succ g) (.var 0)) (ren Nat.succ z) (ren Nat.succ s) (ren Nat.succ l)) n
  have e : subst (cons n var)
      (app3 (.app (ren Nat.succ g) (.var 0)) (ren Nat.succ z) (ren Nat.succ s) (ren Nat.succ l)) =
      app3 (.app g n) z s l := by
    show app3 (.app (subst _ (ren Nat.succ g)) n) (subst _ (ren Nat.succ z))
      (subst _ (ren Nat.succ s)) (subst _ (ren Nat.succ l)) = _
    simp only [subst_ren]
    rw [show (cons n var ∘ Nat.succ : Nat → F.Tm) = var from rfl, subst_var, subst_var, subst_var,
      subst_var]
  rw [e] at h
  exact h

/-! ## The relation -/

/-- `RelT u τ`: the term `u` represents the tree `τ`. -/
def RelT (f : Nat → Nat) (u : F.Tm) : Eps.BTree → Prop
  | .zero => ∀ z s l, Steps f (app3 u z s l) z
  | .succ σ => ∃ u', RelT f u' σ ∧ ∀ z s l, Steps f (app3 u z s l) (.app s (app3 u' z s l))
  | .lim h => ∃ g, (∀ n m, Steps f n (num m) → RelT f (.app g n) (h m)) ∧
      ∀ z s l, Steps f (app3 u z s l) (.app l (limArg g z s l))

theorem app3_steps {u u' : F.Tm} (h : Steps f u u') (z s l : F.Tm) :
    Steps f (app3 u z s l) (app3 u' z s l) :=
  Steps.appL l (Steps.appL s (Steps.appL z h))

theorem RelT.expand {u u' : F.Tm} (h : Steps f u u') : ∀ {τ : Eps.BTree}, RelT f u' τ → RelT f u τ
  | .zero, hr => fun z s l => (app3_steps h z s l).trans (hr z s l)
  | .succ _, ⟨u'', hr, hs⟩ => ⟨u'', hr, fun z s l => (app3_steps h z s l).trans (hs z s l)⟩
  | .lim _, ⟨g, hg, hs⟩ => ⟨g, hg, fun z s l => (app3_steps h z s l).trans (hs z s l)⟩

/-! ## Level trees: five-argument iterators -/

def app4 (u z s l p : F.Tm) : F.Tm := .app (app3 u z s l) p

def ozeroTm : F.Tm := .lam (.lam (.lam (.lam (.var 3))))

def osuccTm : F.Tm :=
  .lam (.lam (.lam (.lam (.lam (.app (.var 2) (app4 (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)))))))

def olimTm : F.Tm :=
  .lam (.lam (.lam (.lam (.lam (.app (.var 1)
    (.lam (app4 (.app (.var 5) (.var 0)) (.var 4) (.var 3) (.var 2) (.var 1))))))))

/-- `sup = λμ g z s l p. p μ (λx. g x z s l p)`. -/
def osupTm : F.Tm :=
  .lam (.lam (.lam (.lam (.lam (.lam (.app (.app (.var 0) (.var 5))
    (.lam (app4 (.app (.var 5) (.var 0)) (.var 4) (.var 3) (.var 2) (.var 1)))))))))

def ofoldTm : F.Tm :=
  .lam (.lam (.lam (.lam (.lam (app4 (.var 0) (.var 4) (.var 3) (.var 2) (.var 1))))))

/-- The function `λx. g x z s l p`, shifted under its binder. -/
def limArg4 (g z s l p : F.Tm) : F.Tm :=
  .lam (app4 (.app (ren Nat.succ g) (.var 0)) (ren Nat.succ z) (ren Nat.succ s) (ren Nat.succ l)
    (ren Nat.succ p))

theorem subst_up4_beta (b x y z w v : F.Tm) :
    subst (cons v (cons w (cons z (cons y var)))) (subst (up (up (up (up (cons x var))))) b) =
      subst (cons v (cons w (cons z (cons y (cons x var))))) b := by
  rw [subst_subst]
  congr 1
  funext n
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => show subst _ (ren Nat.succ (ren Nat.succ (ren Nat.succ (ren Nat.succ x)))) = x
         rw [ren_ren, ren_ren, ren_ren, subst_ren]; exact subst_var x
  | n + 5 => rfl

theorem steps_beta5 (b x y z w v : F.Tm) :
    Steps f (.app (.app (.app (.app (.app (.lam (.lam (.lam (.lam (.lam b))))) x) y) z) w) v)
      (subst (cons v (cons w (cons z (cons y (cons x var))))) b) := by
  have h₁ : Steps f (.app (.app (.app (.app (.app (.lam (.lam (.lam (.lam (.lam b))))) x) y) z) w) v)
      (.app (.app (.app (.app (.lam (.lam (.lam (.lam (subst (up (up (up (up (cons x var))))) b)))))
        y) z) w) v) :=
    Steps.appL v (Steps.appL w (Steps.appL z (Steps.appL y (Steps.beta _ _))))
  refine h₁.trans ?_
  have h₂ := steps_beta4 (f := f) (subst (up (up (up (up (cons x var))))) b) y z w v
  rwa [subst_up4_beta] at h₂

theorem subst_up5_beta (b x y z w v u : F.Tm) :
    subst (cons u (cons v (cons w (cons z (cons y var)))))
      (subst (up (up (up (up (up (cons x var)))))) b) =
      subst (cons u (cons v (cons w (cons z (cons y (cons x var)))))) b := by
  rw [subst_subst]
  congr 1
  funext n
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => show subst _ (ren Nat.succ (ren Nat.succ (ren Nat.succ (ren Nat.succ (ren Nat.succ x))))) = x
         rw [ren_ren, ren_ren, ren_ren, ren_ren, subst_ren]; exact subst_var x
  | n + 6 => rfl

theorem steps_beta6 (b x y z w v u : F.Tm) :
    Steps f (.app (.app (.app (.app (.app (.app (.lam (.lam (.lam (.lam (.lam (.lam b)))))) x) y) z)
      w) v) u)
      (subst (cons u (cons v (cons w (cons z (cons y (cons x var)))))) b) := by
  have h₁ : Steps f (.app (.app (.app (.app (.app (.app (.lam (.lam (.lam (.lam (.lam (.lam b)))))) x)
      y) z) w) v) u)
      (.app (.app (.app (.app (.app (.lam (.lam (.lam (.lam (.lam
        (subst (up (up (up (up (up (cons x var)))))) b)))))) y) z) w) v) u) :=
    Steps.appL u (Steps.appL v (Steps.appL w (Steps.appL z (Steps.appL y (Steps.beta _ _)))))
  refine h₁.trans ?_
  have h₂ := steps_beta5 (f := f) (subst (up (up (up (up (up (cons x var)))))) b) y z w v u
  rwa [subst_up5_beta] at h₂

theorem steps_limArg4 (g z s l p n : F.Tm) :
    Steps f (.app (limArg4 g z s l p) n) (app4 (.app g n) z s l p) := by
  have h := Steps.beta (f := f)
    (app4 (.app (ren Nat.succ g) (.var 0)) (ren Nat.succ z) (ren Nat.succ s) (ren Nat.succ l)
      (ren Nat.succ p)) n
  have e : subst (cons n var)
      (app4 (.app (ren Nat.succ g) (.var 0)) (ren Nat.succ z) (ren Nat.succ s) (ren Nat.succ l)
        (ren Nat.succ p)) = app4 (.app g n) z s l p := by
    show app4 (.app (subst _ (ren Nat.succ g)) n) (subst _ (ren Nat.succ z))
      (subst _ (ren Nat.succ s)) (subst _ (ren Nat.succ l)) (subst _ (ren Nat.succ p)) = _
    simp only [subst_ren]
    rw [show (cons n var ∘ Nat.succ : Nat → F.Tm) = var from rfl, subst_var, subst_var, subst_var,
      subst_var, subst_var]
  rw [e] at h
  exact h

/-- `RelLS R u a`: the term `u` represents the level tree `a`, whose branches
are represented according to `R`. -/
def RelLS (f : Nat → Nat) {A : Type} (R : F.Tm → A → Prop) (u : F.Tm) : Buch.Tr A → Prop
  | .zero => ∀ z s l p, Steps f (app4 u z s l p) z
  | .succ σ => ∃ u', RelLS f R u' σ ∧ ∀ z s l p, Steps f (app4 u z s l p) (.app s (app4 u' z s l p))
  | .lim h => ∃ g, (∀ n m, Steps f n (num m) → RelLS f R (.app g n) (h m)) ∧
      ∀ z s l p, Steps f (app4 u z s l p) (.app l (limArg4 g z s l p))
  | .sup μ h => ∃ t g, Steps f t (num μ) ∧ (∀ w x, R w x → RelLS f R (.app g w) (h x)) ∧
      ∀ z s l p, Steps f (app4 u z s l p) (.app (.app p t) (limArg4 g z s l p))

/-- The relation for the branches of level `m`. -/
def RelP (f : Nat → Nat) : (m : Nat) → F.Tm → Buch.P m → Prop
  | 0 => fun u n => Steps f u (num n)
  | m + 1 => RelLS f (RelP f m)

theorem app4_steps {u u' : F.Tm} (h : Steps f u u') (z s l p : F.Tm) :
    Steps f (app4 u z s l p) (app4 u' z s l p) :=
  Steps.appL p (app3_steps h z s l)

theorem RelLS.expand {A : Type} {R : F.Tm → A → Prop} {u u' : F.Tm} (h : Steps f u u') :
    ∀ {a : Buch.Tr A}, RelLS f R u' a → RelLS f R u a
  | .zero, hr => fun z s l p => (app4_steps h z s l p).trans (hr z s l p)
  | .succ _, ⟨u'', hr, hs⟩ => ⟨u'', hr, fun z s l p => (app4_steps h z s l p).trans (hs z s l p)⟩
  | .lim _, ⟨g, hg, hs⟩ => ⟨g, hg, fun z s l p => (app4_steps h z s l p).trans (hs z s l p)⟩
  | .sup _ _, ⟨t, g, ht, hg, hs⟩ =>
      ⟨t, g, ht, hg, fun z s l p => (app4_steps h z s l p).trans (hs z s l p)⟩

def Rel (f : Nat → Nat) : (σ : Ty) → F.Tm → den σ → Prop
  | .nat, u, n => Steps f u (num n)
  | .tree, u, τ => RelT f u τ
  | .lev m, u, a => RelLS f (RelP f m) u a
  | .arr a b, u, g => ∀ w x, Rel f a w x → Rel f b (.app u w) (g x)

theorem Rel.expand : ∀ {σ : Ty} {u u' : F.Tm} {x : den σ}, Steps f u u' → Rel f σ u' x → Rel f σ u x
  | .nat, _, _, _, h, hr => h.trans hr
  | .tree, _, _, _, h, hr => RelT.expand h hr
  | .lev _, _, _, _, h, hr => RelLS.expand h hr
  | .arr _ _, _, _, _, h, hr => fun w y hw => Rel.expand (Steps.appL w h) (hr w y hw)

/-! ## Trees -/

theorem rel_foldT {r : Ty} {z s l : F.Tm} {zv : den r} {sv : den r → den r}
    {lv : (Nat → den r) → den r} (hz : Rel f r z zv) (hs : Rel f (.arr r r) s sv)
    (hl : Rel f (.arr (.arr .nat r) r) l lv) :
    ∀ (τ : Eps.BTree) (u : F.Tm), RelT f u τ → Rel f r (app3 u z s l) (fold zv sv lv τ)
  | .zero, _, hu => Rel.expand (hu z s l) hz
  | .succ σ, _, ⟨u', hu', hsu⟩ => Rel.expand (hsu z s l) (hs _ _ (rel_foldT hz hs hl σ u' hu'))
  | .lim h, _, ⟨g, hg, hsu⟩ =>
      Rel.expand (hsu z s l) (hl _ _ fun n m hn =>
        Rel.expand (steps_limArg g z s l n) (rel_foldT hz hs hl (h m) _ (hg n m hn)))

theorem rel_tzero : Rel f .tree tzeroTm Eps.BTree.zero := fun z s l => steps_beta3 _ z s l

theorem rel_tsucc : Rel f (.arr .tree .tree) tsuccTm Eps.BTree.succ := fun w σ hw =>
  ⟨w, hw, fun z s l => by
    have h := steps_beta4 (f := f) (.app (.var 1) (app3 (.var 3) (.var 2) (.var 1) (.var 0))) w z s l
    exact h⟩

theorem rel_tlim : Rel f (.arr (.arr .nat .tree) .tree) tlimTm Eps.BTree.lim := fun g h hg =>
  ⟨g, fun n m hn => hg n m hn, fun z s l => by
    have h := steps_beta4 (f := f)
      (.app (.var 0) (.lam (app3 (.app (.var 4) (.var 0)) (.var 3) (.var 2) (.var 1)))) g z s l
    exact h⟩

theorem rel_fold (r : Ty) :
    Rel f (.arr r (.arr (.arr r r) (.arr (.arr (.arr .nat r) r) (.arr .tree r)))) foldTm fold :=
  fun z zv hz s sv hs l lv hl t τ ht => by
    have h := steps_beta4 (f := f) (app3 (.var 0) (.var 3) (.var 2) (.var 1)) z s l t
    exact Rel.expand h (rel_foldT hz hs hl τ t ht)

/-! ## `Ω`-trees -/

theorem rel_lfoldL {r : Ty} {A : Type} {R : F.Tm → A → Prop} {z s l p : F.Tm} {zv : den r}
    {sv : den r → den r} {lv : (Nat → den r) → den r} {pv : Nat → (A → den r) → den r}
    (hz : Rel f r z zv) (hs : Rel f (.arr r r) s sv) (hl : Rel f (.arr (.arr .nat r) r) l lv)
    (hp : ∀ t μ, Steps f t (num μ) → ∀ g gv, (∀ w x, R w x → Rel f r (.app g w) (gv x)) →
      Rel f r (.app (.app p t) g) (pv μ gv)) :
    ∀ (a : Buch.Tr A) (u : F.Tm), RelLS f R u a → Rel f r (app4 u z s l p) (lfold zv sv lv pv a)
  | .zero, _, hu => Rel.expand (hu z s l p) hz
  | .succ σ, _, ⟨u', hu', hsu⟩ =>
      Rel.expand (hsu z s l p) (hs _ _ (rel_lfoldL hz hs hl hp σ u' hu'))
  | .lim h, _, ⟨g, hg, hsu⟩ =>
      Rel.expand (hsu z s l p) (hl _ _ fun n m hn =>
        Rel.expand (steps_limArg4 g z s l p n) (rel_lfoldL hz hs hl hp (h m) _ (hg n m hn)))
  | .sup μ h, _, ⟨t, g, ht, hg, hsu⟩ =>
      Rel.expand (hsu z s l p) (hp t μ ht _ _ fun w x hw =>
        Rel.expand (steps_limArg4 g z s l p w) (rel_lfoldL hz hs hl hp (h x) _ (hg w x hw)))

theorem rel_lzero (m : Nat) : Rel f (.lev m) ozeroTm Buch.Tr.zero :=
  fun z s l p => steps_beta4 _ z s l p

theorem rel_lsucc (m : Nat) : Rel f (.arr (.lev m) (.lev m)) osuccTm Buch.Tr.succ := fun w σ hw =>
  ⟨w, hw, fun z s l p => by
    have h := steps_beta5 (f := f)
      (.app (.var 2) (app4 (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))) w z s l p
    exact h⟩

theorem rel_llim (m : Nat) : Rel f (.arr (.arr .nat (.lev m)) (.lev m)) olimTm Buch.Tr.lim :=
  fun g h hg =>
  ⟨g, fun n m hn => hg n m hn, fun z s l p => by
    have h := steps_beta5 (f := f)
      (.app (.var 1) (.lam (app4 (.app (.var 5) (.var 0)) (.var 4) (.var 3) (.var 2) (.var 1))))
      g z s l p
    exact h⟩

theorem rel_lsup0 :
    Rel f (.arr .nat (.arr (.arr .nat (.lev 0)) (.lev 0))) osupTm Buch.Tr.sup :=
  fun t μ ht g h hg =>
  ⟨t, g, ht, fun w x hw => hg w x hw, fun z s l p => by
    have h := steps_beta6 (f := f)
      (.app (.app (.var 0) (.var 5))
        (.lam (app4 (.app (.var 5) (.var 0)) (.var 4) (.var 3) (.var 2) (.var 1)))) t g z s l p
    exact h⟩

theorem rel_lsup (m : Nat) :
    Rel f (.arr .nat (.arr (.arr (.lev m) (.lev (m + 1))) (.lev (m + 1)))) osupTm Buch.Tr.sup :=
  fun t μ ht g h hg =>
  ⟨t, g, ht, fun w x hw => hg w x hw, fun z s l p => by
    have h := steps_beta6 (f := f)
      (.app (.app (.var 0) (.var 5))
        (.lam (app4 (.app (.var 5) (.var 0)) (.var 4) (.var 3) (.var 2) (.var 1)))) t g z s l p
    exact h⟩

theorem rel_lfold0 (r : Ty) :
    Rel f (.arr r (.arr (.arr r r) (.arr (.arr (.arr .nat r) r)
      (.arr (.arr .nat (.arr (.arr .nat r) r)) (.arr (.lev 0) r))))) ofoldTm lfold :=
  fun z zv hz s sv hs l lv hl p pv hp t a ht => by
    have h := steps_beta5 (f := f) (app4 (.var 0) (.var 4) (.var 3) (.var 2) (.var 1)) z s l p t
    exact Rel.expand h (rel_lfoldL (R := RelP f 0) hz hs hl
      (fun t μ ht g gv hg => hp t μ ht g gv hg) a t ht)

theorem rel_lfoldS (m : Nat) (r : Ty) :
    Rel f (.arr r (.arr (.arr r r) (.arr (.arr (.arr .nat r) r)
      (.arr (.arr .nat (.arr (.arr (.lev m) r) r)) (.arr (.lev (m + 1)) r))))) ofoldTm lfold :=
  fun z zv hz s sv hs l lv hl p pv hp t a ht => by
    have h := steps_beta5 (f := f) (app4 (.var 0) (.var 4) (.var 3) (.var 2) (.var 1)) z s l p t
    exact Rel.expand h (rel_lfoldL (R := RelP f (m + 1)) hz hs hl
      (fun t μ ht g gv hg => hp t μ ht g gv hg) a t ht)

/-! ## Numbers -/

theorem rel_succ : Rel f (.arr .nat .nat) succTm Nat.succ :=
  fun w n hw => BusyLean.Indep.Emb.rel_succ (f := f) w n hw

theorem rel_iter {r : Ty} {g : F.Tm} {z : F.Tm} {g' : Nat → den r → den r} {z' : den r}
    (hz : Rel f r z z') (hg : Rel f (.arr .nat (.arr r r)) g g') :
    ∀ j, ∃ x y, Steps f (iterTm (.app stepTm g) (.app (.app pairTm (num 0)) z) j)
      (.app (.app pairTm x) y) ∧ Rel f .nat x j ∧ Rel f r y (recursion z' g' j)
  | 0 => ⟨num 0, z, Steps.refl _, Steps.refl _, hz⟩
  | j + 1 => by
      obtain ⟨x, y, hs, hx, hy⟩ := rel_iter hz hg j
      refine ⟨_, _, (Steps.appR _ hs).trans (steps_step g x y), ?_, ?_⟩
      · exact rel_succ _ j (Rel.expand (steps_fst x y) hx)
      · exact hg _ j (Rel.expand (steps_fst x y) hx) _ _ (Rel.expand (steps_snd x y) hy)

theorem rel_rec (r : Ty) :
    Rel f (.arr r (.arr (.arr .nat (.arr r r)) (.arr .nat r))) recTm recursion := by
  intro z z' hz g g' hg w n hw
  have h₁ : Steps f (.app (.app (.app recTm z) g) w)
      (sndTm (.app (.app w (.app stepTm g)) (.app (.app pairTm (num 0)) z))) := by
    have h := steps_beta3 (f := f)
      (sndTm (.app (.app (.var 0) (.app stepTm (.var 1))) (.app (.app pairTm (num 0)) (.var 2)))) z g w
    have e : subst (cons w (cons g (cons z var)))
        (sndTm (.app (.app (.var 0) (.app stepTm (.var 1))) (.app (.app pairTm (num 0)) (.var 2)))) =
        sndTm (.app (.app w (.app (subst (cons w (cons g (cons z var))) stepTm) g))
          (.app (.app (subst (cons w (cons g (cons z var))) pairTm)
            (subst (cons w (cons g (cons z var))) (num 0))) z)) := rfl
    have hs : ∀ σ : Nat → F.Tm, subst σ stepTm = stepTm := fun σ => rfl
    have hp : ∀ σ : Nat → F.Tm, subst σ pairTm = pairTm := fun σ => rfl
    rw [e, hs, hp, subst_num] at h
    exact h
  refine Rel.expand h₁ ?_
  obtain ⟨x, y, hs, _, hy⟩ := rel_iter hz hg n
  refine Rel.expand (Steps.appL _ ((Steps.appL _ (Steps.appL _ hw)).trans
    (steps_num_app n _ _))) ?_
  exact Rel.expand ((Steps.appL _ hs).trans (steps_snd x y)) hy

/-! ## The translation and the fundamental lemma -/

def utrT : {Γ : List Ty} → {σ : Ty} → Tm Γ σ → F.Tm
  | _, _, .var v => .var v.idx
  | _, _, .lam b => .lam (utrT b)
  | _, _, .app s u => .app (utrT s) (utrT u)
  | _, _, .zero => num 0
  | _, _, .succ => succTm
  | _, _, .nrec _ => recTm
  | _, _, .tzero => tzeroTm
  | _, _, .tsucc => tsuccTm
  | _, _, .tlim => tlimTm
  | _, _, .fold _ => foldTm
  | _, _, .lzero _ => ozeroTm
  | _, _, .lsucc _ => osuccTm
  | _, _, .llim _ => olimTm
  | _, _, .lsup _ => osupTm
  | _, _, .lsup0 => osupTm
  | _, _, .lfold0 _ => ofoldTm
  | _, _, .lfoldS _ _ => ofoldTm

def EnvRel (f : Nat → Nat) {Γ : List Ty} (σs : Nat → F.Tm) (ρ : Env Γ) : Prop :=
  ∀ τ (v : Var Γ τ), Rel f τ (σs v.idx) (ρ τ v)

theorem EnvRel.cons {Γ : List Ty} {σs : Nat → F.Tm} {ρ : Env Γ} (h : EnvRel f σs ρ) {a : Ty}
    {w : F.Tm} {x : den a} (hw : Rel f a w x) : EnvRel f (cons w σs) (Env.cons x ρ) := fun τ v => by
  cases v with
  | here => exact hw
  | there v => exact h τ v

theorem rel_utrT : ∀ {Γ : List Ty} {σ : Ty} (t : Tm Γ σ) {σs : Nat → F.Tm} {ρ : Env Γ},
    EnvRel f σs ρ → Rel f σ (subst σs (utrT t)) (eval t ρ)
  | _, _, .var v, _, _, h => h _ v
  | _, _, .lam b, σs, ρ, h => fun w x hw => by
      have h₁ := Steps.beta (f := f) (subst (up σs) (utrT b)) w
      rw [subst_beta] at h₁
      exact Rel.expand h₁ (rel_utrT b (h.cons hw))
  | _, _, .app s u, _, _, h => rel_utrT s h _ _ (rel_utrT u h)
  | _, _, .zero, _, _, _ => by
      show Steps f (subst _ (num 0)) (num 0)
      rw [subst_num]; exact Steps.refl _
  | _, _, .succ, _, _, _ => rel_succ
  | _, _, .nrec r, _, _, _ => rel_rec r
  | _, _, .tzero, _, _, _ => rel_tzero
  | _, _, .tsucc, _, _, _ => rel_tsucc
  | _, _, .tlim, _, _, _ => rel_tlim
  | _, _, .fold r, _, _, _ => rel_fold r
  | _, _, .lzero m, _, _, _ => rel_lzero m
  | _, _, .lsucc m, _, _, _ => rel_lsucc m
  | _, _, .llim m, _, _, _ => rel_llim m
  | _, _, .lsup m, _, _, _ => rel_lsup m
  | _, _, .lsup0, _, _, _ => rel_lsup0
  | _, _, .lfold0 r, _, _, _ => rel_lfold0 r
  | _, _, .lfoldS m r, _, _, _ => rel_lfoldS m r

/-- A closed program of type `nat` reduces to the numeral of its value. -/
theorem utrT_steps (t : Tm [] .nat) : Steps f (utrT t) (num (eval t env0)) := by
  have h := rel_utrT (f := f) t (σs := var) (ρ := env0) (fun _ v => nomatch v)
  rw [subst_var] at h
  exact h

end BusyLean.Indep.TT
