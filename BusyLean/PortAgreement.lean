import BusyLean.Contender5
import BigNumber.Proofs

/-!
# Agreement of P5's old-language port with the exact port

Proposal P5 (`BigNumber`, in `proposals/P5-w-reflection`) re-implements the old
STLC+NatRec language *inside* its larger W-language: it uses the W-language's
type codes, its W-aware casts and interpreter, and replaces the `maxBy` winner
selection with a plain maximum (`BigNumber.oldMaximum`). P5 asserts that this
equals Contender 5 but does not prove it.

This file proves the assertion for every depth:

  `largestSTLCNatRecNatOfDepth n = BigNumber.oldMaximum n`.

The proof relates the two interpreters with a logical relation (equality at
`nat`, pointwise preservation at arrows), so no function extensionality is
needed.
-/

namespace BusyLean.PortAgreement

open BusyLean

/-! ## Translation of types and terms -/

def trTy : C5.Ty → BigNumber.Ty
  | .nat => .nat
  | .arr a b => .arr (trTy a) (trTy b)

def trTerm : C5.Term → BigNumber.Term
  | .var x => .var x
  | .lam a b t => .lam (trTy a) (trTy b) (trTerm t)
  | .app t u => .app (trTerm t) (trTerm u)
  | .zero => .zero
  | .succ => .succ
  | .natRec r => .natrec (trTy r)

/-! ## The logical relation -/

/-- Values of corresponding types that behave identically. -/
def Rel : (a : C5.Ty) → BigNumber.den (trTy a) → C5.den a → Prop
  | .nat, x, y => x = y
  | .arr a b, f, g => ∀ x y, Rel a x y → Rel b (f x) (g y)

/-- A P5 value is related to an old value if it has the translated type and a
related payload. -/
def RelV (v : BigNumber.Value) (w : C5.Value) : Prop :=
  ∃ x, v = ⟨trTy w.1, x⟩ ∧ Rel w.1 x w.2

inductive EnvRel : List BigNumber.Value → List C5.Value → Prop where
  | nil : EnvRel [] []
  | cons {v w env e} : RelV v w → EnvRel env e → EnvRel (v :: env) (w :: e)

inductive OptRel : Option BigNumber.Value → Option C5.Value → Prop where
  | none : OptRel none none
  | some {v w} : RelV v w → OptRel (some v) (some w)

/-! ## Types and casts -/

theorem eqb_tr : ∀ a b : C5.Ty, BigNumber.eqb (trTy a) (trTy b) = C5.typeEqb a b
  | .nat, .nat => rfl
  | .nat, .arr _ _ => rfl
  | .arr _ _, .nat => rfl
  | .arr a b, .arr c d => by
      show (BigNumber.eqb (trTy a) (trTy c) && BigNumber.eqb (trTy b) (trTy d)) = _
      rw [eqb_tr a c, eqb_tr b d]
      rfl

theorem rel_error : ∀ a : C5.Ty, Rel a (BigNumber.defaultValue (trTy a)) (C5.error a)
  | .nat => rfl
  | .arr _ b => fun _ _ _ => rel_error b

theorem castPair_arr_true {a b c d : BigNumber.Ty}
    (h : (BigNumber.eqb a c && BigNumber.eqb b d) = true) :
    BigNumber.castPair (.arr a b) (.arr c d) =
      (fun f x => (BigNumber.castPair b d).1 (f ((BigNumber.castPair a c).2 x)),
       fun f x => (BigNumber.castPair b d).2 (f ((BigNumber.castPair a c).1 x))) := by
  rw [BigNumber.castPair, if_pos h]
  rfl

theorem castPair_arr_false {a b c d : BigNumber.Ty}
    (h : (BigNumber.eqb a c && BigNumber.eqb b d) = false) :
    BigNumber.castPair (.arr a b) (.arr c d) = BigNumber.badCast (.arr a b) (.arr c d) := by
  rw [BigNumber.castPair, ite_eq_right_iff.mpr (fun h' => absurd (h.symm.trans h') Bool.false_ne_true)]

theorem castImpl_arr_true {a b c d : C5.Ty} (h : (C5.typeEqb a c && C5.typeEqb b d) = true) :
    C5.castImpl (.arr a b) (.arr c d) =
      (fun f x => (C5.castImpl b d).1 (f ((C5.castImpl a c).2 x)),
       fun f x => (C5.castImpl b d).2 (f ((C5.castImpl a c).1 x))) := by
  rw [C5.castImpl, h]
  rfl

theorem castImpl_arr_false {a b c d : C5.Ty} (h : (C5.typeEqb a c && C5.typeEqb b d) = false) :
    C5.castImpl (.arr a b) (.arr c d) = C5.castError (.arr a b) (.arr c d) := by
  rw [C5.castImpl, h]

/-- Both directions of the casts preserve the relation. -/
theorem rel_cast : ∀ a b : C5.Ty,
    (∀ x y, Rel a x y →
      Rel b ((BigNumber.castPair (trTy a) (trTy b)).1 x) ((C5.castImpl a b).1 y)) ∧
    (∀ x y, Rel b x y →
      Rel a ((BigNumber.castPair (trTy a) (trTy b)).2 x) ((C5.castImpl a b).2 y))
  | .nat, .nat => ⟨fun _ _ h => h, fun _ _ h => h⟩
  | .nat, .arr c d => ⟨fun _ _ _ => rel_error (.arr c d), fun _ _ _ => rel_error .nat⟩
  | .arr a b, .nat => ⟨fun _ _ _ => rel_error .nat, fun _ _ _ => rel_error (.arr a b)⟩
  | .arr a b, .arr c d => by
      have hE : (BigNumber.eqb (trTy a) (trTy c) && BigNumber.eqb (trTy b) (trTy d)) =
          (C5.typeEqb a c && C5.typeEqb b d) := by rw [eqb_tr, eqb_tr]
      cases h : C5.typeEqb a c && C5.typeEqb b d with
      | true =>
          rw [h] at hE
          show (∀ x y, Rel (.arr a b) x y →
              Rel (.arr c d) ((BigNumber.castPair (.arr (trTy a) (trTy b))
                (.arr (trTy c) (trTy d))).1 x) ((C5.castImpl (.arr a b) (.arr c d)).1 y)) ∧
            (∀ x y, Rel (.arr c d) x y →
              Rel (.arr a b) ((BigNumber.castPair (.arr (trTy a) (trTy b))
                (.arr (trTy c) (trTy d))).2 x) ((C5.castImpl (.arr a b) (.arr c d)).2 y))
          rw [castPair_arr_true hE, castImpl_arr_true h]
          have hac := rel_cast a c
          have hbd := rel_cast b d
          exact ⟨fun f g hfg x y hxy => hbd.1 _ _ (hfg _ _ (hac.2 x y hxy)),
                 fun f g hfg x y hxy => hbd.2 _ _ (hfg _ _ (hac.1 x y hxy))⟩
      | false =>
          rw [h] at hE
          show (∀ x y, Rel (.arr a b) x y →
              Rel (.arr c d) ((BigNumber.castPair (.arr (trTy a) (trTy b))
                (.arr (trTy c) (trTy d))).1 x) ((C5.castImpl (.arr a b) (.arr c d)).1 y)) ∧
            (∀ x y, Rel (.arr c d) x y →
              Rel (.arr a b) ((BigNumber.castPair (.arr (trTy a) (trTy b))
                (.arr (trTy c) (trTy d))).2 x) ((C5.castImpl (.arr a b) (.arr c d)).2 y))
          rw [castPair_arr_false hE, castImpl_arr_false h]
          exact ⟨fun _ _ _ => rel_error (.arr c d), fun _ _ _ => rel_error (.arr a b)⟩

/-! ## Environments -/

theorem EnvRel.length_eq {env e} (h : EnvRel env e) : env.length = e.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem EnvRel.nth {env e} (h : EnvRel env e) :
    ∀ n, OptRel (BigNumber.nth? env n) (C5.nthError e n) := by
  induction h with
  | nil => intro n; exact OptRel.none
  | cons hvw _ ih =>
      intro n
      cases n with
      | zero => exact OptRel.some hvw
      | succ n => exact ih n

theorem EnvRel.lookup {env e} (h : EnvRel env e) (n : Nat) :
    OptRel (BigNumber.lookup env n) (C5.lookup e n) := by
  have hc : C5.lookup e n = (match Nat.ble e.length n with
      | true => none
      | false => C5.nthError e (e.length - (n + 1))) := rfl
  rw [hc]
  unfold BigNumber.lookup
  rw [h.length_eq]
  cases hb : Nat.ble e.length n with
  | true =>
      rw [if_pos (Nat.le_of_ble_eq_true hb)]
      exact OptRel.none
  | false =>
      have hn : ¬ e.length ≤ n := fun hle => by
        rw [Nat.ble_eq_true_of_le hle] at hb
        exact Bool.noConfusion hb
      rw [if_neg hn]
      exact h.nth _

/-! ## The fundamental lemma -/

theorem rel_natRec (r : C5.Ty) (z : BigNumber.den (trTy r)) (z' : C5.den r) (hz : Rel r z z')
    (s : Nat → BigNumber.den (trTy r) → BigNumber.den (trTy r))
    (s' : Nat → C5.den r → C5.den r)
    (hs : ∀ i i', i = i' → ∀ x y, Rel r x y → Rel r (s i x) (s' i' y)) :
    ∀ n, Rel r (Nat.rec (motive := fun _ => BigNumber.den (trTy r)) z
      (fun i acc => s i acc) n) (C5.recursion z' s' n)
  | 0 => hz
  | n + 1 => hs n n rfl _ _ (rel_natRec r z z' hz s s' hs n)

theorem interp_rel : ∀ (t : C5.Term) {env : List BigNumber.Value} {e : List C5.Value},
    EnvRel env e → RelV (BigNumber.interpret env (trTerm t)) (C5.interp e t)
  | .var x, env, e, henv => by
      have h := henv.lookup x
      show RelV (match BigNumber.lookup env x with
          | some v => v
          | none => ⟨.nat, (0 : Nat)⟩)
        (match C5.lookup e x with
          | some r => r
          | none => ⟨.nat, C5.error .nat⟩)
      generalize BigNumber.lookup env x = p at h ⊢
      generalize C5.lookup e x = q at h ⊢
      cases h with
      | none => exact ⟨(0 : Nat), rfl, rfl⟩
      | some hvw => exact hvw
  | .lam a b body, env, e, henv => by
      refine ⟨_, rfl, ?_⟩
      intro x y hxy
      obtain ⟨x0, hv, hr⟩ :=
        interp_rel body (EnvRel.cons (v := ⟨trTy a, x⟩) (w := ⟨a, y⟩) ⟨x, rfl, hxy⟩ henv)
      show Rel b (BigNumber.castValue (trTy b)
          (BigNumber.interpret (⟨trTy a, x⟩ :: env) (trTerm body)).2)
        (C5.cast b (C5.interp (⟨a, y⟩ :: e) body).2)
      rw [hv]
      exact (rel_cast _ b).1 _ _ hr
  | .app t u, env, e, henv => by
      have h1 := interp_rel t henv
      have h2 := interp_rel u henv
      show RelV
        (match BigNumber.interpret env (trTerm t) with
          | ⟨.nat, _⟩ => ⟨.nat, (0 : Nat)⟩
          | ⟨.wt _, _⟩ => ⟨.nat, (0 : Nat)⟩
          | ⟨.arr a b, f⟩ =>
              ⟨b, f (BigNumber.castValue a (BigNumber.interpret env (trTerm u)).2)⟩)
        (match C5.interp e t, C5.interp e u with
          | ⟨.nat, _⟩, _ => ⟨.nat, C5.error .nat⟩
          | ⟨.arr a _, r₁⟩, ⟨_, r₂⟩ => ⟨_, r₁ (C5.cast a r₂)⟩)
      generalize C5.interp e t = W1 at h1 ⊢
      generalize C5.interp e u = W2 at h2 ⊢
      obtain ⟨R1, y1⟩ := W1
      obtain ⟨R2, y2⟩ := W2
      obtain ⟨x1, hv1, hr1⟩ := h1
      obtain ⟨x2, hv2, hr2⟩ := h2
      rw [hv1, hv2]
      cases R1 with
      | nat => exact ⟨(0 : Nat), rfl, rfl⟩
      | arr A B => exact ⟨_, rfl, hr1 _ _ ((rel_cast R2 A).1 _ _ hr2)⟩
  | .zero, _, _, _ => ⟨(0 : Nat), rfl, rfl⟩
  | .succ, _, _, _ => ⟨Nat.succ, rfl, fun x y (h : x = y) => congrArg Nat.succ h⟩
  | .natRec r, _, _, _ =>
      ⟨_, rfl, fun z z' hz s s' hs n n' (hn : n = n') => by
        subst hn
        exact rel_natRec r z z' hz s s' (fun i i' hi x y hxy => by
          subst hi
          exact hs i i rfl x y hxy) n⟩

theorem evaluate_trTerm (t : C5.Term) : BigNumber.evaluate (trTerm t) = C5.eval t := by
  have h := interp_rel t EnvRel.nil
  unfold BigNumber.evaluate C5.eval
  generalize C5.interp [] t = W at h ⊢
  obtain ⟨R, y⟩ := W
  obtain ⟨x, hv, hr⟩ := h
  rw [hv]
  cases R with
  | nat => exact hr
  | arr _ _ => rfl

/-! ## Enumerations -/

theorem cross_map {α β γ δ : Type} (f : α → γ) (g : β → δ) :
    ∀ (xs : List α) (ys : List β),
      BigNumber.cross (xs.map f) (ys.map g) =
        (C5.listProd xs ys).map (fun p => (f p.1, g p.2))
  | [], _ => rfl
  | x :: xs, ys => by
      show (ys.map g).map (fun y => (f x, y)) ++ BigNumber.cross (xs.map f) (ys.map g) = _
      rw [cross_map f g xs ys]
      simp only [C5.listProd, List.map_append, List.map_map]
      rfl

theorem natsUpTo_eq : ∀ n, BigNumber.natsUpTo n = C5.natsUpTo n
  | 0 => rfl
  | n + 1 => congrArg (n :: ·) (natsUpTo_eq n)

theorem oldTypes_eq : ∀ n, BigNumber.oldTypes n = (C5.typesUpTo n).map trTy
  | 0 => rfl
  | n + 1 => by
      show BigNumber.Ty.nat :: (BigNumber.cross (BigNumber.oldTypes n)
          (BigNumber.oldTypes n)).map (fun p => .arr p.1 p.2) =
        (C5.Ty.nat :: (C5.listProd (C5.typesUpTo n) (C5.typesUpTo n)).map
          (fun p => C5.Ty.arr p.1 p.2)).map trTy
      rw [oldTypes_eq n, cross_map]
      simp only [List.map_cons, List.map_map]
      rfl

theorem oldTerms_eq : ∀ n, BigNumber.oldTerms n = (C5.termsUpTo n).map trTerm
  | 0 => rfl
  | n + 1 => by
      show (BigNumber.natsUpTo n).map BigNumber.Term.var ++
          (BigNumber.cross (BigNumber.cross (BigNumber.oldTypes n) (BigNumber.oldTypes n))
            (BigNumber.oldTerms n)).map (fun p => .lam p.1.1 p.1.2 p.2) ++
          (BigNumber.cross (BigNumber.oldTerms n) (BigNumber.oldTerms n)).map
            (fun p => .app p.1 p.2) ++
          [.zero] ++ [.succ] ++ (BigNumber.oldTypes n).map BigNumber.Term.natrec =
        ((C5.natsUpTo n).map C5.Term.var ++
          ((C5.listProd (C5.listProd (C5.typesUpTo n) (C5.typesUpTo n)) (C5.termsUpTo n)).map
              (fun p => C5.Term.lam p.1.1 p.1.2 p.2) ++
          ((C5.listProd (C5.termsUpTo n) (C5.termsUpTo n)).map
              (fun p => C5.Term.app p.1 p.2) ++
          ([C5.Term.zero] ++ ([C5.Term.succ] ++ (C5.typesUpTo n).map C5.Term.natRec))))).map
          trTerm
      rw [natsUpTo_eq, oldTypes_eq, oldTerms_eq n, cross_map, cross_map, cross_map]
      simp only [List.map_append, List.map_map, List.append_assoc, List.map_cons,
        List.map_nil, List.cons_append, List.nil_append]
      rfl

/-! ## Maxima -/

theorem maxN_zero_right : ∀ a, BigNumber.maxN a 0 = a
  | 0 => rfl
  | _ + 1 => rfl

theorem maxN_eq_right : ∀ {a b : Nat}, a ≤ b → BigNumber.maxN a b = b
  | 0, _, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | a + 1, b + 1, h => congrArg Nat.succ (maxN_eq_right (Nat.le_of_succ_le_succ h))

theorem maxN_eq_left : ∀ {a b : Nat}, b ≤ a → BigNumber.maxN a b = a
  | _, 0, _ => maxN_zero_right _
  | 0, _ + 1, h => absurd h (Nat.not_succ_le_zero _)
  | a + 1, b + 1, h => congrArg Nat.succ (maxN_eq_left (Nat.le_of_succ_le_succ h))

theorem maxN_le {a b c : Nat} (ha : a ≤ c) (hb : b ≤ c) : BigNumber.maxN a b ≤ c := by
  cases Nat.le_total a b with
  | inl h => rw [maxN_eq_right h]; exact hb
  | inr h => rw [maxN_eq_left h]; exact ha

/-- Absorbing a smaller middle argument. -/
theorem maxN_absorb {a c m : Nat} (hc : c ≤ a) :
    BigNumber.maxN a (BigNumber.maxN c m) = BigNumber.maxN a m := by
  cases Nat.le_total m a with
  | inl hm =>
      rw [maxN_eq_left hm, maxN_eq_left (maxN_le hc hm)]
  | inr hm =>
      rw [maxN_eq_right hm, maxN_eq_right (Nat.le_trans hc hm), maxN_eq_right hm]

/-- `maxBy`, started from `(f b, b)`, selects an element attaining the maximum. -/
theorem maxBy_spec {α : Type} (f : α → Nat) :
    ∀ (l : List α) (b : α),
      f (C5.maxBy f (f b) b l) = BigNumber.maxN (f b) (BigNumber.maximum f l)
  | [], b => (maxN_zero_right (f b)).symm
  | h :: t, b => by
      show f (match Nat.blt (f b) (f h) with
          | true => C5.maxBy f (f h) h t
          | false => C5.maxBy f (f b) b t) =
        BigNumber.maxN (f b) (BigNumber.maxN (f h) (BigNumber.maximum f t))
      cases hlt : Nat.blt (f b) (f h) with
      | true =>
          have hbh : f b + 1 ≤ f h := Nat.le_of_ble_eq_true hlt
          show f (C5.maxBy f (f h) h t) = _
          rw [maxBy_spec f t h]
          exact (maxN_eq_right (Nat.le_trans (Nat.le_of_succ_le hbh)
            (BigNumber.le_maxN_left _ _))).symm
      | false =>
          have hhb : f h ≤ f b := Nat.le_of_not_lt fun hlt' => by
            rw [show Nat.blt (f b) (f h) = true from Nat.ble_eq_true_of_le hlt'] at hlt
            exact Bool.noConfusion hlt
          show f (C5.maxBy f (f b) b t) = _
          rw [maxBy_spec f t b]
          exact (maxN_absorb hhb).symm

theorem maximum_map {α β : Type} (s : β → Nat) (g : α → β) :
    ∀ l : List α, BigNumber.maximum s (l.map g) = BigNumber.maximum (fun x => s (g x)) l
  | [] => rfl
  | x :: l => congrArg (BigNumber.maxN (s (g x))) (maximum_map s g l)

theorem maximum_congr {α : Type} {f g : α → Nat} (h : ∀ x, f x = g x) :
    ∀ l : List α, BigNumber.maximum f l = BigNumber.maximum g l
  | [] => rfl
  | x :: l => by
      show BigNumber.maxN (f x) _ = BigNumber.maxN (g x) _
      rw [h x, maximum_congr h l]

/-- **P5's numerical port is exact**: at every depth, the maximum computed by P5
equals the value of the Coq-style `maxBy` winner. -/
theorem largest_eq_oldMaximum (n : Nat) :
    C5.largestSTLCNatRecNatOfDepth n = BigNumber.oldMaximum n := by
  show C5.eval (C5.maxBy C5.eval (C5.eval .zero) .zero (C5.termsUpTo n)) = _
  rw [maxBy_spec C5.eval (C5.termsUpTo n) .zero]
  show BigNumber.maximum C5.eval (C5.termsUpTo n) =
    BigNumber.maximum BigNumber.evaluate (BigNumber.oldTerms n)
  rw [oldTerms_eq, maximum_map]
  exact maximum_congr (fun t => (evaluate_trTerm t).symm) _

/-- Contender 5 is exactly the number that P5 compares against. -/
theorem contender_5_eq_p5 : contender_5 = BigNumber.contender_5 :=
  largest_eq_oldMaximum 42

end BusyLean.PortAgreement
