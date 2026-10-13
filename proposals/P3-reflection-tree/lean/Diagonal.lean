import OracleFacts
import Enumeration

namespace Biggest

theorem exprDepth_pos (e : Expr) : 0 < exprDepth e := by
  cases e <;> exact Nat.zero_lt_succ _

theorem exprsUpTo_complete (n : Nat) (e : Expr) (h : exprDepth e ≤ n) :
    e ∈ exprsUpTo n := by
  induction n generalizing e with
  | zero => exact False.elim ((Nat.not_lt_of_ge h) (exprDepth_pos e))
  | succ n ih =>
      cases e with
      | quote t =>
          apply memAppendLeft
          exact memMap Expr.quote
            (termsUpTo_complete n t (Nat.le_of_succ_le_succ h))
      | var x =>
          apply memAppendRight
          apply memAppendLeft
          exact memMap Expr.var
            (natsUpTo_complete n x (Nat.le_of_succ_le_succ h))
      | lam a b body =>
          have hm : max (max (typeDepth a) (typeDepth b)) (exprDepth body) ≤ n :=
            Nat.le_of_succ_le_succ h
          have hab : max (typeDepth a) (typeDepth b) ≤ n :=
            Nat.le_trans (leMaxLeft _ _) hm
          have ha : a ∈ typesUpTo n :=
            typesUpTo_complete n a (Nat.le_trans (leMaxLeft _ _) hab)
          have hb : b ∈ typesUpTo n :=
            typesUpTo_complete n b (Nat.le_trans (leMaxRight _ _) hab)
          have hbody : body ∈ exprsUpTo n :=
            ih body (Nat.le_trans (leMaxRight _ _) hm)
          apply memAppendRight
          apply memAppendRight
          apply memAppendLeft
          exact memMap (fun ((a, b), body) => Expr.lam a b body)
            (mem_listProd (a, b) body _ _ (mem_listProd a b _ _ ha hb) hbody)
      | app f x =>
          have hm : max (exprDepth f) (exprDepth x) ≤ n :=
            Nat.le_of_succ_le_succ h
          have hf : f ∈ exprsUpTo n :=
            ih f (Nat.le_trans (leMaxLeft _ _) hm)
          have hx : x ∈ exprsUpTo n :=
            ih x (Nat.le_trans (leMaxRight _ _) hm)
          apply memAppendRight
          apply memAppendRight
          apply memAppendRight
          apply memAppendLeft
          exact memMap (fun (f, x) => Expr.app f x) (mem_listProd f x _ _ hf hx)
      | input =>
          apply memAppendRight
          apply memAppendRight
          apply memAppendRight
          apply memAppendRight
          apply memAppendLeft
          exact List.Mem.head _
      | oracle =>
          apply memAppendRight
          apply memAppendRight
          apply memAppendRight
          apply memAppendRight
          apply memAppendLeft
          exact List.Mem.tail Expr.input (List.Mem.head _)
      | zero =>
          apply memAppendRight
          apply memAppendRight
          apply memAppendRight
          apply memAppendRight
          apply memAppendLeft
          exact List.Mem.tail Expr.input (List.Mem.tail Expr.oracle (List.Mem.head _))
      | succ =>
          apply memAppendRight
          apply memAppendRight
          apply memAppendRight
          apply memAppendRight
          apply memAppendLeft
          exact List.Mem.tail Expr.input
            (List.Mem.tail Expr.oracle (List.Mem.tail Expr.zero (List.Mem.head _)))
      | natRec r =>
          have hr : r ∈ typesUpTo n :=
            typesUpTo_complete n r (Nat.le_of_succ_le_succ h)
          apply memAppendRight
          apply memAppendRight
          apply memAppendRight
          apply memAppendRight
          apply memAppendRight
          exact memMap Expr.natRec hr

theorem exprsUpTo_sound (n : Nat) (e : Expr) (h : e ∈ exprsUpTo n) :
    exprDepth e ≤ n := by
  induction n generalizing e with
  | zero => cases h
  | succ n ih =>
      cases ofMemAppend h with
      | inl hq =>
          obtain ⟨t, ht, heq⟩ := ofMemMap Expr.quote _ e hq
          cases heq
          exact Nat.succ_le_succ (termsUpTo_sound n t ht)
      | inr hrest =>
          cases ofMemAppend hrest with
          | inl hv =>
              obtain ⟨x, hx, heq⟩ := ofMemMap Expr.var _ e hv
              cases heq
              exact Nat.succ_le_succ (natsUpTo_sound n x hx)
          | inr hrest =>
              cases ofMemAppend hrest with
              | inl hl =>
                  obtain ⟨⟨⟨a, b⟩, body⟩, hp, heq⟩ :=
                    ofMemMap (fun ((a, b), body) => Expr.lam a b body) _ e hl
                  cases heq
                  have hp' := ofMemListProd hp
                  have hab := ofMemListProd hp'.1
                  exact Nat.succ_le_succ (maxLe
                    (maxLe (typesUpTo_sound n a hab.1) (typesUpTo_sound n b hab.2))
                    (ih body hp'.2))
              | inr hrest =>
                  cases ofMemAppend hrest with
                  | inl ha =>
                      obtain ⟨⟨f, x⟩, hp, heq⟩ :=
                        ofMemMap (fun (f, x) => Expr.app f x) _ e ha
                      cases heq
                      have hp' := ofMemListProd hp
                      exact Nat.succ_le_succ (maxLe (ih f hp'.1) (ih x hp'.2))
                  | inr hrest =>
                      cases ofMemAppend hrest with
                      | inl hc =>
                          cases hc with
                          | head => exact Nat.succ_le_succ (Nat.zero_le n)
                          | tail _ ht =>
                              cases ht with
                              | head => exact Nat.succ_le_succ (Nat.zero_le n)
                              | tail _ ht =>
                                  cases ht with
                                  | head => exact Nat.succ_le_succ (Nat.zero_le n)
                                  | tail _ ht =>
                                      cases ht with
                                      | head => exact Nat.succ_le_succ (Nat.zero_le n)
                                      | tail _ ht => cases ht
                      | inr hr =>
                          obtain ⟨r, hm, heq⟩ := ofMemMap Expr.natRec _ e hr
                          cases heq
                          exact Nat.succ_le_succ (typesUpTo_sound n r hm)

theorem exprsUpTo_correct (n : Nat) (e : Expr) :
    exprDepth e ≤ n ↔ e ∈ exprsUpTo n :=
  ⟨exprsUpTo_complete n e, exprsUpTo_sound n e⟩

/-- Every fixed oracle program is beaten at every input above its depth. -/
theorem reflect_dominates_program (f : Nat → Nat) (e : Expr) (n : Nat)
    (h : exprDepth e ≤ n) : evalExpr f n e < reflect f n :=
  reflect_gt_member f n e (exprsUpTo_complete n e h)

/-- The diagonal is not expressible by one fixed program with the same oracle. -/
theorem no_fixed_program_defines_reflect (f : Nat → Nat) (e : Expr)
    (h : ∀ n, evalExpr f n e = reflect f n) : False := by
  have hlt := reflect_dominates_program f e (exprDepth e) (Nat.le_refl _)
  exact (Nat.ne_of_lt hlt) (h (exprDepth e))

/-- Even agreement on an arbitrary final segment of the inputs is impossible. -/
theorem no_program_eventually_defines_reflect (f : Nat → Nat) (e : Expr)
    (threshold : Nat)
    (h : ∀ n, threshold ≤ n → evalExpr f n e = reflect f n) : False := by
  let n := max threshold (exprDepth e)
  have hlt := reflect_dominates_program f e n (leMaxRight _ _)
  exact (Nat.ne_of_lt hlt) (h n (leMaxLeft _ _))

end Biggest
