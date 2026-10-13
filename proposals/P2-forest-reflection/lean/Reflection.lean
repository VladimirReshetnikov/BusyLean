import Original

/-!
A constructive reflection operator for the exact interpreter in Original.
The finite language adds an oracle Nat -> Nat and an input value, and allows
both under higher-type lambda abstraction and application. Base expressions
embed every original raw term, including ill-typed terms and their prescribed
error behavior. No normalization assertion is postulated: interpretation is
structural recursion into Lean's total function types.
-/

namespace Reflection

inductive Expr where
  | base : Original.Term → Expr
  | oracle : Expr
  | input : Expr
  | app : Expr → Expr → Expr
  | lam : Original.Ty → Original.Ty → Expr → Expr

def depth : Expr → Nat
  | .base t => Original.termDepth t
  | .oracle => 1
  | .input => 1
  | .app f x => Nat.succ (Nat.max (depth f) (depth x))
  | .lam a b body =>
      Nat.succ (Nat.max (Nat.max (Original.typeDepth a) (Original.typeDepth b))
        (depth body))

def interp (f : Nat → Nat) (n : Nat) : List Original.Value → Expr → Original.Value
  | env, .base t => Original.interpTerm env t
  | _, .oracle => ⟨.arr .nat .nat, f⟩
  | _, .input => ⟨.nat, n⟩
  | env, .app t₁ t₂ =>
      let value₁ := interp f n env t₁
      let value₂ := interp f n env t₂
      match value₁ with
      | ⟨.nat, _⟩ => ⟨.nat, (0 : Nat)⟩
      | ⟨.arr a b, g⟩ => ⟨b, g (Original.cast a value₂.2)⟩
  | env, .lam a b body =>
      ⟨.arr a b, fun x =>
        let value := interp f n (⟨a, x⟩ :: env) body
        Original.cast b value.2⟩
termination_by structural _ t => t

def eval (f : Nat → Nat) (n : Nat) (t : Expr) : Nat :=
  match interp f n [] t with
  | ⟨.nat, value⟩ => value
  | ⟨.arr _ _, _⟩ => 0

def termsUpTo : Nat → List Expr
  | 0 => []
  | k + 1 =>
      (Original.termsUpTo (k + 1)).map Expr.base ++
      ([.oracle, .input] ++
      ((Original.listProd
        (Original.listProd (Original.typesUpTo k) (Original.typesUpTo k))
        (termsUpTo k)).map (fun ((a, b), body) => .lam a b body) ++
      (Original.listProd (termsUpTo k) (termsUpTo k)).map
        (fun (g, x) => .app g x)))

/-- Finite constructive reflection at syntactic depth `n + 3`. -/
def R (f : Nat → Nat) (n : Nat) : Nat :=
  (n + 1) + Nat.max (f n)
    (Original.foldMax (eval f n) 0 (termsUpTo (n + 3)))

theorem eval_base (f : Nat → Nat) (n : Nat) (t : Original.Term) :
    eval f n (.base t) = Original.eval t := rfl

theorem eval_input (f : Nat → Nat) (n : Nat) : eval f n .input = n := rfl

theorem eval_oracle_input (f : Nat → Nat) (n : Nat) :
    eval f n (.app .oracle .input) = f n := rfl

/-- Reflection strictly exceeds its input function at every argument. -/
theorem self_lt_R (f : Nat → Nat) (n : Nat) : f n < R f n :=
  Nat.lt_of_le_of_lt
    (Original.le_natMax_left (f n)
      (Original.foldMax (eval f n) 0 (termsUpTo (n + 3))))
    (Nat.lt_add_of_pos_left (Nat.succ_pos n))

theorem input_lt_R (f : Nat → Nat) (n : Nat) : n < R f n :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self n)
    (Nat.le_add_right (n + 1)
      (Nat.max (f n) (Original.foldMax (eval f n) 0 (termsUpTo (n + 3)))))

/-- The defining bounded-language diagonal inequality. -/
theorem eval_lt_R_of_mem (f : Nat → Nat) (n : Nat) (t : Expr)
    (h : t ∈ termsUpTo (n + 3)) : eval f n t < R f n :=
  Nat.lt_of_le_of_lt
    (Nat.le_trans
      (Original.le_foldMax_of_mem (eval f n) (termsUpTo (n + 3)) t h 0)
      (Original.le_natMax_right (f n)
        (Original.foldMax (eval f n) 0 (termsUpTo (n + 3)))))
    (Nat.lt_add_of_pos_left (Nat.succ_pos n))

/-- A fold stays below every common bound on its start and entries. -/
theorem foldMax_le {α : Type} (g : α → Nat) (xs : List α)
    (current upper : Nat) (hc : current ≤ upper)
    (hs : ∀ x, x ∈ xs → g x ≤ upper) :
    Original.foldMax g current xs ≤ upper := by
  induction xs generalizing current with
  | nil => exact hc
  | cons x xs ih =>
      apply ih (Nat.max current (g x))
      · change (if current ≤ g x then g x else current) ≤ upper
        by_cases h : current ≤ g x
        · rw [if_pos h]
          exact hs x (List.Mem.head xs)
        · rw [if_neg h]
          exact hc
      · intro y hy
        exact hs y (List.Mem.tail x hy)

/-- Every source term at the same budget is present literally as a base node. -/
theorem base_mem (k : Nat) (t : Original.Term)
    (h : t ∈ Original.termsUpTo k) : Expr.base t ∈ termsUpTo k := by
  cases k with
  | zero => cases h
  | succ k =>
      exact List.mem_append_left _ (Original.map_mem Expr.base h)

theorem depth_pos (t : Expr) : 1 ≤ depth t := by
  cases t with
  | base t => exact Original.termDepth_pos t
  | oracle => exact Nat.le_refl 1
  | input => exact Nat.le_refl 1
  | app g x => exact Nat.succ_le_succ (Nat.zero_le _)
  | lam a b body => exact Nat.succ_le_succ (Nat.zero_le _)

/-- The finite enumeration contains every expression within its depth budget. -/
theorem termsUpTo_complete (k : Nat) (t : Expr) (h : depth t ≤ k) :
    t ∈ termsUpTo k := by
  induction k generalizing t with
  | zero =>
      exact False.elim (Nat.not_succ_le_zero 0 (Nat.le_trans (depth_pos t) h))
  | succ k ih =>
      cases t with
      | base t => exact base_mem (k + 1) t (Original.termsUpTo_complete (k + 1) t h)
      | oracle =>
          exact List.mem_append_right _ (List.mem_append_left _ (.head _))
      | input =>
          exact List.mem_append_right _ (List.mem_append_left _ (.tail _ (.head _)))
      | app g x =>
          have hm := Nat.le_of_succ_le_succ h
          exact List.mem_append_right _ (List.mem_append_right _
            (List.mem_append_right _
              (Original.map_mem (fun (g, x) => Expr.app g x)
                (Original.listProd_mem
                  (ih g (Nat.le_trans (Original.le_natMax_left _ _) hm))
                  (ih x (Nat.le_trans (Original.le_natMax_right _ _) hm))))))
      | lam a b body =>
          have hm := Nat.le_of_succ_le_succ h
          have hab := Nat.le_trans (Original.le_natMax_left _ _) hm
          have hb := Nat.le_trans (Original.le_natMax_right _ _) hm
          exact List.mem_append_right _ (List.mem_append_right _
            (List.mem_append_left _
              (Original.map_mem (fun ((a, b), body) => Expr.lam a b body)
                (Original.listProd_mem
                  (Original.listProd_mem
                    (Original.typesUpTo_complete k a
                      (Nat.le_trans (Original.le_natMax_left _ _) hab))
                    (Original.typesUpTo_complete k b
                      (Nat.le_trans (Original.le_natMax_right _ _) hab)))
                  (ih body hb)))))

theorem natMax_le {a b c : Nat} (ha : a ≤ c) (hb : b ≤ c) :
    Nat.max a b ≤ c := by
  change (if a ≤ b then b else a) ≤ c
  by_cases h : a ≤ b
  · rw [if_pos h]
    exact hb
  · rw [if_neg h]
    exact ha

/-- No expression outside the depth budget enters the finite enumeration. -/
theorem termsUpTo_sound (k : Nat) (t : Expr) (h : t ∈ termsUpTo k) :
    depth t ≤ k := by
  induction k generalizing t with
  | zero => cases h
  | succ k ih =>
      cases Original.of_append_mem _ _ h with
      | inl hbase =>
          obtain ⟨u, hu, he⟩ := Original.of_map_mem Expr.base hbase
          cases he
          exact Original.termsUpTo_sound (k + 1) u hu
      | inr hrest =>
          cases Original.of_append_mem _ _ hrest with
          | inl hconst =>
              cases hconst with
              | head => exact Nat.succ_le_succ (Nat.zero_le _)
              | tail _ hinput =>
                  cases hinput with
                  | head => exact Nat.succ_le_succ (Nat.zero_le _)
                  | tail _ hnil => cases hnil
          | inr hlamapp =>
              cases Original.of_append_mem _ _ hlamapp with
              | inl hlam =>
                  obtain ⟨⟨⟨a, b⟩, body⟩, hprod, he⟩ :=
                    Original.of_map_mem (fun ((a, b), body) => Expr.lam a b body) hlam
                  cases he
                  have hp := Original.of_listProd_mem hprod
                  have hab := Original.of_listProd_mem hp.1
                  exact Nat.succ_le_succ
                    (natMax_le
                      (natMax_le
                        (Original.typesUpTo_sound k a hab.1)
                        (Original.typesUpTo_sound k b hab.2))
                      (ih body hp.2))
              | inr happ =>
                  obtain ⟨⟨g, x⟩, hprod, he⟩ :=
                    Original.of_map_mem (fun (g, x) => Expr.app g x) happ
                  cases he
                  have hp := Original.of_listProd_mem hprod
                  exact Nat.succ_le_succ (natMax_le (ih g hp.1) (ih x hp.2))

theorem termsUpTo_mono {j k : Nat} (h : j ≤ k) {t : Expr}
    (ht : t ∈ termsUpTo j) : t ∈ termsUpTo k :=
  termsUpTo_complete k t (Nat.le_trans (termsUpTo_sound j t ht) h)

/-- Uniform domination of every program fitting the argument-dependent budget. -/
theorem eval_lt_R_of_depth_le (f : Nat → Nat) (n : Nat) (t : Expr)
    (h : depth t ≤ n + 3) : eval f n t < R f n :=
  eval_lt_R_of_mem f n t (termsUpTo_complete (n + 3) t h)

/-- Every fixed oracle program is eventually strictly dominated by reflection. -/
theorem eventually_lt_R (f : Nat → Nat) (t : Expr) (n : Nat)
    (h : depth t ≤ n) : eval f n t < R f n :=
  eval_lt_R_of_depth_le f n t (Nat.le_trans h (Nat.le_add_right n 3))

/-- The explicit application formulation for a fixed unary expression. -/
theorem application_eventually_lt_R (f : Nat → Nat) (t : Expr) (n : Nat)
    (h : depth t ≤ n) : eval f n (.app t .input) < R f n := by
  apply eval_lt_R_of_depth_le
  change Nat.succ (Nat.max (depth t) 1) ≤ n + 3
  rw [Original.natMax_eq_left (depth_pos t)]
  exact Nat.le_trans (Nat.succ_le_succ h) (Nat.le_add_right (n + 1) 2)

/-- A fixed term of this oracle language cannot define its own reflection. -/
theorem R_not_representable (f : Nat → Nat) (t : Expr) :
    ¬ (∀ n, eval f n t = R f n) := by
  intro h
  have hs := eventually_lt_R f t (depth t) (Nat.le_refl _)
  rw [h (depth t)] at hs
  exact Nat.lt_irrefl _ hs

/-- The original finite maximum embeds in every larger reflection budget. -/
theorem source_largest_le_fold (f : Nat → Nat) (k n : Nat)
    (h : k ≤ n + 3) :
    Original.largestSTLCNatRecNatOfDepth k ≤
      Original.foldMax (eval f n) 0 (termsUpTo (n + 3)) := by
  rw [Original.largestSTLCNatRecNatOfDepth_eq_foldMax]
  apply foldMax_le Original.eval (Original.termsUpTo k) 0 _ (Nat.zero_le _)
  intro t ht
  exact Original.le_foldMax_of_mem (eval f n) (termsUpTo (n + 3)) (.base t)
    (base_mem (n + 3) t (Original.termsUpTo_mono h ht)) 0

/-- Strict comparison with the exact source interpreter, at any covered budget. -/
theorem source_largest_lt_R (f : Nat → Nat) (k n : Nat)
    (h : k ≤ n + 3) : Original.largestSTLCNatRecNatOfDepth k < R f n :=
  Nat.lt_of_le_of_lt
    (Nat.le_trans (source_largest_le_fold f k n h)
      (Original.le_natMax_right (f n)
        (Original.foldMax (eval f n) 0 (termsUpTo (n + 3)))))
    (Nat.lt_add_of_pos_left (Nat.succ_pos n))

/-- The requested exact Contender 5 comparison; no evaluation of it occurs. -/
theorem contender5_lt_R (f : Nat → Nat) : Original.contender5 < R f 42 :=
  source_largest_lt_R f 42 42 (by decide)

end Reflection
