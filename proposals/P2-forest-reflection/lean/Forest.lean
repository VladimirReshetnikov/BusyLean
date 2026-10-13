import Arboreal
import Hierarchy

/-!
# Reflection with an accessible family of function oracles

The entire family is available to programs, including dynamic selection of
an oracle index.  This retains access to individual child values at a limit;
taking their pointwise maximum alone would not retain that information.
-/

namespace Forest

abbrev Oracles := Nat → Nat → Nat

inductive Expr where
  | base : Arboreal.Term → Expr
  | oracle : Nat → Expr
  | family : Expr
  | app : Expr → Expr → Expr
  | lam : Arboreal.Ty → Arboreal.Ty → Expr → Expr

def depth : Expr → Nat
  | .base t => Arboreal.depth t
  | .oracle i => i + 1
  | .family => 1
  | .app f x => Nat.succ (Nat.max (depth f) (depth x))
  | .lam a b body =>
      Nat.succ (Nat.max (Nat.max (Arboreal.typeDepth a) (Arboreal.typeDepth b))
        (depth body))

def interp (fs : Oracles) (n : Nat) : List Arboreal.Value → Expr → Arboreal.Value
  | env, .base t => Arboreal.interp (fs 0) n env t
  | _, .oracle i => ⟨.arr .nat .nat, fs i⟩
  | _, .family => ⟨.arr .nat (.arr .nat .nat), fs⟩
  | env, .app t₁ t₂ =>
      let value₁ := interp fs n env t₁
      let value₂ := interp fs n env t₂
      match value₁ with
      | ⟨.nat, _⟩ => ⟨.nat, (0 : Nat)⟩
      | ⟨.tree, _⟩ => ⟨.nat, (0 : Nat)⟩
      | ⟨.arr a b, g⟩ => ⟨b, g (Arboreal.cast a value₂.2)⟩
  | env, .lam a b body =>
      ⟨.arr a b, fun x =>
        let value := interp fs n (⟨a, x⟩ :: env) body
        Arboreal.cast b value.2⟩
termination_by structural _ t => t

def eval (fs : Oracles) (n : Nat) (t : Expr) : Nat :=
  match interp fs n [] t with
  | ⟨.nat, value⟩ => value
  | ⟨.tree, _⟩ => 0
  | ⟨.arr _ _, _⟩ => 0

def termsUpTo : Nat → List Expr
  | 0 => []
  | k + 1 =>
      (Arboreal.termsUpTo (k + 1)).map Expr.base ++
      ((Original.natsUpTo (k + 1)).map Expr.oracle ++
      ([.family] ++
      ((Original.listProd
        (Original.listProd (Arboreal.typesUpTo k) (Arboreal.typesUpTo k))
        (termsUpTo k)).map (fun ((a, b), body) => .lam a b body) ++
      (Original.listProd (termsUpTo k) (termsUpTo k)).map
        (fun (g, x) => .app g x))))

/-- A finite maximum over a language with access to the whole oracle family. -/
def reflect (fs : Oracles) (n : Nat) : Nat :=
  (n + 2) + Nat.max (Hierarchy.prefixMax (fun i => fs i n) n)
    (Original.foldMax (eval fs n) 0 (termsUpTo (n + 3)))

theorem eval_base (fs : Oracles) (n : Nat) (t : Arboreal.Term) :
    eval fs n (.base t) = Arboreal.eval (fs 0) n t := rfl

theorem eval_oracle_input (fs : Oracles) (n i : Nat) :
    eval fs n (.app (.oracle i) (.base .input)) = fs i n := rfl

theorem eval_family_input (fs : Oracles) (n : Nat) :
    eval fs n (.app (.app .family (.base .input)) (.base .input)) = fs n n := rfl

theorem oracle_lt_reflect (fs : Oracles) (n i : Nat) (hi : i ≤ n) :
    fs i n < reflect fs n :=
  Nat.lt_of_le_of_lt
    (Nat.le_trans (Hierarchy.le_prefixMax (fun j => fs j n) n i hi)
      (Original.le_natMax_left (Hierarchy.prefixMax (fun j => fs j n) n)
        (Original.foldMax (eval fs n) 0 (termsUpTo (n + 3)))))
    (Nat.lt_add_of_pos_left (Nat.succ_pos (n + 1)))

theorem input_lt_reflect (fs : Oracles) (n : Nat) : n < reflect fs n :=
  Nat.lt_of_lt_of_le
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_succ (n + 1)))
    (Nat.le_add_right (n + 2)
      (Nat.max (Hierarchy.prefixMax (fun i => fs i n) n)
        (Original.foldMax (eval fs n) 0 (termsUpTo (n + 3)))))

theorem eval_lt_reflect_of_mem (fs : Oracles) (n : Nat) (t : Expr)
    (h : t ∈ termsUpTo (n + 3)) : eval fs n t < reflect fs n :=
  Nat.lt_of_le_of_lt
    (Nat.le_trans
      (Original.le_foldMax_of_mem (eval fs n) (termsUpTo (n + 3)) t h 0)
      (Original.le_natMax_right (Hierarchy.prefixMax (fun i => fs i n) n)
        (Original.foldMax (eval fs n) 0 (termsUpTo (n + 3)))))
    (Nat.lt_add_of_pos_left (Nat.succ_pos (n + 1)))

theorem base_mem (k : Nat) (t : Arboreal.Term)
    (h : t ∈ Arboreal.termsUpTo k) : Expr.base t ∈ termsUpTo k := by
  cases k with
  | zero => cases h
  | succ k => exact List.mem_append_left _ (Original.map_mem Expr.base h)

theorem depth_pos (t : Expr) : 1 ≤ depth t := by
  cases t with
  | base t => exact Arboreal.depth_pos t
  | oracle i => exact Nat.succ_le_succ (Nat.zero_le i)
  | family => exact Nat.le_refl 1
  | app g x => exact Nat.succ_le_succ (Nat.zero_le _)
  | lam a b body => exact Nat.succ_le_succ (Nat.zero_le _)

theorem termsUpTo_complete (k : Nat) (t : Expr) (h : depth t ≤ k) :
    t ∈ termsUpTo k := by
  induction k generalizing t with
  | zero =>
      exact False.elim (Nat.not_succ_le_zero 0 (Nat.le_trans (depth_pos t) h))
  | succ k ih =>
      cases t with
      | base t => exact base_mem (k + 1) t (Arboreal.termsUpTo_complete (k + 1) t h)
      | oracle i =>
          exact List.mem_append_right _ (List.mem_append_left _
            (Original.map_mem Expr.oracle (Original.natsUpTo_complete (k + 1) i h)))
      | family =>
          exact List.mem_append_right _ (List.mem_append_right _
            (List.mem_append_left _ (.head _)))
      | app g x =>
          have hm := Nat.le_of_succ_le_succ h
          exact List.mem_append_right _ (List.mem_append_right _
            (List.mem_append_right _ (List.mem_append_right _
              (Original.map_mem (fun (g, x) => Expr.app g x)
                (Original.listProd_mem
                  (ih g (Nat.le_trans (Original.le_natMax_left _ _) hm))
                  (ih x (Nat.le_trans (Original.le_natMax_right _ _) hm)))))))
      | lam a b body =>
          have hm := Nat.le_of_succ_le_succ h
          have hab := Nat.le_trans (Original.le_natMax_left _ _) hm
          have hb := Nat.le_trans (Original.le_natMax_right _ _) hm
          exact List.mem_append_right _ (List.mem_append_right _
            (List.mem_append_right _ (List.mem_append_left _
              (Original.map_mem (fun ((a, b), body) => Expr.lam a b body)
                (Original.listProd_mem
                  (Original.listProd_mem
                    (Arboreal.typesUpTo_complete k a
                      (Nat.le_trans (Original.le_natMax_left _ _) hab))
                    (Arboreal.typesUpTo_complete k b
                      (Nat.le_trans (Original.le_natMax_right _ _) hab)))
                  (ih body hb))))))

theorem termsUpTo_sound (k : Nat) (t : Expr) (h : t ∈ termsUpTo k) :
    depth t ≤ k := by
  induction k generalizing t with
  | zero => cases h
  | succ k ih =>
      cases Original.of_append_mem _ _ h with
      | inl hbase =>
          obtain ⟨u, hu, he⟩ := Original.of_map_mem Expr.base hbase
          cases he
          exact Arboreal.termsUpTo_sound (k + 1) u hu
      | inr hrest =>
          cases Original.of_append_mem _ _ hrest with
          | inl horacle =>
              obtain ⟨i, hi, he⟩ := Original.of_map_mem Expr.oracle horacle
              cases he
              exact Original.natsUpTo_sound (k + 1) i hi
          | inr hremaining =>
              cases Original.of_append_mem _ _ hremaining with
              | inl hfamily =>
                  cases hfamily with
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
                        (Original.natMax_le
                          (Original.natMax_le
                            (Arboreal.typesUpTo_sound k a hab.1)
                            (Arboreal.typesUpTo_sound k b hab.2))
                          (ih body hp.2))
                  | inr happ =>
                      obtain ⟨⟨g, x⟩, hprod, he⟩ :=
                        Original.of_map_mem (fun (g, x) => Expr.app g x) happ
                      cases he
                      have hp := Original.of_listProd_mem hprod
                      exact Nat.succ_le_succ (Original.natMax_le (ih g hp.1) (ih x hp.2))

theorem termsUpTo_correct (k : Nat) (t : Expr) :
    depth t ≤ k ↔ t ∈ termsUpTo k :=
  ⟨termsUpTo_complete k t, termsUpTo_sound k t⟩

theorem termsUpTo_mono {j k : Nat} (h : j ≤ k) {t : Expr}
    (ht : t ∈ termsUpTo j) : t ∈ termsUpTo k :=
  termsUpTo_complete k t (Nat.le_trans (termsUpTo_sound j t ht) h)

theorem eval_lt_reflect_of_depth_le (fs : Oracles) (n : Nat) (t : Expr)
    (h : depth t ≤ n + 3) : eval fs n t < reflect fs n :=
  eval_lt_reflect_of_mem fs n t (termsUpTo_complete (n + 3) t h)

theorem eventually_lt_reflect (fs : Oracles) (t : Expr) (n : Nat)
    (h : depth t ≤ n) : eval fs n t < reflect fs n :=
  eval_lt_reflect_of_depth_le fs n t (Nat.le_trans h (Nat.le_add_right n 3))

theorem application_eventually_lt_reflect (fs : Oracles) (t : Expr) (n : Nat)
    (h : depth t ≤ n) : eval fs n (.app t (.base .input)) < reflect fs n := by
  apply eval_lt_reflect_of_depth_le
  change Nat.succ (Nat.max (depth t) 1) ≤ n + 3
  rw [Original.natMax_eq_left (depth_pos t)]
  exact Nat.le_trans (Nat.succ_le_succ h) (Nat.le_add_right (n + 1) 2)

theorem reflect_not_representable (fs : Oracles) (t : Expr) :
    ¬ (∀ n, eval fs n t = reflect fs n) := by
  intro h
  have hs := eventually_lt_reflect fs t (depth t) (Nat.le_refl _)
  rw [h (depth t)] at hs
  exact Nat.lt_irrefl _ hs

theorem arboreal_max_le (fs : Oracles) (n k : Nat) :
    Original.foldMax (Arboreal.eval (fs 0) n) 0 (Arboreal.termsUpTo k) ≤
      Original.foldMax (eval fs n) 0 (termsUpTo k) := by
  apply Arboreal.foldMax_le
  · exact Nat.zero_le _
  · intro t ht
    exact Original.le_foldMax_of_mem (eval fs n) (termsUpTo k) (.base t)
      (base_mem k t ht) 0

theorem Arboreal_Rw_lt_reflect (fs : Oracles) (n : Nat) :
    Arboreal.Rw (fs 0) n < reflect fs n := by
  have hmax :
      Nat.max (fs 0 n)
          (Original.foldMax (Arboreal.eval (fs 0) n) 0 (Arboreal.termsUpTo (n + 3))) ≤
        Nat.max (Hierarchy.prefixMax (fun i => fs i n) n)
          (Original.foldMax (eval fs n) 0 (termsUpTo (n + 3))) :=
    Original.natMax_le
      (Nat.le_trans (Hierarchy.le_prefixMax (fun i => fs i n) n 0 (Nat.zero_le _))
        (Original.le_natMax_left _ _))
      (Nat.le_trans (arboreal_max_le fs n (n + 3)) (Original.le_natMax_right _ _))
  exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hmax (n + 1))
    (Nat.add_lt_add_right (Nat.lt_succ_self (n + 1)) _)

theorem contender5_lt_reflect (fs : Oracles) : Original.contender5 < reflect fs 42 :=
  Nat.lt_trans (Arboreal.contender5_lt_Rw (fs 0)) (Arboreal_Rw_lt_reflect fs 42)

end Forest

#print axioms Forest.reflect
#print axioms Forest.termsUpTo_correct
#print axioms Forest.Arboreal_Rw_lt_reflect
#print axioms Forest.contender5_lt_reflect
#print axioms Forest.reflect_not_representable
