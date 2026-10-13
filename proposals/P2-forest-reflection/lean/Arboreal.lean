import Original
import Trees

/-!
Constructive bounded-program reflection for natural numbers, all finite
function types, and the strictly positive countably branching tree type.
The tree recursor eliminates into every object-language result type.

Every `old` node denotes the exact *closed numerical evaluation* of its
original source term, preserving the repository's raw-term maximum.
-/

namespace Arboreal

inductive Ty where
  | nat : Ty
  | tree : Ty
  | arr : Ty → Ty → Ty
  deriving Repr, DecidableEq

def typeEqb : Ty → Ty → Bool
  | .nat, .nat => true
  | .tree, .tree => true
  | .arr a b, .arr c d => typeEqb a c && typeEqb b d
  | _, _ => false

def typeDepth : Ty → Nat
  | .nat => 1
  | .tree => 1
  | .arr a b => Nat.succ (Nat.max (typeDepth a) (typeDepth b))

def interpType : Ty → Type
  | .nat => Nat
  | .tree => BTree
  | .arr a b => interpType a → interpType b

def error : (t : Ty) → interpType t
  | .nat => (0 : Nat)
  | .tree => BTree.zero
  | .arr _ b => fun _ => error b

def castError (src dst : Ty) :
    (interpType src → interpType dst) × (interpType dst → interpType src) :=
  (fun _ => error dst, fun _ => error src)

def castImpl : (src dst : Ty) →
    (interpType src → interpType dst) × (interpType dst → interpType src)
  | .nat, .nat => (id, id)
  | .tree, .tree => (id, id)
  | .arr a b, .arr c d =>
      if typeEqb a c && typeEqb b d then
        let p := castImpl a c
        let q := castImpl b d
        (fun f x => q.1 (f (p.2 x)), fun f x => q.2 (f (p.1 x)))
      else castError (.arr a b) (.arr c d)
  | src, dst => castError src dst

def cast {src : Ty} (dst : Ty) : interpType src → interpType dst :=
  (castImpl src dst).1

abbrev Value := (t : Ty) × interpType t

def natRecTy (r : Ty) : Ty :=
  .arr r (.arr (.arr .nat (.arr r r)) (.arr .nat r))

def treeRecTy (r : Ty) : Ty :=
  .arr r (.arr (.arr .tree (.arr r r))
    (.arr (.arr (.arr .nat .tree) (.arr (.arr .nat r) r)) (.arr .tree r)))

inductive Term where
  | old : Original.Term → Term
  | var : Nat → Term
  | lam : Ty → Ty → Term → Term
  | app : Term → Term → Term
  | zero : Term
  | succ : Term
  | natRec : Ty → Term
  | treeZero : Term
  | treeSucc : Term
  | treeLim : Term
  | treeRec : Ty → Term
  | oracle : Term
  | input : Term
  deriving Repr, DecidableEq

def depth : Term → Nat
  | .old t => Original.termDepth t
  | .var x => Nat.succ (Original.natDepth x)
  | .lam a b body =>
      Nat.succ (Nat.max (Nat.max (typeDepth a) (typeDepth b)) (depth body))
  | .app f x => Nat.succ (Nat.max (depth f) (depth x))
  | .natRec r => Nat.succ (typeDepth r)
  | .treeRec r => Nat.succ (typeDepth r)
  | _ => 1

def natRecValue {α : Type} (initial : α) (step : Nat → α → α) : Nat → α
  | 0 => initial
  | k + 1 => step k (natRecValue initial step k)

def treeRecValue {α : Type} (initial : α) (successor : BTree → α → α)
    (limit : (Nat → BTree) → (Nat → α) → α) : BTree → α
  | .zero => initial
  | .succ t => successor t (treeRecValue initial successor limit t)
  | .lim g => limit g (fun k => treeRecValue initial successor limit (g k))

def interp (f : Nat → Nat) (n : Nat) : List Value → Term → Value
  | _, .old t => ⟨.nat, Original.eval t⟩
  | env, .var x =>
      match Original.lookup env x with
      | some value => value
      | none => ⟨.nat, (0 : Nat)⟩
  | env, .lam a b body =>
      ⟨.arr a b, fun x =>
        let value := interp f n (⟨a, x⟩ :: env) body
        cast b value.2⟩
  | env, .app t₁ t₂ =>
      let value₁ := interp f n env t₁
      let value₂ := interp f n env t₂
      match value₁ with
      | ⟨.arr a b, g⟩ => ⟨b, g (cast a value₂.2)⟩
      | ⟨.nat, _⟩ => ⟨.nat, (0 : Nat)⟩
      | ⟨.tree, _⟩ => ⟨.nat, (0 : Nat)⟩
  | _, .zero => ⟨.nat, (0 : Nat)⟩
  | _, .succ => ⟨.arr .nat .nat, Nat.succ⟩
  | _, .natRec r => ⟨natRecTy r, fun initial step k => natRecValue initial step k⟩
  | _, .treeZero => ⟨.tree, BTree.zero⟩
  | _, .treeSucc => ⟨.arr .tree .tree, BTree.succ⟩
  | _, .treeLim => ⟨.arr (.arr .nat .tree) .tree, BTree.lim⟩
  | _, .treeRec r =>
      ⟨treeRecTy r, fun initial successor limit t =>
        treeRecValue initial successor limit t⟩
  | _, .oracle => ⟨.arr .nat .nat, f⟩
  | _, .input => ⟨.nat, n⟩
termination_by structural _ t => t

def eval (f : Nat → Nat) (n : Nat) (t : Term) : Nat :=
  match interp f n [] t with
  | ⟨.nat, value⟩ => value
  | ⟨.tree, _⟩ => 0
  | ⟨.arr _ _, _⟩ => 0

def typesUpTo : Nat → List Ty
  | 0 => []
  | k + 1 =>
      let r := typesUpTo k
      .nat :: .tree :: (Original.listProd r r).map (fun (a, b) => .arr a b)

def termsUpTo : Nat → List Term
  | 0 => []
  | k + 1 =>
      (Original.termsUpTo (k + 1)).map Term.old ++ (
      (Original.natsUpTo k).map Term.var ++ (
      (Original.listProd (Original.listProd (typesUpTo k) (typesUpTo k))
        (termsUpTo k)).map (fun ((a, b), body) => .lam a b body) ++ (
      (Original.listProd (termsUpTo k) (termsUpTo k)).map
        (fun (g, x) => .app g x) ++ (
      [.zero, .succ, .treeZero, .treeSucc, .treeLim, .oracle, .input] ++ (
      (typesUpTo k).map Term.natRec ++ (typesUpTo k).map Term.treeRec)))))

/-- Reflection in the language with full countably branching tree recursion. -/
def Rw (f : Nat → Nat) (n : Nat) : Nat :=
  (n + 1) + Nat.max (f n)
    (Original.foldMax (eval f n) 0 (termsUpTo (n + 3)))

theorem eval_old (f : Nat → Nat) (n : Nat) (t : Original.Term) :
    eval f n (.old t) = Original.eval t := rfl

theorem self_lt_Rw (f : Nat → Nat) (n : Nat) : f n < Rw f n :=
  Nat.lt_of_le_of_lt
    (Original.le_natMax_left (f n)
      (Original.foldMax (eval f n) 0 (termsUpTo (n + 3))))
    (Nat.lt_add_of_pos_left (Nat.succ_pos n))

theorem input_lt_Rw (f : Nat → Nat) (n : Nat) : n < Rw f n :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self n)
    (Nat.le_add_right (n + 1)
      (Nat.max (f n) (Original.foldMax (eval f n) 0 (termsUpTo (n + 3)))))

theorem eval_lt_Rw_of_mem (f : Nat → Nat) (n : Nat) (t : Term)
    (h : t ∈ termsUpTo (n + 3)) : eval f n t < Rw f n :=
  Nat.lt_of_le_of_lt
    (Nat.le_trans
      (Original.le_foldMax_of_mem (eval f n) (termsUpTo (n + 3)) t h 0)
      (Original.le_natMax_right (f n)
        (Original.foldMax (eval f n) 0 (termsUpTo (n + 3)))))
    (Nat.lt_add_of_pos_left (Nat.succ_pos n))

theorem foldMax_le {α : Type} (g : α → Nat) (xs : List α)
    (current upper : Nat) (hc : current ≤ upper)
    (hs : ∀ x, x ∈ xs → g x ≤ upper) :
    Original.foldMax g current xs ≤ upper := by
  induction xs generalizing current with
  | nil => exact hc
  | cons x xs ih =>
      exact ih (Nat.max current (g x))
        (Original.natMax_le hc (hs x (.head _)))
        (fun y hy => hs y (.tail x hy))

theorem old_mem (k : Nat) (t : Original.Term)
    (h : t ∈ Original.termsUpTo k) : Term.old t ∈ termsUpTo k := by
  cases k with
  | zero => cases h
  | succ k => exact List.mem_append_left _ (Original.map_mem Term.old h)

theorem legacy_le_fold (f : Nat → Nat) (n k : Nat) (h : k ≤ n + 3) :
    Original.largestSTLCNatRecNatOfDepth k ≤
      Original.foldMax (eval f n) 0 (termsUpTo (n + 3)) := by
  rw [Original.largestSTLCNatRecNatOfDepth_eq_foldMax]
  apply foldMax_le
  · exact Nat.zero_le _
  · intro t ht
    exact Original.le_foldMax_of_mem (eval f n) (termsUpTo (n + 3)) (.old t)
      (old_mem (n + 3) t (Original.termsUpTo_mono h ht)) 0

theorem legacy_lt_Rw (f : Nat → Nat) (n k : Nat) (h : k ≤ n + 3) :
    Original.largestSTLCNatRecNatOfDepth k < Rw f n :=
  Nat.lt_of_le_of_lt
    (Nat.le_trans (legacy_le_fold f n k h)
      (Original.le_natMax_right (f n)
        (Original.foldMax (eval f n) 0 (termsUpTo (n + 3)))))
    (Nat.lt_add_of_pos_left (Nat.succ_pos n))

theorem contender5_lt_Rw (f : Nat → Nat) : Original.contender5 < Rw f 42 :=
  legacy_lt_Rw f 42 42 (Nat.le_add_right 42 3)

theorem typeDepth_pos (t : Ty) : 1 ≤ typeDepth t := by
  cases t <;> exact Nat.succ_le_succ (Nat.zero_le _)

theorem typesUpTo_complete (k : Nat) (t : Ty) (h : typeDepth t ≤ k) :
    t ∈ typesUpTo k := by
  induction k generalizing t with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 (Nat.le_trans (typeDepth_pos t) h))
  | succ k ih =>
      cases t with
      | nat => exact .head _
      | tree => exact .tail _ (.head _)
      | arr a b =>
          have hm := Nat.le_of_succ_le_succ h
          exact .tail _ (.tail _ (Original.map_mem (fun (x, y) => Ty.arr x y)
            (Original.listProd_mem
              (ih a (Nat.le_trans (Original.le_natMax_left _ _) hm))
              (ih b (Nat.le_trans (Original.le_natMax_right _ _) hm)))))

theorem depth_pos (t : Term) : 1 ≤ depth t := by
  cases t with
  | old t => exact Original.termDepth_pos t
  | var _ => exact Nat.succ_le_succ (Nat.zero_le _)
  | lam _ _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
  | app _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
  | natRec _ => exact Nat.succ_le_succ (Nat.zero_le _)
  | treeRec _ => exact Nat.succ_le_succ (Nat.zero_le _)
  | zero => exact Nat.le_refl 1
  | succ => exact Nat.le_refl 1
  | treeZero => exact Nat.le_refl 1
  | treeSucc => exact Nat.le_refl 1
  | treeLim => exact Nat.le_refl 1
  | oracle => exact Nat.le_refl 1
  | input => exact Nat.le_refl 1

theorem primitive_mem (k : Nat) (t : Term)
    (h : t ∈ [.zero, .succ, .treeZero, .treeSucc, .treeLim, .oracle, .input]) :
    t ∈ termsUpTo (k + 1) :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_left _ h))))

/-- Every finite tree-recursive oracle program occurs at its stated depth. -/
theorem termsUpTo_complete (k : Nat) (t : Term) (h : depth t ≤ k) :
    t ∈ termsUpTo k := by
  induction k generalizing t with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 (Nat.le_trans (depth_pos t) h))
  | succ k ih =>
      cases t with
      | old t => exact old_mem (k + 1) t (Original.termsUpTo_complete (k + 1) t h)
      | var x =>
          exact List.mem_append_right _ (List.mem_append_left _
            (Original.map_mem Term.var
              (Original.natsUpTo_complete k x (Nat.le_of_succ_le_succ h))))
      | lam a b body =>
          have hm := Nat.le_of_succ_le_succ h
          have hab := Nat.le_trans (Original.le_natMax_left _ _) hm
          have hb := Nat.le_trans (Original.le_natMax_right _ _) hm
          exact List.mem_append_right _ (List.mem_append_right _
            (List.mem_append_left _
              (Original.map_mem (fun ((a, b), body) => Term.lam a b body)
                (Original.listProd_mem
                  (Original.listProd_mem
                    (typesUpTo_complete k a
                      (Nat.le_trans (Original.le_natMax_left _ _) hab))
                    (typesUpTo_complete k b
                      (Nat.le_trans (Original.le_natMax_right _ _) hab)))
                  (ih body hb)))))
      | app g x =>
          have hm := Nat.le_of_succ_le_succ h
          exact List.mem_append_right _ (List.mem_append_right _
            (List.mem_append_right _ (List.mem_append_left _
              (Original.map_mem (fun (g, x) => Term.app g x)
                (Original.listProd_mem
                  (ih g (Nat.le_trans (Original.le_natMax_left _ _) hm))
                  (ih x (Nat.le_trans (Original.le_natMax_right _ _) hm)))))))
      | zero => exact primitive_mem k .zero (.head _)
      | succ => exact primitive_mem k .succ (.tail _ (.head _))
      | treeZero => exact primitive_mem k .treeZero (.tail _ (.tail _ (.head _)))
      | treeSucc =>
          exact primitive_mem k .treeSucc (.tail _ (.tail _ (.tail _ (.head _))))
      | treeLim =>
          exact primitive_mem k .treeLim
            (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
      | oracle =>
          exact primitive_mem k .oracle
            (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
      | input =>
          exact primitive_mem k .input
            (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
      | natRec r =>
          exact List.mem_append_right _ (List.mem_append_right _
            (List.mem_append_right _ (List.mem_append_right _
              (List.mem_append_right _ (List.mem_append_left _
                (Original.map_mem Term.natRec
                  (typesUpTo_complete k r (Nat.le_of_succ_le_succ h))))))))
      | treeRec r =>
          exact List.mem_append_right _ (List.mem_append_right _
            (List.mem_append_right _ (List.mem_append_right _
              (List.mem_append_right _ (List.mem_append_right _
                (Original.map_mem Term.treeRec
                  (typesUpTo_complete k r (Nat.le_of_succ_le_succ h))))))))

theorem typesUpTo_sound (k : Nat) (t : Ty) (h : t ∈ typesUpTo k) :
    typeDepth t ≤ k := by
  induction k generalizing t with
  | zero => cases h
  | succ k ih =>
      cases h with
      | head => exact Nat.succ_le_succ (Nat.zero_le k)
      | tail _ h =>
          cases h with
          | head => exact Nat.succ_le_succ (Nat.zero_le k)
          | tail _ h =>
              obtain ⟨⟨a, b⟩, hab, he⟩ :=
                Original.of_map_mem (fun (a, b) => Ty.arr a b) h
              cases he
              obtain ⟨ha, hb⟩ := Original.of_listProd_mem hab
              exact Nat.succ_le_succ (Original.natMax_le (ih a ha) (ih b hb))

theorem primitive_depth (t : Term)
    (h : t ∈ [.zero, .succ, .treeZero, .treeSucc, .treeLim, .oracle, .input]) :
    depth t = 1 := by
  cases h with
  | head => rfl
  | tail _ h =>
      cases h with
      | head => rfl
      | tail _ h =>
          cases h with
          | head => rfl
          | tail _ h =>
              cases h with
              | head => rfl
              | tail _ h =>
                  cases h with
                  | head => rfl
                  | tail _ h =>
                      cases h with
                      | head => rfl
                      | tail _ h =>
                          cases h with
                          | head => rfl
                          | tail _ h => cases h

theorem termsUpTo_sound (k : Nat) (t : Term) (h : t ∈ termsUpTo k) :
    depth t ≤ k := by
  induction k generalizing t with
  | zero => cases h
  | succ k ih =>
      cases Original.of_append_mem _ _ h with
      | inl h =>
          obtain ⟨old, ho, he⟩ := Original.of_map_mem Term.old h
          cases he
          exact Original.termsUpTo_sound (k + 1) old ho
      | inr h =>
          cases Original.of_append_mem _ _ h with
          | inl h =>
              obtain ⟨x, hx, he⟩ := Original.of_map_mem Term.var h
              cases he
              exact Nat.succ_le_succ (Original.natsUpTo_sound k x hx)
          | inr h =>
              cases Original.of_append_mem _ _ h with
              | inl h =>
                  obtain ⟨⟨⟨a, b⟩, body⟩, hab, he⟩ :=
                    Original.of_map_mem (fun ((a, b), body) => Term.lam a b body) h
                  cases he
                  obtain ⟨ht, hb⟩ := Original.of_listProd_mem hab
                  obtain ⟨ha, hb'⟩ := Original.of_listProd_mem ht
                  exact Nat.succ_le_succ (Original.natMax_le
                    (Original.natMax_le (typesUpTo_sound k a ha) (typesUpTo_sound k b hb'))
                    (ih body hb))
              | inr h =>
                  cases Original.of_append_mem _ _ h with
                  | inl h =>
                      obtain ⟨⟨g, x⟩, hgx, he⟩ :=
                        Original.of_map_mem (fun (g, x) => Term.app g x) h
                      cases he
                      obtain ⟨hg, hx⟩ := Original.of_listProd_mem hgx
                      exact Nat.succ_le_succ (Original.natMax_le (ih g hg) (ih x hx))
                  | inr h =>
                      cases Original.of_append_mem _ _ h with
                      | inl h =>
                          rw [primitive_depth t h]
                          exact Nat.succ_le_succ (Nat.zero_le k)
                      | inr h =>
                          cases Original.of_append_mem _ _ h with
                          | inl h =>
                              obtain ⟨r, hr, he⟩ := Original.of_map_mem Term.natRec h
                              cases he
                              exact Nat.succ_le_succ (typesUpTo_sound k r hr)
                          | inr h =>
                              obtain ⟨r, hr, he⟩ := Original.of_map_mem Term.treeRec h
                              cases he
                              exact Nat.succ_le_succ (typesUpTo_sound k r hr)

theorem typesUpTo_correct (k : Nat) (t : Ty) :
    typeDepth t ≤ k ↔ t ∈ typesUpTo k :=
  ⟨typesUpTo_complete k t, typesUpTo_sound k t⟩

theorem termsUpTo_correct (k : Nat) (t : Term) :
    depth t ≤ k ↔ t ∈ termsUpTo k :=
  ⟨termsUpTo_complete k t, termsUpTo_sound k t⟩

/-- The quantitative diagonal bound includes all finite result types. -/
theorem eval_lt_Rw_of_depth_le (f : Nat → Nat) (n : Nat) (t : Term)
    (h : depth t ≤ n + 3) : eval f n t < Rw f n :=
  eval_lt_Rw_of_mem f n t (termsUpTo_complete (n + 3) t h)

theorem eventually_lt_Rw (f : Nat → Nat) (t : Term) (n : Nat)
    (h : depth t ≤ n) : eval f n t < Rw f n :=
  eval_lt_Rw_of_depth_le f n t (Nat.le_trans h (Nat.le_add_right n 3))

theorem application_eventually_lt_Rw (f : Nat → Nat) (t : Term) (n : Nat)
    (h : depth t ≤ n) : eval f n (.app t .input) < Rw f n := by
  apply eval_lt_Rw_of_depth_le
  change Nat.succ (Nat.max (depth t) 1) ≤ n + 3
  rw [Original.natMax_eq_left (depth_pos t)]
  exact Nat.le_trans (Nat.succ_le_succ h) (Nat.le_add_right (n + 1) 2)

/-- No fixed program in this tree-recursive oracle language represents Rw. -/
theorem Rw_not_representable (f : Nat → Nat) (t : Term) :
    ¬ (∀ n, eval f n t = Rw f n) := by
  intro h
  have hs := eventually_lt_Rw f t (depth t) (Nat.le_refl _)
  rw [h (depth t)] at hs
  exact Nat.lt_irrefl _ hs

end Arboreal
