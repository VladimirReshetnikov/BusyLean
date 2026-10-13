import BusyLean7.Definitions
import Lean

/-! Exact syntax-depth certificates, without expanding a large enumeration. -/
namespace BusyLean7
open BigNumber (Ty Term)

def typeRank : Ty → Nat
  | .nat => 1
  | .arr a b => Nat.max (typeRank a) (typeRank b) + 1
  | .wt a => typeRank a + 1

def termRank : Term → Nat
  | .var i => i + 2
  | .zero => 1
  | .succ => 1
  | .lam a b t => Nat.max (Nat.max (typeRank a) (typeRank b)) (termRank t) + 1
  | .app t u => Nat.max (termRank t) (termRank u) + 1
  | .natrec a => typeRank a + 1
  | .wzero a => typeRank a + 1
  | .wnode a => typeRank a + 1
  | .wrec a b => Nat.max (typeRank a) (typeRank b) + 1

theorem mem_cross {A B : Type} {xs : List A} {ys : List B}
    {x : A} {y : B} (hx : x ∈ xs) (hy : y ∈ ys) :
    (x, y) ∈ BigNumber.cross xs ys := by
  apply List.mem_flatMap.mpr
  exact ⟨x, hx, List.mem_map.mpr ⟨y, hy, rfl⟩⟩

theorem mem_natsUpTo {i k : Nat} (h : i < k) : i ∈ BigNumber.natsUpTo k := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hik : i = k
      · subst i
        simp [BigNumber.natsUpTo]
      · have hi : i < k := by omega
        exact List.mem_cons_of_mem _ (ih hi)

theorem nat_mem_types (k : Nat) : Ty.nat ∈ BigNumber.allTypes (k + 1) := by
  simp [BigNumber.allTypes]

theorem arr_mem_types {a b : Ty} {k : Nat}
    (ha : a ∈ BigNumber.allTypes k) (hb : b ∈ BigNumber.allTypes k) :
    Ty.arr a b ∈ BigNumber.allTypes (k + 1) := by
  have hm : Ty.arr a b ∈ (BigNumber.cross (BigNumber.allTypes k)
      (BigNumber.allTypes k)).map (fun p => Ty.arr p.1 p.2) :=
    List.mem_map.mpr ⟨(a, b), mem_cross ha hb, rfl⟩
  simp only [BigNumber.allTypes, List.mem_append, hm, or_true, true_or]

theorem wt_mem_types {a : Ty} {k : Nat} (ha : a ∈ BigNumber.allTypes k) :
    Ty.wt a ∈ BigNumber.allTypes (k + 1) := by
  have hm : Ty.wt a ∈ (BigNumber.allTypes k).map Ty.wt :=
    List.mem_map.mpr ⟨a, ha, rfl⟩
  simp only [BigNumber.allTypes, List.mem_append, hm, or_true, true_or]

theorem type_mem (a : Ty) : ∀ n, typeRank a ≤ n → a ∈ BigNumber.allTypes n := by
  induction a with
  | nat =>
      intro n h
      cases n with
      | zero => simp [typeRank] at h
      | succ n => exact nat_mem_types n
  | arr a b ia ib =>
      intro n h
      cases n with
      | zero => simp [typeRank] at h
      | succ n =>
          have ha : typeRank a ≤ n := by simp only [typeRank] at h; omega
          have hb : typeRank b ≤ n := by simp only [typeRank] at h; omega
          exact arr_mem_types (ia n ha) (ib n hb)
  | wt a ia =>
      intro n h
      cases n with
      | zero => simp [typeRank] at h
      | succ n =>
          have ha : typeRank a ≤ n := by simp only [typeRank] at h; omega
          exact wt_mem_types (ia n ha)

theorem zero_mem (k : Nat) : Term.zero ∈ BigNumber.allTerms (k + 1) := by
  simp [BigNumber.allTerms]

theorem succ_mem (k : Nat) : Term.succ ∈ BigNumber.allTerms (k + 1) := by
  simp [BigNumber.allTerms]

theorem var_mem {i k : Nat} (hi : i < k) :
    Term.var i ∈ BigNumber.allTerms (k + 1) := by
  have hm : Term.var i ∈ (BigNumber.natsUpTo k).map Term.var :=
    List.mem_map.mpr ⟨i, mem_natsUpTo hi, rfl⟩
  simp only [BigNumber.allTerms, List.mem_append, hm, or_true, true_or]

theorem app_mem {t u : Term} {k : Nat}
    (ht : t ∈ BigNumber.allTerms k) (hu : u ∈ BigNumber.allTerms k) :
    Term.app t u ∈ BigNumber.allTerms (k + 1) := by
  have hm : Term.app t u ∈ (BigNumber.cross (BigNumber.allTerms k)
      (BigNumber.allTerms k)).map (fun p => Term.app p.1 p.2) :=
    List.mem_map.mpr ⟨(t, u), mem_cross ht hu, rfl⟩
  simp only [BigNumber.allTerms, List.mem_append, hm, or_true, true_or]

theorem lam_mem {a b : Ty} {t : Term} {k : Nat}
    (ha : a ∈ BigNumber.allTypes k) (hb : b ∈ BigNumber.allTypes k)
    (ht : t ∈ BigNumber.allTerms k) :
    Term.lam a b t ∈ BigNumber.allTerms (k + 1) := by
  have hm : Term.lam a b t ∈ (BigNumber.cross
      (BigNumber.cross (BigNumber.allTypes k) (BigNumber.allTypes k))
      (BigNumber.allTerms k)).map (fun p => Term.lam p.1.1 p.1.2 p.2) :=
    List.mem_map.mpr ⟨((a, b), t), mem_cross (mem_cross ha hb) ht, rfl⟩
  simp only [BigNumber.allTerms, List.mem_append, hm, or_true, true_or]

theorem natrec_mem {a : Ty} {k : Nat} (ha : a ∈ BigNumber.allTypes k) :
    Term.natrec a ∈ BigNumber.allTerms (k + 1) := by
  have hm : Term.natrec a ∈ (BigNumber.allTypes k).map Term.natrec :=
    List.mem_map.mpr ⟨a, ha, rfl⟩
  simp only [BigNumber.allTerms, List.mem_append, hm, or_true, true_or]

theorem wzero_mem {a : Ty} {k : Nat} (ha : a ∈ BigNumber.allTypes k) :
    Term.wzero a ∈ BigNumber.allTerms (k + 1) := by
  have hm : Term.wzero a ∈ (BigNumber.allTypes k).map Term.wzero :=
    List.mem_map.mpr ⟨a, ha, rfl⟩
  simp only [BigNumber.allTerms, List.mem_append, hm, or_true, true_or]

theorem wnode_mem {a : Ty} {k : Nat} (ha : a ∈ BigNumber.allTypes k) :
    Term.wnode a ∈ BigNumber.allTerms (k + 1) := by
  have hm : Term.wnode a ∈ (BigNumber.allTypes k).map Term.wnode :=
    List.mem_map.mpr ⟨a, ha, rfl⟩
  simp only [BigNumber.allTerms, List.mem_append, hm, or_true, true_or]

theorem wrec_mem {a b : Ty} {k : Nat}
    (ha : a ∈ BigNumber.allTypes k) (hb : b ∈ BigNumber.allTypes k) :
    Term.wrec a b ∈ BigNumber.allTerms (k + 1) := by
  have hm : Term.wrec a b ∈ (BigNumber.cross (BigNumber.allTypes k)
      (BigNumber.allTypes k)).map (fun p => Term.wrec p.1 p.2) :=
    List.mem_map.mpr ⟨(a, b), mem_cross ha hb, rfl⟩
  simp only [BigNumber.allTerms, List.mem_append, hm, or_true, true_or]

theorem term_mem (t : Term) : ∀ n, termRank t ≤ n → t ∈ BigNumber.allTerms n := by
  induction t with
  | var i =>
      intro n h
      cases n with
      | zero => simp [termRank] at h
      | succ n =>
          have hi : i < n := by simp only [termRank] at h; omega
          exact var_mem hi
  | zero =>
      intro n h
      cases n with
      | zero => simp [termRank] at h
      | succ n => exact zero_mem n
  | succ =>
      intro n h
      cases n with
      | zero => simp [termRank] at h
      | succ n => exact succ_mem n
  | app t u it iu =>
      intro n h
      cases n with
      | zero => simp [termRank] at h
      | succ n =>
          have ht : termRank t ≤ n := by simp only [termRank] at h; omega
          have hu : termRank u ≤ n := by simp only [termRank] at h; omega
          exact app_mem (it n ht) (iu n hu)
  | lam a b t it =>
      intro n h
      cases n with
      | zero => simp [termRank] at h
      | succ n =>
          have ha : typeRank a ≤ n := by simp only [termRank] at h; omega
          have hb : typeRank b ≤ n := by simp only [termRank] at h; omega
          have ht : termRank t ≤ n := by simp only [termRank] at h; omega
          exact lam_mem (type_mem a n ha) (type_mem b n hb) (it n ht)
  | natrec a =>
      intro n h
      cases n with
      | zero => simp [termRank] at h
      | succ n =>
          have ha : typeRank a ≤ n := by simp only [termRank] at h; omega
          exact natrec_mem (type_mem a n ha)
  | wzero a =>
      intro n h
      cases n with
      | zero => simp [termRank] at h
      | succ n =>
          have ha : typeRank a ≤ n := by simp only [termRank] at h; omega
          exact wzero_mem (type_mem a n ha)
  | wnode a =>
      intro n h
      cases n with
      | zero => simp [termRank] at h
      | succ n =>
          have ha : typeRank a ≤ n := by simp only [termRank] at h; omega
          exact wnode_mem (type_mem a n ha)
  | wrec a b =>
      intro n h
      cases n with
      | zero => simp [termRank] at h
      | succ n =>
          have ha : typeRank a ≤ n := by simp only [termRank] at h; omega
          have hb : typeRank b ≤ n := by simp only [termRank] at h; omega
          exact wrec_mem (type_mem a n ha) (type_mem b n hb)

theorem rank_zero_certificate : termRank (amplifiedCall .zero) = 11 := by decide
theorem rank_input_certificate : termRank (amplifiedCall (.var 1)) = 11 := by decide

theorem zero_certificate_mem {n : Nat} (h : 11 ≤ n) :
    amplifiedCall .zero ∈ BigNumber.allTerms n :=
  term_mem _ n (by rw [rank_zero_certificate]; exact h)

theorem input_certificate_mem {n : Nat} (h : 11 ≤ n) :
    amplifiedCall (.var 1) ∈ BigNumber.allTerms n :=
  term_mem _ n (by rw [rank_input_certificate]; exact h)

end BusyLean7
