import Mirror.Compiler
import Lean

/-! Enumeration certificates. No large list is evaluated by these proofs. -/
namespace BusyLean.Mirror

open BigNumber (Ty Term)

private theorem mem_cross {A B : Type} {xs : List A} {ys : List B}
    {x : A} {y : B} (hx : x ∈ xs) (hy : y ∈ ys) :
    (x, y) ∈ BigNumber.cross xs ys :=
  List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨y, hy, rfl⟩⟩

private theorem mem_natsUpTo {i n : Nat} (h : i < n) :
    i ∈ BigNumber.natsUpTo n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases he : i = n
      · subst i; exact List.Mem.head _
      · exact List.Mem.tail _ (ih (by omega))

theorem typeRank_pos (a : Ty) : 0 < typeRank a := by
  cases a <;> simp [typeRank]

theorem termRank_pos (t : Term) : 0 < termRank t := by
  cases t <;> simp [termRank] <;> omega

theorem mem_allTypes_of_rank (a : Ty) {d : Nat}
    (h : typeRank a ≤ d) : a ∈ BigNumber.allTypes d := by
  induction a generalizing d with
  | nat =>
      cases d with
      | zero => simp [typeRank] at h
      | succ d => simp [BigNumber.allTypes]
  | arr a b iha ihb =>
      cases d with
      | zero => have := typeRank_pos (.arr a b); omega
      | succ d =>
          have hab : Nat.max (typeRank a) (typeRank b) ≤ d :=
            Nat.le_of_succ_le_succ h
          have ha := iha (Nat.le_trans (Nat.le_max_left _ _) hab)
          have hb := ihb (Nat.le_trans (Nat.le_max_right _ _) hab)
          have hm : Ty.arr a b ∈
              (BigNumber.cross (BigNumber.allTypes d) (BigNumber.allTypes d)).map
                (fun p => Ty.arr p.1 p.2) :=
            List.mem_map.mpr ⟨(a, b), mem_cross ha hb, rfl⟩
          simp only [BigNumber.allTypes, List.mem_append, hm, or_true, true_or]
  | wt a iha =>
      cases d with
      | zero => have := typeRank_pos (.wt a); omega
      | succ d =>
          have ha := iha (Nat.le_of_succ_le_succ h)
          have hm : Ty.wt a ∈ (BigNumber.allTypes d).map Ty.wt :=
            List.mem_map.mpr ⟨a, ha, rfl⟩
          simp only [BigNumber.allTypes, List.mem_append, hm, or_true, true_or]

theorem mem_allTerms_of_rank (t : Term) {d : Nat}
    (h : termRank t ≤ d) : t ∈ BigNumber.allTerms d := by
  induction t generalizing d with
  | var i =>
      cases d with
      | zero => have := termRank_pos (.var i); omega
      | succ d =>
          have hi : i < d := by change i + 2 ≤ d + 1 at h; omega
          have hm : Term.var i ∈ (BigNumber.natsUpTo d).map Term.var :=
            List.mem_map.mpr ⟨i, mem_natsUpTo hi, rfl⟩
          simp only [BigNumber.allTerms, List.mem_append, hm, or_true, true_or]
  | lam a b t iht =>
      cases d with
      | zero => have := termRank_pos (.lam a b t); omega
      | succ d =>
          have hab : Nat.max (Nat.max (typeRank a) (typeRank b)) (termRank t) ≤ d :=
            Nat.le_of_succ_le_succ h
          have ht := iht (Nat.le_trans (Nat.le_max_right _ _) hab)
          have hab' := Nat.le_trans (Nat.le_max_left _ _) hab
          have ha := mem_allTypes_of_rank a
            (Nat.le_trans (Nat.le_max_left _ _) hab')
          have hb := mem_allTypes_of_rank b
            (Nat.le_trans (Nat.le_max_right _ _) hab')
          have hm : Term.lam a b t ∈
              (BigNumber.cross
                (BigNumber.cross (BigNumber.allTypes d) (BigNumber.allTypes d))
                (BigNumber.allTerms d)).map
                  (fun p => Term.lam p.1.1 p.1.2 p.2) :=
            List.mem_map.mpr ⟨((a, b), t), mem_cross (mem_cross ha hb) ht, rfl⟩
          simp only [BigNumber.allTerms, List.mem_append, hm, or_true, true_or]
  | app t u iht ihu =>
      cases d with
      | zero => have := termRank_pos (.app t u); omega
      | succ d =>
          have htu : Nat.max (termRank t) (termRank u) ≤ d :=
            Nat.le_of_succ_le_succ h
          have ht := iht (Nat.le_trans (Nat.le_max_left _ _) htu)
          have hu := ihu (Nat.le_trans (Nat.le_max_right _ _) htu)
          have hm : Term.app t u ∈
              (BigNumber.cross (BigNumber.allTerms d) (BigNumber.allTerms d)).map
                (fun p => Term.app p.1 p.2) :=
            List.mem_map.mpr ⟨(t, u), mem_cross ht hu, rfl⟩
          simp only [BigNumber.allTerms, List.mem_append, hm, or_true, true_or]
  | zero =>
      cases d with
      | zero => simp [termRank] at h
      | succ d => simp [BigNumber.allTerms]
  | succ =>
      cases d with
      | zero => simp [termRank] at h
      | succ d => simp [BigNumber.allTerms]
  | natrec a =>
      cases d with
      | zero => have := termRank_pos (.natrec a); omega
      | succ d =>
          have ha := mem_allTypes_of_rank a (Nat.le_of_succ_le_succ h)
          have hm : Term.natrec a ∈ (BigNumber.allTypes d).map Term.natrec :=
            List.mem_map.mpr ⟨a, ha, rfl⟩
          simp only [BigNumber.allTerms, List.mem_append, hm, or_true, true_or]
  | wzero a =>
      cases d with
      | zero => have := termRank_pos (.wzero a); omega
      | succ d =>
          have ha := mem_allTypes_of_rank a (Nat.le_of_succ_le_succ h)
          have hm : Term.wzero a ∈ (BigNumber.allTypes d).map Term.wzero :=
            List.mem_map.mpr ⟨a, ha, rfl⟩
          simp only [BigNumber.allTerms, List.mem_append, hm, or_true, true_or]
  | wnode a =>
      cases d with
      | zero => have := termRank_pos (.wnode a); omega
      | succ d =>
          have ha := mem_allTypes_of_rank a (Nat.le_of_succ_le_succ h)
          have hm : Term.wnode a ∈ (BigNumber.allTypes d).map Term.wnode :=
            List.mem_map.mpr ⟨a, ha, rfl⟩
          simp only [BigNumber.allTerms, List.mem_append, hm, or_true, true_or]
  | wrec a b =>
      cases d with
      | zero => have := termRank_pos (.wrec a b); omega
      | succ d =>
          have hab : Nat.max (typeRank a) (typeRank b) ≤ d :=
            Nat.le_of_succ_le_succ h
          have ha := mem_allTypes_of_rank a
            (Nat.le_trans (Nat.le_max_left _ _) hab)
          have hb := mem_allTypes_of_rank b
            (Nat.le_trans (Nat.le_max_right _ _) hab)
          have hm : Term.wrec a b ∈
              (BigNumber.cross (BigNumber.allTypes d) (BigNumber.allTypes d)).map
                (fun p => Term.wrec p.1 p.2) :=
            List.mem_map.mpr ⟨(a, b), mem_cross ha hb, rfl⟩
          simp only [BigNumber.allTerms, List.mem_append, hm, or_true, true_or]

theorem boostProgram_rank : termRank boostProgram = 17 := by decide

theorem boostProgram_mem (n : Nat) :
    boostProgram ∈ BigNumber.allTerms (budget n) :=
  mem_allTerms_of_rank boostProgram (by rw [boostProgram_rank]; unfold budget; omega)

end BusyLean.Mirror
