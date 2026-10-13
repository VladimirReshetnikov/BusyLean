import BusyLeanNext.Definitions
import BusyLean.Comparison

/-!
# Comparison-proof source

There are no placeholders. These proofs have been reviewed as source but
NOT run through Lean in the authoring environment. See VALIDATION.md.
-/
namespace BusyLean.V7

open BigNumber (Ty Value)
open BusyLean.W (Family)

/-! ## Elementary tower inequalities -/

theorem one_le_exp2 : ∀ n, 1 ≤ exp2 n
  | 0 => Nat.le_refl _
  | n + 1 => Nat.le_trans (one_le_exp2 n) (Nat.le_add_right _ _)

theorem self_le_exp2 : ∀ n, n ≤ exp2 n
  | 0 => Nat.zero_le _
  | n + 1 => Nat.add_le_add (self_le_exp2 n) (one_le_exp2 n)

theorem exp2_mono {a b : Nat} (h : a ≤ b) : exp2 a ≤ exp2 b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step h ih => exact Nat.le_trans ih (Nat.le_add_right _ _)

theorem iterate_mono_start (f : Nat → Nat)
    (hf : ∀ {a b}, a ≤ b → f a ≤ f b) :
    ∀ k {a b}, a ≤ b → BigNumber.iterate f k a ≤ BigNumber.iterate f k b
  | 0, _, _, h => h
  | k + 1, _, _, h => iterate_mono_start f hf k (hf h)

theorem iterate_mono_count (f : Nat → Nat)
    (hf : ∀ {a b}, a ≤ b → f a ≤ f b) (hg : ∀ x, x ≤ f x)
    {a b : Nat} (h : a ≤ b) (x : Nat) :
    BigNumber.iterate f a x ≤ BigNumber.iterate f b x := by
  induction h with
  | refl => exact Nat.le_refl _
  | step h ih =>
      exact Nat.le_trans ih (iterate_mono_start f hf _ (hg x))

theorem self_le_tower (x : Nat) : x ≤ tower x :=
  BigNumber.le_iterate exp2 self_le_exp2 x x

theorem tower_mono {a b : Nat} (h : a ≤ b) : tower a ≤ tower b :=
  Nat.le_trans (iterate_mono_start exp2 exp2_mono a h)
    (iterate_mono_count exp2 exp2_mono self_le_exp2 h b)

theorem self_le_towerOrbit (b : Nat) : ∀ k, b ≤ towerOrbit b k
  | 0 => Nat.le_refl _
  | k + 1 => Nat.le_trans (self_le_towerOrbit b k) (self_le_tower _)

/-! ## Finite enumeration, without evaluating it -/

theorem atom_mem_atoms (a : Atom) : a ∈ atoms := by
  cases a <;> simp [atoms]

theorem mem_programs_step {p : Program} {n : Nat}
    (h : p ∈ programs n) : p ∈ programs (n + 1) :=
  List.mem_append.mpr (Or.inl h)

theorem mem_programs_mono {p : Program} {k n : Nat}
    (hkn : k ≤ n) (hp : p ∈ programs k) : p ∈ programs n := by
  induction hkn with
  | refl => exact hp
  | step h ih => exact mem_programs_step ih

theorem atom_mem_programs (a : Atom) (n : Nat) :
    Program.atom a ∈ programs (n + 1) :=
  List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl
    (List.mem_map.mpr ⟨a, atom_mem_atoms a, rfl⟩))))

theorem app_mem_programs {p q : Program} {n : Nat}
    (hp : p ∈ programs n) (hq : q ∈ programs n) :
    Program.app p q ∈ programs (n + 1) := by
  have hc : (p, q) ∈ BigNumber.cross (programs n) (programs n) :=
    List.mem_flatMap.mpr ⟨p, hp, List.mem_map.mpr ⟨q, hq, rfl⟩⟩
  exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr
    (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨(p, q), hc, rfl⟩))))))

theorem old_mem_programs {t : BigNumber.Term} {n : Nat}
    (ht : t ∈ BigNumber.allTerms (n + 1)) :
    Program.old t ∈ programs (n + 1) :=
  List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr
    (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨t, ht, rfl⟩))))))

theorem numeral_mem : ∀ i, numeral i ∈ programs (i + 1)
  | 0 => atom_mem_programs .zero 0
  | i + 1 => app_mem_programs (atom_mem_programs .succ i) (numeral_mem i)

theorem lowerFunction_mem (i : Nat) : lowerFunction i ∈ programs (i + 4) := by
  have hr := app_mem_programs (atom_mem_programs .lowerRun i) (numeral_mem i)
  have hs := app_mem_programs hr (atom_mem_programs .seed (i + 1))
  have ht := app_mem_programs (atom_mem_programs .lowerIndex i) (numeral_mem i)
  exact app_mem_programs hs (mem_programs_step ht)

theorem lowerCall_mem (i : Nat) : lowerCall i ∈ programs (i + 5) :=
  app_mem_programs (lowerFunction_mem i) (atom_mem_programs .input (i + 3))

theorem towerProgram_mem (i : Nat) : towerProgram i ∈ programs (i + 7) := by
  have he : Program.app (.atom .iterate) (.atom .exp) ∈ programs 2 :=
    app_mem_programs (atom_mem_programs .iterate 0) (atom_mem_programs .exp 0)
  have hb : 2 ≤ i + 5 :=
    Nat.le_trans (by decide : 2 ≤ 5) (Nat.le_add_left 5 i)
  have hfirst := app_mem_programs (mem_programs_mono hb he) (lowerCall_mem i)
  exact app_mem_programs hfirst (mem_programs_step (lowerCall_mem i))

/-! ## Exact denotations of the witnesses -/

theorem eval_numeral (cs : Nat → World) (fs : Family) (n : Nat) :
    ∀ i, eval cs fs n (numeral i) = ⟨.nat, i⟩
  | 0 => rfl
  | i + 1 => by
      change applyValue (atomValue cs fs n .succ) (eval cs fs n (numeral i)) = _
      rw [eval_numeral cs fs n i]
      rfl

theorem eval_lowerFunction (cs : Nat → World) (fs : Family) (n i : Nat) :
    eval cs fs n (lowerFunction i) = ⟨unaryTy, fun x => score (cs i) x⟩ := by
  simp only [lowerFunction, eval, eval_numeral] <;> rfl

theorem eval_lowerCall (cs : Nat → World) (fs : Family) (n i : Nat) :
    eval cs fs n (lowerCall i) = ⟨.nat, score (cs i) n⟩ := by
  simp only [lowerCall, eval, eval_lowerFunction] <;> rfl

theorem evalNat_towerProgram (cs : Nat → World) (fs : Family) (n i : Nat) :
    evalNat cs fs n (towerProgram i) = tower (score (cs i) n) := by
  simp only [evalNat, towerProgram, eval, eval_lowerCall] <;> rfl

/-! ## Reflection and world comparisons -/

theorem program_lt_nextReflect (cs : Nat → World) (fs : Family) (n : Nat)
    {p : Program} (hp : p ∈ programs n) :
    evalNat cs fs n p < nextReflect cs fs n := by
  let m := BigNumber.maxN (BusyLean.W.prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (evalNat cs fs n) (programs n))
  have hm : evalNat cs fs n p ≤ m :=
    Nat.le_trans (BusyLean.W.le_maximum (evalNat cs fs n) hp)
      (BigNumber.le_maxN_right _ _)
  have hsucc : m + 1 ≤ n + 1 + m := by
    rw [Nat.add_comm m 1]
    exact Nat.add_le_add_right (Nat.le_add_left 1 n) m
  exact Nat.lt_of_le_of_lt hm
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hsucc)

theorem tower_lt_nextReflect (cs : Nat → World) (fs : Family) (i n : Nat)
    (hn : i + 7 ≤ n) : tower (score (cs i) n) < nextReflect cs fs n := by
  have h := program_lt_nextReflect cs fs n
    (mem_programs_mono hn (towerProgram_mem i))
  rw [evalNat_towerProgram] at h
  exact h

theorem tower_lt_foldReflect (cs : Nat → World) (seed : Family) (a : Tree)
    (i n : Nat) (hn : i + 7 ≤ n) :
    tower (score (cs i) n) < foldReflect (nextReflect cs) seed a n := by
  cases a with
  | leaf => exact tower_lt_nextReflect cs seed i n hn
  | node f =>
      exact tower_lt_nextReflect cs
        (fun j => foldReflect (nextReflect cs) seed (f j)) i n hn

theorem tower_lt_score_extend (cs : Nat → World) (i n : Nat)
    (hn : i + 7 ≤ n) : tower (score (cs i) n) < score (extend cs) n :=
  tower_lt_foldReflect cs BusyLean.p5Family (nextIndex cs) i n hn

theorem tower_lt_score_ramify (base : World) (a : Tree) (n : Nat)
    (hn : 7 ≤ n) : tower (score base n) < score (ramify base a) n := by
  cases a with
  | leaf => exact tower_lt_score_extend (fun _ => base) 0 n hn
  | node f =>
      exact tower_lt_score_extend
        (fun i => match i with
          | 0 => base
          | j + 1 => ramify base (f j)) 0 n hn

theorem level_growth (k n : Nat) (hn : 7 ≤ n) :
    tower (score (levels k) n) < score (levels (k + 1)) n :=
  tower_lt_score_ramify (levels k) (levels k).index n hn

theorem levels_mono (n : Nat) (hn : 7 ≤ n) {a b : Nat} (hab : a ≤ b) :
    score (levels a) n ≤ score (levels b) n := by
  induction hab with
  | refl => exact Nat.le_refl _
  | step h ih =>
      exact Nat.le_trans ih (Nat.le_of_lt (Nat.lt_of_le_of_lt
        (self_le_tower _) (level_growth _ n hn)))

theorem fixed_level_lt_diagonal (k n : Nat) (hn : 7 ≤ n) (hk : k < n) :
    score (levels k) n < diagonalScore n :=
  Nat.lt_of_lt_of_le
    (Nat.lt_of_le_of_lt (self_le_tower _) (level_growth k n hn))
    (levels_mono n hn (Nat.succ_le_of_lt hk))

theorem base_score (n : Nat) : score baseWorld n = BusyLean.finalFamily n := rfl

theorem orbit_le_levels (n : Nat) (hn : 7 ≤ n) :
    ∀ k, towerOrbit (score baseWorld n) k ≤ score (levels k) n
  | 0 => Nat.le_refl _
  | k + 1 => Nat.le_of_lt (Nat.lt_of_le_of_lt
      (tower_mono (orbit_le_levels n hn k)) (level_growth k n hn))

theorem orbit_lt_levels_succ (n : Nat) (hn : 7 ≤ n) (k : Nat) :
    towerOrbit (score baseWorld n) (k + 1) < score (levels (k + 1)) n :=
  Nat.lt_of_le_of_lt (tower_mono (orbit_le_levels n hn k)) (level_growth k n hn)

/-- A much stronger comparison than mere strict inequality. -/
theorem towerOrbit_contender6_lt_contender7 :
    towerOrbit BusyLean.contender_6 42 < contender_7 := by
  have h := orbit_lt_levels_succ 42 (by decide : 7 ≤ 42) 41
  simpa only [base_score, BusyLean.contender_6, contender_7] using h

theorem contender_6_lt_contender_7 : BusyLean.contender_6 < contender_7 :=
  Nat.lt_of_le_of_lt (self_le_towerOrbit BusyLean.contender_6 42)
    towerOrbit_contender6_lt_contender7

theorem p5_lt_contender_7 : BigNumber.contender_6 < contender_7 :=
  Nat.lt_trans BusyLean.p5_lt_contender_6 contender_6_lt_contender_7

theorem contender_5_lt_contender_7 : BusyLean.contender_5 < contender_7 :=
  Nat.lt_trans BusyLean.contender_5_lt_contender_6 contender_6_lt_contender_7

/-! ## The semantic tree index is not definable by its own input language -/

theorem indexed_tree_lt (cs : Nat → World) (seed : Family)
    {k i n : Nat} (hk : k ≤ n) (hi : i ≤ n) :
    BusyLean.W.stage seed
      (programTree cs (BusyLean.nthD (programs k) i (.atom .zero))) n <
      BusyLean.W.stage seed (nextIndex cs) n :=
  Nat.lt_trans
    (BusyLean.W.stage_child_lt seed
      (fun j => programTree cs (BusyLean.nthD (programs k) j (.atom .zero))) hi)
    (BusyLean.W.stage_child_lt seed
      (fun d => .node fun j =>
        programTree cs (BusyLean.nthD (programs d) j (.atom .zero))) hk)

theorem programTree_eventually_lt_index (cs : Nat → World) (seed : Family)
    {p : Program} {k : Nat} (hp : p ∈ programs k) :
    ∃ N, ∀ n, N ≤ n →
      BusyLean.W.stage seed (programTree cs p) n <
      BusyLean.W.stage seed (nextIndex cs) n := by
  obtain ⟨i, hi⟩ := BusyLean.exists_nthD_of_mem (d := Program.atom .zero) hp
  refine ⟨k + i, fun n hn => ?_⟩
  have h := indexed_tree_lt cs seed
    (Nat.le_trans (Nat.le_add_right k i) hn)
    (Nat.le_trans (Nat.le_add_left i k) hn)
  rw [hi] at h
  exact h

theorem no_programTree_eq_index (cs : Nat → World)
    {p : Program} {k : Nat} (hp : p ∈ programs k) :
    programTree cs p ≠ nextIndex cs := by
  intro heq
  obtain ⟨N, hN⟩ := programTree_eventually_lt_index cs BusyLean.p5Family hp
  have hlt := hN N (Nat.le_refl N)
  rw [heq] at hlt
  exact Nat.lt_irrefl _ hlt

/-! ## The local semantic-separation theorem -/

theorem eval_oracleFree (cs : Nat → World) (fs gs : Family) (n : Nat) :
    ∀ p, OracleFree p → eval cs fs n p = eval cs gs n p
  | .old _, _ => rfl
  | .atom a, h => by
      cases a <;> simp_all [OracleFree, eval, atomValue]
  | .app p q, h => by
      change applyValue (eval cs fs n p) (eval cs fs n q) = _
      rw [eval_oracleFree cs fs gs n p h.1,
        eval_oracleFree cs fs gs n q h.2]
      rfl

theorem oracleFree_program_lt_fold (cs : Nat → World) (seed : Family)
    (a : Tree) (n : Nat) {p : Program} (hp : p ∈ programs n)
    (hfree : OracleFree p) :
    evalNat cs (fun _ _ => 0) n p < foldReflect (nextReflect cs) seed a n := by
  have h (fs : Family) :
      evalNat cs (fun _ _ => 0) n p < nextReflect cs fs n := by
    have he : evalNat cs (fun _ _ => 0) n p = evalNat cs fs n p :=
      congrArg natValue (eval_oracleFree cs (fun _ _ => 0) fs n p hfree)
    rw [he]
    exact program_lt_nextReflect cs fs n hp
  cases a with
  | leaf => exact h seed
  | node f => exact h (fun i => foldReflect (nextReflect cs) seed (f i))

/-- The new score eventually exceeds every fixed program using the lower
worlds' full runners and indices, not merely every fixed iterate of a score. -/
theorem lower_language_eventually_lt (cs : Nat → World)
    {p : Program} {k : Nat} (hp : p ∈ programs k) (hfree : OracleFree p) :
    ∀ n, k ≤ n → evalNat cs (fun _ _ => 0) n p < score (extend cs) n :=
  fun n hn => oracleFree_program_lt_fold cs BusyLean.p5Family (nextIndex cs) n
    (mem_programs_mono hn hp) hfree

theorem no_lower_language_representation (cs : Nat → World)
    {p : Program} {k : Nat} (hp : p ∈ programs k) (hfree : OracleFree p) :
    ¬ (∀ n, evalNat cs (fun _ _ => 0) n p = score (extend cs) n) := by
  intro h
  have hlt := lower_language_eventually_lt cs hp hfree k (Nat.le_refl k)
  rw [h k] at hlt
  exact Nat.lt_irrefl _ hlt

/-- No enumerated program can compute this very reflection function at every
input in the same externally supplied oracle context. This is a relative
statement, NOT a universal evaluator or an uncomputable Busy Beaver. -/
theorem no_uniform_self_representation (cs : Nat → World) (fs : Family)
    {p : Program} {k : Nat} (hp : p ∈ programs k) :
    ¬ (∀ n, evalNat cs fs n p = nextReflect cs fs n) := by
  intro h
  have hlt := program_lt_nextReflect cs fs k hp
  rw [h k] at hlt
  exact Nat.lt_irrefl _ hlt

/-- The eventual version uses only persistence of enumeration membership. -/
theorem program_eventually_lt (cs : Nat → World) (fs : Family)
    {p : Program} {k : Nat} (hp : p ∈ programs k) :
    ∀ n, k ≤ n → evalNat cs fs n p < nextReflect cs fs n :=
  fun n hn => program_lt_nextReflect cs fs n (mem_programs_mono hn hp)

end BusyLean.V7
