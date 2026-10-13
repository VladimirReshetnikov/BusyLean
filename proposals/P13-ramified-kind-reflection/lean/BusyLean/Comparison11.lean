import BusyLean.Contender11
import BusyLean.Comparison10

/-!
# Contender 11: comparison and structural theorems

The required theorem is `contender_10_lt_contender_11`.  The remaining
results record the much larger structural margin: every ramification level
strictly exceeds the preceding one, every fixed level is eventually below the
diagonal family, and every bounded kind-polymorphic program is already beaten
at the base reflection level.
-/

namespace BusyLean

namespace RK

/-- An operator dominates every visible member of its input family. -/
def Dominates (op : Operator) : Prop :=
  ∀ (fs : W.Family) {i n : Nat}, i ≤ n → fs i n < op fs n

/-! ## The base reflector -/

theorem lt_reflect {fs : W.Family} {n m : Nat}
    (h : m ≤ BigNumber.maxN
      (W.prefixMax (fun i => fs i n) n)
      (BigNumber.maximum (Fk.fvalue (packFamily fs) n) (Fk.ctmsUpTo n))) :
    m < reflect fs n := by
  unfold reflect
  omega

/-- Every visible oracle-family value is below one reflection step. -/
theorem oracle_lt_reflect (fs : W.Family) {i n : Nat} (hi : i ≤ n) :
    fs i n < reflect fs n :=
  lt_reflect (Nat.le_trans
    (W.le_prefixMax (fun j => fs j n) hi)
    (BigNumber.le_maxN_left _ _))

/-- Every accepted kind-polymorphic program in the current syntax budget is
below one reflection step. -/
theorem fvalue_lt_reflect (fs : W.Family) {n : Nat} {t : Fk.CTm}
    (ht : t ∈ Fk.ctmsUpTo n) :
    Fk.fvalue (packFamily fs) n t < reflect fs n :=
  lt_reflect (Nat.le_trans
    (W.le_maximum (Fk.fvalue (packFamily fs) n) ht)
    (BigNumber.le_maxN_right _ _))

/-- The input itself is below one reflection step. -/
theorem input_lt_reflect (fs : W.Family) (n : Nat) : n < reflect fs n := by
  unfold reflect
  omega

/-- The base reflector dominates its input family. -/
theorem reflect_dominates : Dominates reflect := by
  intro fs i n hi
  exact oracle_lt_reflect fs hi

/-! ## Generic autonomous lifting -/

/-- A node strictly dominates each visible child whenever the operator used at
that node dominates its input family. -/
theorem lift_child_lt {op : Operator} (hop : Dominates op)
    (seed : W.Family) (g : Nat → BigNumber.WTree Nat) {i n : Nat}
    (hi : i ≤ n) :
    lift op seed (g i) n < lift op seed (.node g) n := by
  change lift op seed (g i) n < op (fun j => lift op seed (g j)) n
  exact hop (fun j => lift op seed (g j)) hi

/-- The autonomous lift strictly exceeds the unlifted operator at every input.
The proof follows the concrete path
`leaf < treesOfDepth 0 < index`. -/
theorem op_lt_autonomous {op : Operator} (hop : Dominates op)
    (seed : W.Family) (n : Nat) :
    op seed n < autonomous op seed n := by
  have h₂ :
      lift op seed
          (defTree (nthD (BigNumber.allTerms 0) 0 .zero)) n <
        lift op seed (treesOfDepth 0) n :=
    lift_child_lt hop seed
      (fun j => defTree (nthD (BigNumber.allTerms 0) j .zero))
      (Nat.zero_le n)
  have h₃ :
      lift op seed (treesOfDepth 0) n < lift op seed index n := by
    simpa [index] using
      (lift_child_lt hop seed treesOfDepth (i := 0) (n := n)
        (Nat.zero_le n))
  have h₂' : op seed n < lift op seed (treesOfDepth 0) n := by
    simpa [first_tree_leaf, lift] using h₂
  exact Nat.lt_trans h₂' h₃

/-- Autonomous lifting preserves family domination. -/
theorem autonomous_dominates {op : Operator} (hop : Dominates op) :
    Dominates (autonomous op) := by
  intro seed i n hi
  exact Nat.lt_trans
    (hop seed (i := i) (n := n) hi)
    (op_lt_autonomous hop seed n)

/-! ## Ramification -/

/-- Every ramification level dominates its input family. -/
theorem ramified_dominates : ∀ r : Nat, Dominates (ramified r)
  | 0 => reflect_dominates
  | r + 1 => by
      simpa [ramified] using autonomous_dominates (ramified_dominates r)

/-- Each successor ramification level is strictly larger than its predecessor
at every seed and input. -/
theorem ramified_level_lt (r : Nat) (seed : W.Family) (n : Nat) :
    ramified r seed n < ramified (r + 1) seed n := by
  change ramified r seed n < autonomous (ramified r) seed n
  exact op_lt_autonomous (ramified_dominates r) seed n

/-- Strict monotonicity in the ramification rank. -/
theorem ramified_lt_of_lt {r s : Nat} (hrs : r < s)
    (seed : W.Family) (n : Nat) :
    ramified r seed n < ramified s seed n := by
  induction s generalizing r with
  | zero => omega
  | succ s ih =>
      by_cases h : r = s
      · subst r
        exact ramified_level_lt s seed n
      · have hrs' : r < s := by omega
        exact Nat.lt_trans (ih hrs') (ramified_level_lt s seed n)

end RK

/-! ## The diagonal contender -/

/-- The inherited family already strictly exceeds its input. -/
theorem input_lt_family10 (n : Nat) : n < family10 n := by
  change n < F10 (F10 n)
  exact Nat.lt_trans
    (Fk.input_lt_reflectFk family9 n)
    (Fk.input_lt_reflectFk family9 (F10 n))

/-- At every input, `F11` exceeds the entire Contender 10 family. -/
theorem family10_lt_F11 (n : Nat) : family10 n < F11 n := by
  unfold F11
  exact RK.ramified_dominates (family10 n + 1)
    (fun _ => family10) (i := 0) (n := n) (Nat.zero_le n)

/-- `F11` strictly exceeds its input. -/
theorem input_lt_F11 (n : Nat) : n < F11 n :=
  Nat.lt_trans (input_lt_family10 n) (family10_lt_F11 n)

/-- Every fixed ramification rank is eventually dominated by the diagonal
family.  In fact input `n ≥ r` suffices. -/
theorem fixed_rank_eventually_lt_F11 (r : Nat) :
    ∀ n : Nat, r ≤ n →
      RK.ramified r (fun _ => family10) n < F11 n := by
  intro n hr
  unfold F11
  apply RK.ramified_lt_of_lt
  exact Nat.lt_of_le_of_lt hr
    (Nat.lt_trans (input_lt_family10 n) (Nat.lt_succ_self _))

/-- Every accepted kind-polymorphic program in the input budget is below the
diagonal family, already because rank zero is below the selected rank. -/
theorem fvalue_lt_F11 {n : Nat} {t : Fk.CTm} (ht : t ∈ Fk.ctmsUpTo n) :
    Fk.fvalue (packFamily (fun _ => family10)) n t < F11 n := by
  have hbase :
      Fk.fvalue (packFamily (fun _ => family10)) n t <
        RK.ramified 0 (fun _ => family10) n := by
    simpa [RK.ramified] using
      (RK.fvalue_lt_reflect (fun _ => family10) ht)
  have hrank :
      RK.ramified 0 (fun _ => family10) n <
        RK.ramified (family10 n + 1) (fun _ => family10) n :=
    RK.ramified_lt_of_lt (by omega) (fun _ => family10) n
  exact Nat.lt_trans hbase (by simpa [F11] using hrank)

/-- At input 42 the chosen ramification rank is exactly one more than the
current accepted contender. -/
theorem F11_rank_at_42 :
    F11 42 = RK.ramified (contender_10 + 1) (fun _ => family10) 42 := rfl

/-- **Required comparison:** Contender 10 is strictly smaller than
Contender 11. -/
theorem contender_10_lt_contender_11 : contender_10 < contender_11 := by
  change family10 42 < F11 (F11 42)
  exact Nat.lt_trans (family10_lt_F11 42) (input_lt_F11 (F11 42))

/-- The entire accepted chain is therefore below Contender 11. -/
theorem contender_9_lt_contender_11 : contender_9 < contender_11 :=
  Nat.lt_trans contender_9_lt_contender_10 contender_10_lt_contender_11

end BusyLean
