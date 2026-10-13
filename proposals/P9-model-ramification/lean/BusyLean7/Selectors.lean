import BusyLean7.Comparison

/-! Explicit access to every child model, with a calculable syntax overhead. -/
namespace BusyLean7
open BigNumber (Term)

def numeral : Nat → Term
  | 0 => .zero
  | k + 1 => .app .succ (numeral k)

theorem numeral_rank (k : Nat) : termRank (numeral k) = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [numeral, termRank, ih]
      omega

theorem amplified_rank (s : Term) :
    termRank (amplifiedCall s) = Nat.max 11 (termRank s + 5) := by
  simp only [amplifiedCall, callAt, termRank]
  omega

theorem numeral_certificate_mem {n k : Nat} (hn : 11 ≤ n) (hk : k + 6 ≤ n) :
    amplifiedCall (numeral k) ∈ BigNumber.allTerms n := by
  apply term_mem
  rw [amplified_rank, numeral_rank]
  omega

theorem interpret_numeral (env : BigNumber.Env) (k : Nat) :
    BigNumber.interpret env (numeral k) = ⟨.nat, k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      exact interpret_app_exact
        (show BigNumber.interpret env Term.succ = ⟨.arr .nat .nat, Nat.succ⟩ from rfl) ih

theorem eval_amplified_numeral (M : Model) (fs : Family) (n k : Nat) :
    eval M fs n (amplifiedCall (numeral k)) =
      theta (M.lowerStage k BusyLean.p5Family (M.lowerTree k) n) :=
  congrArg score (interpret_amplified M fs n k (numeral k)
    (interpret_numeral (modelEnv M fs n) k))

theorem amplified_numeral_lt_value (M : Model) {n k : Nat}
    (hn : 11 ≤ n) (hk : k + 6 ≤ n) :
    theta (M.lowerStage k BusyLean.p5Family (M.lowerTree k) n) < value M n :=
  uniform_lt_stage M BusyLean.p5Family (modelIndex M)
    (numeral_certificate_mem hn hk) (fun fs => eval_amplified_numeral M fs n k)

theorem join_child_margin (base : Model) (children : Nat → Model)
    {n i : Nat} (hn : 11 ≤ n) (hi : i + 7 ≤ n) :
    theta (value (children i) n) < value (join base children) n := by
  have h := amplified_numeral_lt_value (join base children) hn (k := i + 1) hi
  simpa only [join, value] using h

theorem ramify_child_margin (base : Model) (f : Nat → Tree)
    {n i : Nat} (hn : 11 ≤ n) (hi : i + 7 ≤ n) :
    theta (value (ramify base (f i)) n) < value (ramify base (.node f)) n := by
  let children := fun j => ramify base (f j)
  have h0 := join_child_margin base children hn hi
  have h1 := omega_base_margin (join base children) hn
  exact Nat.lt_trans h0 (Nat.lt_trans (self_lt_theta _) h1)

theorem ramify_child_lt (base : Model) (f : Nat → Tree)
    {n i : Nat} (hn : 11 ≤ n) (hi : i + 7 ≤ n) :
    value (ramify base (f i)) n < value (ramify base (.node f)) n :=
  Nat.lt_trans (self_lt_theta _) (ramify_child_margin base f hn hi)

end BusyLean7
