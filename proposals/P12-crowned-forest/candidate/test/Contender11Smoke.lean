import BusyLean.Comparison11

/-! Definitional smoke tests.  None evaluates a contender. -/

namespace BusyLean

example (a : BigNumber.WTree Nat) : crown11 0 a = a := rfl

example (a : BigNumber.WTree Nat) :
    crown11 2 a = .node (fun _ => .node (fun _ => a)) := rfl

example : family10 42 = contender_10 := rfl

example (n : Nat) :
    F11 n = stage11 (fun _ => family10) (crown11 (n + 1) index) n := rfl

#check contender_10_lt_contender_11
#check root_program_lt_F11
#check defined_tree_eventually_lt11

end BusyLean
