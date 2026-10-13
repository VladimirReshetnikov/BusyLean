import BusyLean.Comparison54

namespace BusyLean

/-- The semantic order-two branch computes ordinary iteration. -/
example : largeElim Nat.succ (ramify .zero 1) 3 = 6 := rfl

/-- A limit observes its first `n+1` branches. -/
example :
    largeElim Nat.succ (.lim fun i => if i = 0 then .zero else .succ .zero) 2 = 3 := rfl

-- The formal comparison theorems have the intended closed statements.
#check contender_53_lt_contender_54
#check iter_contender_53_lt_contender_54
#check ramified_core_le_F54

end BusyLean
