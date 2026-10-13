import BusyLean.Contender39
open BusyLean BusyLean.Ordinal

/-- Branch 0 of a limit. -/
def branch0 : CTree → CTree
  | .lim g => g 0
  | t => t

def height : CTree → Nat
  | .succ t => height t + 1
  | _ => 0

-- Branch 0 of `mixed` is the jump; branch 0 of a bootstrap step is its input.
#eval height (branch0 (branch0 (mixed 0 (.succ (.succ .zero)))))   -- 0: jump 0 t = bootT along t
#eval hier Nat.succ (branch0 (mixed 0 .zero)) 3                     -- jump 0 zero = zero: 4
