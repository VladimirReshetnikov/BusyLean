import Oracle
import Trees

namespace Biggest

/-- Finite sampling at a limit; all sampled branches contribute. -/
def hierarchy : Stage → Nat → Nat
  | .zero, n => n + 1
  | .succ a, n => reflect (hierarchy a) n
  | .lim s, n => maximum (fun k => hierarchy (s k) n) (natsUpTo (n + 1)) + 1

/-- The submitted closed natural number. No previous contender occurs here. -/
def contender_6 : Nat := hierarchy finalStage 43

end Biggest
