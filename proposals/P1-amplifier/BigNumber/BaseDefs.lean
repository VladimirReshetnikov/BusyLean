import BigNumber.BaselineDefs

namespace BigNumber

/-- Inclusive running sum of the total-language envelopes. -/
def prefixEnvelope : Nat → Nat
  | 0 => Baseline.envelope 0
  | n + 1 => prefixEnvelope n + Baseline.envelope (n + 1)

/-- A constructive, inflationary base defined independently of any contender. -/
def base (n : Nat) : Nat := Nat.succ (prefixEnvelope n + n)

end BigNumber
