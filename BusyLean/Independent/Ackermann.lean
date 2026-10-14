/-!
# Independent tower, rung 1: a three-argument Ackermann function

The first rung of the independent tower is codyroux's Contender 4 of the
original Coq contest (`docs/name-the-biggest-number-master/Contender.v`),
ported definition by definition. The idea is **nested recursion on numbers**:
level `n + 1` iterates level `n`.

This file imports nothing. **Do not evaluate `contender_1`.**
-/

namespace BusyLean.Indep

/-- `iter f b = f^b 1` (Coq's `iter`). -/
def iter (f : Nat → Nat) : Nat → Nat
  | 0 => 1
  | b + 1 => f (iter f b)

/-- Coq's `ack`: `ack 0 a b = b + 1`, `ack 1 a b = a + b`, and level `n + 2`
iterates level `n + 1` (multiplication, exponentiation, towers, …). -/
def ack : Nat → Nat → Nat → Nat
  | 0, _, b => b + 1
  | 1, a, b => a + b
  | n + 2, a, b => iter (ack (n + 1) a) b

/-- **Rung 1** (Contender 4 of the Coq contest): `ack 5 42 10002`. -/
def contender_1 : Nat := ack 5 42 10002

end BusyLean.Indep
