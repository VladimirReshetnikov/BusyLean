import BusyLean.Independent.Ackermann
import BusyLean.Independent.SystemT
import BusyLean.Independent.SystemTFacts

/-!
# Rung 1 < rung 2: Ackermann is a System T program

A port of the proof of `contender_4_lt_contender_5` in the original Coq file.
The Ackermann function is written as a System T term `ackT` (using natural
recursion at types `nat → nat` and `nat → nat → nat`), together with the
arguments `5`, `6 · 7` and `10^4 + 2`. One more `succ` gives a closed program
of depth `≤ 42` whose value is `ack 5 42 10002 + 1`, so the maximum over all
programs of depth `42` exceeds rung 1.

Terms use Contender 5's *reversed* de Bruijn indices (`var 0` is the outermost
binder), so the combinators below are parametrized by the depth `d` of the
environment they are placed in.
-/

namespace BusyLean.Indep

open BusyLean.C5

/-! ## Arithmetic by natural recursion (Coq's `add'`, `mul'`, `pow'`, `ack'`) -/

def add' : Nat → Nat → Nat :=
  recursion (fun m => m) (fun _ rec m => Nat.succ (rec m))

def mul' : Nat → Nat → Nat :=
  recursion (fun _ => 0) (fun _ rec m => add' m (rec m))

def pow' (n : Nat) : Nat → Nat :=
  recursion 1 (fun _ rec => mul' n rec)

def ack' (n : Nat) : Nat → Nat → Nat :=
  recursion (fun _ b => Nat.succ b)
    (fun pred0 _ =>
      recursion add' (fun _ rec => fun a b => recursion 1 (fun _ rec1 => rec a rec1) b) pred0)
    n

theorem add'_eq : ∀ n m, add' n m = n + m
  | 0, m => (Nat.zero_add m).symm
  | n + 1, m => by
      show Nat.succ (add' n m) = n + 1 + m
      rw [add'_eq n m]; omega

theorem mul'_eq : ∀ n m, mul' n m = n * m
  | 0, m => (Nat.zero_mul m).symm
  | n + 1, m => by
      show add' m (mul' n m) = (n + 1) * m
      rw [add'_eq, mul'_eq n m, Nat.succ_mul]; omega

theorem pow'_eq (n : Nat) : ∀ m, pow' n m = n ^ m
  | 0 => rfl
  | m + 1 => by
      show mul' n (pow' n m) = n ^ (m + 1)
      rw [mul'_eq, pow'_eq n m, Nat.pow_succ, Nat.mul_comm]

theorem iter_eq_recursion (f : Nat → Nat) : ∀ b, recursion 1 (fun _ r => f r) b = iter f b
  | 0 => rfl
  | b + 1 => congrArg f (iter_eq_recursion f b)

theorem ack'_eq : ∀ n a b, ack' n a b = ack n a b
  | 0, _, _ => rfl
  | 1, a, b => add'_eq a b
  | n + 2, a, b => by
      show recursion 1 (fun _ rec1 => ack' (n + 1) a rec1) b = iter (ack (n + 1) a) b
      have h : (fun (_ : Nat) (rec1 : Nat) => ack' (n + 1) a rec1) =
          fun _ rec1 => ack (n + 1) a rec1 := by
        funext _ r; exact ack'_eq (n + 1) a r
      rw [h, iter_eq_recursion]

/-! ## The terms -/

/-- `add'` in an environment of depth `d`. -/
def addT (d : Nat) : Term :=
  .app (.app (.natRec N2) (.lam N N (.var d)))
    (.lam N (.arr N2 N2) (.lam N2 N2 (.lam N N (.app .succ (.app (.var (d + 1)) (.var (d + 2)))))))

/-- `mul'` in an environment of depth `d`. -/
def mulT (d : Nat) : Term :=
  .app (.app (.natRec N2) (.lam N N .zero))
    (.lam N (.arr N2 N2) (.lam N2 N2 (.lam N N
      (.app (.app (addT (d + 3)) (.var (d + 2))) (.app (.var (d + 1)) (.var (d + 2)))))))

/-- `pow'` in an environment of depth `d`. -/
def powT (d : Nat) : Term :=
  .lam N N2 (.app (.app (.natRec N) (numT 1))
    (.lam N (.arr N N) (.lam N N (.app (.app (mulT (d + 3)) (.var d)) (.var (d + 2))))))

/-- `ack'` in an environment of depth `d`. -/
def ackT (d : Nat) : Term :=
  .app (.app (.natRec N3) (.lam N N2 (.lam N N (.app .succ (.var (d + 1))))))
    (.lam N (.arr N3 N3) (.lam N3 N3
      (.app (.app (.app (.natRec N3) (addT (d + 2)))
        (.lam N (.arr N3 N3) (.lam N3 N3 (.lam N N2 (.lam N N
          (.app (.app (.app (.natRec N) (numT 1))
            (.lam N (.arr N N) (.lam N N
              (.app (.app (.var (d + 3)) (.var (d + 4))) (.var (d + 7))))))
            (.var (d + 5))))))))
        (.var d))))

theorem interp_addT : interp [] (addT 0) = ⟨N3, add'⟩ := rfl

theorem interp_mulT : interp [] (mulT 0) = ⟨N3, mul'⟩ := rfl

theorem interp_powT : interp [] (powT 0) = ⟨N3, pow'⟩ := rfl

theorem interp_ackT : interp [] (ackT 0) = ⟨.arr .nat N3, ack'⟩ := rfl

/-- `ack' 5 (mul' 6 7) (succ (succ (pow' 10 4)))`, Coq's `contender_4''`. -/
def ackProgram : Term :=
  .app (.app (.app (ackT 0) (numT 5)) (.app (.app (mulT 0) (numT 6)) (numT 7)))
    (.app .succ (.app .succ (.app (.app (powT 0) (numT 10)) (numT 4))))

theorem interp_ackProgram :
    interp [] ackProgram =
      (⟨.nat, ack' 5 (mul' 6 7) (Nat.succ (Nat.succ (pow' 10 4)))⟩ : Value) := by
  have h1 := interp_app interp_ackT (interp_numT [] 5)
  have h3 := interp_app (interp_app interp_mulT (interp_numT [] 6)) (interp_numT [] 7)
  have h5 := interp_app (interp_app interp_powT (interp_numT [] 10)) (interp_numT [] 4)
  have h7 := interp_app (interp_succ []) (interp_app (interp_succ []) h5)
  unfold ackProgram
  exact (interp_app (interp_app h1 h3) h7 :)

theorem eval_ackProgram : eval (.app .succ ackProgram) = Nat.succ (ack 5 42 10002) := by
  have h := eval_of_interp (interp_app (interp_succ []) interp_ackProgram :)
  have e1 : mul' 6 7 = 42 := by rw [mul'_eq]
  have e2 : Nat.succ (Nat.succ (pow' 10 4)) = 10002 := by rw [pow'_eq]
  rw [h, e1, e2, ack'_eq]

/-! ## The comparison -/

set_option maxRecDepth 10000 in
theorem depth_succ_ackProgram : depth (.app .succ ackProgram) ≤ 42 :=
  Nat.le_of_ble_eq_true rfl

/-- **Rung 1 < rung 2.** -/
theorem contender_1_lt_contender_2 : contender_1 < contender_2 := by
  have h := eval_le_largest depth_succ_ackProgram
  rw [eval_ackProgram] at h
  unfold contender_1 contender_2
  exact Nat.lt_of_succ_le h

end BusyLean.Indep
