import BusyLean.Ordinal.SortedLex
import BusyLean.SystemFL.Transfinite

/-!
# Atoms below `ω^ω`

A sorted (non-increasing) list of natural numbers `[a₁, …, a_k]` denotes
`ω^a₁ + ⋯ + ω^a_k`. With the lexicographic order these are notations for the
ordinals below `ω^ω`, and `SortedLex` proves the order well-founded. They serve
as the atoms of a transfinite ladder: the universe `wfUniv f omegaPow_wf` has
one level for every ordinal below `ω^ω`.
-/

namespace BusyLean.Ordinal

def natLt (a b : Nat) : Bool := decide (a < b)

theorem acc_nat : ∀ n : Nat, Acc (LT' natLt) n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih => exact Acc.intro n fun m h => ih m (of_decide_eq_true h)

/-- Notations for the ordinals below `ω^ω`. -/
def OmegaPow : Type := {l : List Nat // sorted natLt l = true}

instance : DecidableEq OmegaPow := fun a b =>
  if h : a.1 = b.1 then isTrue (Subtype.ext h) else isFalse (fun e => h (congrArg Subtype.val e))

instance : FL.AtomOrder OmegaPow := ⟨fun a b => llt natLt a.1 b.1⟩

theorem omegaPow_wf : WellFounded (FL.ALt (α := OmegaPow)) := wf_sorted acc_nat

/-- Lists of length `≤ L` with entries below `m`. -/
def listsUpTo (m : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | L + 1 => [] :: (List.range m).flatMap fun x => (listsUpTo m L).map (x :: ·)

/-- Atoms of enumeration depth `n`: notations with `≤ n` terms and exponents `< n`. -/
def omegaPowUpTo (n : Nat) : List OmegaPow :=
  (listsUpTo n n).filterMap fun l => if h : sorted natLt l = true then some ⟨l, h⟩ else none

end BusyLean.Ordinal
