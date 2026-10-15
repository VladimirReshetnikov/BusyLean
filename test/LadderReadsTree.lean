import BusyLean.SystemFLT2.Numbers

/-!
# A ladder program that reads its input tree

Run with `lake env lean test/LadderReadsTree.lean`.

Rung 4 of the independent tower reads the trees it builds: its programs are
ladder programs over System FT2's terms (`SystemFLT2`), which recurse over an
input tree at every type. This test checks that a single such program:

* type checks at the numeric reader type `FLT2.natReaderTy` (the verified
  checker `FLT2.infer`), and
* computes more from a larger tree: it is the Hardy hierarchy `H_T(3)` along
  its input tree `T`, and returns `3, 6, 6, 12, 24` on the trees
  `0, 3, ω, ω·2, ω²` (normal-order reduction with a step budget).

A ladder program that does not read its input computes the same number for
every tree, since erasure forgets the atoms of its types.
-/

open BusyLean BusyLean.FL BusyLean.FLT2 BusyLean.Ordinal

abbrev A := Addr (.zero : CTree)

def NN : Ty A := .arr Ty.nat Ty.nat

/-- The Church successor. -/
def SUCC : CTm A := .lam Ty.nat (.tlam .star (.lam (.arr (.tvar 0) (.tvar 0)) (.lam (.tvar 0)
  (.app (.var 1) (.app (.app (.tapp (.var 2) (.tvar 0)) (.var 1)) (.var 0))))))

/-- The Church numeral `k`. -/
def NUM (k : Nat) : CTm A := .tlam .star (.lam (.arr (.tvar 0) (.tvar 0)) (.lam (.tvar 0) (iter k)))
where iter : Nat → CTm A
  | 0 => .var 0
  | k + 1 => .app (.var 1) (iter k)

/-- `H_0 = id`, `H_{a+1}(y) = H_a(y + 1)`, `H_{lim f}(y) = H_{f y}(y)`. -/
def Z : CTm A := .lam Ty.nat (.var 0)
def S : CTm A := .lam NN (.lam Ty.nat (.app (.var 1) (.app SUCC (.var 0))))
def L : CTm A := .lam (.arr Ty.nat NN) (.lam Ty.nat (.app (.app (.var 1) (.var 0)) (.var 0)))

/-- `ΛX. λ rec x. rec [nat → nat] Z S L x k`: the Hardy hierarchy along the input tree at `k`. -/
def hardyReader (k : Nat) : CTm A :=
  .tlam .star (.lam recTy (.lam (.tvar 0)
    (.app (.app (.app (.app (.app (.tapp (.var 1) NN) Z) S) L) (.var 0)) (NUM k))))

#guard infer 50 [] [] (hardyReader 3) == some natReaderTy

/-- Normal-order reduction with oracle tree `T`, for at most `fuel` steps. -/
def run (T : CTree) (fuel : Nat) (t : FT2.Tm) : Option Nat :=
  (go fuel t).bind FT2.Tm.num?
where go : Nat → FT2.Tm → Option FT2.Tm
  | 0, _ => none
  | n + 1, u =>
      match FT2.nstep ⟨Nat.succ, T⟩ u with
      | none => some u
      | some v => go n v

def finT : Nat → CTree
  | 0 => .zero
  | k + 1 => .succ (finT k)

def plusT (a : CTree) : CTree → CTree
  | .zero => a
  | .succ b => .succ (plusT a b)
  | .lim f => .lim fun i => plusT a (f i)
  | t => t

def omegaT : CTree := .lim finT

def omegaMul : Nat → CTree
  | 0 => .zero
  | k + 1 => plusT (omegaMul k) omegaT

def omegaSq : CTree := .lim omegaMul

def prog : FT2.Tm := applyNatReader (erase (hardyReader 3))

#guard run (finT 0) 200000 prog == some 3
#guard run (finT 3) 200000 prog == some 6
#guard run omegaT 200000 prog == some 6
#guard run (omegaMul 2) 200000 prog == some 12
#guard run omegaSq 200000 prog == some 24
