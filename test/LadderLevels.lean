import BusyLean.SystemFLV.Numbers

/-!
# Experiment: ladder programs with universe levels, on short and long trees

Run with `lake env lean test/LadderLevels.lean`.

`SystemFLV` is the ladder over System FT2's terms, extended with level
variables: bounded quantification `∀b ≤ l. A`, level-indexed operators
`λb ≤ l. A` with their applications, and atoms at level variables. Its
programs are checked by the verified checker `FLV.infer` and run by
normal-order reduction with the tree `T` as oracle. The atoms are the
addresses of `T`, ordered by descent.

Ten programs. The first five use the level features and do not read the
tree; the last five read it.

1. `levelId`: level abstraction and application, `(Λb ≤ root. λx. x) root 3`.
2. `twoLevels`: nested bounds, `Λb ≤ root. Λc ≤ b. λx. x`.
3. `familyOp`: a level-indexed operator `F = λb ≤ root. nat → nat`; the
   argument type `F root` converts to `nat → nat`.
4. `packedLevel`: a type packed into the atom at a level variable and unpacked.
5. `packBelow`: under `b ≤ kid`, the kind `atom b` fits the atom `root`
   because `b ≤ kid < root`. It type checks only when `kid` is a valid
   address, i.e. not on the empty tree.
6. `hardyReader`: the Hardy hierarchy along the input tree, `H_T(3)`.
7. `constReader`: a reader that ignores its input.
8. `levelReader`: the Hardy reader under a level abstraction.
9. `familyReader`: the Hardy reader whose recursor is instantiated at the
   level-indexed family `F root`.
10. `twiceReader`: `H_T(H_T(3))`.

Findings. The level programs 1-5 compute the same number on every tree on
which they type check: their typing uses only the named atoms, and erasure
forgets levels. The readers 6, 8, 9, 10 compute more from longer trees. So
levels give a richer *language*, and reading gives *growth*; rung 4 of the
independent tower uses both.
-/

open BusyLean BusyLean.FLV BusyLean.Ordinal

section Programs

variable {α : Type}

def NN : Ty α := .arr Ty.nat Ty.nat

/-- The Church successor. -/
def SUCC : CTm α := .lam Ty.nat (.tlam .star (.lam (.arr (.tvar 0) (.tvar 0)) (.lam (.tvar 0)
  (.app (.var 1) (.app (.app (.tapp (.var 2) (.tvar 0)) (.var 1)) (.var 0))))))

/-- The Church numeral `k`. -/
def NUM (k : Nat) : CTm α := .tlam .star (.lam (.arr (.tvar 0) (.tvar 0)) (.lam (.tvar 0) (iter k)))
where iter : Nat → CTm α
  | 0 => .var 0
  | k + 1 => .app (.var 1) (iter k)

/-- `H_0 = id`, `H_{a+1}(y) = H_a(y + 1)`, `H_{lim f}(y) = H_{f y}(y)`. -/
def Z : CTm α := .lam Ty.nat (.var 0)
def S : CTm α := .lam NN (.lam Ty.nat (.app (.var 1) (.app SUCC (.var 0))))
def L : CTm α := .lam (.arr Ty.nat NN) (.lam Ty.nat (.app (.app (.var 1) (.var 0)) (.var 0)))

/-- `rec [Y] Z S L x`, with the recursor `var 1` and the input `var 0`. -/
def hardyAt (Y : Ty α) : CTm α := .app (.app (.app (.app (.tapp (.var 1) Y) Z) S) L) (.var 0)

/-- `ΛX. λ rec x. body`. -/
def reader (body : CTm α) : CTm α := .tlam .star (.lam recTy (.lam (.tvar 0) body))

end Programs

section Levels

variable (T : CTree)

def root : Lvl (Addr T) := .const TreePath.root
def kid : Lvl (Addr T) := .const (TreePath.child .root 0)

/-- The family `λb ≤ root. nat → nat`. -/
def F : Ty (Addr T) := .llam (root T) NN

def levelId : CTm (Addr T) :=
  .app (.lapp (.llam (root T) (.lam Ty.nat (.var 0))) (root T)) (NUM 3)

def twoLevels : CTm (Addr T) :=
  .app (.lapp (.lapp (.llam (root T) (.llam (.var 0) (.lam Ty.nat (.var 0)))) (root T)) (root T))
    (NUM 4)

def familyOp : CTm (Addr T) :=
  .app (.lam (.lapp (root T) (F T) (root T)) (.app (.var 0) (NUM 2))) SUCC

def packedLevel : CTm (Addr T) :=
  .app (.lapp (.llam (root T)
    (.lam (.aunpack (.var 0) .star (.apack (.var 0) .star Ty.nat)) (.var 0))) (root T)) (NUM 4)

/-- `x : unpack_b (unpack_root (pack_root (pack_b nat)))`, under `b ≤ kid`. -/
def packBelow : CTm (Addr T) :=
  .app (.lapp (.llam (kid T)
    (.lam (.aunpack (.var 0) .star (.aunpack (root T) (.atom (.var 0))
      (.apack (root T) (.atom (.var 0)) (.apack (.var 0) .star Ty.nat)))) (.var 0))) (kid T))
    (NUM 5)

def hardyReader : CTm (Addr T) := reader (.app (hardyAt NN) (NUM 3))

def constReader : CTm (Addr T) := reader (NUM 7)

def levelReader : CTm (Addr T) := .lapp (.llam (root T) (hardyReader T)) (root T)

def familyReader : CTm (Addr T) := reader (.app (hardyAt (.lapp (root T) (F T) (root T))) (NUM 3))

def twiceReader : CTm (Addr T) := reader (.app (hardyAt NN) (.app (hardyAt NN) (NUM 3)))

end Levels

/-! ## Trees -/

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

/-! ## Type checking (the verified checker, fuel 50) -/

def checks (T : CTree) (p : CTm (Addr T)) (A : Ty (Addr T)) : Bool :=
  infer 50 [] [] [] p == some A

#guard checks (finT 3) (levelId _) Ty.nat
#guard checks (finT 3) (twoLevels _) Ty.nat
#guard checks (finT 3) (familyOp _) Ty.nat
#guard checks (finT 3) (packedLevel _) Ty.nat
#guard checks (finT 3) (packBelow _) Ty.nat
#guard checks omegaSq (packBelow _) Ty.nat
-- `kid` is not an address of the empty tree, so `atom b` does not fit `root` there.
#guard !checks (finT 0) (packBelow _) Ty.nat
#guard checks (finT 0) (levelId _) Ty.nat
#guard checks (finT 3) (hardyReader _) natReaderTy
#guard checks (finT 3) (constReader _) natReaderTy
#guard checks (finT 3) (levelReader _) natReaderTy
#guard checks (finT 3) (familyReader _) natReaderTy
#guard checks (finT 3) (twiceReader _) natReaderTy

/-! ## Values (normal-order reduction with a step budget) -/

/-- Normal-order reduction with oracle tree `T`, for at most `fuel` steps. -/
def run (T : CTree) (fuel : Nat) (t : FT2.Tm) : Option Nat :=
  (go fuel t).bind FT2.Tm.num?
where go : Nat → FT2.Tm → Option FT2.Tm
  | 0, _ => none
  | n + 1, u =>
      match FT2.nstep ⟨Nat.succ, T⟩ u with
      | none => some u
      | some v => go n v

def value (T : CTree) (p : CTm (Addr T)) : Option Nat := run T 400000 (erase p)

def readValue (T : CTree) (p : CTm (Addr T)) : Option Nat :=
  run T 400000 (FLT2.applyNatReader (erase p))

-- Level programs: the same number on short and long trees.
#guard value (finT 1) (levelId _) == some 3 && value omegaSq (levelId _) == some 3
#guard value (finT 1) (twoLevels _) == some 4 && value omegaSq (twoLevels _) == some 4
#guard value (finT 1) (familyOp _) == some 3 && value omegaSq (familyOp _) == some 3
#guard value (finT 1) (packedLevel _) == some 4 && value omegaSq (packedLevel _) == some 4
#guard value (finT 1) (packBelow _) == some 5 && value omegaSq (packBelow _) == some 5
#guard readValue (finT 1) (constReader _) == some 7 && readValue omegaSq (constReader _) == some 7

-- Readers: more from longer trees.
#guard readValue (finT 0) (hardyReader _) == some 3
#guard readValue (finT 3) (hardyReader _) == some 6
#guard readValue omegaT (hardyReader _) == some 6
#guard readValue (omegaMul 2) (hardyReader _) == some 12
#guard readValue omegaSq (hardyReader _) == some 24
#guard readValue (omegaMul 2) (levelReader _) == some 12
#guard readValue omegaSq (levelReader _) == some 24
#guard readValue (omegaMul 2) (familyReader _) == some 12
#guard readValue omegaSq (familyReader _) == some 24
#guard readValue (finT 0) (twiceReader _) == some 3
#guard readValue (finT 3) (twiceReader _) == some 9
#guard readValue omegaT (twiceReader _) == some 12
#guard readValue (omegaMul 2) (twiceReader _) == some 48
