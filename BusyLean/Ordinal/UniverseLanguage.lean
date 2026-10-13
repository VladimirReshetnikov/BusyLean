import BusyLean.Ordinal.RelUniverses

/-!
# A total language with first-class universes

The existing tree languages manipulate natural numbers, countable ordinal
codes, and functions.  Universe builders remain meta-level Lean definitions.
This module adds a genuinely new object-language base type, `univ`, interpreted
by `U2.Univ`, together with constructors for universe formation, closure at the
universe and universe-operator levels, and collapse relative to a program-built
tree operator.

The language is simply typed and its interpreter is structural.  Every closed
program therefore denotes constructively.  Raw programs of bounded depth form
a finite list, so their output trees may be joined into one computable tree.
-/

namespace BusyLean.Ordinal

namespace UL

/-- Object-language types.  `univ` is the new base kind. -/
inductive Ty where
  | nat : Ty
  | tree : Ty
  | univ : Ty
  | arr : Ty → Ty → Ty
  deriving DecidableEq

/-- Semantic interpretation.  Universe values force the codomain to `Type 1`.
The small base types are lifted uniformly into that universe. -/
def Ty.den : Ty → Type 1
  | .nat => ULift Nat
  | .tree => ULift CTree
  | .univ => U2.Univ
  | .arr a b => a.den → b.den

/-- Intrinsically typed de Bruijn variables. -/
inductive Var : List Ty → Ty → Type where
  | here : Var (a :: Γ) a
  | there : Var Γ a → Var (b :: Γ) a

/-- Intrinsically typed terms.

`tin` is the input tree and `jin` is the input closure operator.  The remaining
new constants expose universe construction to object-language programs.
-/
inductive Tm : List Ty → Ty → Type where
  | var : Var Γ a → Tm Γ a
  | lam : Tm (a :: Γ) b → Tm Γ (.arr a b)
  | app : Tm Γ (.arr a b) → Tm Γ a → Tm Γ b
  | zero : Tm Γ .nat
  | succ : Tm Γ .nat → Tm Γ .nat
  | natRec : Tm Γ a → Tm Γ (.arr a a) → Tm Γ .nat → Tm Γ a
  | tzero : Tm Γ .tree
  | tsucc : Tm Γ .tree → Tm Γ .tree
  | tlim : Tm Γ (.arr .nat .tree) → Tm Γ .tree
  | treeRec : Tm Γ a → Tm Γ (.arr a a) →
      Tm Γ (.arr (.arr .nat a) a) → Tm Γ .tree → Tm Γ a
  | tin : Tm Γ .tree
  | jin : Tm Γ (.arr .tree .tree)
  | ubase : Tm Γ .univ
  | unext : Tm Γ .univ → Tm Γ .univ
  | uunion : Tm Γ (.arr .nat .univ) → Tm Γ .univ
  | uphi : Tm Γ (.arr .univ .univ) → Tm Γ .univ → Tm Γ .univ
  | uopClose :
      Tm Γ (.arr (.arr .univ .univ) (.arr .univ .univ)) →
      Tm Γ (.arr .univ .univ) → Tm Γ (.arr .univ .univ)
  | uindex : Tm Γ .tree → Tm Γ .univ
  | ucollapse : Tm Γ (.arr .tree .tree) → Tm Γ .univ → Tm Γ .tree

/-- Semantic environments. -/
def Env : List Ty → Type 1
  | [] => ULift Unit
  | a :: Γ => a.den × Env Γ

/-- The unique closed environment. -/
def emptyEnv : Env [] := ULift.up ()

def Var.get : Var Γ a → Env Γ → a.den
  | .here, (x, _) => x
  | .there v, (_, ρ) => v.get ρ

/-- Iteration at an arbitrary semantic type. -/
def natIter {α : Type 1} (z : α) (s : α → α) : Nat → α
  | 0 => z
  | n + 1 => s (natIter z s n)

/-- Structural iteration over countable trees at an arbitrary semantic type. -/
def treeIter {α : Type 1} (z : α) (s : α → α)
    (l : (ULift Nat → α) → α) : CTree → α
  | .zero => z
  | .succ t => s (treeIter z s l t)
  | .lim f => l fun n => treeIter z s l (f n.down)
  | .supL _ => z
  | .supH _ => z

/-- Total semantic interpreter.

The two parameters are the input closure operator and input tree.  In
particular, `ucollapse` may collapse any universe constructed by the program
relative to any tree operator constructed by the same program.
-/
def Tm.eval (jinF : CTree → CTree) (tinT : CTree) :
    Tm Γ a → Env Γ → a.den
  | .var v, ρ => v.get ρ
  | .lam t, ρ => fun x => t.eval jinF tinT (x, ρ)
  | .app t u, ρ => (t.eval jinF tinT ρ) (u.eval jinF tinT ρ)
  | .zero, _ => ULift.up 0
  | .succ t, ρ => ULift.up (Nat.succ (t.eval jinF tinT ρ).down)
  | .natRec z s n, ρ =>
      natIter (z.eval jinF tinT ρ) (s.eval jinF tinT ρ)
        (n.eval jinF tinT ρ).down
  | .tzero, _ => ULift.up (Tre.zero : CTree)
  | .tsucc t, ρ =>
      ULift.up (Tre.succ (t.eval jinF tinT ρ).down : CTree)
  | .tlim f, ρ =>
      ULift.up (Tre.lim (fun n =>
        (f.eval jinF tinT ρ (ULift.up n)).down) : CTree)
  | .treeRec z s l t, ρ =>
      treeIter (z.eval jinF tinT ρ) (s.eval jinF tinT ρ)
        (l.eval jinF tinT ρ) (t.eval jinF tinT ρ).down
  | .tin, _ => ULift.up tinT
  | .jin, _ => fun t => ULift.up (jinF t.down)
  | .ubase, _ => U2.Univ.base
  | .unext u, ρ => U2.Univ.next (u.eval jinF tinT ρ)
  | .uunion f, ρ =>
      U2.Univ.union fun n => f.eval jinF tinT ρ (ULift.up n)
  | .uphi f u, ρ => U2.Φ (f.eval jinF tinT ρ) (u.eval jinF tinT ρ)
  | .uopClose f g, ρ =>
      U2.closureA 1 (f.eval jinF tinT ρ) (g.eval jinF tinT ρ)
  | .uindex t, ρ =>
      let T := (t.eval jinF tinT ρ).down
      U2.transTypeUniv (U2.ΦT T) T
  | .ucollapse j u, ρ =>
      ULift.up (U2.universeTreeJ (u.eval jinF tinT ρ)
        (fun t => (j.eval jinF tinT ρ (ULift.up t)).down))

/-! ## Raw syntax and decidable type checking -/

/-- Raw terms; lambdas carry their argument type. -/
inductive Raw where
  | var : Nat → Raw
  | lam : Ty → Raw → Raw
  | app : Raw → Raw → Raw
  | zero : Raw
  | succ : Raw → Raw
  | natRec : Raw → Raw → Raw → Raw
  | tzero : Raw
  | tsucc : Raw → Raw
  | tlim : Raw → Raw
  | treeRec : Raw → Raw → Raw → Raw → Raw
  | tin : Raw
  | jin : Raw
  | ubase : Raw
  | unext : Raw → Raw
  | uunion : Raw → Raw
  | uphi : Raw → Raw → Raw
  | uopClose : Raw → Raw → Raw
  | uindex : Raw → Raw
  | ucollapse : Raw → Raw → Raw

def lookup : (Γ : List Ty) → Nat → Option (Σ a, Var Γ a)
  | [], _ => none
  | a :: _, 0 => some ⟨a, .here⟩
  | _ :: Γ, n + 1 =>
      (lookup Γ n).map fun ⟨a, v⟩ => ⟨a, .there v⟩

/-- Cast an intrinsically typed term after a decidable type equality check. -/
def cast? {Γ : List Ty} {a : Ty} (b : Ty) (t : Tm Γ a) :
    Option (Tm Γ b) :=
  if h : a = b then some (h ▸ t) else none

/-- Decidable type inference. -/
def infer (Γ : List Ty) : Raw → Option (Σ a, Tm Γ a)
  | .var n => (lookup Γ n).map fun ⟨a, v⟩ => ⟨a, .var v⟩
  | .lam a r =>
      (infer (a :: Γ) r).map fun ⟨b, t⟩ => ⟨.arr a b, .lam t⟩
  | .app r s => do
      let ⟨ab, t⟩ ← infer Γ r
      let ⟨_, u⟩ ← infer Γ s
      match ab, t with
      | .arr a b, t => do
          let u' ← cast? a u
          pure ⟨b, .app t u'⟩
      | _, _ => none
  | .zero => some ⟨.nat, .zero⟩
  | .succ r => do
      let ⟨_, t⟩ ← infer Γ r
      let t' ← cast? .nat t
      pure ⟨.nat, .succ t'⟩
  | .natRec z s n => do
      let ⟨a, tz⟩ ← infer Γ z
      let ⟨_, ts⟩ ← infer Γ s
      let ⟨_, tn⟩ ← infer Γ n
      let ts' ← cast? (.arr a a) ts
      let tn' ← cast? .nat tn
      pure ⟨a, .natRec tz ts' tn'⟩
  | .tzero => some ⟨.tree, .tzero⟩
  | .tsucc r => do
      let ⟨_, t⟩ ← infer Γ r
      let t' ← cast? .tree t
      pure ⟨.tree, .tsucc t'⟩
  | .tlim r => do
      let ⟨_, t⟩ ← infer Γ r
      let t' ← cast? (.arr .nat .tree) t
      pure ⟨.tree, .tlim t'⟩
  | .treeRec z s l r => do
      let ⟨a, tz⟩ ← infer Γ z
      let ⟨_, ts⟩ ← infer Γ s
      let ⟨_, tl⟩ ← infer Γ l
      let ⟨_, tr⟩ ← infer Γ r
      let ts' ← cast? (.arr a a) ts
      let tl' ← cast? (.arr (.arr .nat a) a) tl
      let tr' ← cast? .tree tr
      pure ⟨a, .treeRec tz ts' tl' tr'⟩
  | .tin => some ⟨.tree, .tin⟩
  | .jin => some ⟨.arr .tree .tree, .jin⟩
  | .ubase => some ⟨.univ, .ubase⟩
  | .unext r => do
      let ⟨_, t⟩ ← infer Γ r
      let t' ← cast? .univ t
      pure ⟨.univ, .unext t'⟩
  | .uunion r => do
      let ⟨_, t⟩ ← infer Γ r
      let t' ← cast? (.arr .nat .univ) t
      pure ⟨.univ, .uunion t'⟩
  | .uphi r s => do
      let ⟨_, tr⟩ ← infer Γ r
      let ⟨_, ts⟩ ← infer Γ s
      let tr' ← cast? (.arr .univ .univ) tr
      let ts' ← cast? .univ ts
      pure ⟨.univ, .uphi tr' ts'⟩
  | .uopClose r s => do
      let ⟨_, tr⟩ ← infer Γ r
      let ⟨_, ts⟩ ← infer Γ s
      let op := Ty.arr .univ .univ
      let tr' ← cast? (.arr op op) tr
      let ts' ← cast? op ts
      pure ⟨op, .uopClose tr' ts'⟩
  | .uindex r => do
      let ⟨_, t⟩ ← infer Γ r
      let t' ← cast? .tree t
      pure ⟨.univ, .uindex t'⟩
  | .ucollapse r s => do
      let ⟨_, tr⟩ ← infer Γ r
      let ⟨_, ts⟩ ← infer Γ s
      let tr' ← cast? (.arr .tree .tree) tr
      let ts' ← cast? .univ ts
      pure ⟨.tree, .ucollapse tr' ts'⟩

/-! ## Finite bounded enumeration -/

/-- Object-language types generated by depth `n`. -/
def tysUpTo : Nat → List Ty
  | 0 => []
  | n + 1 =>
      let ts := tysUpTo n
      .nat :: .tree :: .univ ::
        ts.flatMap fun a => ts.map fun b => .arr a b

/-- Raw terms generated by depth `n`, with variables below `n`. -/
def rawsUpTo : Nat → List Raw
  | 0 => []
  | n + 1 =>
      let rs := rawsUpTo n
      let ts := tysUpTo n
      (List.range n).map .var ++ [.zero, .tzero, .tin, .jin, .ubase] ++
      ts.flatMap (fun a => rs.map (.lam a)) ++
      rs.flatMap (fun r => rs.map (.app r)) ++
      rs.map .succ ++ rs.map .tsucc ++ rs.map .tlim ++
      rs.map .unext ++ rs.map .uunion ++ rs.map .uindex ++
      rs.flatMap (fun r => rs.map (.uphi r)) ++
      rs.flatMap (fun r => rs.map (.uopClose r)) ++
      rs.flatMap (fun r => rs.map (.ucollapse r)) ++
      rs.flatMap (fun z => rs.flatMap fun s => rs.map (.natRec z s)) ++
      rs.flatMap (fun z =>
        rs.flatMap fun s => rs.flatMap fun l => rs.map (.treeRec z s l))

/-- Values of all closed tree programs in the bounded raw enumeration. -/
def treesUpTo (jinF : CTree → CTree) (tinT : CTree) (n : Nat) :
    List CTree :=
  (rawsUpTo n).filterMap fun r =>
    match infer [] r with
    | some ⟨.tree, t⟩ => some (t.eval jinF tinT emptyEnv).down
    | _ => none

/-! ## Canonical witness programs -/

/-- The old `boost31J` operation is represented by a constant-size program. -/
def oldBoostTerm : Tm [] .tree :=
  .ucollapse .jin (.uindex .tin)

/-- The universe successor operator as a closed term. -/
def nextOperator : Tm [] (.arr .univ .univ) :=
  .lam (.unext (.var .here))

/-- The transformer `g ↦ Φ g` on universe operators. -/
def phiTransformer :
    Tm [] (.arr (.arr .univ .univ) (.arr .univ .univ)) :=
  .lam (.lam (.uphi (.var (.there .here)) (.var .here)))

/-- A canonical higher-kind program.  It closes `next` under repeated
`g ↦ Φ g`, applies the resulting universe operator above the indexed input
universe, and collapses the result relative to `jin`.
-/
def operatorClosureTerm : Tm [] .tree :=
  .ucollapse .jin
    (.app (.uopClose phiTransformer nextOperator) (.uindex .tin))

/-- Definitional embedding of Contender 46's universe-relative primitive. -/
theorem oldBoostTerm_eval (J : CTree → CTree) (T : CTree) :
    (oldBoostTerm.eval J T emptyEnv).down = boost31J J T := rfl

end UL

/-- Join a canonical higher-kind universe program with every bounded closed
universe-language program of result type `tree`. -/
def universeProgramTree (J : CTree → CTree) (T : CTree) (n : Nat) : CTree :=
  .lim fun i =>
    if i = 0 then (UL.operatorClosureTerm.eval J T UL.emptyEnv).down
    else ((UL.treesUpTo J T n)[i - 1]?).getD .zero

/-- An inflationary universe-language jump. -/
def universeLanguageLift (J : CTree → CTree) (T : CTree) (n : Nat) : CTree :=
  .lim fun i => if i = 0 then T else universeProgramTree J T n

end BusyLean.Ordinal
