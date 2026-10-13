import BusyLean.Ordinal.TreeUniverses5

/-!
# A programming language for tree ordinals

Contenders 25–31 are each one particular combination of tree-ordinal
operations. Here the combinations become programs. The language is Gödel's
System T with an extra base type of countable tree ordinals:

* types: `nat`, `tree`, `a ⇒ b`;
* constants: numerals, `natRec`, `tzero`, `tsucc`, `tlim : (nat ⇒ tree) ⇒ tree`;
* `treeRec : A → (A → A) → ((nat → A) → A) → tree → A`, iteration along any
  tree, at any type;
* `boost : tree ⇒ tree`, the strongest construction so far (Contender 31's,
  as a function of its index tree).

The language is simply typed and predicative, so it has a direct *semantic*
interpreter. Types denote Lean types and intrinsically typed terms denote Lean
values, by structural recursion. No normalization proof is needed, and
evaluation is computable. A small type checker turns raw terms into typed ones.
At input `n`, `programTree boost n` is the limit of all closed `tree`-typed
programs of size `≤ n`.
-/

namespace BusyLean.Ordinal

namespace TL

/-- Types. -/
inductive Ty where
  | nat : Ty
  | tree : Ty
  | arr : Ty → Ty → Ty
  deriving DecidableEq

/-- Denotations. -/
def Ty.den : Ty → Type
  | .nat => Nat
  | .tree => CTree
  | .arr a b => a.den → b.den

/-- Variables in a context. -/
inductive Var : List Ty → Ty → Type where
  | here : Var (a :: Γ) a
  | there : Var Γ a → Var (b :: Γ) a

/-- Intrinsically typed terms; `boost` is a primitive of type `tree ⇒ tree`. -/
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
  | treeRec : Tm Γ a → Tm Γ (.arr a a) → Tm Γ (.arr (.arr .nat a) a) → Tm Γ .tree → Tm Γ a
  | boost : Tm Γ .tree → Tm Γ .tree

/-- Environments. -/
def Env : List Ty → Type
  | [] => Unit
  | a :: Γ => a.den × Env Γ

def Var.get : Var Γ a → Env Γ → a.den
  | .here, (x, _) => x
  | .there v, (_, ρ) => v.get ρ

def natIter {α : Type} (z : α) (s : α → α) : Nat → α
  | 0 => z
  | n + 1 => s (natIter z s n)

/-- Iteration along a tree. -/
def treeIter {α : Type} (z : α) (s : α → α) (l : (Nat → α) → α) : CTree → α
  | .zero => z
  | .succ t => s (treeIter z s l t)
  | .lim f => l fun n => treeIter z s l (f n)
  | .supL _ => z
  | .supH _ => z

/-- **The interpreter**: structural recursion on typed terms. -/
def Tm.eval (boostF : CTree → CTree) : Tm Γ a → Env Γ → a.den
  | .var v, ρ => v.get ρ
  | .lam t, ρ => fun x => t.eval boostF (x, ρ)
  | .app t u, ρ => (t.eval boostF ρ) (u.eval boostF ρ)
  | .zero, _ => (0 : Nat)
  | .succ t, ρ => Nat.succ (t.eval boostF ρ)
  | .natRec z s n, ρ => natIter (z.eval boostF ρ) (s.eval boostF ρ) (n.eval boostF ρ)
  | .tzero, _ => (Tre.zero : CTree)
  | .tsucc t, ρ => (Tre.succ (t.eval boostF ρ) : CTree)
  | .tlim f, ρ => (Tre.lim (f.eval boostF ρ) : CTree)
  | .treeRec z s l t, ρ => treeIter (z.eval boostF ρ) (s.eval boostF ρ) (l.eval boostF ρ) (t.eval boostF ρ)
  | .boost t, ρ => boostF (t.eval boostF ρ)

/-! ## Raw terms and type checking -/

/-- Raw terms (lambdas carry their argument type). -/
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
  | boost : Raw → Raw

def lookup : (Γ : List Ty) → Nat → Option (Σ a, Var Γ a)
  | [], _ => none
  | a :: _, 0 => some ⟨a, .here⟩
  | _ :: Γ, n + 1 => (lookup Γ n).map fun ⟨a, v⟩ => ⟨a, .there v⟩

/-- Check a term against an expected type. -/
def cast? {Γ : List Ty} {a : Ty} (b : Ty) (t : Tm Γ a) : Option (Tm Γ b) :=
  if h : a = b then some (h ▸ t) else none

/-- Type inference. -/
def infer (Γ : List Ty) : Raw → Option (Σ a, Tm Γ a)
  | .var n => (lookup Γ n).map fun ⟨a, v⟩ => ⟨a, .var v⟩
  | .lam a r => (infer (a :: Γ) r).map fun ⟨b, t⟩ => ⟨.arr a b, .lam t⟩
  | .app r s => do
      let ⟨ab, t⟩ ← infer Γ r
      let ⟨_, u⟩ ← infer Γ s
      match ab, t with
      | .arr a b, t => do let u' ← cast? a u; pure ⟨b, .app t u'⟩
      | _, _ => none
  | .zero => some ⟨.nat, .zero⟩
  | .succ r => do let ⟨_, t⟩ ← infer Γ r; let t' ← cast? .nat t; pure ⟨.nat, .succ t'⟩
  | .natRec z s n => do
      let ⟨a, tz⟩ ← infer Γ z
      let ⟨_, ts⟩ ← infer Γ s
      let ⟨_, tn⟩ ← infer Γ n
      let ts' ← cast? (.arr a a) ts
      let tn' ← cast? .nat tn
      pure ⟨a, .natRec tz ts' tn'⟩
  | .tzero => some ⟨.tree, .tzero⟩
  | .tsucc r => do let ⟨_, t⟩ ← infer Γ r; let t' ← cast? .tree t; pure ⟨.tree, .tsucc t'⟩
  | .tlim r => do let ⟨_, t⟩ ← infer Γ r; let t' ← cast? (.arr .nat .tree) t; pure ⟨.tree, .tlim t'⟩
  | .treeRec z s l r => do
      let ⟨a, tz⟩ ← infer Γ z
      let ⟨_, ts⟩ ← infer Γ s
      let ⟨_, tl⟩ ← infer Γ l
      let ⟨_, tr⟩ ← infer Γ r
      let ts' ← cast? (.arr a a) ts
      let tl' ← cast? (.arr (.arr .nat a) a) tl
      let tr' ← cast? .tree tr
      pure ⟨a, .treeRec tz ts' tl' tr'⟩
  | .boost r => do let ⟨_, t⟩ ← infer Γ r; let t' ← cast? .tree t; pure ⟨.tree, .boost t'⟩

/-! ## Enumeration -/

/-- Types of size `≤ n`. -/
def tysUpTo : Nat → List Ty
  | 0 => []
  | n + 1 =>
      let ts := tysUpTo n
      .nat :: .tree :: ts.flatMap fun a => ts.map fun b => .arr a b

/-- Raw terms of size `≤ n` with variables below `n`. -/
def rawsUpTo : Nat → List Raw
  | 0 => []
  | n + 1 =>
      let rs := rawsUpTo n
      let ts := tysUpTo n
      (List.range n).map .var ++ [.zero, .tzero] ++
      ts.flatMap (fun a => rs.map (.lam a)) ++
      rs.flatMap (fun r => rs.map (.app r)) ++
      rs.map .succ ++ rs.map .tsucc ++ rs.map .tlim ++ rs.map .boost ++
      rs.flatMap (fun z => rs.flatMap fun s => rs.map (.natRec z s)) ++
      rs.flatMap (fun z => rs.flatMap fun s => rs.flatMap fun l => rs.map (.treeRec z s l))

/-- Closed tree programs of size `≤ n`, evaluated. -/
def treesUpTo (boostF : CTree → CTree) (n : Nat) : List CTree :=
  (rawsUpTo n).filterMap fun r =>
    match infer [] r with
    | some ⟨.tree, t⟩ => some (t.eval boostF ())
    | _ => none

end TL

/-- The limit of all closed tree programs of size `≤ n`. -/
def programTree (boostF : CTree → CTree) (n : Nat) : CTree :=
  .lim fun i => ((TL.treesUpTo boostF n)[i]?).getD .zero

/-- Contender 31's construction as a function of its index tree. -/
def boost31 (Λ : CTree) : CTree :=
  U2.universeTree (U2.transTypeUniv (U2.ΦT Λ) Λ)

/-- The tree of input `n`: all programs of size `≤ n + 3` over `boost31`, above Contender 31's tree. -/
def languageTree (n : Nat) : CTree :=
  .lim fun i => if i = 0 then transTypeTree n else programTree boost31 (n + 3)

end BusyLean.Ordinal
