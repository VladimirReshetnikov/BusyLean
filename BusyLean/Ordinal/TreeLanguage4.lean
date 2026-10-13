import BusyLean.Ordinal.TreeLanguage3

/-!
# An operator meta-language for tree ordinals

`TreeLanguage3` iterates the operation `langLift` along a tree ordinal, but
`langLift` itself remains external to the object language.  This module moves
one level up: the object language receives a primitive

```
lang : (tree -> tree) -> (tree -> tree)
```

whose denotation is `Ordinal.langLift`.  Programs may therefore abstract over,
compose, and iterate language-extension operators at arbitrary simple types,
including by natural and tree recursion.  The interpreter is semantic and
structurally recursive, so every accepted program denotes a total Lean value.

`operatorMetaLift b` collects every closed `tree -> tree` program over seed
`b`.  `operatorBoostT b a` then stacks this entire operator meta-language along
the tree `a`.  At input `n` we use Contender 34's tree both as the height and
as the argument, with `boostT` at that height as the seed primitive.
-/

namespace BusyLean.Ordinal

namespace OML

/-- Simple types for the operator meta-language. -/
inductive Ty where
  | nat : Ty
  | tree : Ty
  | arr : Ty -> Ty -> Ty
  deriving DecidableEq

/-- Semantic denotations. -/
def Ty.den : Ty -> Type
  | .nat => Nat
  | .tree => CTree
  | .arr a b => a.den -> b.den

/-- De Bruijn variables in a typed context. -/
inductive Var : List Ty -> Ty -> Type where
  | here : Var (a :: Γ) a
  | there : Var Γ a -> Var (b :: Γ) a

/--
Intrinsically typed terms.  Besides the tree primitive `boost`, the constructor
`lang` internalizes the previous round's whole-language closure.
-/
inductive Tm : List Ty -> Ty -> Type where
  | var : Var Γ a -> Tm Γ a
  | lam : Tm (a :: Γ) b -> Tm Γ (.arr a b)
  | app : Tm Γ (.arr a b) -> Tm Γ a -> Tm Γ b
  | zero : Tm Γ .nat
  | succ : Tm Γ .nat -> Tm Γ .nat
  | natRec : Tm Γ a -> Tm Γ (.arr a a) -> Tm Γ .nat -> Tm Γ a
  | tzero : Tm Γ .tree
  | tsucc : Tm Γ .tree -> Tm Γ .tree
  | tlim : Tm Γ (.arr .nat .tree) -> Tm Γ .tree
  | treeRec : Tm Γ a -> Tm Γ (.arr a a) -> Tm Γ (.arr (.arr .nat a) a) ->
      Tm Γ .tree -> Tm Γ a
  | boost : Tm Γ .tree -> Tm Γ .tree
  | lang : Tm Γ (.arr .tree .tree) -> Tm Γ (.arr .tree .tree)

/-- Environments. -/
def Env : List Ty -> Type
  | [] => Unit
  | a :: Γ => a.den × Env Γ

def Var.get : Var Γ a -> Env Γ -> a.den
  | .here, (x, _) => x
  | .there v, (_, ρ) => v.get ρ

def natIter {α : Type} (z : α) (s : α -> α) : Nat -> α
  | 0 => z
  | n + 1 => s (natIter z s n)

/-- Structural recursion on a tree into an arbitrary semantic type. -/
def treeIter {α : Type} (z : α) (s : α -> α) (l : (Nat -> α) -> α) : CTree -> α
  | .zero => z
  | .succ t => s (treeIter z s l t)
  | .lim f => l fun n => treeIter z s l (f n)
  | .supL _ => z
  | .supH _ => z

/--
The total semantic interpreter.  The `lang` case is ordinary application of
the already-total Lean function `langLift`; no evaluator reflection or partial
normalization procedure is involved.
-/
def Tm.eval (boostF : CTree -> CTree) : Tm Γ a -> Env Γ -> a.den
  | .var v, ρ => v.get ρ
  | .lam t, ρ => fun x => t.eval boostF (x, ρ)
  | .app t u, ρ => (t.eval boostF ρ) (u.eval boostF ρ)
  | .zero, _ => (0 : Nat)
  | .succ t, ρ => Nat.succ (t.eval boostF ρ)
  | .natRec z s n, ρ => natIter (z.eval boostF ρ) (s.eval boostF ρ) (n.eval boostF ρ)
  | .tzero, _ => (Tre.zero : CTree)
  | .tsucc t, ρ => (Tre.succ (t.eval boostF ρ) : CTree)
  | .tlim f, ρ => (Tre.lim (f.eval boostF ρ) : CTree)
  | .treeRec z s l t, ρ =>
      treeIter (z.eval boostF ρ) (s.eval boostF ρ) (l.eval boostF ρ) (t.eval boostF ρ)
  | .boost t, ρ => boostF (t.eval boostF ρ)
  | .lang f, ρ => langLift (f.eval boostF ρ)

/-! ## Raw syntax and a sound-by-construction type checker -/

/-- Raw terms; lambda binders carry their argument type. -/
inductive Raw where
  | var : Nat -> Raw
  | lam : Ty -> Raw -> Raw
  | app : Raw -> Raw -> Raw
  | zero : Raw
  | succ : Raw -> Raw
  | natRec : Raw -> Raw -> Raw -> Raw
  | tzero : Raw
  | tsucc : Raw -> Raw
  | tlim : Raw -> Raw
  | treeRec : Raw -> Raw -> Raw -> Raw -> Raw
  | boost : Raw -> Raw
  | lang : Raw -> Raw

def lookup : (Γ : List Ty) -> Nat -> Option (Σ a, Var Γ a)
  | [], _ => none
  | a :: _, 0 => some ⟨a, .here⟩
  | _ :: Γ, n + 1 => (lookup Γ n).map fun ⟨a, v⟩ => ⟨a, .there v⟩

/-- Cast an intrinsically typed term after decidable type equality. -/
def cast? {Γ : List Ty} {a : Ty} (b : Ty) (t : Tm Γ a) : Option (Tm Γ b) :=
  if h : a = b then some (h ▸ t) else none

/-- Type inference into intrinsically typed syntax. -/
def infer (Γ : List Ty) : Raw -> Option (Σ a, Tm Γ a)
  | .var n => (lookup Γ n).map fun ⟨a, v⟩ => ⟨a, .var v⟩
  | .lam a r => (infer (a :: Γ) r).map fun ⟨b, t⟩ => ⟨.arr a b, .lam t⟩
  | .app r s => do
      let ⟨ab, t⟩ <- infer Γ r
      let ⟨_, u⟩ <- infer Γ s
      match ab, t with
      | .arr a b, t => do
          let u' <- cast? a u
          pure ⟨b, .app t u'⟩
      | _, _ => none
  | .zero => some ⟨.nat, .zero⟩
  | .succ r => do
      let ⟨_, t⟩ <- infer Γ r
      let t' <- cast? .nat t
      pure ⟨.nat, .succ t'⟩
  | .natRec z s n => do
      let ⟨a, tz⟩ <- infer Γ z
      let ⟨_, ts⟩ <- infer Γ s
      let ⟨_, tn⟩ <- infer Γ n
      let ts' <- cast? (.arr a a) ts
      let tn' <- cast? .nat tn
      pure ⟨a, .natRec tz ts' tn'⟩
  | .tzero => some ⟨.tree, .tzero⟩
  | .tsucc r => do
      let ⟨_, t⟩ <- infer Γ r
      let t' <- cast? .tree t
      pure ⟨.tree, .tsucc t'⟩
  | .tlim r => do
      let ⟨_, t⟩ <- infer Γ r
      let t' <- cast? (.arr .nat .tree) t
      pure ⟨.tree, .tlim t'⟩
  | .treeRec z s l r => do
      let ⟨a, tz⟩ <- infer Γ z
      let ⟨_, ts⟩ <- infer Γ s
      let ⟨_, tl⟩ <- infer Γ l
      let ⟨_, tr⟩ <- infer Γ r
      let ts' <- cast? (.arr a a) ts
      let tl' <- cast? (.arr (.arr .nat a) a) tl
      let tr' <- cast? .tree tr
      pure ⟨a, .treeRec tz ts' tl' tr'⟩
  | .boost r => do
      let ⟨_, t⟩ <- infer Γ r
      let t' <- cast? .tree t
      pure ⟨.tree, .boost t'⟩
  | .lang r => do
      let ⟨_, t⟩ <- infer Γ r
      let t' <- cast? (.arr .tree .tree) t
      pure ⟨.arr .tree .tree, .lang t'⟩

/-! ## Finite enumerations -/

/-- Types generated up to stage `n`. -/
def tysUpTo : Nat -> List Ty
  | 0 => []
  | n + 1 =>
      let ts := tysUpTo n
      .nat :: .tree :: ts.flatMap fun a => ts.map fun b => .arr a b

/-- Raw terms generated up to stage `n`, with variables below `n`. -/
def rawsUpTo : Nat -> List Raw
  | 0 => []
  | n + 1 =>
      let rs := rawsUpTo n
      let ts := tysUpTo n
      (List.range n).map .var ++ [.zero, .tzero] ++
      ts.flatMap (fun a => rs.map (.lam a)) ++
      rs.flatMap (fun r => rs.map (.app r)) ++
      rs.map .succ ++ rs.map .tsucc ++ rs.map .tlim ++ rs.map .boost ++ rs.map .lang ++
      rs.flatMap (fun z => rs.flatMap fun s => rs.map (.natRec z s)) ++
      rs.flatMap (fun z => rs.flatMap fun s => rs.flatMap fun l => rs.map (.treeRec z s l))

/-- Closed `tree -> tree` programs of bounded generation depth, as functions. -/
def funsUpTo (boostF : CTree -> CTree) (m : Nat) : List (CTree -> CTree) :=
  (rawsUpTo m).filterMap fun r =>
    match infer [] r with
    | some ⟨.arr .tree .tree, t⟩ => some (t.eval boostF ())
    | _ => none

end OML

/--
The whole operator meta-language over primitive `b`, applied to `t`.
Every closed `tree -> tree` program of every finite size contributes a branch.
-/
def operatorMetaLift (b : CTree -> CTree) (t : CTree) : CTree :=
  .lim fun m => .lim fun i => (((OML.funsUpTo b m)[i]?).map (· t)).getD .zero

/--
Stack the operator meta-language along a countable tree ordinal.  Successor
stages replace the primitive by the closure of the whole previous
meta-language; limit stages take pointwise limits.
-/
def operatorBoostT (base : CTree -> CTree) : CTree -> CTree -> CTree
  | .zero => base
  | .succ a => operatorMetaLift (operatorBoostT base a)
  | .lim f => fun t => .lim fun i => operatorBoostT base (f i) t
  | .supL _ => base
  | .supH _ => base

/--
The Contender 35 tree at input `n`.  Let `T` be Contender 34's tree.  The seed
primitive is the old transfinite language stack `boostT T`; the new operator
meta-language is itself stacked to height `T` and applied to `T`.
-/
def operatorStackedTree (n : Nat) : CTree :=
  let T := treeStackedTree n
  let base := boostT T
  .lim fun i => if i = 0 then T else operatorBoostT base T T

end BusyLean.Ordinal
