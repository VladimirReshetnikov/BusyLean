import BusyLean.Ordinal.TreeLanguage3

/-!
# A metalanguage for tree-ordinal languages

`TreeLanguage3` iterates the first-order language-closure operator `langLift`
along a countable tree ordinal.  This module raises the construction by one
functional type.  Its object language has two primitives:

* `boost : tree -> tree`, an arbitrary tree transformer;
* `lift : (tree -> tree) -> tree -> tree`, an arbitrary language-closure
  operator acting on tree transformers.

The language can therefore construct a transformer, pass it to the lower-level
language-closure operator, and continue computing with the resulting tree.
Closed programs of type `tree -> tree` are enumerated semantically, exactly as
in `TreeLanguage2`.

`metaLangLift L b` is the whole metalanguage over closure operator `L` and base
transformer `b`.  `metaBoostT` then iterates this operation along a countable
tree ordinal.  At input `n`, the height, base-transformer index, and argument
are all built from Contender 34's tree.
-/

namespace BusyLean.Ordinal

namespace MTL

/-- Intrinsically typed metalanguage terms.  The type system is the same
simply typed system used by `TL`; only the primitive operations are richer. -/
inductive Tm : List TL.Ty → TL.Ty → Type where
  | var : TL.Var Γ a → Tm Γ a
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
  | boost : Tm Γ .tree → Tm Γ .tree
  | lift : Tm Γ (.arr .tree .tree) → Tm Γ .tree → Tm Γ .tree

/-- Semantic interpreter.  It is total by structural recursion on the typed
term; no normalization theorem and no classical principle are needed. -/
def Tm.eval
    (liftF : (CTree → CTree) → CTree → CTree)
    (boostF : CTree → CTree) :
    Tm Γ a → TL.Env Γ → TL.Ty.den a
  | .var v, ρ => TL.Var.get v ρ
  | .lam t, ρ => fun x => t.eval liftF boostF (x, ρ)
  | .app t u, ρ => (t.eval liftF boostF ρ) (u.eval liftF boostF ρ)
  | .zero, _ => (0 : Nat)
  | .succ t, ρ => Nat.succ (t.eval liftF boostF ρ)
  | .natRec z s n, ρ =>
      TL.natIter (z.eval liftF boostF ρ) (s.eval liftF boostF ρ)
        (n.eval liftF boostF ρ)
  | .tzero, _ => (Tre.zero : CTree)
  | .tsucc t, ρ => (Tre.succ (t.eval liftF boostF ρ) : CTree)
  | .tlim f, ρ => (Tre.lim (f.eval liftF boostF ρ) : CTree)
  | .treeRec z s l t, ρ =>
      TL.treeIter (z.eval liftF boostF ρ) (s.eval liftF boostF ρ)
        (l.eval liftF boostF ρ) (t.eval liftF boostF ρ)
  | .boost t, ρ => boostF (t.eval liftF boostF ρ)
  | .lift b t, ρ =>
      liftF (b.eval liftF boostF ρ) (t.eval liftF boostF ρ)

/-! ## Raw terms and type checking -/

/-- Raw syntax; lambdas carry their argument type. -/
inductive Raw where
  | var : Nat → Raw
  | lam : TL.Ty → Raw → Raw
  | app : Raw → Raw → Raw
  | zero : Raw
  | succ : Raw → Raw
  | natRec : Raw → Raw → Raw → Raw
  | tzero : Raw
  | tsucc : Raw → Raw
  | tlim : Raw → Raw
  | treeRec : Raw → Raw → Raw → Raw → Raw
  | boost : Raw → Raw
  | lift : Raw → Raw → Raw

/-- Cast an intrinsically typed term after decidable type equality. -/
def cast? {Γ : List TL.Ty} {a : TL.Ty} (b : TL.Ty)
    (t : Tm Γ a) : Option (Tm Γ b) :=
  if h : a = b then some (h ▸ t) else none

/-- Sound-by-construction type inference from raw terms. -/
def infer (Γ : List TL.Ty) : Raw → Option (Σ a, Tm Γ a)
  | .var n => (TL.lookup Γ n).map fun ⟨a, v⟩ => ⟨a, .var v⟩
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
  | .boost r => do
      let ⟨_, t⟩ ← infer Γ r
      let t' ← cast? .tree t
      pure ⟨.tree, .boost t'⟩
  | .lift b r => do
      let ⟨_, tb⟩ ← infer Γ b
      let ⟨_, tr⟩ ← infer Γ r
      let tb' ← cast? (.arr .tree .tree) tb
      let tr' ← cast? .tree tr
      pure ⟨.tree, .lift tb' tr'⟩

/-! ## Enumeration -/

/-- Raw metalanguage terms of size at most `n`, with variables below `n`. -/
def rawsUpTo : Nat → List Raw
  | 0 => []
  | n + 1 =>
      let rs := rawsUpTo n
      let ts := TL.tysUpTo n
      (List.range n).map .var ++ [.zero, .tzero] ++
      ts.flatMap (fun a => rs.map (.lam a)) ++
      rs.flatMap (fun r => rs.map (.app r)) ++
      rs.map .succ ++ rs.map .tsucc ++ rs.map .tlim ++ rs.map .boost ++
      rs.flatMap (fun b => rs.map fun r => .lift b r) ++
      rs.flatMap (fun z => rs.flatMap fun s => rs.map (.natRec z s)) ++
      rs.flatMap (fun z =>
        rs.flatMap fun s => rs.flatMap fun l => rs.map (.treeRec z s l))

/-- Closed metalanguage programs of type `tree -> tree` and size at most `m`,
interpreted as actual total Lean functions. -/
def funsUpTo
    (liftF : (CTree → CTree) → CTree → CTree)
    (boostF : CTree → CTree) (m : Nat) : List (CTree → CTree) :=
  (rawsUpTo m).filterMap fun r =>
    match infer [] r with
    | some ⟨.arr .tree .tree, t⟩ => some (t.eval liftF boostF ())
    | _ => none

end MTL

/-- The whole metalanguage over closure operator `liftF` and tree transformer
`b`, applied to `t`.  Every closed `tree -> tree` program of every finite size
occurs in the two nested limits. -/
def metaLangLift
    (liftF : (CTree → CTree) → CTree → CTree)
    (b : CTree → CTree) (t : CTree) : CTree :=
  .lim fun m => .lim fun i =>
    (((MTL.funsUpTo liftF b m)[i]?).map fun p => p t).getD .zero

/-- Metalanguages stacked along a countable tree ordinal.  The zero stage uses
`langLift`; a successor closes a language that can invoke the entire previous
closure operator; limits are pointwise limits. -/
def metaBoostT : CTree → (CTree → CTree) → CTree → CTree
  | .zero => langLift
  | .succ a => metaLangLift (metaBoostT a)
  | .lim f => fun b t => .lim fun i => metaBoostT (f i) b t
  | .supL _ => langLift
  | .supH _ => langLift

/-- The input tree for Contender 35.  Branch zero retains Contender 34's tree.
Every other branch iterates the metalanguage hierarchy to that same height,
starting from a first-order language hierarchy also indexed by Contender 34's
tree, and applies it to Contender 34's tree. -/
def metaLanguageTree (n : Nat) : CTree :=
  .lim fun i =>
    if i = 0 then treeStackedTree n
    else metaBoostT (treeStackedTree n)
      (boostT (treeStackedTree n)) (treeStackedTree n)

end BusyLean.Ordinal
