import BusyLean.Ordinal.TreeLanguage

/-!
# System T over trees with an arbitrary environment of primitives

`TL` (Contender 32) has one primitive `boost : tree → tree`, and P27's
metalanguage has two. `PTL` takes a list `P` of primitive types and an
environment `σ : TL.Env P` of their values, which can be anything Lean
defines: tree operators, closure operators, iteration functionals. Terms refer
to primitives by index. The interpreter is still structural recursion on typed
terms, and closed programs of type `tree` of every size are enumerated.

With iteration functionals as primitives, programs can define hierarchies of
them by tree recursion at higher types, at levels and heights they build
themselves.
-/

namespace BusyLean.Ordinal

namespace PTL

open TL (Ty Var Env)

/-- Intrinsically typed terms over the primitive context `P`. -/
inductive Tm (P : List Ty) : List Ty → Ty → Type where
  | var : Var Γ a → Tm P Γ a
  | prim : Var P a → Tm P Γ a
  | lam : Tm P (a :: Γ) b → Tm P Γ (.arr a b)
  | app : Tm P Γ (.arr a b) → Tm P Γ a → Tm P Γ b
  | zero : Tm P Γ .nat
  | succ : Tm P Γ .nat → Tm P Γ .nat
  | natRec : Tm P Γ a → Tm P Γ (.arr a a) → Tm P Γ .nat → Tm P Γ a
  | tzero : Tm P Γ .tree
  | tsucc : Tm P Γ .tree → Tm P Γ .tree
  | tlim : Tm P Γ (.arr .nat .tree) → Tm P Γ .tree
  | treeRec : Tm P Γ a → Tm P Γ (.arr a a) → Tm P Γ (.arr (.arr .nat a) a) →
      Tm P Γ .tree → Tm P Γ a

/-- **The interpreter**, given the values of the primitives. -/
def Tm.eval {P : List Ty} (σ : Env P) : Tm P Γ a → Env Γ → a.den
  | .var v, ρ => v.get ρ
  | .prim v, _ => v.get σ
  | .lam t, ρ => fun x => t.eval σ (x, ρ)
  | .app t u, ρ => (t.eval σ ρ) (u.eval σ ρ)
  | .zero, _ => (0 : Nat)
  | .succ t, ρ => Nat.succ (t.eval σ ρ)
  | .natRec z s n, ρ => TL.natIter (z.eval σ ρ) (s.eval σ ρ) (n.eval σ ρ)
  | .tzero, _ => (Tre.zero : CTree)
  | .tsucc t, ρ => (Tre.succ (t.eval σ ρ) : CTree)
  | .tlim f, ρ => (Tre.lim (f.eval σ ρ) : CTree)
  | .treeRec z s l t, ρ =>
      TL.treeIter (z.eval σ ρ) (s.eval σ ρ) (l.eval σ ρ) (t.eval σ ρ)

/-- Raw terms; `prim i` is the `i`-th primitive. -/
inductive Raw where
  | var : Nat → Raw
  | prim : Nat → Raw
  | lam : Ty → Raw → Raw
  | app : Raw → Raw → Raw
  | zero : Raw
  | succ : Raw → Raw
  | natRec : Raw → Raw → Raw → Raw
  | tzero : Raw
  | tsucc : Raw → Raw
  | tlim : Raw → Raw
  | treeRec : Raw → Raw → Raw → Raw → Raw

def cast? {P Γ : List Ty} {a : Ty} (b : Ty) (t : Tm P Γ a) : Option (Tm P Γ b) :=
  if h : a = b then some (h ▸ t) else none

/-- Type inference. -/
def infer (P : List Ty) (Γ : List Ty) : Raw → Option (Σ a, Tm P Γ a)
  | .var n => (TL.lookup Γ n).map fun ⟨a, v⟩ => ⟨a, .var v⟩
  | .prim n => (TL.lookup P n).map fun ⟨a, v⟩ => ⟨a, .prim v⟩
  | .lam a r => (infer P (a :: Γ) r).map fun ⟨b, t⟩ => ⟨.arr a b, .lam t⟩
  | .app r s => do
      let ⟨ab, t⟩ ← infer P Γ r
      let ⟨_, u⟩ ← infer P Γ s
      match ab, t with
      | .arr a b, t => do let u' ← cast? a u; pure ⟨b, .app t u'⟩
      | _, _ => none
  | .zero => some ⟨.nat, .zero⟩
  | .succ r => do let ⟨_, t⟩ ← infer P Γ r; let t' ← cast? .nat t; pure ⟨.nat, .succ t'⟩
  | .natRec z s n => do
      let ⟨a, tz⟩ ← infer P Γ z
      let ⟨_, ts⟩ ← infer P Γ s
      let ⟨_, tn⟩ ← infer P Γ n
      let ts' ← cast? (.arr a a) ts
      let tn' ← cast? .nat tn
      pure ⟨a, .natRec tz ts' tn'⟩
  | .tzero => some ⟨.tree, .tzero⟩
  | .tsucc r => do let ⟨_, t⟩ ← infer P Γ r; let t' ← cast? .tree t; pure ⟨.tree, .tsucc t'⟩
  | .tlim r => do
      let ⟨_, t⟩ ← infer P Γ r; let t' ← cast? (.arr .nat .tree) t; pure ⟨.tree, .tlim t'⟩
  | .treeRec z s l r => do
      let ⟨a, tz⟩ ← infer P Γ z
      let ⟨_, ts⟩ ← infer P Γ s
      let ⟨_, tl⟩ ← infer P Γ l
      let ⟨_, tr⟩ ← infer P Γ r
      let ts' ← cast? (.arr a a) ts
      let tl' ← cast? (.arr (.arr .nat a) a) tl
      let tr' ← cast? .tree tr
      pure ⟨a, .treeRec tz ts' tl' tr'⟩

/-- Raw terms of size `≤ n`, with variables below `n` and primitives below `k`. -/
def rawsUpTo (k : Nat) : Nat → List Raw
  | 0 => []
  | n + 1 =>
      let rs := rawsUpTo k n
      let ts := TL.tysUpTo n
      (List.range n).map .var ++ (List.range k).map .prim ++ [.zero, .tzero] ++
      ts.flatMap (fun a => rs.map (.lam a)) ++
      rs.flatMap (fun r => rs.map (.app r)) ++
      rs.map .succ ++ rs.map .tsucc ++ rs.map .tlim ++
      rs.flatMap (fun z => rs.flatMap fun s => rs.map (.natRec z s)) ++
      rs.flatMap (fun z => rs.flatMap fun s => rs.flatMap fun l => rs.map (.treeRec z s l))

/-- Closed tree programs of size `≤ n` over the primitives, evaluated. -/
def treesUpTo (P : List Ty) (σ : Env P) (n : Nat) : List CTree :=
  (rawsUpTo P.length n).filterMap fun r =>
    match infer P [] r with
    | some ⟨.tree, t⟩ => some (t.eval σ ())
    | _ => none

end PTL

/-- All closed tree programs over the primitives, of every size, as one tree. -/
def primLangTree (P : List TL.Ty) (σ : TL.Env P) : CTree :=
  .lim fun m => .lim fun i => ((PTL.treesUpTo P σ m)[i]?).getD .zero

end BusyLean.Ordinal

namespace BusyLean.Ordinal

namespace PTL

/-- Closed programs of type `tree → tree` and size `≤ n` over the primitives, evaluated. -/
def funsUpTo (P : List TL.Ty) (σ : TL.Env P) (n : Nat) : List (CTree → CTree) :=
  (rawsUpTo P.length n).filterMap fun r =>
    match infer P [] r with
    | some ⟨.arr .tree .tree, t⟩ => some (t.eval σ ())
    | _ => none

end PTL

/-- The closure of `b` under the language over the primitives `P` plus `b`, applied to `t`:
every closed `tree → tree` program of every size. -/
def ptlLift (P : List TL.Ty) (σ : TL.Env P) (b : CTree → CTree) (t : CTree) : CTree :=
  .lim fun m => .lim fun i =>
    (((PTL.funsUpTo (.arr .tree .tree :: P) (b, σ) m)[i]?).map (· t)).getD .zero

/-- The type of a closure operator, `(tree → tree) → tree → tree`. -/
def liftTy : TL.Ty := .arr (.arr .tree .tree) (.arr .tree .tree)

/-- Languages over the primitives stacked along a tree: each successor level adds the
previous level's closure as a first-class primitive `lift`. -/
def ptlStack (P : List TL.Ty) (σ : TL.Env P) : CTree → (CTree → CTree) → CTree → CTree
  | .zero => ptlLift P σ
  | .succ a => ptlLift (liftTy :: P) (ptlStack P σ a, σ)
  | .lim f => fun b t => .lim fun i => ptlStack P σ (f i) b t
  | .supL _ => ptlLift P σ
  | .supH _ => ptlLift P σ

end BusyLean.Ordinal

namespace BusyLean.Ordinal

namespace PTL

/-- Closed programs of type `nat` and size `≤ n` over the primitives, evaluated. -/
def natsUpTo (P : List TL.Ty) (σ : TL.Env P) (n : Nat) : List Nat :=
  (rawsUpTo P.length n).filterMap fun r =>
    match infer P [] r with
    | some ⟨.nat, t⟩ => some (t.eval σ ())
    | _ => none

end PTL

end BusyLean.Ordinal
