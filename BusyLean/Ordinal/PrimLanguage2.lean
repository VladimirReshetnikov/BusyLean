import BusyLean.Ordinal.PrimLanguage
import BigNumber.Definitions

/-!
# System T over trees with products and an environment of primitives

`PTL` (Contender 51) has types `nat`, `tree` and arrows. Closure operators
on tree operators and on number functions come in pairs, so a language that
manipulates them as values needs products. `PTL2` adds `prod a b` with pairing
and projections, with the same structure as `PTL`: intrinsically typed terms,
an environment of primitives, a structural interpreter, type inference, and
enumeration of closed programs.
-/

namespace BusyLean.Ordinal

namespace PTL2

/-- Types: naturals, trees, arrows and products. -/
inductive Ty where
  | nat : Ty
  | tree : Ty
  | arr : Ty → Ty → Ty
  | prod : Ty → Ty → Ty
  deriving DecidableEq

def Ty.den : Ty → Type
  | .nat => Nat
  | .tree => CTree
  | .arr a b => a.den → b.den
  | .prod a b => a.den × b.den

inductive Var : List Ty → Ty → Type where
  | here : Var (a :: Γ) a
  | there : Var Γ a → Var (b :: Γ) a

def Env : List Ty → Type
  | [] => Unit
  | a :: Γ => a.den × Env Γ

def Var.get : Var Γ a → Env Γ → a.den
  | .here, (x, _) => x
  | .there v, (_, ρ) => v.get ρ

inductive Tm (P : List Ty) : List Ty → Ty → Type where
  | var : Var Γ a → Tm P Γ a
  | prim : Var P a → Tm P Γ a
  | lam : Tm P (a :: Γ) b → Tm P Γ (.arr a b)
  | app : Tm P Γ (.arr a b) → Tm P Γ a → Tm P Γ b
  | pair : Tm P Γ a → Tm P Γ b → Tm P Γ (.prod a b)
  | fst : Tm P Γ (.prod a b) → Tm P Γ a
  | snd : Tm P Γ (.prod a b) → Tm P Γ b
  | zero : Tm P Γ .nat
  | succ : Tm P Γ .nat → Tm P Γ .nat
  | natRec : Tm P Γ a → Tm P Γ (.arr a a) → Tm P Γ .nat → Tm P Γ a
  | tzero : Tm P Γ .tree
  | tsucc : Tm P Γ .tree → Tm P Γ .tree
  | tlim : Tm P Γ (.arr .nat .tree) → Tm P Γ .tree
  | treeRec : Tm P Γ a → Tm P Γ (.arr a a) → Tm P Γ (.arr (.arr .nat a) a) →
      Tm P Γ .tree → Tm P Γ a

/-- The interpreter. -/
def Tm.eval {P : List Ty} (σ : Env P) : Tm P Γ a → Env Γ → a.den
  | .var v, ρ => v.get ρ
  | .prim v, _ => v.get σ
  | .lam t, ρ => fun x => t.eval σ (x, ρ)
  | .app t u, ρ => (t.eval σ ρ) (u.eval σ ρ)
  | .pair t u, ρ => (t.eval σ ρ, u.eval σ ρ)
  | .fst t, ρ => (t.eval σ ρ).1
  | .snd t, ρ => (t.eval σ ρ).2
  | .zero, _ => (0 : Nat)
  | .succ t, ρ => Nat.succ (t.eval σ ρ)
  | .natRec z s n, ρ => TL.natIter (z.eval σ ρ) (s.eval σ ρ) (n.eval σ ρ)
  | .tzero, _ => (Tre.zero : CTree)
  | .tsucc t, ρ => (Tre.succ (t.eval σ ρ) : CTree)
  | .tlim f, ρ => (Tre.lim (f.eval σ ρ) : CTree)
  | .treeRec z s l t, ρ =>
      TL.treeIter (z.eval σ ρ) (s.eval σ ρ) (l.eval σ ρ) (t.eval σ ρ)

inductive Raw where
  | var : Nat → Raw
  | prim : Nat → Raw
  | lam : Ty → Raw → Raw
  | app : Raw → Raw → Raw
  | pair : Raw → Raw → Raw
  | fst : Raw → Raw
  | snd : Raw → Raw
  | zero : Raw
  | succ : Raw → Raw
  | natRec : Raw → Raw → Raw → Raw
  | tzero : Raw
  | tsucc : Raw → Raw
  | tlim : Raw → Raw
  | treeRec : Raw → Raw → Raw → Raw → Raw

def lookup : (Γ : List Ty) → Nat → Option (Σ a, Var Γ a)
  | [], _ => none
  | a :: _, 0 => some ⟨a, .here⟩
  | _ :: Γ, n + 1 => (lookup Γ n).map fun ⟨a, v⟩ => ⟨a, .there v⟩

def cast? {P Γ : List Ty} {a : Ty} (b : Ty) (t : Tm P Γ a) : Option (Tm P Γ b) :=
  if h : a = b then some (h ▸ t) else none

/-- Type inference. -/
def infer (P : List Ty) (Γ : List Ty) : Raw → Option (Σ a, Tm P Γ a)
  | .var n => (lookup Γ n).map fun ⟨a, v⟩ => ⟨a, .var v⟩
  | .prim n => (lookup P n).map fun ⟨a, v⟩ => ⟨a, .prim v⟩
  | .lam a r => (infer P (a :: Γ) r).map fun ⟨b, t⟩ => ⟨.arr a b, .lam t⟩
  | .app r s => do
      let ⟨ab, t⟩ ← infer P Γ r
      let ⟨_, u⟩ ← infer P Γ s
      match ab, t with
      | .arr a b, t => do let u' ← cast? a u; pure ⟨b, .app t u'⟩
      | _, _ => none
  | .pair r s => do
      let ⟨a, t⟩ ← infer P Γ r
      let ⟨b, u⟩ ← infer P Γ s
      pure ⟨.prod a b, .pair t u⟩
  | .fst r => do
      let ⟨ab, t⟩ ← infer P Γ r
      match ab, t with
      | .prod a _, t => pure ⟨a, .fst t⟩
      | _, _ => none
  | .snd r => do
      let ⟨ab, t⟩ ← infer P Γ r
      match ab, t with
      | .prod _ b, t => pure ⟨b, .snd t⟩
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

/-- Types of size `≤ n`. -/
def tysUpTo : Nat → List Ty
  | 0 => []
  | n + 1 =>
      let ts := tysUpTo n
      .nat :: .tree :: (ts.flatMap fun a => ts.map fun b => .arr a b) ++
        (ts.flatMap fun a => ts.map fun b => .prod a b)

/-- Raw terms of size `≤ n`, with variables below `n` and primitives below `k`. -/
def rawsUpTo (k : Nat) : Nat → List Raw
  | 0 => []
  | n + 1 =>
      let rs := rawsUpTo k n
      let ts := tysUpTo n
      (List.range n).map .var ++ (List.range k).map .prim ++ [.zero, .tzero] ++
      ts.flatMap (fun a => rs.map (.lam a)) ++
      rs.flatMap (fun r => rs.map (.app r)) ++
      rs.flatMap (fun r => rs.map (.pair r)) ++ rs.map .fst ++ rs.map .snd ++
      rs.map .succ ++ rs.map .tsucc ++ rs.map .tlim ++
      rs.flatMap (fun z => rs.flatMap fun s => rs.map (.natRec z s)) ++
      rs.flatMap (fun z => rs.flatMap fun s => rs.flatMap fun l => rs.map (.treeRec z s l))

/-- Closed programs of type `tree → tree` and size `≤ n`, evaluated. -/
def funsUpTo (P : List Ty) (σ : Env P) (n : Nat) : List (CTree → CTree) :=
  (rawsUpTo P.length n).filterMap fun r =>
    match infer P [] r with
    | some ⟨.arr .tree .tree, t⟩ => some (t.eval σ ())
    | _ => none

/-- Closed programs of type `nat` and size `≤ n`, evaluated. -/
def natsUpTo (P : List Ty) (σ : Env P) (n : Nat) : List Nat :=
  (rawsUpTo P.length n).filterMap fun r =>
    match infer P [] r with
    | some ⟨.nat, t⟩ => some (t.eval σ ())
    | _ => none

end PTL2

/-- The tree closure of `b` under the language over the primitives `P` plus `b`. -/
def ptl2Lift (P : List PTL2.Ty) (σ : PTL2.Env P) (b : CTree → CTree) (t : CTree) : CTree :=
  .lim fun m => .lim fun i =>
    (((PTL2.funsUpTo (.arr .tree .tree :: P) (b, σ) m)[i]?).map (· t)).getD .zero

/-- The number closure of `g` under the language over the primitives `P` plus `g`. -/
def num2Lift (P : List PTL2.Ty) (σ : PTL2.Env P) (g : Nat → Nat) (m : Nat) : Nat :=
  m + 1 + BigNumber.maxN (g m) (BigNumber.maximum id (PTL2.natsUpTo (.arr .nat .nat :: P) (g, σ) m))

end BusyLean.Ordinal
