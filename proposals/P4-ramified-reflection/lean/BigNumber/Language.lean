import BigNumber.Legacy

/-! Total finite-type language with a Brouwer-tree recursor and a binary oracle. -/
namespace BigNumber

inductive Tree : Type where
  | zero
  | sup (children : Nat → Tree)

/-- The W-recursion operation exposed to the object language. -/
def treeFold {α : Type} (z : α)
    (s : (Nat → Tree) → (Nat → α) → α) : Tree → α
  | .zero => z
  | .sup f => s f (fun n => treeFold z s (f n))

namespace Language
open BigNumber.Lists

inductive Ty : Type where
  | nat
  | tree
  | arr (dom cod : Ty)

def Den : Ty → Type
  | .nat => Nat
  | .tree => Tree
  | .arr a b => Den a → Den b

def eqb : Ty → Ty → Bool
  | .nat, .nat => true
  | .tree, .tree => true
  | .arr a b, .arr c d => eqb a c && eqb b d
  | _, _ => false

def typeDepth : Ty → Nat
  | .nat | .tree => 1
  | .arr a b => 1 + Nat.max (typeDepth a) (typeDepth b)

def defaultVal : (a : Ty) → Den a
  | .nat => (0 : Nat)
  | .tree => Tree.zero
  | .arr _ b => fun _ => defaultVal b

/-- No equality transport through an opaque proof is used in computation. -/
def castPair : (a b : Ty) → (Den a → Den b) × (Den b → Den a)
  | .nat, .nat => (fun x => x, fun x => x)
  | .tree, .tree => (fun x => x, fun x => x)
  | .arr a b, .arr c d =>
      if eqb a c && eqb b d then
        let ac := castPair a c
        let bd := castPair b d
        (fun f x => bd.1 (f (ac.2 x)),
         fun f x => bd.2 (f (ac.1 x)))
      else
        (fun _ => defaultVal (.arr c d), fun _ => defaultVal (.arr a b))
  | a, b => (fun _ => defaultVal b, fun _ => defaultVal a)

abbrev Pack := Sigma Den

def cast (b : Ty) (v : Pack) : Den b := (castPair v.1 b).1 v.2

inductive Tm : Type where
  | var (i : Nat)
  | lam (dom cod : Ty) (body : Tm)
  | app (fn arg : Tm)
  | zero
  | succ
  | treeZero
  | treeSup
  | oracle
  | natRec (result : Ty)
  | treeRec (result : Ty)
  | quote (rawLegacyTerm : Legacy.Tm)

/-- Quotation ranges over the whole old language, not its winning constant. -/
def depth : Tm → Nat
  | .var i => i + 2
  | .lam a b t => 1 + Nat.max (Nat.max (typeDepth a) (typeDepth b)) (depth t)
  | .app f x => 1 + Nat.max (depth f) (depth x)
  | .zero | .succ | .treeZero | .treeSup | .oracle => 1
  | .natRec r | .treeRec r => 1 + typeDepth r
  | .quote t => 1 + Legacy.depth t

def interp (q : Nat → Nat → Nat) : Tm → List Pack → Pack
  | .var i, env =>
      match lookup env i with
      | some v => v
      | none => ⟨.nat, (0 : Nat)⟩
  | .lam a b body, env =>
      ⟨.arr a b, fun x => cast b (interp q body (⟨a, x⟩ :: env))⟩
  | .app f x, env =>
      let fv := interp q f env
      let xv := interp q x env
      match fv with
      | ⟨.nat, _⟩ => ⟨.nat, (0 : Nat)⟩
      | ⟨.tree, _⟩ => ⟨.nat, (0 : Nat)⟩
      | ⟨.arr a b, g⟩ => ⟨b, g (cast a xv)⟩
  | .zero, _ => ⟨.nat, (0 : Nat)⟩
  | .succ, _ => ⟨.arr .nat .nat, Nat.succ⟩
  | .treeZero, _ => ⟨.tree, Tree.zero⟩
  | .treeSup, _ => ⟨.arr (.arr .nat .tree) .tree, Tree.sup⟩
  | .oracle, _ => ⟨.arr .nat (.arr .nat .nat), q⟩
  | .natRec r, _ =>
      ⟨.arr r (.arr (.arr .nat (.arr r r)) (.arr .nat r)),
       fun z s n => Nat.rec (motive := fun _ => Den r) z s n⟩
  | .treeRec r, _ =>
      ⟨.arr r
        (.arr (.arr (.arr .nat .tree) (.arr (.arr .nat r) r))
          (.arr .tree r)),
       fun z s t => treeFold z s t⟩
  | .quote t, _ => ⟨.nat, Legacy.value t⟩

def value (q : Nat → Nat → Nat) (t : Tm) : Nat :=
  match interp q t [] with
  | ⟨.nat, n⟩ => n
  | ⟨.tree, _⟩ => 0
  | ⟨.arr _ _, _⟩ => 0

def types : Nat → List Ty
  | 0 => []
  | n + 1 =>
      let ts := types n
      .nat :: .tree :: map (fun p => Ty.arr p.1 p.2) (prod ts ts)

/-- Cumulative enumeration. Duplicates are harmless and make inclusion explicit. -/
def terms : Nat → List Tm
  | 0 => []
  | n + 1 =>
      let ts := types n
      let es := terms n
      flatten [
        es,
        [Tm.zero, Tm.succ, Tm.treeZero, Tm.treeSup, Tm.oracle],
        map Tm.var (nats n),
        map (fun p => Tm.lam p.1.1 p.1.2 p.2) (prod (prod ts ts) es),
        map (fun p => Tm.app p.1 p.2) (prod es es),
        map Tm.natRec ts,
        map Tm.treeRec ts,
        map Tm.quote (Legacy.terms n)]

def envelope (q : Nat → Nat → Nat) (d : Nat) : Nat :=
  maximum (value q) (terms d)

def numeral : Nat → Tm
  | 0 => .zero
  | n + 1 => .app .succ (numeral n)

def oracleWitness (i n : Nat) : Tm :=
  .app .succ (.app (.app .oracle (numeral i)) (numeral n))

end Language
end BigNumber
