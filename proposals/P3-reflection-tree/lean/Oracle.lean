import Baseline

namespace Biggest

/-! A total, oracle-extended language, with literal quotations of old terms. -/

inductive Expr where
  | quote : Term → Expr
  | input : Expr
  | oracle : Expr
  | var : Nat → Expr
  | lam : Ty → Ty → Expr → Expr
  | app : Expr → Expr → Expr
  | zero : Expr
  | succ : Expr
  | natRec : Ty → Expr
  deriving Repr, DecidableEq

def exprDepth : Expr → Nat
  | .quote t => termDepth t + 1
  | .input => 1
  | .oracle => 1
  | .var x => natDepth x + 1
  | .lam a b body => max (max (typeDepth a) (typeDepth b)) (exprDepth body) + 1
  | .app f x => max (exprDepth f) (exprDepth x) + 1
  | .zero => 1
  | .succ => 1
  | .natRec r => typeDepth r + 1

/-- `quote` evaluates the old term in the empty old environment. -/
def interpExpr (oracle : Nat → Nat) (input : Nat) (env : List Value) :
    Expr → Value
  | .quote t => interpTerm [] t
  | .input => ⟨.nat, input⟩
  | .oracle => ⟨.arr .nat .nat, oracle⟩
  | .var x =>
      match lookup env x with
      | some v => v
      | none => ⟨.nat, error .nat⟩
  | .lam a b body =>
      ⟨.arr a b, fun x =>
        let result := interpExpr oracle input (⟨a, x⟩ :: env) body
        cast result.1 b result.2⟩
  | .app f x =>
      let vf := interpExpr oracle input env f
      let vx := interpExpr oracle input env x
      match vf with
      | ⟨.nat, _⟩ => ⟨.nat, error .nat⟩
      | ⟨.arr a b, fn⟩ => ⟨b, fn (cast vx.1 a vx.2)⟩
  | .zero => ⟨.nat, (0 : Nat)⟩
  | .succ => ⟨.arr .nat .nat, Nat.succ⟩
  | .natRec r =>
      ⟨.arr r (.arr (.arr .nat (.arr r r)) (.arr .nat r)),
        fun z step n => Nat.rec z (fun k previous => step k previous) n⟩

def evalExpr (oracle : Nat → Nat) (input : Nat) (e : Expr) : Nat :=
  match interpExpr oracle input [] e with
  | ⟨.nat, n⟩ => n
  | ⟨.arr _ _, _⟩ => 0

def exprsUpTo : Nat → List Expr
  | 0 => []
  | n + 1 =>
      let tys := typesUpTo n
      let smaller := exprsUpTo n
      (termsUpTo n).map .quote ++ (
      (natsUpTo n).map .var ++ (
      (listProd (listProd tys tys) smaller).map
        (fun ((a, b), body) => .lam a b body) ++ (
      (listProd smaller smaller).map (fun (f, x) => .app f x) ++ (
      [.input, .oracle, .zero, .succ] ++ tys.map .natRec))))

/-- One uniform diagonal reflection step, never a reference to a contender. -/
def reflect (f : Nat → Nat) (n : Nat) : Nat :=
  2 ^ (max (f n) (maximum (evalExpr f n) (exprsUpTo n)) + n + 1)

end Biggest
