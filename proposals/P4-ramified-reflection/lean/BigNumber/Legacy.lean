import BigNumber.ListKit

/-!
Computational port of the Contender-5 language, not of its proof automation.
Upstream: codyroux/name-the-biggest-number, Contender.v
Content blob: f92db72deb0f3a4d4e3b575b4949eda73b1417a0
Upstream license: MIT; see provenance/UPSTREAM_LICENSE.txt.
In particular: binder *levels*, default values, and recursive casts are retained.
-/
namespace BigNumber.Legacy
open BigNumber.Lists

inductive Ty : Type where
  | nat
  | arr (dom cod : Ty)

def Den : Ty → Type
  | .nat => Nat
  | .arr a b => Den a → Den b

def eqb : Ty → Ty → Bool
  | .nat, .nat => true
  | .arr a b, .arr c d => eqb a c && eqb b d
  | _, _ => false

def typeDepth : Ty → Nat
  | .nat => 1
  | .arr a b => 1 + Nat.max (typeDepth a) (typeDepth b)

def defaultVal : (a : Ty) → Den a
  | .nat => 0
  | .arr _ b => fun _ => defaultVal b

def castPair : (a b : Ty) → (Den a → Den b) × (Den b → Den a)
  | .nat, .nat => (fun x => x, fun x => x)
  | .nat, .arr c d =>
      (fun _ => defaultVal (.arr c d), fun _ => defaultVal .nat)
  | .arr a b, .nat =>
      (fun _ => defaultVal .nat, fun _ => defaultVal (.arr a b))
  | .arr a b, .arr c d =>
      if eqb a c && eqb b d then
        let ac := castPair a c
        let bd := castPair b d
        (fun f x => bd.1 (f (ac.2 x)),
         fun f x => bd.2 (f (ac.1 x)))
      else
        (fun _ => defaultVal (.arr c d), fun _ => defaultVal (.arr a b))

abbrev Pack := Sigma Den

def cast (b : Ty) (v : Pack) : Den b := (castPair v.1 b).1 v.2

inductive Tm : Type where
  | var (i : Nat)
  | lam (dom cod : Ty) (body : Tm)
  | app (fn arg : Tm)
  | zero
  | succ
  | natRec (result : Ty)

def depth : Tm → Nat
  | .var i => i + 2
  | .lam a b t => 1 + Nat.max (Nat.max (typeDepth a) (typeDepth b)) (depth t)
  | .app f x => 1 + Nat.max (depth f) (depth x)
  | .zero | .succ => 1
  | .natRec r => 1 + typeDepth r

def interp : Tm → List Pack → Pack
  | .var i, env =>
      match lookup env i with
      | some v => v
      | none => ⟨.nat, 0⟩
  | .lam a b body, env =>
      ⟨.arr a b, fun x => cast b (interp body (⟨a, x⟩ :: env))⟩
  | .app f x, env =>
      let fv := interp f env
      let xv := interp x env
      match fv with
      | ⟨.nat, _⟩ => ⟨.nat, 0⟩
      | ⟨.arr a b, g⟩ => ⟨b, g (cast a xv)⟩
  | .zero, _ => ⟨.nat, 0⟩
  | .succ, _ => ⟨.arr .nat .nat, Nat.succ⟩
  | .natRec r, _ =>
      ⟨.arr r (.arr (.arr .nat (.arr r r)) (.arr .nat r)),
       fun z s n => Nat.rec (motive := fun _ => Den r) z s n⟩

def value (t : Tm) : Nat :=
  match interp t [] with
  | ⟨.nat, n⟩ => n
  | ⟨.arr _ _, _⟩ => 0

def types : Nat → List Ty
  | 0 => []
  | n + 1 =>
      let ts := types n
      .nat :: map (fun p => Ty.arr p.1 p.2) (prod ts ts)

def terms : Nat → List Tm
  | 0 => []
  | n + 1 =>
      let ts := types n
      let es := terms n
      flatten [
        map Tm.var (nats n),
        map (fun p => Tm.lam p.1.1 p.1.2 p.2) (prod (prod ts ts) es),
        map (fun p => Tm.app p.1 p.2) (prod es es),
        [Tm.zero], [Tm.succ], map Tm.natRec ts]

end BigNumber.Legacy
