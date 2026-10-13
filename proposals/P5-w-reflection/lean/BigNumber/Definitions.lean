import Init

/-!
A conservative finite-type W-language and a constructive large-number entry.
Definitions only; no evaluation of contender_6 is requested.
See the README for the validation status of this source.
-/
namespace BigNumber

inductive WTree (A : Type) : Type where
  | leaf : WTree A
  | node : (A → WTree A) → WTree A

/-- Reindexing the branches, contravariantly in the branching type. -/
def wmap {A B : Type} (g : B → A) : WTree A → WTree B :=
  WTree.rec WTree.leaf (fun _ ih => WTree.node (fun b => ih (g b)))

inductive Ty where
  | nat : Ty
  | arr : Ty → Ty → Ty
  | wt : Ty → Ty

def eqb : Ty → Ty → Bool
  | .nat, .nat => true
  | .arr a b, .arr c d => eqb a c && eqb b d
  | .wt a, .wt b => eqb a b
  | _, _ => false

def den : Ty → Type
  | .nat => Nat
  | .arr a b => den a → den b
  | .wt a => WTree (den a)

def defaultValue : (a : Ty) → den a
  | .nat => 0
  | .arr _ b => fun _ => defaultValue b
  | .wt _ => .leaf

def badCast (a b : Ty) : (den a → den b) × (den b → den a) :=
  (fun _ => defaultValue b, fun _ => defaultValue a)

/-- The original arrow casts are retained, not replaced by dynamic typing. -/
def castPair : (a b : Ty) → (den a → den b) × (den b → den a)
  | .nat, .nat => (fun x => x, fun x => x)
  | .arr a b, .arr c d =>
      if eqb a c && eqb b d then
        let ac := castPair a c
        let bd := castPair b d
        (fun f x => bd.1 (f (ac.2 x)),
         fun f x => bd.2 (f (ac.1 x)))
      else badCast (.arr a b) (.arr c d)
  | .wt a, .wt b =>
      if eqb a b then
        let ab := castPair a b
        (wmap ab.2, wmap ab.1)
      else badCast (.wt a) (.wt b)
  | a, b => badCast a b

def castValue {a : Ty} (b : Ty) (x : den a) : den b :=
  (castPair a b).1 x

inductive Term where
  | var : Nat → Term
  | lam : Ty → Ty → Term → Term
  | app : Term → Term → Term
  | zero : Term
  | succ : Term
  | natrec : Ty → Term
  | wzero : Ty → Term
  | wnode : Ty → Term
  | wrec : Ty → Ty → Term

abbrev Value := Sigma den
abbrev Env := List Value

/-- An explicit list lookup avoids any library-specific indexing convention. -/
def nth? {A : Type} : List A → Nat → Option A
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: xs, n+1 => nth? xs n

/-- 0 refers to the oldest binding, exactly as in Contender.v. -/
def lookup {A : Type} (xs : List A) (n : Nat) : Option A :=
  if xs.length ≤ n then none else nth? xs (xs.length - (n+1))

def interpret (env : Env) : Term → Value
  | .var n =>
      match lookup env n with
      | some v => v
      | none => ⟨.nat, 0⟩
  | .lam a b body =>
      ⟨.arr a b, fun x =>
        let r := interpret (⟨a, x⟩ :: env) body
        castValue b r.2⟩
  | .app t u =>
      let v := interpret env t
      let w := interpret env u
      match v with
      | ⟨.nat, _⟩ => ⟨.nat, 0⟩
      | ⟨.wt _, _⟩ => ⟨.nat, 0⟩
      | ⟨.arr a b, f⟩ => ⟨b, f (castValue a w.2)⟩
  | .zero => ⟨.nat, 0⟩
  | .succ => ⟨.arr .nat .nat, Nat.succ⟩
  | .natrec r =>
      ⟨.arr r (.arr (.arr .nat (.arr r r)) (.arr .nat r)),
       fun z s n => Nat.rec z (fun i acc => s i acc) n⟩
  | .wzero a => ⟨.wt a, WTree.leaf⟩
  | .wnode a =>
      ⟨.arr (.arr a (.wt a)) (.wt a), WTree.node⟩
  | .wrec a r =>
      ⟨.arr r
        (.arr (.arr (.arr a (.wt a)) (.arr (.arr a r) r))
          (.arr (.wt a) r)),
       fun z s w => WTree.rec z (fun f ih => s f ih) w⟩
termination_by structural t => t

def evaluate (t : Term) : Nat :=
  match interpret [] t with
  | ⟨.nat, n⟩ => n
  | ⟨.arr _ _, _⟩ => 0
  | ⟨.wt _, _⟩ => 0

def cross {A B : Type} (xs : List A) (ys : List B) : List (A × B) :=
  xs.flatMap (fun x => ys.map (fun y => (x, y)))

def natsUpTo : Nat → List Nat
  | 0 => []
  | n+1 => n :: natsUpTo n

/-- The reference enumerators use only the six original term constructors. -/
def oldTypes : Nat → List Ty
  | 0 => []
  | n+1 =>
      let ts := oldTypes n
      .nat :: (cross ts ts).map (fun p => .arr p.1 p.2)

def oldTerms : Nat → List Term
  | 0 => []
  | n+1 =>
      let ts := oldTypes n
      let es := oldTerms n
      (natsUpTo n).map Term.var ++
      (cross (cross ts ts) es).map (fun p => .lam p.1.1 p.1.2 p.2) ++
      (cross es es).map (fun p => .app p.1 p.2) ++
      [.zero] ++ [.succ] ++ ts.map Term.natrec

/-- Full closure under arrows and W-types, with no external type oracle. -/
def allTypes : Nat → List Ty
  | 0 => []
  | n+1 =>
      let ts := allTypes n
      [.nat] ++ (cross ts ts).map (fun p => .arr p.1 p.2) ++ ts.map Ty.wt

def allTerms : Nat → List Term
  | 0 => []
  | n+1 =>
      let ts := allTypes n
      let es := allTerms n
      (natsUpTo n).map Term.var ++
      (cross (cross ts ts) es).map (fun p => .lam p.1.1 p.1.2 p.2) ++
      (cross es es).map (fun p => .app p.1 p.2) ++
      [.zero] ++ [.succ] ++ ts.map Term.natrec ++
      ts.map Term.wzero ++ ts.map Term.wnode ++
      (cross ts ts).map (fun p => .wrec p.1 p.2)

/-- Primitive maximum: no comparison theorem or classical dependency is hidden. -/
def maxN : Nat → Nat → Nat
  | 0, b => b
  | a+1, 0 => a+1
  | a+1, b+1 => Nat.succ (maxN a b)

def maximum {A : Type} (score : A → Nat) : List A → Nat
  | [] => 0
  | a :: xs => maxN (score a) (maximum score xs)

/-- Numerically the original selector has this value; see the port audit. -/
def oldMaximum (n : Nat) : Nat := maximum evaluate (oldTerms n)
def wMaximum (n : Nat) : Nat := maximum evaluate (allTerms n)

/-- The redundant maximum makes the conservative inclusion explicit. -/
def envelope (n : Nat) : Nat := maxN (oldMaximum n) (wMaximum n)

def pow2 : Nat → Nat
  | 0 => 1
  | n+1 => 2 * pow2 n

/-- Seed for a hierarchy, not an invocation of the previous named contender. -/
def seed (n : Nat) : Nat :=
  Nat.succ (maxN n (maxN (envelope n) (pow2 (n+1))))

/-- Tail-recursive iteration, structurally decreasing in the count. -/
def iterate {A : Type} (f : A → A) : Nat → A → A
  | 0, x => x
  | k+1, x => iterate f k (f x)

def rows (f : Nat → Nat) : Nat → Nat → Nat
  | 0, n => f n
  | k+1, n =>
      rows f k n + iterate (rows f k) (n+1) (n+1) + 1

/-- A first diagonal across all the finite rows. -/
def jump (f : Nat → Nat) (n : Nat) : Nat := rows f n n

/-- A second, independent iteration of the diagonalization operator. -/
def ranks : Nat → Nat → Nat
  | 0 => seed
  | k+1 => jump (ranks k)

def diagonal (n : Nat) : Nat := ranks n n

/-- The proposed entry. It does not depend on contender_5. -/
def contender_6 : Nat := iterate diagonal 42 42

end BigNumber
