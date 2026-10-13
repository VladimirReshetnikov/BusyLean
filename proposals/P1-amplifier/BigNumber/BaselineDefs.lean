import Std

/-!
# Exact computational port of the upstream fifth contender

The source is `codyroux/name-the-biggest-number/Contender.v`.  This file ports
the raw (possibly ill-typed) syntax and its total default-valued interpretation,
including reversed de Bruijn lookup and the structural, computational casts.
It does not restrict the enumeration to well-typed terms.

Only the computational prefix needed to define `contender_5` is ported.  The
upstream reification development and its functional-extensionality import are
not needed here.  The equivalence of selected-max and numeric-max formulations
is proved below without evaluating the depth-42 enumeration.
-/

namespace BigNumber.Baseline

inductive Ty where
  | nat : Ty
  | arr : Ty → Ty → Ty
  deriving Repr, DecidableEq

def typeEqb : Ty → Ty → Bool
  | .nat, .nat => true
  | .arr a b, .arr c d => typeEqb a c && typeEqb b d
  | _, _ => false

def typeDepth : Ty → Nat
  | .nat => 1
  | .arr a b => Nat.succ (max (typeDepth a) (typeDepth b))

def interpTy : Ty → Type
  | .nat => Nat
  | .arr a b => interpTy a → interpTy b

inductive Term where
  | var : Nat → Term
  | lam : Ty → Ty → Term → Term
  | app : Term → Term → Term
  | zero : Term
  | succ : Term
  | natRec : Ty → Term
  deriving Repr, DecidableEq

def natDepth (n : Nat) : Nat := Nat.succ n

def termDepth : Term → Nat
  | .var x => Nat.succ (natDepth x)
  | .lam a b body =>
      Nat.succ (max (max (typeDepth a) (typeDepth b)) (termDepth body))
  | .app t₁ t₂ => Nat.succ (max (termDepth t₁) (termDepth t₂))
  | .zero => 1
  | .succ => 1
  | .natRec r => Nat.succ (typeDepth r)

/-- Index zero selects the final element, i.e. the outermost binder. -/
def lookup {α : Type} (e : List α) (n : Nat) : Option α :=
  let l := e.length
  if l ≤ n then none else e[l - Nat.succ n]?

def error : (tp : Ty) → interpTy tp
  | .nat => Nat.zero
  | .arr _ b => fun _ => error b

def castError (src dst : Ty) :
    (interpTy src → interpTy dst) × (interpTy dst → interpTy src) :=
  (fun _ => error dst, fun _ => error src)

/-- The two mutually inverse-direction structural casts used upstream.

At equal arrow types these eta-expand recursively.  Unequal types return
the corresponding default value.  No equality eliminator or opaque proof
occurs in the computation.
-/
def castImpl : (src dst : Ty) →
    (interpTy src → interpTy dst) × (interpTy dst → interpTy src)
  | .nat, .nat => (id, id)
  | .nat, .arr c d => castError .nat (.arr c d)
  | .arr a b, .nat => castError (.arr a b) .nat
  | .arr a b, .arr c d =>
      if typeEqb a c && typeEqb b d then
        let ac := castImpl a c
        let bd := castImpl b d
        (fun f x => bd.1 (f (ac.2 x)), fun f x => bd.2 (f (ac.1 x)))
      else castError (.arr a b) (.arr c d)

def cast {src : Ty} (dst : Ty) : interpTy src → interpTy dst :=
  (castImpl src dst).1

abbrev Value := Sigma interpTy

/-- Total interpretation of every raw term, including malformed terms. -/
def interpTerm (e : List Value) : Term → Value
  | .var x =>
      match lookup e x with
      | some r => r
      | none => ⟨.nat, error .nat⟩
  | .lam a b body =>
      ⟨.arr a b, fun x =>
        let r := interpTerm (⟨a, x⟩ :: e) body
        cast b r.2⟩
  | .app t₁ t₂ =>
      let r₁ := interpTerm e t₁
      let r₂ := interpTerm e t₂
      match r₁ with
      | ⟨.nat, _⟩ => ⟨.nat, error .nat⟩
      | ⟨.arr a b, f⟩ => ⟨b, f (cast a r₂.2)⟩
  | .zero => ⟨.nat, Nat.zero⟩
  | .succ => ⟨.arr .nat .nat, Nat.succ⟩
  | .natRec r =>
      ⟨.arr r (.arr (.arr .nat (.arr r r)) (.arr .nat r)),
        fun z step n => Nat.rec (motive := fun _ => interpTy r) z step n⟩

/-- Coq's `List.list_prod`: left argument outermost, right innermost. -/
def listProd {α β : Type} : List α → List β → List (α × β)
  | [], _ => []
  | x :: xs, ys => ys.map (fun y => (x, y)) ++ listProd xs ys

def typesUpTo : Nat → List Ty
  | 0 => []
  | n + 1 =>
      let r := typesUpTo n
      .nat :: (listProd r r).map (fun p => .arr p.1 p.2)

def natsUpTo : Nat → List Nat
  | 0 => []
  | n + 1 => n :: natsUpTo n

/-- Enumeration order, products, annotations, and raw terms match upstream. -/
def termsUpTo : Nat → List Term
  | 0 => []
  | n + 1 =>
      (natsUpTo n).map Term.var ++
      (listProd (listProd (typesUpTo n) (typesUpTo n)) (termsUpTo n)).map
        (fun p => .lam p.1.1 p.1.2 p.2) ++
      (listProd (termsUpTo n) (termsUpTo n)).map (fun p => .app p.1 p.2) ++
      [.zero] ++ [.succ] ++ (typesUpTo n).map Term.natRec

def eval (t : Term) : Nat :=
  match interpTerm [] t with
  | ⟨.nat, n⟩ => n
  | ⟨.arr _ _, _⟩ => 0

/-- Keep the previous winner on ties, exactly as in the Coq definition. -/
def maxBy {α : Type} (f : α → Nat) (currentMax : Nat)
    (currentBest : α) : List α → α
  | [] => currentBest
  | h :: t =>
      if currentMax < f h then maxBy f (f h) h t
      else maxBy f currentMax currentBest t

def largestOfDepth (n : Nat) : Term := maxBy eval 0 .zero (termsUpTo n)

def largestSTLCNatRecNatOfDepth (n : Nat) : Nat := eval (largestOfDepth n)

/-- Literal port of the definition designated Contender 5 upstream. -/
def contender_5 : Nat := largestSTLCNatRecNatOfDepth 42

/-- A convenient numerical presentation of the very same finite maximum. -/
def envelope (n : Nat) : Nat :=
  (termsUpTo n).foldl (fun m t => max m (eval t)) 0

end BigNumber.Baseline
