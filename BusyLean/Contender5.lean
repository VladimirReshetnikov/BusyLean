/-!
# Contender 5, ported from Coq

A definition-by-definition port of the computational part of
`docs/name-the-biggest-number-master/Contender.v` (STLC + natural recursion,
"Contender 5" by samuelgruetter). Each Lean definition below carries the name of
the Coq definition it ports.

The port keeps the source's quirks deliberately, because they affect the value:

* terms are *raw*: ill-typed terms are interpreted too, with `error` defaults;
* variables use reversed de Bruijn indices (`0` = outermost binder);
* lambdas carry both a domain and a codomain annotation, and the body is cast to
  the codomain;
* casts between arrow types recurse only when both components are equal
  according to `typeEqb`, and otherwise produce `error`;
* the winner is selected by `maxBy`, with a strict `<?` update starting from
  `tO`.

Only the reification machinery and proofs of `Contender.v` are omitted; nothing
there is needed to define `contender_5`.
-/

namespace BusyLean.C5

/-- `type` -/
inductive Ty where
  | nat : Ty
  | arr : Ty → Ty → Ty

/-- `type_eqb` -/
def typeEqb : Ty → Ty → Bool
  | .nat, .nat => true
  | .arr a b, .arr c d => typeEqb a c && typeEqb b d
  | .nat, .arr _ _ => false
  | .arr _ _, .nat => false

/-- `interp_type` -/
def den : Ty → Type
  | .nat => Nat
  | .arr a b => den a → den b

/-- `term` -/
inductive Term where
  | var : Nat → Term
  | lam : Ty → Ty → Term → Term
  | app : Term → Term → Term
  | zero : Term
  | succ : Term
  | natRec : Ty → Term

/-- Coq's `nth_error`. -/
def nthError {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => nthError xs n

/-- `lookup`: index `0` is the *last* element of the environment, i.e. the
outermost binder. -/
def lookup {α : Type} (e : List α) (n : Nat) : Option α :=
  let l := e.length
  match Nat.ble l n with
  | true => none
  | false => nthError e (l - (n + 1))

/-- `error` -/
def error : (t : Ty) → den t
  | .nat => (0 : Nat)
  | .arr _ b => fun _ => error b

/-- `cast_error` -/
def castError (src dst : Ty) : (den src → den dst) × (den dst → den src) :=
  (fun _ => error dst, fun _ => error src)

/-- `cast_impl` -/
def castImpl : (src dst : Ty) → (den src → den dst) × (den dst → den src)
  | .nat, .nat => (id, id)
  | .nat, .arr c d => castError .nat (.arr c d)
  | .arr a b, .nat => castError (.arr a b) .nat
  | .arr a b, .arr c d =>
      match typeEqb a c && typeEqb b d with
      | true =>
          let ac := castImpl a c
          let bd := castImpl b d
          (fun f x => bd.1 (f (ac.2 x)), fun f x => bd.2 (f (ac.1 x)))
      | false => castError (.arr a b) (.arr c d)

/-- `cast` -/
def cast {src : Ty} (dst : Ty) : den src → den dst := (castImpl src dst).1

abbrev Value := (t : Ty) × den t

/-- Coq's `Nat.recursion`. -/
def recursion {α : Type} (a : α) (f : Nat → α → α) : Nat → α
  | 0 => a
  | n + 1 => f n (recursion a f n)

/-- `interp_term` -/
def interp : List Value → Term → Value
  | e, .var x =>
      match lookup e x with
      | some r => r
      | none => ⟨.nat, error .nat⟩
  | e, .lam a b body =>
      ⟨.arr a b, fun x => cast b (interp (⟨a, x⟩ :: e) body).2⟩
  | e, .app t₁ t₂ =>
      match interp e t₁, interp e t₂ with
      | ⟨.nat, _⟩, _ => ⟨.nat, error .nat⟩
      | ⟨.arr a _, r₁⟩, ⟨_, r₂⟩ => ⟨_, r₁ (cast a r₂)⟩
  | _, .zero => ⟨.nat, (0 : Nat)⟩
  | _, .succ => ⟨.arr .nat .nat, Nat.succ⟩
  | _, .natRec r =>
      ⟨.arr r (.arr (.arr .nat (.arr r r)) (.arr .nat r)), recursion⟩

/-- Coq's `list_prod`. -/
def listProd {α β : Type} : List α → List β → List (α × β)
  | [], _ => []
  | x :: xs, ys => ys.map (fun y => (x, y)) ++ listProd xs ys

/-- `typesUpTo` -/
def typesUpTo : Nat → List Ty
  | 0 => []
  | m + 1 =>
      let r := typesUpTo m
      .nat :: (listProd r r).map (fun p => .arr p.1 p.2)

/-- `natsUpTo` -/
def natsUpTo : Nat → List Nat
  | 0 => []
  | m + 1 => m :: natsUpTo m

/-- `termsUpTo` -/
def termsUpTo : Nat → List Term
  | 0 => []
  | m + 1 =>
      (natsUpTo m).map Term.var ++
      ((listProd (listProd (typesUpTo m) (typesUpTo m)) (termsUpTo m)).map
          (fun p => Term.lam p.1.1 p.1.2 p.2) ++
      ((listProd (termsUpTo m) (termsUpTo m)).map (fun p => Term.app p.1 p.2) ++
      ([Term.zero] ++ ([Term.succ] ++ (typesUpTo m).map Term.natRec))))

/-- `eval` -/
def eval (t : Term) : Nat :=
  match interp [] t with
  | ⟨.nat, n⟩ => n
  | ⟨.arr _ _, _⟩ => 0

/-- `maxBy` -/
def maxBy {α : Type} (f : α → Nat) (currentMax : Nat) (currentBest : α) : List α → α
  | [] => currentBest
  | h :: t =>
      match Nat.blt currentMax (f h) with
      | true => maxBy f (f h) h t
      | false => maxBy f currentMax currentBest t

/-- `largest_of_depth` -/
def largestOfDepth (n : Nat) : Term := maxBy eval 0 .zero (termsUpTo n)

/-- `largest_STLCNatRec_nat_of_depth` -/
def largestSTLCNatRecNatOfDepth (n : Nat) : Nat := eval (largestOfDepth n)

end BusyLean.C5

namespace BusyLean

/-- Contender 5 (samuelgruetter): the largest STLC+NatRec numeral of depth 42.
Never evaluate it. -/
def contender_5 : Nat := C5.largestSTLCNatRecNatOfDepth 42

end BusyLean
