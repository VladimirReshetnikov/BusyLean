import Init

/-!
# Faithful executable port of Contender 5

Source: codyroux/name-the-biggest-number, Contender.v.

The total interpreter deliberately retains the source's behavior on malformed
terms, its reversed de Bruijn lookup, and its structurally computed casts.
No elaboration, typing filter, normalization oracle, or exception is inserted.
-/

namespace Biggest

/- These elementary helpers intentionally avoid convenience lemmas whose
   existing proofs depend on propositional or function extensionality. -/

theorem maxRight {a b : Nat} (h : a ≤ b) : max a b = b := if_pos h

theorem maxLeft {a b : Nat} (h : b ≤ a) : max a b = a := by
  by_cases hab : a ≤ b
  · exact (maxRight hab).trans (Nat.le_antisymm h hab)
  · exact if_neg hab

theorem leMaxLeft (a b : Nat) : a ≤ max a b := by
  cases Nat.le_total a b with
  | inl h => rw [maxRight h]; exact h
  | inr h => rw [maxLeft h]; exact Nat.le_refl a

theorem leMaxRight (a b : Nat) : b ≤ max a b := by
  cases Nat.le_total a b with
  | inl h => rw [maxRight h]; exact Nat.le_refl b
  | inr h => rw [maxLeft h]; exact h

theorem maxLe {a b c : Nat} (ha : a ≤ c) (hb : b ≤ c) : max a b ≤ c := by
  cases Nat.le_total a b with
  | inl h => rw [maxRight h]; exact hb
  | inr h => rw [maxLeft h]; exact ha

theorem maxAssoc (a b c : Nat) : max (max a b) c = max a (max b c) := by
  apply Nat.le_antisymm
  · exact maxLe
      (maxLe (leMaxLeft _ _)
        (Nat.le_trans (leMaxLeft b c) (leMaxRight a (max b c))))
      (Nat.le_trans (leMaxRight b c) (leMaxRight a (max b c)))
  · exact maxLe
      (Nat.le_trans (leMaxLeft a b) (leMaxLeft (max a b) c))
      (maxLe
        (Nat.le_trans (leMaxRight a b) (leMaxLeft (max a b) c))
        (leMaxRight (max a b) c))

theorem zeroMax (n : Nat) : max 0 n = n := maxRight (Nat.zero_le n)
theorem maxZero (n : Nat) : max n 0 = n := maxLeft (Nat.zero_le n)

theorem memMap {α β : Type} {x : α} {xs : List α} (f : α → β)
    (h : x ∈ xs) : f x ∈ xs.map f := by
  induction h with
  | head xs => exact List.Mem.head _
  | tail a _ ih => exact List.Mem.tail (f a) ih

theorem memAppendLeft {α : Type} {x : α} {xs : List α} (ys : List α)
    (h : x ∈ xs) : x ∈ xs ++ ys := by
  induction h with
  | head xs => exact List.Mem.head _
  | tail a _ ih => exact List.Mem.tail a ih

theorem memAppendRight {α : Type} {x : α} {ys : List α} (xs : List α)
    (h : x ∈ ys) : x ∈ xs ++ ys := by
  induction xs with
  | nil => exact h
  | cons a xs ih => exact List.Mem.tail a ih

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
  | .arr a b => max (typeDepth a) (typeDepth b) + 1

def InterpTy : Ty → Type
  | .nat => Nat
  | .arr a b => InterpTy a → InterpTy b

inductive Term where
  | var : Nat → Term
  | lam : Ty → Ty → Term → Term
  | app : Term → Term → Term
  | zero : Term
  | succ : Term
  | natRec : Ty → Term
  deriving Repr, DecidableEq

def natDepth (n : Nat) : Nat := n + 1

def termDepth : Term → Nat
  | .var x => natDepth x + 1
  | .lam a b body => max (max (typeDepth a) (typeDepth b)) (termDepth body) + 1
  | .app f x => max (termDepth f) (termDepth x) + 1
  | .zero => 1
  | .succ => 1
  | .natRec r => typeDepth r + 1

/-- Index zero selects the final environment element (the outermost binder). -/
def lookup {α : Type} (env : List α) (n : Nat) : Option α :=
  if env.length ≤ n then none else env[env.length - (n + 1)]?

def error : (t : Ty) → InterpTy t
  | .nat => (0 : Nat)
  | .arr _ b => fun _ => error b

def castError (a b : Ty) :
    (InterpTy a → InterpTy b) × (InterpTy b → InterpTy a) :=
  (fun _ => error b, fun _ => error a)

/-- The two directional casts are exactly the source's `cast_impl`. -/
def castImpl : (a b : Ty) →
    (InterpTy a → InterpTy b) × (InterpTy b → InterpTy a)
  | .nat, .nat => (id, id)
  | .nat, .arr c d => castError .nat (.arr c d)
  | .arr a b, .nat => castError (.arr a b) .nat
  | .arr a b, .arr c d =>
      if typeEqb a c && typeEqb b d then
        let ac := castImpl a c
        let bd := castImpl b d
        (fun f x => bd.1 (f (ac.2 x)), fun f x => bd.2 (f (ac.1 x)))
      else castError (.arr a b) (.arr c d)

def cast (a b : Ty) : InterpTy a → InterpTy b := (castImpl a b).1

abbrev Value := (t : Ty) × InterpTy t

/-- Total interpretation, including every ill-typed and open raw term. -/
def interpTerm (env : List Value) : Term → Value
  | .var x =>
      match lookup env x with
      | some v => v
      | none => ⟨.nat, error .nat⟩
  | .lam a b body =>
      ⟨.arr a b, fun x =>
        let result := interpTerm (⟨a, x⟩ :: env) body
        cast result.1 b result.2⟩
  | .app f x =>
      let vf := interpTerm env f
      let vx := interpTerm env x
      match vf with
      | ⟨.nat, _⟩ => ⟨.nat, error .nat⟩
      | ⟨.arr a b, fn⟩ => ⟨b, fn (cast vx.1 a vx.2)⟩
  | .zero => ⟨.nat, (0 : Nat)⟩
  | .succ => ⟨.arr .nat .nat, Nat.succ⟩
  | .natRec r =>
      ⟨.arr r (.arr (.arr .nat (.arr r r)) (.arr .nat r)),
        fun z step n => Nat.rec z (fun k previous => step k previous) n⟩

/-- Coq's left-major `list_prod`, defined here without extra libraries. -/
def listProd {α β : Type} : List α → List β → List (α × β)
  | [], _ => []
  | a :: rest, ys => ys.map (fun b => (a, b)) ++ listProd rest ys

def typesUpTo : Nat → List Ty
  | 0 => []
  | n + 1 =>
      let smaller := typesUpTo n
      .nat :: (listProd smaller smaller).map (fun (a, b) => .arr a b)

def natsUpTo : Nat → List Nat
  | 0 => []
  | n + 1 => n :: natsUpTo n

/-- Enumeration order and duplicated occurrences agree with `list_prod`. -/
def termsUpTo : Nat → List Term
  | 0 => []
  | n + 1 =>
      let tys := typesUpTo n
      let smaller := termsUpTo n
      (natsUpTo n).map .var ++
      ((listProd (listProd tys tys) smaller).map
        (fun ((a, b), body) => .lam a b body) ++
      ((listProd smaller smaller).map (fun (f, x) => .app f x) ++
      ([.zero] ++ ([.succ] ++ tys.map .natRec))))

def eval (t : Term) : Nat :=
  match interpTerm [] t with
  | ⟨.nat, n⟩ => n
  | ⟨.arr _ _, _⟩ => 0

def maxBy {α : Type} (f : α → Nat) (currentMax : Nat)
    (currentBest : α) : List α → α
  | [] => currentBest
  | h :: tail =>
      if currentMax < f h then maxBy f (f h) h tail
      else maxBy f currentMax currentBest tail

def largestOfDepth (n : Nat) : Term := maxBy eval 0 .zero (termsUpTo n)

/-- The literal Lean translation of `largest_STLCNatRec_nat_of_depth`. -/
def baseline (n : Nat) : Nat := eval (largestOfDepth n)

/-- This constant denotes the same natural number as the repository's Contender 5. -/
def contender_5 : Nat := baseline 42

/-- Value-only finite maximum, used by the stronger construction. -/
def maximum {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | a :: rest => max (f a) (maximum f rest)

theorem maxBy_value {α : Type} (f : α → Nat) (xs : List α)
    (currentMax : Nat) (currentBest : α) (hinv : f currentBest = currentMax) :
    f (maxBy f currentMax currentBest xs) = max currentMax (maximum f xs) := by
  induction xs generalizing currentMax currentBest with
  | nil =>
      change f currentBest = max currentMax 0
      rw [maxZero, hinv]
  | cons a xs ih =>
      change f (if currentMax < f a then maxBy f (f a) a xs
        else maxBy f currentMax currentBest xs) =
        max currentMax (max (f a) (maximum f xs))
      by_cases h : currentMax < f a
      · rw [if_pos h, ih (f a) a rfl, ← maxAssoc,
          maxRight (Nat.le_of_lt h)]
      · rw [if_neg h, ih currentMax currentBest hinv, ← maxAssoc,
          maxLeft (Nat.le_of_not_gt h)]

theorem baseline_eq_maximum (n : Nat) :
    baseline n = maximum eval (termsUpTo n) := by
  change eval (maxBy eval 0 .zero (termsUpTo n)) = _
  rw [maxBy_value eval (termsUpTo n) 0 .zero rfl, zeroMax]

theorem maximum_le {α : Type} (f : α → Nat) (xs : List α) (bound : Nat)
    (h : ∀ x, x ∈ xs → f x ≤ bound) : maximum f xs ≤ bound := by
  induction xs with
  | nil => exact Nat.zero_le bound
  | cons a xs ih =>
      apply maxLe
      · exact h a (List.Mem.head xs)
      · exact ih (fun x hx => h x (List.Mem.tail a hx))

theorem le_maximum_of_mem {α : Type} (f : α → Nat) (x : α) (xs : List α)
    (h : x ∈ xs) : f x ≤ maximum f xs := by
  induction h with
  | head xs => exact leMaxLeft _ _
  | tail a _ ih => exact Nat.le_trans ih (leMaxRight _ _)

theorem maximum_mono {α : Type} (f : α → Nat) (xs ys : List α)
    (h : ∀ x, x ∈ xs → x ∈ ys) : maximum f xs ≤ maximum f ys :=
  maximum_le f xs (maximum f ys)
    (fun x hx => le_maximum_of_mem f x ys (h x hx))

/-- This identity also covers function-valued and malformed arguments. -/
theorem eval_succ (t : Term) : eval (.app .succ t) = eval t + 1 := by
  unfold eval
  change Nat.succ (cast (interpTerm [] t).1 .nat (interpTerm [] t).2) =
    (match interpTerm [] t with
      | ⟨.nat, n⟩ => n
      | ⟨.arr _ _, _⟩ => 0) + 1
  cases interpTerm [] t with
  | mk ty value => cases ty <;> rfl

theorem typeDepth_pos (t : Ty) : 0 < typeDepth t := by
  cases t with
  | nat => exact Nat.zero_lt_succ 0
  | arr a b => exact Nat.zero_lt_succ _

theorem termDepth_pos (t : Term) : 0 < termDepth t := by
  cases t <;> exact Nat.zero_lt_succ _

/- Tiny definitional checks. No evaluation of the huge contender is attempted. -/
example : lookup [10, 11, 12] 0 = some 12 := rfl
example : lookup [10, 11, 12] 1 = some 11 := rfl
example : lookup [10, 11, 12] 2 = some 10 := rfl
example : lookup [10, 11, 12] 3 = none := rfl
example : eval (.app .succ .zero) = 1 := rfl
example : eval (.app .zero .succ) = 0 := rfl
example : eval (.app .succ .succ) = 1 := rfl
example : eval (.var 0) = 0 := rfl

end Biggest
