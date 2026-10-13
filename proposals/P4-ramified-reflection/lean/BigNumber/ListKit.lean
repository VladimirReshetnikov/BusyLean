import Std

/-! Small computational definitions. Proofs are in Proofs.lean. -/
namespace BigNumber
namespace Lists
universe u v

def cat {α : Type u} : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: cat xs ys

def map {α : Type u} {β : Type v} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: map f xs

def flatten {α : Type u} : List (List α) → List α
  | [] => []
  | xs :: xss => cat xs (flatten xss)

def prod {α : Type u} {β : Type v} : List α → List β → List (α × β)
  | [], _ => []
  | x :: xs, ys => cat (map (fun y => (x, y)) ys) (prod xs ys)

def nats : Nat → List Nat
  | 0 => []
  | n + 1 => n :: nats n

def nth {α : Type u} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => nth xs n

def lookup {α : Type u} (xs : List α) (i : Nat) : Option α :=
  if xs.length ≤ i then none else nth xs (xs.length - (i + 1))

def maximum {α : Type u} (f : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => Nat.max (f x) (maximum f xs)

/-- This is the upstream scan, including its current-maximum argument. -/
def maxBy {α : Type u} (f : α → Nat) (current : Nat) (best : α) : List α → α
  | [] => best
  | x :: xs =>
    if current < f x then maxBy f (f x) x xs
    else maxBy f current best xs

end Lists
end BigNumber
