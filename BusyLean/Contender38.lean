import BusyLean.Contender37

/-!
# Contender 38: a fast-growing hierarchy along the trees

```
contender_38 := F38 (F38 42)
F38 n        := hier family37 (jumpTree n) (family37 n)
```

Contenders 25-37 used their trees as the **atoms** of a ladder. A ladder
program of depth `n` names only addresses of depth `<= n`, and erasure forgets
the rest, so the programs see a finite truncation of the tree. Their values
grew through the oracle seeding and the W-ranked amplifiers, not through the
size of the tree.

Here the tree is used directly. `hier g t` is a fast-growing hierarchy along
`t` with base `g`:

* `hier g zero m = g m`,
* `hier g (succ t) m` iterates `hier g t` `m+1` times,
* `hier g (lim f) m` is the maximum of `hier g (f i) m` over `i <= m`.

Taking the maximum over the first branches makes the hierarchy robust to the
zero padding in the program-list limits. With base Contender 37's family and
the tree `jumpTree n`, every node of the tree contributes. This includes the
System F and ladder program trees and all the stacked languages above them.

**Do not evaluate `contender_38`.**
-/

namespace BusyLean.Ordinal

/-- `iterN h k x = h^[k] x`. -/
def iterN (h : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => iterN h k (h x)

/-- The largest of `h 0, ..., h m`. -/
def maxUpTo (h : Nat → Nat) : Nat → Nat
  | 0 => h 0
  | m + 1 => max (maxUpTo h m) (h (m + 1))

/-- A fast-growing hierarchy along a tree, with base `g` and maxima at limits. -/
def hier (g : Nat → Nat) : CTree → Nat → Nat
  | .zero, m => g m
  | .succ t, m => iterN (hier g t) (m + 1) m
  | .lim f, m => maxUpTo (fun i => hier g (f i) m) m
  | .supL _, m => g m
  | .supH _, m => g m

end BusyLean.Ordinal

namespace BusyLean

/-- Contender 37's construction as a function of its input: `family37 42 = contender_37`. -/
def family37 (n : Nat) : Nat := F37 (F37 n)

/-- The hierarchy along Contender 37's tree, based on Contender 37's family. -/
def F38 (n : Nat) : Nat := Ordinal.hier family37 (jumpTree n) (family37 n)

/-- **Contender 38.** Never evaluate it. -/
def contender_38 : Nat := F38 (F38 42)

end BusyLean
