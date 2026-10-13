import BusyLean.Contender10

/-!
# Contender 11: diagonal forest closure of kind-polymorphic reflection

The current BusyLean contender applies one kind-polymorphic System Fω
reflection step to Contender 9's family.  This construction closes that step
under three independent amplifiers:

1. a *family* of child stages is exposed through the existing computable
   pairing `packFamily`;
2. at input `n`, a unary `Fk.reflectFk` tower whose height is the already
   enormous value `reflect11 fs n + 1` is included explicitly; and
3. the resulting diagonal is iterated along the W-language's self-indexing
   tree `index`.

The extra outer maximum is intentional.  It makes the key comparison facts
transparent to the kernel: the diagonal contains both the direct family-aware
reflection and the full self-height tower, so no informal ordinal calibration
is needed for the strict inequalities.

```
reflect11 fs n  := family-aware Fk reflection over fs
towerFk k f     := k iterated Fk reflection steps over f
diagonal11 fs n := max (reflect11 fs n)
                       (towerFk (reflect11 fs n + 1)
                         (reflect11 fs) n), plus n + 1
stage11 seed    := diagonal11 iterated along a W-tree
F11 n           := stage11 (fun _ => family10) index n
contender_11    := F11 (F11 42)
```

**Do not evaluate `contender_11`.**
-/

namespace BusyLean

/-- One family-aware reflection step for kind-polymorphic System Fω.

The family `fs : Nat -> Nat -> Nat` is presented to the object language through
`packFamily`, while the explicit prefix maximum ensures that every child with
index at most `n` is directly dominated at input `n`. -/
def reflect11 (fs : W.Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (W.prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (Fk.fvalue (packFamily fs) n) (Fk.ctmsUpTo n))

/-- `k` successive unary kind-polymorphic reflection steps over a seed family. -/
def towerFk : Nat -> (Nat -> Nat) -> Nat -> Nat
  | 0, f => f
  | Nat.succ k, f => Fk.reflectFk (towerFk k f)

/-- The diagonal closure at input `n`.

It contains both the direct family-aware reflection and a unary reflection
tower whose height is `reflect11 fs n + 1`. Thus the tower height already
dominates every visible child, every accepted bounded program, and the input.
The additive `n + 1` makes the input itself strictly smaller as well. -/
def diagonal11 (fs : W.Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (reflect11 fs n)
    (towerFk (reflect11 fs n + 1) (reflect11 fs) n)

/-- Diagonal forest closure along a W-tree. -/
def stage11 (seed : W.Family) : BigNumber.WTree Nat -> Nat -> Nat
  | .leaf => diagonal11 seed
  | .node g => diagonal11 (fun i => stage11 seed (g i))

/-- Contender 10's construction as a function of its input:
`family10 42 = contender_10`. -/
def family10 (n : Nat) : Nat := F10 (F10 n)

/-- The Contender 11 family: diagonal forest closure along the W-language's
self-indexing tree, seeded by Contender 10's construction. -/
def F11 (n : Nat) : Nat := stage11 (fun _ => family10) index n

/-- **Contender 11.** Never evaluate it. -/
def contender_11 : Nat := F11 (F11 42)

end BusyLean
