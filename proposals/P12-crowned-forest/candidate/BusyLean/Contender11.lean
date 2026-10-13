import BusyLean.Contender10

/-!
# Contender 11: crowned kind-polymorphic forest reflection

```
family10 n    := F10 (F10 n)
F11 n         := stage11 (fun _ => family10) (crown11 (n + 1) index) n
contender_11  := F11 (F11 42)
```

`reflect11 fs n` reflects the kind-polymorphic System Fω language of
Contender 10 against the packed oracle family `fs`.  `stage11` installs that
reflector at every node of a `WTree Nat`.  The tree `index` is the repository's
self-generated join of every `W Nat` tree denoted by the earlier W-language.
Finally, `crown11 (n + 1) index` puts an input-diagonal unary spine above that
index, so `F11 n` crosses `n + 1` additional strict reflection levels before
reaching the self-generated forest.

The seed is Contender 10's *construction as a family*; this file never names
the scalar `contender_10`.

**Do not evaluate `contender_11`.**
-/

namespace BusyLean

/-- One reflection step over kind-polymorphic System Fω with a countable oracle
family.  The family is encoded as one unary oracle by `packFamily`. -/
def reflect11 (fs : W.Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (W.prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (Fk.fvalue (packFamily fs) n) (Fk.ctmsUpTo n))

/-- Forest reflection: install `reflect11` at every node of a well-founded
countably branching tree. -/
def stage11 (seed : W.Family) : BigNumber.WTree Nat → Nat → Nat
  | .leaf => reflect11 seed
  | .node g => reflect11 (fun i => stage11 seed (g i))

/-- Put `k` unary reflection nodes above `a`.  Every node repeats the same child
at all indices; index `0` is therefore always visible. -/
def crown11 : Nat → BigNumber.WTree Nat → BigNumber.WTree Nat
  | 0, a => a
  | k + 1, a => .node fun _ => crown11 k a

/-- Contender 10's construction as a function of its input:
`family10 42 = contender_10` by definitional equality. -/
def family10 (n : Nat) : Nat := F10 (F10 n)

/-- Kind-polymorphic forest reflection along the W-language's self-generated
index, preceded by an input-diagonal reflection crown. -/
def F11 (n : Nat) : Nat :=
  stage11 (fun _ => family10) (crown11 (n + 1) index) n

/-- **Contender 11.**  Never evaluate it. -/
def contender_11 : Nat := F11 (F11 42)

end BusyLean
