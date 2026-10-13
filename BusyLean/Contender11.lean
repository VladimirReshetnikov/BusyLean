import BusyLean.Contender10

/-!
# Contender 11: kind-polymorphic Fω reflected along the W-language's trees

Contender 9's amplifier (forest reflection along Contender 6's index, every
tree the W-language defines) applied to Contender 10's stronger language,
kind-polymorphic System Fω.

```
stage11 seed .leaf     = reflect11 seed
stage11 seed (.node g) = reflect11 (fun i => stage11 seed (g i))
F11 n          = stage11 (fun _ => family10) index n
contender_11   = F11 (F11 42)
```

The oracle family reaches the language through the same packed unary oracle,
`orc (2^i · (2m+1)) = fs i m`.

**Do not evaluate `contender_11`.**
-/

namespace BusyLean

/-- One reflection step over kind-polymorphic Fω with an oracle family. -/
def reflect11 (fs : W.Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (W.prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (Fk.fvalue (packFamily fs) n) (Fk.ctmsUpTo n))

/-- Forest reflection of kind-polymorphic Fω along a tree of the W-language. -/
def stage11 (seed : W.Family) : BigNumber.WTree Nat → Nat → Nat
  | .leaf => reflect11 seed
  | .node g => reflect11 (fun i => stage11 seed (g i))

/-- Contender 10's construction as a function of its input: `family10 42 = contender_10`. -/
def family10 (n : Nat) : Nat := F10 (F10 n)

/-- Kind-polymorphic Fω forest reflection along the W-language's index. -/
def F11 (n : Nat) : Nat := stage11 (fun _ => family10) index n

/-- **Contender 11.** Never evaluate it. -/
def contender_11 : Nat := F11 (F11 42)

end BusyLean
