import BusyLean.Ordinal.TreeLanguage
import BusyLean.Contender31

/-!
# Contender 32: a programming language for tree ordinals

```
contender_32 := F32 (F32 42)
F32 n        := wDiagonalLift (schedule32 n) (rank32 n) lgTransformer (fun _ => family31) n n
```

Contenders 25–31 are each one particular combination of tree-ordinal
operations. `Ordinal.TreeLanguage` makes the combinations programs. It is
System T with a base type of countable tree ordinals, a recursor iterating along
any tree at any type, and Contender 31's construction as a primitive
`boost : tree ⇒ tree`. The language is simply typed and predicative, so it has a
direct semantic interpreter by structural recursion. No normalization proof is
needed. `languageTree n` is the limit of Contender 31's tree and of all closed
`tree` programs of size `≤ n + 3`, so it contains transfinite and higher-type
iterations of `boost`. Input `n` uses the ladder over its addresses.

The amplifier is the W-ranked lift hierarchy, seeded with Contender 31's
family `family31 n = F31 (F31 n)`.

**Do not evaluate `contender_32`.**
-/

namespace BusyLean.FL

open Ordinal

theorem sn_erase_lgtree {f : Nat → Nat} (L : Nat) {fuel : Nat} {t : CTm (Addr (languageTree L))}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f (addr_wf (languageTree L))) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a program over the addresses of `languageTree L` (type checked with
`fuel`) relative to the oracle `f`. -/
def lgvalue (L : Nat) (f : Nat → Nat) (fuel : Nat) (t : CTm (Addr (languageTree L))) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_lgtree L (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Programs of depth `≤ n` over the addresses of `languageTree n`. -/
def lgtreeLadderUpTo (n : Nat) : List (CTm (Addr (languageTree n))) := ctmsUpTo (addrUpTo (languageTree n) n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Address-ladder reflection with a countable oracle family; the input also picks the tree. -/
def reflectLGFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.lgvalue n (packFamily fs) n) (FL.lgtreeLadderUpTo n))

def lgTransformer : Transformer := fun fs _ n => reflectLGFamily fs n

/-- Contender 31's construction as a function of its input: `family31 42 = contender_31`. -/
def family31 (n : Nat) : Nat := F31 (F31 n)

def schedule32 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family31 n + 42) (Autonomous.encode (schedule31 n)))

def rank32 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family31 n + 42) (Autonomous.encode (schedule32 n)))

/-- W-ranked hyperreflection of the address ladders, seeded with Contender 31's family. -/
def F32 (n : Nat) : Nat :=
  wDiagonalLift (schedule32 n) (rank32 n) lgTransformer (fun _ => family31) n n

/-- **Contender 32.** Never evaluate it. -/
def contender_32 : Nat := F32 (F32 42)

end BusyLean
