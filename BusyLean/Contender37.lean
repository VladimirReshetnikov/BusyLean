import BusyLean.Contender36

/-!
# Contender 37: languages stacked over the ladder jump

```
contender_37 := F37 (F37 42)
F37 n        := wDiagonalLift (schedule37 n) (rank37 n) jtTransformer (fun _ => family36) n n
```

Contender 36's bootstrap is a *jump*: `jump n t = bootT t t` iterates "trees
of the ladder over `Addr t`" along `t` itself. Contenders 33 and 34 stacked
the System T language over trees on a primitive. Here the primitive is the
jump: `stackOver b (a+1) = langLift (stackOver b a)`, with pointwise limits.
Every level is all of System T over trees with the previous level as a
primitive, so the levels iterate the jump transfinitely and diagonalize over
those iterations. At input `n` the height and the argument are both Contender
36's tree, and the ladder runs over the addresses of the result.

**Do not evaluate `contender_37`.**
-/

namespace BusyLean.Ordinal

/-- Languages stacked along a tree ordinal over the base primitive `b`. -/
def stackOver (b : CTree → CTree) : CTree → CTree → CTree
  | .zero => b
  | .succ a => langLift (stackOver b a)
  | .lim f => fun t => .lim fun i => stackOver b (f i) t
  | .supL _ => b
  | .supH _ => b

end BusyLean.Ordinal

namespace BusyLean

/-- Contender 36's construction as a function of its input: `family36 42 = contender_36`. -/
def family36 (n : Nat) : Nat := F36 (F36 n)

/-- The ladder jump at depth `n`: bootstrap `t` along itself. -/
def jump (n : Nat) (t : Ordinal.CTree) : Ordinal.CTree := FLT.bootT family36 n t t

/-- Contender 36's tree, with languages stacked over the jump to its own height. -/
def jumpTree (n : Nat) : Ordinal.CTree :=
  .lim fun i => if i = 0 then bootTree n else Ordinal.stackOver (jump n) (bootTree n) (bootTree n)

end BusyLean

namespace BusyLean.FL

open Ordinal

theorem sn_erase_jumptree {f : Nat → Nat} (L : Nat) {fuel : Nat} {t : CTm (Addr (jumpTree L))}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f (addr_wf (jumpTree L))) (infer_sound fuel t (goodCtx_nil []) h).1

/-- The value of a program over the addresses of `jumpTree L` (type checked with
`fuel`) relative to the oracle `f`. -/
def jtvalue (L : Nat) (f : Nat → Nat) (fuel : Nat) (t : CTm (Addr (jumpTree L))) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode (F.nf f ⟨erase t, sn_erase_jumptree L (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Programs of depth `≤ n` over the addresses of `jumpTree n`. -/
def jtLadderUpTo (n : Nat) : List (CTm (Addr (jumpTree n))) := ctmsUpTo (addrUpTo (jumpTree n) n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Address-ladder reflection with a countable oracle family; the input also picks the tree. -/
def reflectJTFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.jtvalue n (packFamily fs) n) (FL.jtLadderUpTo n))

def jtTransformer : Transformer := fun fs _ n => reflectJTFamily fs n

def schedule37 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family36 n + 42) (Autonomous.encode (schedule36 n)))

def rank37 (n : Nat) : WTree Nat :=
  Autonomous.realize (Autonomous.hyper (family36 n + 42) (Autonomous.encode (schedule37 n)))

/-- W-ranked hyperreflection of the address ladders, seeded with Contender 36's family. -/
def F37 (n : Nat) : Nat :=
  wDiagonalLift (schedule37 n) (rank37 n) jtTransformer (fun _ => family36) n n

/-- **Contender 37.** Never evaluate it. -/
def contender_37 : Nat := F37 (F37 42)

end BusyLean
