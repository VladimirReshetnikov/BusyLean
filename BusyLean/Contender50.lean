import BusyLean.SystemFLT2.Numbers
import BusyLean.Contender49

/-!
# Contender 50: ladder reflection over the tree

```
contender_50 := F50 (F50 42)
F50 n        := hier (ladderReflect family49 T) T N
                where N = family49 n, T = levelIterTree N
```

Contender 49 read its tree with System FT2 programs. The ladder language is
stronger: it has dynamic kinds and a universe for every named atom.
`FLT2.readNat` runs a ladder program of the numeric reader type
(`FLT2.natReaderTy`) on the FT2 recursor and the oracle tree.
`ladderReflect g T m` exceeds Contender 49's reflection and every such program
of depth `<= m` over the addresses of `T`.

**Do not evaluate `contender_50`.**
-/

namespace BusyLean.FLT2

open BusyLean.Ordinal

/-- The number a numeric reader program over the addresses of `T` computes from `T`
(type checked with `fuel`); `0` unless it has the numeric reader type. -/
def readNat (g : Nat → Nat) (T : CTree) (fuel : Nat) (p : CTm (Addr T)) : Nat :=
  match h : infer fuel [] [] p with
  | some A =>
      if hA : A = natReaderTy then
        FT2.decode (FT2.nf ⟨g, T⟩ ⟨applyNatReader (erase p),
          sn_of_natReaderTy (wfUniv ⟨g, T⟩ (addr_wf T))
            (infer_sound fuel p (goodCtx_nil []) (h.trans (congrArg some hA))).1⟩)
      else 0
  | none => 0

end BusyLean.FLT2

namespace BusyLean

/-- Reflection over FT2 and over numeric ladder reader programs, with oracles `g` and `T`. -/
def ladderReflect (g : Nat → Nat) (T : Ordinal.CTree) (m : Nat) : Nat :=
  m + 1 + BigNumber.maxN (treeReflect g T m)
    (BigNumber.maximum (FLT2.readNat g T m) (FLT2.ctmsUpTo (Ordinal.addrUpTo T m) m))

/-- Contender 49's construction as a function of its input: `family49 42 = contender_49`. -/
def family49 (n : Nat) : Nat := F49 (F49 n)

/-- The hierarchy along Contender 48's tree, based on ladder reflection over that tree. -/
def F50 (n : Nat) : Nat :=
  Ordinal.hier (ladderReflect family49 (levelIterTree (family49 n)))
    (levelIterTree (family49 n)) (family49 n)

/-- **Contender 50.** Never evaluate it. -/
def contender_50 : Nat := F50 (F50 42)

end BusyLean
