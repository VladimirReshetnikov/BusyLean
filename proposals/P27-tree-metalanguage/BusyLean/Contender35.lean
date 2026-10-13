import BusyLean.Ordinal.TreeLanguage4
import BusyLean.Contender34

/-!
# Contender 35: metalanguages stacked along tree ordinals

```
contender_35 := F35 (F35 42)
F35 n        := wDiagonalLift (schedule35 n) (rank35 n)
                  metaTransformer (fun _ => family34) n n
```

Contender 34 iterated a first-order language-closure operator along a tree
ordinal.  Contender 35 raises the closure operator itself to an object-language
primitive and iterates the resulting metalanguages along Contender 34's tree.
The numerical reflection layer then runs over addresses of the resulting tree
and is seeded by the whole Contender 34 family.

**Do not evaluate `contender_35`.**
-/

namespace BusyLean.FL

open Ordinal

/-- Every accepted System-F term over addresses of the metalanguage tree is
strongly normalizing. -/
theorem sn_erase_metatree {f : Nat → Nat} (L : Nat) {fuel : Nat}
    {t : CTm (Addr (metaLanguageTree L))}
    (h : infer fuel [] [] t = some Ty.nat) : F.SN f (erase t) :=
  sn_of_typed (wfUniv f (addr_wf (metaLanguageTree L)))
    (infer_sound fuel t (goodCtx_nil []) h).1

/-- Value of a checked program over addresses of `metaLanguageTree L`, relative
to oracle `f`. -/
def metavalue (L : Nat) (f : Nat → Nat) (fuel : Nat)
    (t : CTm (Addr (metaLanguageTree L))) : Nat :=
  match h : infer fuel [] [] t with
  | some A =>
      if hA : A = Ty.nat then
        F.decode
          (F.nf f ⟨erase t, sn_erase_metatree L (h.trans (congrArg some hA))⟩)
      else 0
  | none => 0

/-- Programs of depth at most `n` over addresses of `metaLanguageTree n`. -/
def metatreeLadderUpTo (n : Nat) :
    List (CTm (Addr (metaLanguageTree n))) :=
  ctmsUpTo (addrUpTo (metaLanguageTree n) n) n

end BusyLean.FL

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- Family-aware reflection over the metalanguage tree. -/
def reflectMetaFamily (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (prefixMax (fun i => fs i n) n)
    (BigNumber.maximum (FL.metavalue n (packFamily fs) n)
      (FL.metatreeLadderUpTo n))

def metaTransformer : Transformer := fun fs _ n => reflectMetaFamily fs n

/-- Contender 34's construction as a family.  In particular,
`family34 42 = contender_34`, definitionally. -/
def family34 (n : Nat) : Nat := F34 (F34 n)

/-- A schedule strictly above the previous schedule, expanded by the whole
Contender 34 family at the current input. -/
def schedule35 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (family34 n + 42) (Autonomous.encode (schedule34 n)))

/-- A W-tree rank above the new schedule. -/
def rank35 (n : Nat) : WTree Nat :=
  Autonomous.realize
    (Autonomous.hyper (family34 n + 42) (Autonomous.encode (schedule35 n)))

/-- W-ranked hyperreflection over metalanguage address ladders, seeded with
Contender 34's family. -/
def F35 (n : Nat) : Nat :=
  wDiagonalLift (schedule35 n) (rank35 n) metaTransformer
    (fun _ => family34) n n

/-- **Contender 35.**  Never evaluate it. -/
def contender_35 : Nat := F35 (F35 42)

end BusyLean
