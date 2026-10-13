import BusyLean.Contender52

/-!
# Contender 53: reflection iterated along the tree

```
contender_53 := F53 (F53 42)
F53 n        := hier (reflAlong T family52 T) T N
                where N = family52 n, T = stackTree N
```

Contenders 49-52 read the final tree with one reflection: FT2 and ladder
programs that recurse over the tree, with a fixed number oracle. Here the
reflection is iterated along the tree itself:

* `reflAlong T g 0 = g`;
* `reflAlong T g (a+1) = ladderReflect (reflAlong T g a) T`: programs reading
  `T` may call the previous level as their number oracle;
* limits take the maximum over the first `m+1` branches, as in `hier`.

Each successor level closes the previous one under all FT2 and ladder
programs over `T`, so this is hyperreflection (Contenders 17 and 23) along the
giant tree. `hier` then runs along the tree with this base.

**Do not evaluate `contender_53`.**
-/

namespace BusyLean

open Ordinal (CTree)

/-- Ladder reflection over `T`, iterated along a tree, starting from `g`. -/
def reflAlong (T : CTree) (g : Nat → Nat) : CTree → Nat → Nat
  | .zero => g
  | .succ a => ladderReflect (reflAlong T g a) T
  | .lim f => fun m => Ordinal.maxUpTo (fun i => reflAlong T g (f i) m) m
  | .supL _ => g
  | .supH _ => g

/-- Contender 52's construction as a function of its input: `family52 42 = contender_52`. -/
def family52 (n : Nat) : Nat := F52 (F52 n)

/-- The hierarchy along the stacked tree, based on reflection iterated along it. -/
def F53 (n : Nat) : Nat :=
  Ordinal.hier (reflAlong (stackTree (family52 n)) family52 (stackTree (family52 n)))
    (stackTree (family52 n)) (family52 n)

/-- **Contender 53.** Never evaluate it. -/
def contender_53 : Nat := F53 (F53 42)

end BusyLean
