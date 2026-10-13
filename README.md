# BusyLean: name the biggest number, in Lean

This is a Lean 4 edition of Cody Roux's
[name-the-biggest-number](https://github.com/codyroux/name-the-biggest-number)
contest; a snapshot of the original is in
[`docs/`](docs/name-the-biggest-number-master). The game is the same as in
[Scott Aaronson's essay](https://www.scottaaronson.com/writings/bignumbers.html):
name a bigger number than the previous contender. The number must be
**constructive**, and the claim must come with a **formal proof**. The only
change is that the proof assistant is Lean instead of Coq.

## Current contender: Contender 41

```lean
def family40 (n : Nat) : Nat := F40 (F40 n)                  -- Contender 40 = family40 42
def base41 (N : Nat) (t : CTree) : CTree :=                  -- BusyLean/Contender41.lean
  .lim fun i => if i = 0 then FLT2.jumpL family40 N t else base40 N t
def readerTree (N : Nat) : CTree :=
  .lim fun i => if i = 0 then metaTree N else metaBoostT (metaTree N) (base41 N) (metaTree N)
def F41 (n : Nat) : Nat := hier family40 (readerTree (family40 n)) (family40 n)
def contender_41 : Nat := F41 (F41 42)

theorem contender_40_lt_contender_41 : contender_40 < contender_41   -- BusyLean/Comparison41.lean
```

[`SystemFLT2/`](BusyLean/SystemFLT2) is the ladder language over System FT2's
terms. A ladder program of the reader type receives the tree constructors, a
recursor, and the input tree, and denotes a well-founded tree
(`FLT2.wt_of_readerTy`). `FLT2.jumpL g N T` joins `T` with the trees that all
reader programs of depth ≤ `N` over `Addr T` build from `T`. Contender 41 adds this
jump to Contender 40's base under P27's metalanguages.

| Theorem | Statement |
|---|---|
| `contender_40_lt_contender_41` | Contender 40 < Contender 41 |
| `family40_lt_F41` | Contender 40's family is beaten at every input |
| `FLT2.wt_of_readerTy` | ladder reader programs denote well-founded trees |

## Contender 40

```lean
def family39 (n : Nat) : Nat := F39 (F39 n)                  -- Contender 39 = family39 42
def base40 (N : Nat) (t : CTree) : CTree :=                  -- BusyLean/Contender40.lean
  .lim fun i => if i = 0 then FT2.jumpF family39 N t
    else if i = 1 then boost31 (FT2.jumpF family39 N t) else mixed N t
def metaTree (N : Nat) : CTree :=
  .lim fun i => if i = 0 then mixTree N else metaBoostT (mixTree N) (base40 N) (mixTree N)
def F40 (n : Nat) : Nat := hier family39 (metaTree (family39 n)) (family39 n)
def contender_40 : Nat := F40 (F40 42)

theorem contender_39_lt_contender_40 : contender_39 < contender_40   -- BusyLean/Comparison40.lean
```

**A genuine impredicative jump.** [`SystemFT2/`](BusyLean/SystemFT2) is System F
with tree constructors, a tree recursor `trec : ∀X. X → (X → X) → ((nat → X) → X)
→ tree → X`, and an oracle tree `tin`, read lazily by address. Reducibility
candidates prove that every typed program of type `tree` is a well-founded tree
(`FT2.wt_of_typed`, `FT2.trec_mem`). So `FT2.jumpF g N t` holds every tree that
System F builds *from* `t`. (The ladder "jump" of Contenders 36–37 never read
its input.) Contender 40 puts this jump, with collapse, under P27's
metalanguages with first-class language closure (`metaBoostT`), stacked to the
height of Contender 39's tree, and reads off the number with `hier`.

| Theorem | Statement |
|---|---|
| `contender_39_lt_contender_40` | Contender 39 < Contender 40 |
| `family39_lt_F40` | Contender 39's family is beaten at every input |
| `FT2.wt_of_typed` | typed System FT2 programs of type `tree` are well-founded trees |

## Contender 39

```lean
def mixed (N : Nat) (t : CTree) : CTree :=                   -- BusyLean/Contender39.lean
  .lim fun i => if i = 0 then jump N t else boost31 (jump N t)
def mixTree (N : Nat) : CTree :=
  .lim fun i => if i = 0 then jumpTree N else stackOver (mixed N) (jumpTree N) (jumpTree N)
def family38 (n : Nat) : Nat := F38 (F38 n)                  -- Contender 38 = family38 42
def F39 (n : Nat) : Nat := hier family38 (mixTree (family38 n)) (family38 n)
def contender_39 : Nat := F39 (F39 42)

theorem contender_38_lt_contender_39 : contender_38 < contender_39   -- BusyLean/Comparison39.lean
```

The stacked tree languages get a primitive that applies both the impredicative
jump and Contender 31's predicative collapse operator `boost31`, so every level
interleaves them. The enumeration depth inside the tree is `family38 n`, and the
number is read off with Contender 38's hierarchy.

| Theorem | Statement |
|---|---|
| `contender_38_lt_contender_39` | Contender 38 < Contender 39 |
| `family38_lt_F39` | Contender 38's family is beaten at every input |

## Contender 38

```lean
def family37 (n : Nat) : Nat := F37 (F37 n)                  -- Contender 37 = family37 42
def hier (g : Nat → Nat) : CTree → Nat → Nat                 -- BusyLean/Contender38.lean
  | .zero, m => g m
  | .succ t, m => iterN (hier g t) (m + 1) m
  | .lim f, m => maxUpTo (fun i => hier g (f i) m) m
  | _, m => g m
def F38 (n : Nat) : Nat := hier family37 (jumpTree n) (family37 n)
def contender_38 : Nat := F38 (F38 42)

theorem contender_37_lt_contender_38 : contender_37 < contender_38   -- BusyLean/Comparison38.lean
```

**A correction.** A ladder program of depth `n` can name only atoms of size or
depth ≤ `n`, and erasure forgets types. So ladder values depend only on the
finite order on named atoms, whose chains have length ≤ `n + 1` for address
atoms. Contenders 15–37 are all proved larger than their predecessors, but they
grew through oracle seeding and the W-ranked amplifiers, not through the size of
their atom orders. Contender 38 uses the trees directly: a fast-growing
hierarchy along `jumpTree n` with base Contender 37's family. Maxima over the
first branches at limits make it robust to the zero padding of program-list
limits.

| Theorem | Statement |
|---|---|
| `contender_37_lt_contender_38` | Contender 37 < Contender 38 |
| `family37_lt_F38` | Contender 37's family is beaten at every input |
| `Ordinal.le_hier` | the hierarchy dominates its base and argument (inflationary base) |

## Contender 37

```lean
def family36 (n : Nat) : Nat := F36 (F36 n)                  -- Contender 36 = family36 42
def jump (n : Nat) (t : CTree) : CTree := FLT.bootT family36 n t t
def jumpTree (n : Nat) : CTree :=
  .lim fun i => if i = 0 then bootTree n else stackOver (jump n) (bootTree n) (bootTree n)
def F37 (n : Nat) : Nat :=                                   -- BusyLean/Contender37.lean
  wDiagonalLift (schedule37 n) (rank37 n) jtTransformer (fun _ => family36) n n
def contender_37 : Nat := F37 (F37 42)

theorem contender_36_lt_contender_37 : contender_36 < contender_37   -- BusyLean/Comparison37.lean
```

Contender 36's bootstrap, read as an operator on trees, is a **jump**. `stackOver b`
stacks the System T language over trees on the primitive `b`, along a tree
(Contender 34's `boostT` used the fixed primitive `boost31`). With `b = jump n`,
the language levels iterate the impredicative jump transfinitely.

| Theorem | Statement |
|---|---|
| `contender_36_lt_contender_37` | Contender 36 < Contender 37 |
| `family36_lt_F37` | Contender 36's family is beaten at every input |
| `jtvalue_lt_F37` | every program of depth ≤ `n` over the addresses of `jumpTree n` is below `F37 n` |

## Contender 36

```lean
def family35 (n : Nat) : Nat := F35 (F35 n)                  -- Contender 35 = family35 42
def bootTree (n : Nat) : CTree := FLT.bootT family35 n (ftTree n) (ftTree n)
def F36 (n : Nat) : Nat :=                                   -- BusyLean/Contender36.lean
  wDiagonalLift (schedule36 n) (rank36 n) btTransformer (fun _ => family35) n n
def contender_36 : Nat := F36 (F36 42)

theorem contender_35_lt_contender_36 : contender_35 < contender_36   -- BusyLean/Comparison36.lean
```

**Ladders that build their own length.** [`SystemFLT/`](BusyLean/SystemFLT) is the
ladder language over the terms of System FT. A ladder program of the Church tree
type `∀X. X → (X → X) → ((nat → X) → X) → X`, applied to the inert constructors,
is a well-founded tree (`FLT.wt_of_treeTy`). `FLT.ladderTree` joins a tree `t`
with the trees of all ladder programs over `Addr t`, and `FLT.bootT` iterates this
along a tree index. `bootTree n` iterates it along Contender 35's tree, and
the final ladder runs over its addresses.

| Theorem | Statement |
|---|---|
| `contender_35_lt_contender_36` | Contender 35 < Contender 36 |
| `family35_lt_F36` | Contender 35's family is beaten at every input |
| `btvalue_lt_F36` | every program of depth ≤ `n` over the addresses of `bootTree n` is below `F36 n` |
| `FLT.wt_of_treeTy` | ladder programs of the Church tree type denote well-founded trees |

## Contender 35

```lean
def family34 (n : Nat) : Nat := F34 (F34 n)                  -- Contender 34 = family34 42
def ftTree (n : Nat) : CTree := FT.progSup family34 (treeStackedTree n) n
def F35 (n : Nat) : Nat :=                                   -- BusyLean/Contender35.lean
  wDiagonalLift (schedule35 n) (rank35 n) ftTransformer (fun _ => family34) n n
def contender_35 : Nat := F35 (F35 42)

theorem contender_34_lt_contender_35 : contender_34 < contender_35   -- BusyLean/Comparison35.lean
```

**Impredicative trees.** [`SystemFT/`](BusyLean/SystemFT) is System F with a base
type `tree` and inert constructors `con 0 : tree`, `con 1 : tree → tree`,
`con 2 : (nat → tree) → tree`. A reducibility candidate for trees (`WT`, with
constructor-headed terms excluded from the neutral terms) proves that every
program of type `tree` denotes a well-founded tree (`FT.wt_of_typed`).
`FT.toTree` reads the tree off by well-founded recursion. Through Church
encodings instantiated at `tree`, programs build every tree System F can
describe. `ftTree n` joins Contender 34's tree with the trees of all programs of
depth ≤ `n`, and the ladder runs over its addresses.

| Theorem | Statement |
|---|---|
| `contender_34_lt_contender_35` | Contender 34 < Contender 35 |
| `family34_lt_F35` | Contender 34's family is beaten at every input |
| `ftvalue_lt_F35` | every program of depth ≤ `n` over the addresses of `ftTree n` is below `F35 n` |
| `FT.wt_of_typed` | typed System FT programs of type `tree` are well-founded trees |

## Contender 34

```lean
def family33 (n : Nat) : Nat := F33 (F33 n)                  -- Contender 33 = family33 42
def F34 (n : Nat) : Nat :=                                   -- BusyLean/Contender34.lean
  wDiagonalLift (schedule34 n) (rank34 n) tsTransformer (fun _ => family33) n n
def contender_34 : Nat := F34 (F34 42)

theorem contender_33_lt_contender_34 : contender_33 < contender_34   -- BusyLean/Comparison34.lean
```

The tree-ordinal language is stacked **along a tree ordinal**
([`Ordinal/TreeLanguage3.lean`](BusyLean/Ordinal/TreeLanguage3.lean)):
`boostT (a+1) = langLift (boostT a)`, with pointwise limits. At input `n`, the
height and the argument are both Contender 33's tree.

| Theorem | Statement |
|---|---|
| `contender_33_lt_contender_34` | Contender 33 < Contender 34 |
| `family33_lt_F34` | Contender 33's family is beaten at every input |
| `tsvalue_lt_F34` | every program of depth ≤ `n` over the addresses of `treeStackedTree n` is below `F34 n` |

## Contender 33

```lean
def family32 (n : Nat) : Nat := F32 (F32 n)                  -- Contender 32 = family32 42
def F33 (n : Nat) : Nat :=                                   -- BusyLean/Contender33.lean
  wDiagonalLift (schedule33 n) (rank33 n) skTransformer (fun _ => family32) n n
def contender_33 : Nat := F33 (F33 42)

theorem contender_32_lt_contender_33 : contender_32 < contender_33   -- BusyLean/Comparison33.lean
```

The whole tree-ordinal language becomes the next primitive
([`Ordinal/TreeLanguage2.lean`](BusyLean/Ordinal/TreeLanguage2.lean)).
`langLift b t` applies every closed `tree ⇒ tree` program over `b`, of every
size, to `t`, and `boostK (k+1) = langLift (boostK k)`. Input `n` uses the ladder
over the addresses of `boostK (n+1)` applied to Contender 32's tree.

| Theorem | Statement |
|---|---|
| `contender_32_lt_contender_33` | Contender 32 < Contender 33 |
| `family32_lt_F33` | Contender 32's family is beaten at every input |
| `skvalue_lt_F33` | every program of depth ≤ `n` over the addresses of `stackedTree n` is below `F33 n` |

## Contender 32

```lean
def family31 (n : Nat) : Nat := F31 (F31 n)                  -- Contender 31 = family31 42
def F32 (n : Nat) : Nat :=                                   -- BusyLean/Contender32.lean
  wDiagonalLift (schedule32 n) (rank32 n) lgTransformer (fun _ => family31) n n
def contender_32 : Nat := F32 (F32 42)

theorem contender_31_lt_contender_32 : contender_31 < contender_32   -- BusyLean/Comparison32.lean
```

The tree-ordinal constructions become **programs**
([`Ordinal/TreeLanguage.lean`](BusyLean/Ordinal/TreeLanguage.lean)). The
language is System T with a base type of tree ordinals, a tree recursor (at any
type), and Contender 31's construction as a primitive `boost`. It has a
semantic interpreter by structural recursion, so no normalization proof and no
axioms are needed. `languageTree n` is the limit of all closed tree programs of
size `≤ n + 3` (and Contender 31's tree), so it includes transfinite and
higher-type iterations of `boost`. Input `n` uses the ladder over its
addresses.

| Theorem | Statement |
|---|---|
| `contender_31_lt_contender_32` | Contender 31 < Contender 32 |
| `family31_lt_F32` | Contender 31's family is beaten at every input |
| `lgvalue_lt_F32` | every program of depth ≤ `n` over the addresses of `languageTree n` is below `F32 n` |

## Contender 31

```lean
def family30 (n : Nat) : Nat := F30 (F30 n)                  -- Contender 30 = family30 42
def F31 (n : Nat) : Nat :=                                   -- BusyLean/Contender31.lean
  wDiagonalLift (schedule31 n) (rank31 n) ttTransformer (fun _ => family30) n n
def contender_31 : Nat := F31 (F31 42)

theorem contender_30_lt_contender_31 : contender_30 < contender_31   -- BusyLean/Comparison31.lean
```

The closure types are indexed by **tree ordinals**
([`Ordinal/TreeUniverses5.lean`](BusyLean/Ordinal/TreeUniverses5.lean)):
`AT (a+1) = AT a → AT a` and `AT (lim f) = Π i, AT (f i)`. Canonical
functionals are evaluated down to a universe. The type height at input `n` is
Contender 30's tree. No axioms are used.

| Theorem | Statement |
|---|---|
| `contender_30_lt_contender_31` | Contender 30 < Contender 31 |
| `family30_lt_F31` | Contender 30's family is beaten at every input |
| `ttvalue_lt_F31` | every program of depth ≤ `n` over the addresses of `transTypeTree n` is below `F31 n` |

## Contender 30

```lean
def family29 (n : Nat) : Nat := F29 (F29 n)                  -- Contender 29 = family29 42
def F30 (n : Nat) : Nat :=                                   -- BusyLean/Contender30.lean
  wDiagonalLift (schedule30 n) (rank30 n) tlTransformer (fun _ => family29) n n
def contender_30 : Nat := F30 (F30 42)

theorem contender_29_lt_contender_30 : contender_29 < contender_30   -- BusyLean/Comparison30.lean
```

Closure points are lifted to **all finite types over universes**
([`Ordinal/TreeUniverses4.lean`](BusyLean/Ordinal/TreeUniverses4.lean)):
`A 0 = Univ`, `A (k+1) = A k → A k`, and `closureA k f` is the union of `f`'s
iterates. At input `n` the chain `closureA n, …, closureA 0` is applied to
Contender 29's operator and then to the base universe. The result is
collapsed to a countable tree, and the ladder runs over its addresses. No
axioms are used.

| Theorem | Statement |
|---|---|
| `contender_29_lt_contender_30` | Contender 29 < Contender 30 |
| `family29_lt_F30` | Contender 29's family is beaten at every input |
| `tlvalue_lt_F30` | every program of depth ≤ `n` over the addresses of `typeLevelTree n` is below `F30 n` |

## Contender 29

```lean
def family28 (n : Nat) : Nat := F28 (F28 n)                  -- Contender 28 = family28 42
def F29 (n : Nat) : Nat :=                                   -- BusyLean/Contender29.lean
  wDiagonalLift (schedule29 n) (rank29 n) otTransformer (fun _ => family28) n n
def contender_29 : Nat := F29 (F29 42)

theorem contender_28_lt_contender_29 : contender_28 < contender_29   -- BusyLean/Comparison29.lean
```

Universe-building **operators are themselves iterated**
([`Ordinal/TreeUniverses3.lean`](BusyLean/Ordinal/TreeUniverses3.lean)).
`Φ F U` is the closure point of `F` above `U`, so `Φ next` jumps to the next
inaccessible-like universe. Operators are indexed by tree ordinals
(`ΦT (a+1) = Φ (ΦT a)`, unions at limits), and each round collapses inside the
universe after `ΦT Λ base`, with `Λ` the previous round's tree. No axioms are
used. Input `n` uses the ladder over the addresses of `operatorTree n`.

| Theorem | Statement |
|---|---|
| `contender_28_lt_contender_29` | Contender 28 < Contender 29 |
| `family28_lt_F29` | Contender 28's family is beaten at every input |
| `otvalue_lt_F29` | every program of depth ≤ `n` over the addresses of `operatorTree n` is below `F29 n` |

## Contender 28

```lean
def family27 (n : Nat) : Nat := F27 (F27 n)                  -- Contender 27 = family27 42
def F28 (n : Nat) : Nat :=                                   -- BusyLean/Contender28.lean
  wDiagonalLift (schedule28 n) (rank28 n) rtTransformer (fun _ => family27) n n
def contender_28 : Nat := F28 (F28 42)

theorem contender_27_lt_contender_28 : contender_27 < contender_28   -- BusyLean/Comparison28.lean
```

Universes of level codes are stacked **along countable tree ordinals**
([`Ordinal/TreeUniverses2.lean`](BusyLean/Ordinal/TreeUniverses2.lean)).
Unions of universes are universes, so `univT` is defined by structural
recursion on a tree. The height of the stack is itself the previous round's
collapsed tree: `roundTree n` iterates `n+1` rounds from Contender 27's tree.
No axioms are used. Input `n` uses the ladder over the addresses of
`roundTree n`.

| Theorem | Statement |
|---|---|
| `contender_27_lt_contender_28` | Contender 27 < Contender 28 |
| `family27_lt_F28` | Contender 27's family is beaten at every input |
| `rtvalue_lt_F28` | every program of depth ≤ `n` over the addresses of `roundTree n` is below `F28 n` |

## Contender 27

```lean
def family26 (n : Nat) : Nat := F26 (F26 n)                  -- Contender 26 = family26 42
def F27 (n : Nat) : Nat :=                                   -- BusyLean/Contender27.lean
  wDiagonalLift (schedule27 n) (rank27 n) uTransformer (fun _ => family26) n n
def contender_27 : Nat := F27 (F27 42)

theorem contender_26_lt_contender_27 : contender_26 < contender_27   -- BusyLean/Comparison27.lean
```

Level codes form **stratified universes**
([`Ordinal/TreeUniverses.lean`](BusyLean/Ordinal/TreeUniverses.lean)). The
codes of universe `k+1` have suprema ranging over the lower parts of
universe-`k` levels, so they can denote much larger levels. Each universe has
its own collapse, defined by structural recursion with no axioms. Input `n`
uses the ladder over the addresses of `universeLadderTree n`, the collapse in
universe `n+1`. Heuristically the nesting `Ω_{Ω_{⋯}}` grows with `n`, toward the
first fixed point of `α ↦ Ω_α`.

| Theorem | Statement |
|---|---|
| `contender_26_lt_contender_27` | Contender 26 < Contender 27 |
| `family26_lt_F27` | Contender 26's family is beaten at every input |
| `uvalue_lt_F27` | every program of depth ≤ `n` over the addresses of `universeLadderTree n` is below `F27 n` |

## Contender 26

```lean
def family25 (n : Nat) : Nat := F25 (F25 n)                  -- Contender 25 = family25 42
def F26 (n : Nat) : Nat :=                                   -- BusyLean/Contender26.lean
  wDiagonalLift (schedule26 n) (rank26 n) ltTransformer (fun _ => family25) n n
def contender_26 : Nat := F26 (F26 42)

theorem contender_25_lt_contender_26 : contender_25 < contender_26   -- BusyLean/Comparison26.lean
```

The collapsing levels are now **countable tree ordinals themselves**
([`Ordinal/TreeLevels.lean`](BusyLean/Ordinal/TreeLevels.lean)). Everything
below a level is lumped by structural recursion on the level tree. Arguments
carry the level of each supremum (`supAt c g`), so collapsing never needs to
compare levels. `DL` diagonalizes successor levels Buchholz-style and takes
limits at limit levels, all by structural recursion. `ladderTree n` iterates
`Λ ↦ ψ₀(ε_{Ω_Λ+1})`, heuristically toward the fixed points of `α ↦ ψ₀(Ω_α)`.
Input `n` uses the ladder over `Addr (ladderTree n)`, which is well-founded
structurally.

| Theorem | Statement |
|---|---|
| `contender_25_lt_contender_26` | Contender 25 < Contender 26 |
| `family25_lt_F26` | Contender 25's family is beaten at every input |
| `lvalue26_lt_F26` | every program of depth ≤ `n` over the addresses of `ladderTree n` is below `F26 n` |

## Contender 25

```lean
def family24 (n : Nat) : Nat := F24 (F24 n)                  -- Contender 24 = family24 42
def F25 (n : Nat) : Nat :=                                   -- BusyLean/Contender25.lean
  wDiagonalLift (schedule25 n) (rank25 n) aTransformer (fun _ => family24) n n
def contender_25 : Nat := F25 (F25 42)

theorem contender_24_lt_contender_25 : contender_24 < contender_25   -- BusyLean/Comparison25.lean
```

**Well-foundedness for free.** Following proposal P25, the atoms are finite
*addresses* in a Lean-defined tree ordinal, ordered by strict descent
([`Ordinal/TreeAddress.lean`](BusyLean/Ordinal/TreeAddress.lean)). The order is
decidable and well-founded by structural recursion on the tree, so the ladder
length is just the tree's rank, with no ordinal-notation proof.

The tree at input `n` comes from Buchholz-style **collapsing functions on tree
ordinals** for all finite levels
([`Ordinal/TreeCollapse.lean`](BusyLean/Ordinal/TreeCollapse.lean)). `D v`
collapses arguments with suprema at every finite level, using Buchholz's
diagonal for higher-level suprema. It is defined by plain structural recursion
and uses no axioms. `bigTree n` is heuristically `ψ₀(ε_{Ω_ω+n})`, beyond the
reach of the notation-based Contenders 16–24.

| Theorem | Statement |
|---|---|
| `Ordinal.addr_wf` | the strict-descendant order on addresses of any tree is well-founded |
| `contender_24_lt_contender_25` | Contender 24 < Contender 25 |
| `family24_lt_F25` | Contender 24's family is beaten at every input |
| `avalue_lt_F25` | every program of depth ≤ `n` over the addresses of `bigTree n` is below `F25 n` |

## Contender 24

```lean
def family23 (n : Nat) : Nat := F23 (F23 n)                  -- Contender 23 = family23 42
def F24 (n : Nat) : Nat :=                                   -- BusyLean/Contender24.lean
  wDiagonalLift (schedule24 n) (rank24 n) rTransformer (fun _ => family23) n n
def contender_24 : Nat := F24 (F24 42)

theorem contender_23_lt_contender_24 : contender_23 < contender_24   -- BusyLean/Comparison24.lean
```

Contender 22's tower of relativized Buchholz systems now runs along **any
well-founded index** ([`Ordinal/TowerAlong.lean`](BusyLean/Ordinal/TowerAlong.lean)).
The stage at `j` collapses over the union of all stages below `j`, and the union
of all stages is again a well-founded order. So it indexes the next round:
`roundTower (k+1) = limitAlong (roundTower k)`. Input `n` uses the ladder over
`roundTower n`, with Contender 23's W-ranked amplifier. Heuristically the rounds
climb the fixed points of `x ↦ ψ₀(Ω_ω·x)`.

| Theorem | Statement |
|---|---|
| `Ordinal.roundTower_wf` | every round is well-founded |
| `contender_23_lt_contender_24` | Contender 23 < Contender 24 |
| `family23_lt_F24` | Contender 23's family is beaten at every input |
| `rvalue_lt_F24` | every program of depth ≤ `n` over the atoms of `roundTower n` is below `F24 n` |

## Contender 23

```lean
def family22 (n : Nat) : Nat := F22 (F22 n)                  -- Contender 22 = family22 42
def F23 (n : Nat) : Nat :=                                   -- BusyLean/Contender23.lean
  wDiagonalLift (schedule23 n) (rank23 n) twTransformer (fun _ => family22) n n
def contender_23 : Nat := F23 (F23 42)

theorem contender_22_lt_contender_23 : contender_22 < contender_23   -- BusyLean/Comparison23.lean
```

The language is Contender 22's (the ladder over `tower n` at input `n`). The
amplifier adopts proposal P22's idea
([`TreeHyperReflection.lean`](BusyLean/TreeHyperReflection.lean), taken
unchanged): the rank of the hierarchy of transformer lifts is a well-founded
W-tree instead of a natural number. Here the rank is an autonomous notation
above the schedule, so it is a large countable ordinal.

| Theorem | Statement |
|---|---|
| `wDiagonalLift_strictlyInflationary` | every W-tree rank strictly exceeds its base |
| `contender_22_lt_contender_23` | Contender 22 < Contender 23 |
| `family22_lt_F23` | Contender 22's family is beaten at every input |
| `tvalue22_lt_F23` | every program of depth ≤ `n` over the atoms of `tower n` is below `F23 n` |

## Contender 22

```lean
def family21 (n : Nat) : Nat := F21 (F21 n)                  -- Contender 21 = family21 42
def F22 (n : Nat) : Nat :=                                   -- BusyLean/Contender22.lean
  diagonalLift (schedule22 n) (family21 n + 1) twTransformer (fun _ => family21) n n
def contender_22 : Nat := F22 (F22 42)

theorem contender_21_lt_contender_22 : contender_21 < contender_22   -- BusyLean/Comparison22.lean
```

Input `n` uses the ladder over `tower n`
([`Ordinal/BuchholzBase.lean`](BusyLean/Ordinal/BuchholzBase.lean)):

* the level-bounded Buchholz systems are relativized to *base atoms* from a
  transitive, well-founded order. Atoms lie below every collapse but may occur
  inside collapse arguments, and the well-foundedness proof is Contender 21's
  level step, with atoms accessible from the base's own well-foundedness;
* the union of all level-bounded systems over a base, ordered by the bound
  first, is again such an order, so it becomes the next base:
  `tower (k+1) = (tower k).next`.

`tower 1` has order type `ψ₀(Ω_ω)`, and each step collapses over everything
below (heuristically `ψ₀(Ω_ω·k)`). A single notation for all levels at once
would need Buchholz's distinguished sets; that is the next real step.

| Theorem | Statement |
|---|---|
| `Ordinal.BuchB.stepR` | the level step, relativized to a well-founded base |
| `Ordinal.tower_wf` | every stage of the tower is well-founded |
| `contender_21_lt_contender_22` | Contender 21 < Contender 22 |
| `family21_lt_F22` | Contender 21's family is beaten at every input |
| `tvalue22_lt_F22` | every program of depth ≤ `n` over the atoms of `tower n` is below `F22 n` |

## Contender 21

```lean
def family20 (n : Nat) : Nat := F20 (F20 n)                  -- Contender 20 = family20 42
def F21 (n : Nat) : Nat :=                                   -- BusyLean/Contender21.lean
  diagonalLift (schedule21 n) (family20 n + 1) zTransformer (fun _ => family20) n n
def contender_21 : Nat := F21 (F21 42)

theorem contender_20_lt_contender_21 : contender_20 < contender_21   -- BusyLean/Comparison21.lean
```

The ladders now use **Buchholz-style collapsing terms with `L+1` levels**
(`D u a = ψ_u(a)`, [`Ordinal/Buchholz.lean`](BusyLean/Ordinal/Buchholz.lean)),
whose normal forms reach `ψ₀(ε_{Ω_L+1})`. Input `n` uses the level bound `n`,
so the ladder lengths climb to Buchholz's ordinal `ψ₀(Ω_ω)`.

With unbounded levels, the impredicative argument of Contender 20 regresses
forever (`ψ₀(Ω₉) < Ω₁`). With a level bound it becomes a downward induction:
`Buch.stepR` derives "every in-scope term is accessible, given that all
in-scope terms below level `u` are" from the same statement at level `u+1`. It
applies the level-`u+1` statement twice: once to the scope restricted to terms
with accessible `u`-components, and once to the original scope.

| Theorem | Statement |
|---|---|
| `Ordinal.Buch.stepR` | the level step of the relativized well-foundedness argument |
| `Ordinal.buchholz_wf` | for every `L`, the order on normal terms with levels `≤ L` is well-founded |
| `contender_20_lt_contender_21` | Contender 20 < Contender 21 |
| `family20_lt_F21` | Contender 20's family is beaten at every input |
| `zvalue_lt_F21` | every program of depth ≤ `n` over the level-`n` atoms is below `F21 n` |

## Contender 20

```lean
def family19 (n : Nat) : Nat := F19 (F19 n)                  -- Contender 19 = family19 42
def F20 (n : Nat) : Nat :=                                   -- BusyLean/Contender20.lean
  diagonalLift (schedule20 n) (family19 n + 1) bTransformer (fun _ => family19) n n
def contender_20 : Nat := F20 (F20 42)

theorem contender_19_lt_contender_20 : contender_19 < contender_20   -- BusyLean/Comparison20.lean
```

The ladder of universes now has **Bachmann–Howard length**. Its atoms are
Buchholz-style collapsing terms with two levels, `D₀ a = ψ₀(a)` and
`D₁ a = ψ₁(a)` ([`Ordinal/BachmannHoward.lean`](BusyLean/Ordinal/BachmannHoward.lean)).
`Dᵤ a` is normal only when every element of `Gᵤ(a)` is below `a`. Without this
condition the order would descend forever (`D₁0 > D₀D₁0 > D₀D₀D₁0 > ⋯`).

The well-foundedness proof is the classical impredicative argument, carried by
Lean's inductive `Acc`. Let `M` be the set of terms whose top-level `D₀`
components are accessible. The order restricted to `M` is well-founded
(predicative), and induction along it makes every `D₀ a` accessible. This needs
transitivity, which is a structural induction here.

| Theorem | Statement |
|---|---|
| `Ordinal.BH.accD0` | `D₀ a` is accessible for every `a` accessible within `M` |
| `Ordinal.bachmannHoward_wf` | the order on normal collapsing terms is well-founded |
| `contender_19_lt_contender_20` | Contender 19 < Contender 20 |
| `family19_lt_F20` | Contender 19's family is beaten at every input |
| `bvalue_lt_F20` | every program of depth ≤ `n` over these atoms is below `F20 n` |

## Contender 19

```lean
def family18 (n : Nat) : Nat := F18 (F18 n)                  -- Contender 18 = family18 42
def F19 (n : Nat) : Nat :=                                   -- BusyLean/Contender19.lean
  diagonalLift (schedule19 n) (family18 n + 1) lTransformer (fun _ => family18) n n
def contender_19 : Nat := F19 (F19 42)

theorem contender_18_lt_contender_19 : contender_18 < contender_19   -- BusyLean/Comparison19.lean
```

The ladder of universes now has **large-Veblen length**. Its atoms are
Schütte's Klammersymbole ([`Ordinal/LargeVeblen.lean`](BusyLean/Ordinal/LargeVeblen.lean)):
`φ` applied to argument arrays of `(position, value)` entries, where positions
are themselves terms. Arrays are compared at the most significant difference.
`φ(A) < φ(B)` iff `A < B` and every value of `A` is below `φ(B)`, or otherwise
`φ(A) ≤` some value of `B`.

Well-foundedness again follows only the comparison's case split. Argument
arrays use a variant of the sorted-list lemma restricted to "good" entries,
those with accessible position and value
([`Ordinal/SortedLexQ.lean`](BusyLean/Ordinal/SortedLexQ.lean)).

| Theorem | Statement |
|---|---|
| `Ordinal.LVeblen.acc_phi` | `φ(A)` is accessible for every accessible array of good entries |
| `Ordinal.largeVeblen_wf` | the order on normal Klammersymbole is well-founded |
| `contender_18_lt_contender_19` | Contender 18 < Contender 19 |
| `family18_lt_F19` | Contender 18's family is beaten at every input |
| `lvalue_lt_F19` | every program of depth ≤ `n` over these atoms is below `F19 n` |

## Contender 18

```lean
def family17 (n : Nat) : Nat := F17 (F17 n)                  -- Contender 17 = family17 42
def F18 (n : Nat) : Nat :=                                   -- BusyLean/Contender18.lean
  diagonalLift (schedule18 n) (family17 n + 1) gTransformer (fun _ => family17) n n
def contender_18 : Nat := F18 (F18 42)

theorem contender_17_lt_contender_18 : contender_17 < contender_18   -- BusyLean/Comparison18.lean
```

The ladder of universes now has length **`Γ₀`**. Its atoms are hereditarily
sorted binary Veblen terms ([`Ordinal/Veblen.lean`](BusyLean/Ordinal/Veblen.lean)),
compared by Veblen's rule (`φ(a,b) < φ(c,d)` iff `a<c ∧ b<φ(c,d)`, or
`a=c ∧ b<d`, or otherwise `φ(a,b) ≤ d`).

`Veblen.acc_phi` is Schütte's argument, reorganized to follow only the case
split of the Boolean comparison, with no transitivity or ordinal arithmetic. It
inducts on `a`, then `b`, then the size of the predecessor. The universes are
`FL.wfUniv` and normalization is `FL.sn_of_typed`, unchanged.

| Theorem | Statement |
|---|---|
| `Ordinal.Veblen.acc_phi` | `φ(a,b)` is accessible when `a` and `b` are |
| `Ordinal.gamma0_wf` | the order on normal Veblen terms is well-founded |
| `contender_17_lt_contender_18` | Contender 17 < Contender 18 |
| `family17_lt_F18` | Contender 17's family is beaten at every input |
| `gvalue_lt_F18` | every Γ₀-ladder program of depth ≤ `n` is below `F18 n` |

## Contender 17

```lean
def family16 (n : Nat) : Nat := F16 (F16 n)                  -- Contender 16 = family16 42
def F17 (n : Nat) : Nat :=                                   -- BusyLean/Contender17.lean
  diagonalLift (schedule17 n) (family16 n + 1) eTransformer (fun _ => family16) n n
def contender_17 : Nat := F17 (F17 42)

theorem contender_16_lt_contender_17 : contender_16 < contender_17   -- BusyLean/Comparison17.lean
```

The transfinite ladder of Contender 16 now has length **`ε₀`**. Its atoms are
Cantor normal form trees `node [a₁, …, a_k] = ω^a₁ + ⋯ + ω^a_k`
([`Ordinal/Epsilon0.lean`](BusyLean/Ordinal/Epsilon0.lean)).
`Ordinal.epsilon0_wf` applies the sorted-list lemma hereditarily, with normality
built into the element order, because the lexicographic order on non-normal
trees has infinite descending chains. The universes are `FL.wfUniv` and
normalization is `FL.sn_of_typed`, unchanged. At depth `n`, programs use levels
up to ω-towers of height about `n`.

| Theorem | Statement |
|---|---|
| `Ordinal.epsilon0_wf` | the order on Cantor normal forms below `ε₀` is well-founded |
| `contender_16_lt_contender_17` | Contender 16 < Contender 17 |
| `family16_lt_F17` | Contender 16's family is beaten at every input |
| `evalue_lt_F17` | every ε₀-ladder program of depth ≤ `n` is below `F17 n` |

## Contender 16

```lean
def family15 (n : Nat) : Nat := F15 (F15 n)                  -- Contender 15 = family15 42
def F16 (n : Nat) : Nat :=                                   -- BusyLean/Contender16.lean
  diagonalLift (schedule16 n) (family15 n + 1) tTransformer (fun _ => family15) n n
def contender_16 : Nat := F16 (F16 42)

theorem contender_15_lt_contender_16 : contender_15 < contender_16   -- BusyLean/Comparison16.lean
```

The ladder of universes becomes **transfinite**.

* [`SystemFL/Transfinite.lean`](BusyLean/SystemFL/Transfinite.lean):
  `FL.wfUniv` builds a universe for *every* well-founded atom order, by
  well-founded recursion: the domain of atom `a` is the sum of the semantics of
  all base kinds whose atoms lie below `a`. So the ladder language normalizes for
  ladders of any well-founded length.
* [`Ordinal/SortedLex.lean`](BusyLean/Ordinal/SortedLex.lean): the
  lexicographic order on non-increasing lists (Cantor normal forms) is
  well-founded whenever the exponents are accessible.
* [`Ordinal/OmegaPow.lean`](BusyLean/Ordinal/OmegaPow.lean): atoms are notations
  below `ω^ω`. At depth `n`, programs use levels up to `ω^(n-1)·n`; for example,
  the universe at `ω` holds operators from every finite level.
* The amplifier is Contender 15's rank hierarchy of lifts, seeded with
  Contender 15's family.

| Theorem | Statement |
|---|---|
| `FL.wfUniv` | a universe for every well-founded atom order |
| `Ordinal.wf_sorted` | sorted lists of accessible elements are well-founded lexicographically |
| `contender_15_lt_contender_16` | Contender 15 < Contender 16 |
| `family15_lt_F16` | Contender 15's family is beaten at every input |
| `tvalue_lt_F16` | every transfinite-ladder program of depth ≤ `n` is below `F16 n` |

## Contender 15

```lean
def family14 (n : Nat) : Nat := F14 (F14 n)                  -- Contender 14 = family14 42
def F15 (n : Nat) : Nat :=                                   -- BusyLean/Contender15.lean
  diagonalLift (schedule15 n) (family14 n + 1) flFamilyTransformer (fun _ => family14) n n
def contender_15 : Nat := F15 (F15 42)

theorem contender_14_lt_contender_15 : contender_14 < contender_15   -- BusyLean/Comparison15.lean
```

Contender 15 applies the strongest amplifier received so far to the strongest
language here.

* **Language:** the ladder of universes of Contender 14. `reflectFLFamily fs n`
  exceeds every visible coordinate of an oracle family and every level-`n`
  ladder program of depth `≤ n`; the programs see the whole family through a
  packed oracle.
* **Amplifier:** proposal P17's rank hierarchy of transformer lifts
  ([`HyperReflection.lean`](BusyLean/HyperReflection.lean), adopted
  unchanged; P20 found the same idea). Rank `k+1` traverses a schedule using
  rank `k` as the lift at every node. The schedule is
  `family14 n + 42` hyper-closures above `tree12`, and the rank is
  `family14 n + 1`.

| Theorem | Statement |
|---|---|
| `contender_14_lt_contender_15` | Contender 14 < Contender 15 |
| `family14_lt_F15` | Contender 14's family is beaten at every input |
| `fvalue_lt_F15` | every level-`n` ladder program of depth ≤ `n` is below `F15 n` |
| `diagonalLift_strictlyInflationary` | every rank strictly exceeds its base, with no monotonicity |

## Contender 14

```lean
def family13 (n : Nat) : Nat := F13 (F13 n)               -- Contender 13 = family13 42
def F14 (n : Nat) : Nat := FL.reflectFL family13 n        -- BusyLean/Contender14.lean
def contender_14 : Nat := F14 (F14 42)

theorem contender_13_lt_contender_14 : contender_13 < contender_14   -- BusyLean/Comparison14.lean
```

`reflectFL f n` exceeds `f n` and the value of every closed program of the
**level-`n` ladder language** of depth `≤ n` with the Church numeral type.
The level-`ℓ` language is Contender 13's dynamic-kind Fω plus atomic kinds
`dyn₀, …, dyn_{ℓ-1}`:

* atom `dyn_i` denotes the `dyn` of the level-`i` language;
* `apack a K A : a` and `aunpack a K X : K` move operators into and out of an
  atom from the kinds strictly below it, with `aunpack (apack A) ≡ A`. For
  example, an operator of kind `dyn₀ → ★` can be packed into `dyn₁`.

The syntax and the SN proof are parametric in a `Universe` of atoms (domains,
packing, reading, and the law `rd (pk v) = v`). So **one** theorem,
`FL.sn_of_typed`, normalizes every level. `FL.Univ f ℓ` builds level `ℓ` by
recursion ([`SystemFL/Ladder.lean`](BusyLean/SystemFL/Ladder.lean)). Input `n`
uses level `n`, so the reflection diagonalizes over the ladder itself.

| Theorem | Statement |
|---|---|
| `FL.sn_of_typed` | for every universe, every ladder term (with oracle) is strongly normalizing |
| `FL.infer_sound` | the checker is sound, for every atom type |
| `contender_13_lt_contender_14` | Contender 13 < Contender 14 |
| `family13_lt_F14` | Contender 13's family is beaten at every input |
| `fvalue_lt_contender_14` | every level-`F14 42` program of depth ≤ `F14 42` is exceeded |

## Contender 13

```lean
def family12 (n : Nat) : Nat := F12 (F12 n)               -- Contender 12 = family12 42
def F13 (n : Nat) : Nat := Fd.reflectFd family12 n        -- BusyLean/Contender13.lean
def contender_13 : Nat := F13 (F13 42)

theorem contender_12_lt_contender_13 : contender_12 < contender_13   -- BusyLean/Comparison13.lean
```

`reflectFd f n` exceeds `f n` and the value of every closed program of
**dynamic-kind System Fω** of depth `≤ n` with the Church numeral type. The
language adds a predicative universe of operators to kind-polymorphic Fω:

* a kind `dyn` whose elements are operators of *every* dyn-free kind
  (semantically `Σ k, Sem k`), with type-level `pack K A : dyn`,
  `unpack K X : K`, and `unpack K (pack K A) ≡ A`;
* kind variables at two levels. Level-1 variables range over kinds built from
  `dyn`, so programs can climb `dyn, dyn → ★, …` at run time (uniform orders
  ω + n).

Kinds still cannot quantify over kinds, so `dyn` never contains itself, and
the semantic SN proof (`Fd.sn_of_typed`) certifies consistency.

| Theorem | Statement |
|---|---|
| `Fd.sn_of_typed` | every dynamic-kind Fω term (with oracle) is strongly normalizing |
| `Fd.infer_sound` | the checker is sound |
| `contender_12_lt_contender_13` | Contender 12 < Contender 13 |
| `family12_lt_F13` | Contender 12's family is beaten at every input |
| `fvalue_lt_contender_13` | every program of depth ≤ `F13 42` is exceeded |

## Contender 12

```lean
def fkTransformer : Transformer := fun fs _ n => reflect11 fs n        -- BusyLean/Contender12.lean
def tree12 := Autonomous.realize (Autonomous.hyper 42 (Autonomous.encode index))
def F12 (n : Nat) : Nat := operatorStage fkTransformer tree12 (fun _ => family11) n n
def contender_12 : Nat := F12 (F12 42)                                  -- family11 n = F11 (F11 n)

theorem contender_11_lt_contender_12 : contender_11 < contender_12     -- BusyLean/Comparison12.lean
```

This contender reuses two ideas from the second batch of proposals (see
[the review](proposals/REVIEW.md)), with attribution, on top of this
repository's strongest language:

* **P6's operator stage**: reflection lifted to *transformers* of families,
  iterated along the index, with the lift itself iterated along a tree. It
  exponentiates where forest reflection multiplies.
* **P7's ordinal notations**: explicit Veblen-style closures stacked *above*
  Contender 6's language-defined index.
* The base transformer is Contender 11's reflection over **kind-polymorphic
  System Fω**.

| Theorem | Statement |
|---|---|
| `contender_11_lt_contender_12` | Contender 11 < Contender 12 |
| `family11_lt_F12` | Contender 11's family is beaten at every input |
| `fkTransformer_progressive` | kind-polymorphic Fω reflection is a progressive transformer |

## Contender 11

`F11 n = stage11 (fun _ => family10) index n`, `contender_11 = F11 (F11 42)`:
Contender 9's amplifier (forest reflection along the W-language's index)
applied to Contender 10's kind-polymorphic language. Theorems:
`contender_10_lt_contender_11`, `family10_lt_F11`, `defined_tree_eventually_lt11`.

## Contender 10

```lean
def family9 (n : Nat) : Nat := F9 (F9 n)                  -- Contender 9 = family9 42
def F10 (n : Nat) : Nat := Fk.reflectFk family9 n         -- BusyLean/Contender10.lean
def contender_10 : Nat := F10 (F10 42)

theorem contender_9_lt_contender_10 : contender_9 < contender_10   -- BusyLean/Comparison10.lean
```

`reflectFk f n` exceeds `f n` and the value of every closed program of
**kind-polymorphic System Fω** of depth `≤ n` with the Church numeral type.
Types may quantify over kinds (`∀κ. A`), so a single program can iterate
through kinds of unbounded order chosen at run time, via existential packages
`∃κ. B κ`. Proving such programs total needs candidates for all finite types
uniformly, beyond higher-order arithmetic (the limit of Fω).

* **Consistency and normalization** (`Fk.sn_of_typed`): kinds cannot quantify
  over kinds (no rule (△,□), so no Girard–Hurkens paradox). `∀κ. A` is modeled
  as a countable intersection over closed kinds.
* **Type checking** (`Fk.infer_sound`): Contender 8's sound checker plus kind
  abstraction and application.

| Theorem | Statement |
|---|---|
| `Fk.sn_of_typed` | every kind-polymorphic Fω term (with oracle) is strongly normalizing |
| `Fk.infer_sound` | the checker is sound |
| `contender_9_lt_contender_10` | Contender 9 < Contender 10 |
| `family9_lt_F10` | Contender 9's family is beaten at every input |
| `fvalue_lt_contender_10` | every program of depth ≤ `F10 42` is exceeded |

## Contender 9

```lean
def stage9 (seed : Family) : WTree ℕ → ℕ → ℕ               -- BusyLean/Contender9.lean
  | .leaf   => reflect9 seed
  | .node g => reflect9 (fun i => stage9 seed (g i))
def F9 (n : Nat) : Nat := stage9 (fun _ => family8) index n
def contender_9 : Nat := F9 (F9 42)                        -- family8 n = F8 (F8 n)

theorem contender_8_lt_contender_9 : contender_8 < contender_9   -- BusyLean/Comparison9.lean
```

Contender 6's forest reflection, with **System Fω** as the reflected language,
along Contender 6's index (every tree the W-language defines). A node's family
of child stages reaches Fω through the unary oracle as
`orc (2^i·(2m+1)) = fs i m` (`unpair2_code` proves the decoding). Informally
this is about f<sub>|Z_ω|·ψ(Ω_ω)²</sub>: a multiplicative step. The article
explains why the Calculus of Constructions would *not* be a growth-rate jump
over Fω, and why the next qualitative jump needs large elimination.

| Theorem | Statement |
|---|---|
| `contender_8_lt_contender_9` | Contender 8 < Contender 9 |
| `family8_lt_F9` | Contender 8's family is beaten at every input |
| `defined_tree_eventually_lt9` | every W-definable tree is eventually dominated |
| `unpair2_code` | the oracle-family code is decoded correctly |

## Contender 8

```lean
def family7 (n : Nat) : Nat := F7 (F7 n)                  -- Contender 7 = family7 42
def F8 (n : Nat) : Nat := Fw.reflectFw family7 n          -- BusyLean/Contender8.lean
def contender_8 : Nat := F8 (F8 42)

theorem contender_7_lt_contender_8 : contender_7 < contender_8   -- BusyLean/Comparison8.lean
```

`reflectFw f n` exceeds `f n` and the value of every closed **System Fω**
program of enumeration depth `≤ n` with the Church numeral type. Fω adds
*type operators* (kinds `★ | κ → κ`) to System F, reaching the strength of
higher-order arithmetic.

* **Normalization** (`Fw.sn_of_typed`): Girard's candidates lifted to kinds.
  The semantic domain of kind `κ₁ → κ₂` is the type of Lean functions between
  domains, so type-level β is literally function application.
* **Type checking** (`Fw.infer_sound`) decides type equality by comparing
  fuel-bounded type normal forms. It is sound (accepted programs are typable)
  and uses the syntax budget as fuel.
* The oracle is Contender 7's family, which Fω can amplify.

| Theorem | Statement |
|---|---|
| `Fw.sn_of_typed` | every System Fω term (with oracle) is strongly normalizing |
| `Fw.infer_sound` | the fuel-bounded type checker is sound |
| `contender_7_lt_contender_8` | Contender 7 < Contender 8 |
| `family7_lt_F8` | Contender 7's family is beaten at every input |
| `fvalue_lt_contender_8` | every Fω program of depth ≤ `F8 42` is exceeded |

## Contender 7

```lean
def F7 (n : Nat) : Nat := F.reflectF finalFamily n        -- BusyLean/Contender7.lean
def contender_7 : Nat := F7 (F7 42)

theorem contender_6_lt_contender_7 : contender_6 < contender_7   -- BusyLean/Comparison7.lean
```

`reflectF f n` exceeds `f n` and the value of every closed **System F**
program (Church-style, enumeration depth `≤ n`) of Church numeral type
`∀X. (X → X) → X → X`. Programs may call an oracle `orc : nat → nat`,
interpreted as `f`. A program's value is computed inside Lean: erase the
types, normalize, read off the numeral. Normalization is a total function
because of a formal **strong normalization theorem for System F**
(`F.sn_of_typed`), proved by Girard's reducibility candidates. The
impredicative quantification over candidates is legal because Lean's `Prop`
is impredicative.

* The oracle is Contender 6's family, so System F can amplify Contender 6
  with the strength of second-order arithmetic.
* The outer `F7` runs System F at a syntax budget larger than Contender 6.
* Informally, the numeric functions definable in System F are those provably
  total in second-order arithmetic Z₂, far beyond ψ(Ω_ω) (Contender 6's
  language).

| Theorem | Statement |
|---|---|
| `F.sn_of_typed` | every System F term (with oracle) is strongly normalizing |
| `F.infer_sound` | the type inferrer is sound for the erased term |
| `F.nstep_nf` | the normalizer's output is normal |
| `contender_6_lt_contender_7` | Contender 6 < Contender 7 |
| `finalFamily_lt_F7` | Contender 6's family is beaten at every input |
| `fvalue_lt_contender_7` | every System F program of depth ≤ `F7 42` is exceeded |

All of these use only `propext` and `Quot.sound`.

## Contender 6

```lean
def contender_6 : Nat := stage p5Family index 42        -- BusyLean/Contender6.lean

theorem contender_5_lt_contender_6 : contender_5 < contender_6   -- BusyLean/Comparison.lean
```

It is built in three layers:

1. **Object language.** System T extended with W-types `W A` over every
   finite type `A` (`W ℕ`, `W (W ℕ)`, `W (ℕ → W ℕ)`, …), each with a recursor
   into every type. It is evaluated by a total interpreter on raw terms. This
   language is taken from proposal P5. Its strength is roughly ψ(Ω_ω), the
   ordinal of ID<sub>&lt;ω</sub>, far beyond System T's ε₀.
2. **Forest reflection.** `reflect fs n` exceeds every oracle value `fs i n`
   (`i ≤ n`) and every program of depth `≤ n`, run *relative to the oracle
   family `fs`*. The oracle is simply the outermost variable `var 0`.
   `stage seed a` iterates this along a tree `a : W ℕ`: a node reflects over
   the family of its children's stages, so any child can be called at a
   dynamically computed index.
3. **A self-referential index.** `index` joins *every* `W ℕ` tree that a
   closed program of the language defines. The hierarchy therefore climbs
   through the language's own ordinals, not through a hand-written notation
   system.

The seed `p5Family` is P5's number as a function of its input, so beating
P5 is a theorem (`p5_lt_contender_6`). An informal fast-growing-hierarchy
estimate is f<sub>|L|·|L|</sub>(42) with |L| ≈ ψ(Ω_ω); for comparison, P5 is
about f<sub>|L|+ω²</sub>(42) and Contender 5 about f<sub>&lt;ε₀</sub>(42).

| Theorem | Statement |
|---|---|
| `contender_5_lt_contender_6` | exact port of Contender 5 < Contender 6 |
| `p5_lt_contender_6` | proposal P5's number < Contender 6 |
| `p5Family_lt_finalFamily` | the same at every input `n` |
| `defined_tree_eventually_lt` | every tree the language defines is eventually dominated |
| `program_lt_finalFamily` | every program of depth ≤ n, run with the final oracles, is exceeded |
| `PortAgreement.largest_eq_oldMaximum` | P5's old-language port equals the exact port, at every depth |

These depend on `propext` only; the definition of `contender_5` uses no
axioms.

**Never evaluate any contender.** Checking the definitions and proofs does not
evaluate the numbers.

## Rules (Lean edition)

These are adapted from the [original rules](docs/name-the-biggest-number-master/README.md):

1. **Constructive numbers only.** The number must be a closed, computable
   `Nat` definition. No Busy Beavers or other oracles, and no `noncomputable`,
   `partial`, `unsafe`, `opaque` stand-ins, `implemented_by` or `extern`.
2. **Formal proof.** Submit a definition `contender_N : Nat` and a theorem
   `contender_(N-1)_lt_contender_N`. When the previous contender was written
   in another proof assistant, compare against a faithful port and document
   the port.
3. **Axioms.** Only `propext` and `Quot.sound` (hence `funext`) are allowed.
   `Classical.choice`, `sorryAx` and custom axioms are not. Check with
   `#print axioms`. `native_decide` is not allowed either.
4. **Time budgets.** From a clean build directory, the new contender's
   definition must check in at most 15 s and its proof in at most 60 s, on a
   reasonable machine. The Lean core library may be precompiled, and so may
   the modules of earlier accepted contenders, which were checked under their
   own budgets. (Contenders build on their predecessors, so a fixed budget for
   the whole stack would eventually be exhausted by history alone.) The check
   script also reports the full clean-build time.
5. **No laziness.** Do not use the constant `contender_N` itself to define
   `contender_(N+1)`, and beat it by a large margin. The previous contender's
   *construction* (for example its family of functions) may appear as an
   oracle or seed of a qualitatively stronger construction, which makes the
   comparison formal. The audit checks that the constant itself is never
   mentioned.
6. **No shenanigans.** No exploits of the kernel, the elaborator or the
   toolchain.
7. **Toolchain.** Lean **4.34.0** (`lean-toolchain`). Libraries are allowed if
   widely used; this entry needs only Lean core.

## Checking

With [elan](https://github.com/leanprover/elan) installed:

```bash
python3 scripts/check.py
```

This deletes the build directories, builds the previous contender, times the
current contender's definition and proof phases against the budgets, reports
the total, and runs [`test/Audit.lean`](test/Audit.lean).
On an Intel i7-1355U (Windows 11), Contender 41's definition modules take
about 7 s (including SystemFLT2) and its proofs about 2 s; the full clean build of all contenders
takes about 40–50 s. Plain `lake build` also works, and
`lake env lean test/Contender5Smoke.lean` checks the port against the
reference small-depth table (maxima 0, 0, 1, 2, 3 at depths 0–4).

## Repository layout

| Path | Contents |
|---|---|
| [`BusyLean/Contender5.lean`](BusyLean/Contender5.lean) | definition-by-definition port of `Contender.v` and `contender_5` |
| [`BusyLean/PortAgreement.lean`](BusyLean/PortAgreement.lean) | logical-relation proof that P5's port agrees with it |
| [`BusyLean/Reflection.lean`](BusyLean/Reflection.lean) | oracle relativization, `reflect`, `stage` (definitions) |
| [`BusyLean/ReflectionFacts.lean`](BusyLean/ReflectionFacts.lean) | their inequalities |
| [`BusyLean/Contender6.lean`](BusyLean/Contender6.lean) | `index`, `p5Family`, `contender_6` (definitions) |
| [`BusyLean/Comparison.lean`](BusyLean/Comparison.lean) | all Contender 6 theorems |
| [`BusyLean/SystemF/`](BusyLean/SystemF) | System F: syntax, reduction, types, candidates (SN), Church terms, normalizer |
| [`BusyLean/SystemFLT/`](BusyLean/SystemFLT) | the ladder language over System FT terms; `wt_of_treeTy` (Church-tree programs are well-founded trees) |
| [`BusyLean/SystemFLT2/`](BusyLean/SystemFLT2) | the ladder language over System FT2 terms; `wt_of_readerTy` (reader programs are well-founded trees) |
| [`BusyLean/SystemFT2/`](BusyLean/SystemFT2) | System F with a tree recursor and an oracle tree: `trec_mem`, `wt_tsub`, `jumpF` |
| [`BusyLean/SystemFT/`](BusyLean/SystemFT) | System F with tree constructors: the tree candidate `WT`, `wt_of_typed`, tree extraction `toTree` |
| [`BusyLean/Contender7.lean`](BusyLean/Contender7.lean) | `fvalue`, `reflectF`, `contender_7` (definitions) |
| [`BusyLean/Comparison7.lean`](BusyLean/Comparison7.lean) | Contender 7 theorems |
| [`BusyLean/SystemFw/`](BusyLean/SystemFw) | System Fω: kinds and type β, typing, candidates over kinds (SN), sound checker |
| [`BusyLean/Contender8.lean`](BusyLean/Contender8.lean), [`Comparison8.lean`](BusyLean/Comparison8.lean) | Contender 8 definitions and theorems |
| [`BusyLean/Contender9.lean`](BusyLean/Contender9.lean), [`Comparison9.lean`](BusyLean/Comparison9.lean) | Contender 9 definitions and theorems |
| [`BusyLean/SystemFk/`](BusyLean/SystemFk) | kind-polymorphic Fω: syntax, typing, candidates with kind valuations (SN), sound checker |
| [`BusyLean/Contender10.lean`](BusyLean/Contender10.lean), [`Comparison10.lean`](BusyLean/Comparison10.lean) | Contender 10 definitions and theorems |
| [`BusyLean/Contender11.lean`](BusyLean/Contender11.lean), [`Comparison11.lean`](BusyLean/Comparison11.lean) | Contender 11 definitions and theorems |
| [`BusyLean/MetaReflection.lean`](BusyLean/MetaReflection.lean), [`MetaReflectionFacts.lean`](BusyLean/MetaReflectionFacts.lean) | operator-level reflection (adopted from P6) |
| [`BusyLean/Autonomous.lean`](BusyLean/Autonomous.lean) | ordinal notations above a tree (adopted from P7) |
| [`BusyLean/Contender12.lean`](BusyLean/Contender12.lean), [`Comparison12.lean`](BusyLean/Comparison12.lean) | Contender 12 definitions and theorems |
| [`BusyLean/SystemFd/`](BusyLean/SystemFd) | dynamic-kind Fω: syntax, typing, candidates with `dyn = Σ k, Sem k` (SN), sound checker |
| [`BusyLean/Contender13.lean`](BusyLean/Contender13.lean), [`Comparison13.lean`](BusyLean/Comparison13.lean) | Contender 13 definitions and theorems |
| [`BusyLean/SystemFL/`](BusyLean/SystemFL) | the ladder language, parametric in its atoms: syntax, typing, candidates over a `Universe` (SN), sound checker, the ladder of universes |
| [`BusyLean/Contender14.lean`](BusyLean/Contender14.lean), [`Comparison14.lean`](BusyLean/Comparison14.lean) | Contender 14 definitions and theorems |
| [`BusyLean/HyperReflection.lean`](BusyLean/HyperReflection.lean), [`HyperReflectionFacts.lean`](BusyLean/HyperReflectionFacts.lean) | rank hierarchy of transformer lifts (adopted from P17) |
| [`BusyLean/Contender15.lean`](BusyLean/Contender15.lean), [`Comparison15.lean`](BusyLean/Comparison15.lean) | Contender 15 definitions and theorems |
| [`BusyLean/Ordinal/`](BusyLean/Ordinal) | well-founded ordinal notations: sorted lists, atoms below `ω^ω`, `ε₀`, `Γ₀`, the large Veblen ordinal, Bachmann–Howard, and Buchholz-style `ψ₀(ε_{Ω_L+1})` |
| [`BusyLean/Contender16.lean`](BusyLean/Contender16.lean), [`Comparison16.lean`](BusyLean/Comparison16.lean) | Contender 16 definitions and theorems |
| [`BusyLean/Contender17.lean`](BusyLean/Contender17.lean), [`Comparison17.lean`](BusyLean/Comparison17.lean) | Contender 17 definitions and theorems |
| [`BusyLean/Contender18.lean`](BusyLean/Contender18.lean), [`Comparison18.lean`](BusyLean/Comparison18.lean) | Contender 18 definitions and theorems |
| [`BusyLean/Contender19.lean`](BusyLean/Contender19.lean), [`Comparison19.lean`](BusyLean/Comparison19.lean) | Contender 19 definitions and theorems |
| [`BusyLean/Contender20.lean`](BusyLean/Contender20.lean), [`Comparison20.lean`](BusyLean/Comparison20.lean) | Contender 20 definitions and theorems |
| [`BusyLean/Contender21.lean`](BusyLean/Contender21.lean), [`Comparison21.lean`](BusyLean/Comparison21.lean) | Contender 21 definitions and theorems |
| [`BusyLean/Contender22.lean`](BusyLean/Contender22.lean), [`Comparison22.lean`](BusyLean/Comparison22.lean) | Contender 22 definitions and theorems |
| [`BusyLean/TreeHyperReflection.lean`](BusyLean/TreeHyperReflection.lean), [`TreeHyperReflectionFacts.lean`](BusyLean/TreeHyperReflectionFacts.lean) | W-tree-ranked lift hierarchy (adopted from P22) |
| [`BusyLean/Contender23.lean`](BusyLean/Contender23.lean), [`Comparison23.lean`](BusyLean/Comparison23.lean) | Contender 23 definitions and theorems |
| [`BusyLean/Contender24.lean`](BusyLean/Contender24.lean), [`Comparison24.lean`](BusyLean/Comparison24.lean) | Contender 24 definitions and theorems |
| [`BusyLean/Contender25.lean`](BusyLean/Contender25.lean), [`Comparison25.lean`](BusyLean/Comparison25.lean) | Contender 25 definitions and theorems |
| [`BusyLean/Contender26.lean`](BusyLean/Contender26.lean), [`Comparison26.lean`](BusyLean/Comparison26.lean) | Contender 26 definitions and theorems |
| [`BusyLean/Contender27.lean`](BusyLean/Contender27.lean), [`Comparison27.lean`](BusyLean/Comparison27.lean) | Contender 27 definitions and theorems |
| [`BusyLean/Contender28.lean`](BusyLean/Contender28.lean), [`Comparison28.lean`](BusyLean/Comparison28.lean) | Contender 28 definitions and theorems |
| [`BusyLean/Contender29.lean`](BusyLean/Contender29.lean), [`Comparison29.lean`](BusyLean/Comparison29.lean) | Contender 29 definitions and theorems |
| [`BusyLean/Contender30.lean`](BusyLean/Contender30.lean), [`Comparison30.lean`](BusyLean/Comparison30.lean) | Contender 30 definitions and theorems |
| [`BusyLean/Contender31.lean`](BusyLean/Contender31.lean), [`Comparison31.lean`](BusyLean/Comparison31.lean) | Contender 31 definitions and theorems |
| [`BusyLean/Contender32.lean`](BusyLean/Contender32.lean), [`Comparison32.lean`](BusyLean/Comparison32.lean) | Contender 32 definitions and theorems |
| [`BusyLean/Contender33.lean`](BusyLean/Contender33.lean), [`Comparison33.lean`](BusyLean/Comparison33.lean) | Contender 33 definitions and theorems |
| [`BusyLean/Contender34.lean`](BusyLean/Contender34.lean), [`Comparison34.lean`](BusyLean/Comparison34.lean) | Contender 34 definitions and theorems |
| [`BusyLean/Contender35.lean`](BusyLean/Contender35.lean), [`Comparison35.lean`](BusyLean/Comparison35.lean) | Contender 35 definitions and theorems |
| [`BusyLean/Contender36.lean`](BusyLean/Contender36.lean), [`Comparison36.lean`](BusyLean/Comparison36.lean) | Contender 36 definitions and theorems |
| [`BusyLean/Contender37.lean`](BusyLean/Contender37.lean), [`Comparison37.lean`](BusyLean/Comparison37.lean) | Contender 37 definitions and theorems |
| [`BusyLean/Contender38.lean`](BusyLean/Contender38.lean), [`Comparison38.lean`](BusyLean/Comparison38.lean) | Contender 38 definitions and theorems |
| [`BusyLean/Contender39.lean`](BusyLean/Contender39.lean), [`Comparison39.lean`](BusyLean/Comparison39.lean) | Contender 39 definitions and theorems |
| [`BusyLean/Contender40.lean`](BusyLean/Contender40.lean), [`Comparison40.lean`](BusyLean/Comparison40.lean) | Contender 40 definitions and theorems |
| [`BusyLean/Contender41.lean`](BusyLean/Contender41.lean), [`Comparison41.lean`](BusyLean/Comparison41.lean) | Contender 41 definitions and theorems |
| [`article/`](article) | research notes, LaTeX source and PDF |
| [`test/`](test) | axiom/dependency audit, smoke tests |
| [`proposals/`](proposals) | the twenty-six reviewed proposals and [the review](proposals/REVIEW.md) |
| [`incoming/`](incoming) | drop zone for new proposal archives ([how they are processed](incoming/README.md)) |
| [`docs/`](docs) | snapshot of the original Coq contest |

## History

| # | Proof assistant | Author | Idea |
|---|---|---|---|
| 4 | Coq | codyroux | `ack 5 42 10002`, Ackermann-style |
| 5 | Coq | samuelgruetter | largest STLC + natural recursion (System T) numeral of depth 42 |
| 6 | Lean | this repository | forest reflection over System T + finite-type W-types, along the language's own trees; it combines ideas from proposals P5, P2 and P4 |
| 7 | Lean | this repository | System F (impredicative polymorphism) with Contender 6 as oracle; strong normalization proved in Lean |
| 8 | Lean | this repository | System Fω (type operators) with Contender 7 as oracle; candidates over kinds |
| 9 | Lean | this repository | System Fω reflected along the W-language's own trees, seeded with Contender 8 |
| 10 | Lean | this repository | kind-polymorphic System Fω (unbounded orders at run time), seeded with Contender 9 |
| 11 | Lean | this repository | kind-polymorphic Fω reflected along the W-language's trees |
| 12 | Lean | this repository | operator-level reflection (from P6) along notations above the index (from P7), over kind-polymorphic Fω |
| 13 | Lean | this repository | dynamic-kind Fω: a predicative universe of operators, with two levels of kind variables |
| 14 | Lean | this repository | a ladder of such universes, one SN proof for all levels; input `n` uses level `n` |
| 15 | Lean | this repository | P17's rank hierarchy of transformer lifts over family-aware ladder reflection |
| 16 | Lean | this repository | a transfinite ladder (length `ω^ω`) via a universe for every well-founded atom order |
| 17 | Lean | this repository | the ladder extended to length `ε₀` (hereditary Cantor normal forms) |
| 18 | Lean | this repository | the ladder extended to length `Γ₀` (binary Veblen terms, case-split Schütte proof) |
| 19 | Lean | this repository | the ladder extended to large-Veblen length (Klammersymbole with term positions) |
| 20 | Lean | this repository | the ladder extended to Bachmann–Howard length (collapsing; impredicative WF proof) |
| 21 | Lean | this repository | Buchholz ladders with level bound `n` at input `n`, lengths up to `ψ₀(Ω_ω)` |
| 22 | Lean | this repository | ladders over a tower of Buchholz notations relativized to well-founded bases |
| 23 | Lean | this repository | 22 with P22's transfinite (W-tree) rank for the lift hierarchy |
| 24 | Lean | this repository | towers along well-founded indices, each round indexed by the previous one |
| 25 | Lean | this repository | ladders over addresses in collapsed tree ordinals (P25's idea; well-foundedness for free) |
| 26 | Lean | this repository | collapsing with tree-indexed levels, iterated toward fixed points of `α ↦ ψ₀(Ω_α)` |
| 27 | Lean | this repository | stratified universes of level codes, toward the first fixed point of `α ↦ Ω_α` |
| 28 | Lean | this repository | universes stacked along collapsed tree ordinals |
| 29 | Lean | this repository | higher-order universe operators (closure points), indexed by tree ordinals |
| 30 | Lean | this repository | closure functionals of all finite types over universes |
| 31 | Lean | this repository | closure functionals of transfinite (tree-indexed) type |
| 32 | Lean | this repository | System T over tree ordinals with Contender 31 as a primitive; all programs of bounded size |
| 33 | Lean | this repository | the tree-ordinal language stacked on itself (each language is the next primitive) |
| 34 | Lean | this repository | the language stacked along a collapsed tree ordinal |
| 35 | Lean | this repository | ladder over trees built by impredicative System F programs |
| 36 | Lean | this repository | ladder programs build the next ladder's tree, iterated along a tree |
| 37 | Lean | this repository | tree languages stacked over the ladder jump |
| 38 | Lean | this repository | fast-growing hierarchy along Contender 37's tree |
| 39 | Lean | this repository | languages over the jump mixed with predicative collapse; hierarchy along them |
| 40 | Lean | this repository | System FT2 jump (tree recursion over the input) under P27's metalanguages |
| 41 | Lean | this repository | ladder reader programs (SystemFLT2) as the jump, under the metalanguages |

Proposals P1–P27 (four batches and seven late arrivals) were reviewed, rebuilt and ranked, and six
further archives were retired without import as offering no new idea; see
[`proposals/REVIEW.md`](proposals/REVIEW.md). Upstream code is MIT-licensed
([`docs/.../LICENSE`](docs/name-the-biggest-number-master/LICENSE)); this
repository is MIT-0 ([`LICENSE`](LICENSE)).
