import BusyLean.Contender6

/-!
# Reflection lifted to transformers

Contender 6 applies forest reflection once, along `index`, to a seed family.
This file lifts that construction by one type level.

A `Transformer` maps oracle families to oracle families.  The primitive
transformer performs one ordinary reflection step.  `runTransformer` iterates
an arbitrary transformer along a `WTree Nat`; `liftTransformer` runs it along
the universal tree `index`.  Finally, `operatorStage` iterates this lift itself
along another W-tree.

All definitions are structural and executable.  There is no use of
`noncomputable`, `partial`, `unsafe`, `opaque`, `implemented_by`, or `extern`.
-/

namespace BusyLean

open BigNumber (WTree)
open BusyLean.W

/-- An operation taking one countable oracle family to another. -/
abbrev Transformer := Family → Family

/-- One ordinary reflection step, packaged as a transformer.
The output-family index is deliberately ignored. -/
def reflectionTransformer : Transformer :=
  fun fs _ n => reflect fs n

/-- Assemble a countable family of transformers into one transformer.
Output coordinate `i` selects transformer `i`; the selected transformer's
canonical output coordinate is `0`. -/
def spliceTransformers (ops : Nat → Transformer) : Transformer :=
  fun seed i n => ops i seed 0 n

/-- Iterate a transformer along a well-founded tree.

At a node, coordinate `i` of the input family supplied to `op` is the result of
running the same transformer down child `i`, evaluated at coordinate `i`.
Thus an operator may select a child dynamically through its family argument. -/
def runTransformer (op : Transformer) (seed : Family) :
    WTree Nat → Family
  | .leaf => op seed
  | .node f =>
      op (fun i n => runTransformer op seed (f i) i n)

/-- The autonomous lift of a transformer: iterate it along the same universal
index that Contender 6 uses. -/
def liftTransformer (op : Transformer) : Transformer :=
  fun seed => runTransformer op seed index

/-- Iterate the lifting operation itself along a W-tree.

* At a leaf, lift the base transformer once.
* At a node, splice the recursively generated child transformers, then lift
  the splice along `index`.

Running this construction on `index` is the second, operator-level autonomous
closure used by Contender 7. -/
def operatorStage (base : Transformer) : WTree Nat → Transformer
  | .leaf => liftTransformer base
  | .node f =>
      liftTransformer
        (spliceTransformers (fun i => operatorStage base (f i)))

end BusyLean
