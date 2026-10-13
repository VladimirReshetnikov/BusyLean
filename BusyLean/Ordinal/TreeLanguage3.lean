import BusyLean.Ordinal.TreeLanguage2

/-!
# Languages stacked along tree ordinals

`TreeLanguage2` stacks the tree-ordinal language `k` times (`boostK`). Here
the stacking height is a tree ordinal, by structural recursion:

* `boostT 0 = boost31`;
* `boostT (a+1) = langLift (boostT a)`: the whole language over the previous
  stage;
* `boostT (lim f) t = lim_i boostT (f i) t`.

At input `n`, both the height and the argument are Contender 33's tree
`stackedTree n`.
-/

namespace BusyLean.Ordinal

/-- Languages stacked along a tree ordinal. -/
def boostT : CTree → CTree → CTree
  | .zero => boost31
  | .succ a => langLift (boostT a)
  | .lim f => fun t => .lim fun i => boostT (f i) t
  | .supL _ => boost31
  | .supH _ => boost31

/-- The tree of input `n`: languages stacked to height `stackedTree n`, applied to it. -/
def treeStackedTree (n : Nat) : CTree :=
  .lim fun i => if i = 0 then stackedTree n else boostT (stackedTree n) (stackedTree n)

end BusyLean.Ordinal
