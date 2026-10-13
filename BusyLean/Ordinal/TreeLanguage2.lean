import BusyLean.Ordinal.TreeLanguage

/-!
# Languages stacked on languages

`TreeLanguage` takes all closed tree programs of bounded size over a primitive
`boost`. Here the whole language becomes the next primitive.

* `funsUpTo b m`: the closed programs of type `tree ⇒ tree` and size `≤ m` over
  the primitive `b`, as functions;
* `langLift b t = lim_m lim_i (P_i t)`: every such program, of every size, applied
  to `t`. The new boost absorbs the whole language over the old one, including
  all transfinite and higher-type iterations of `b`;
* `boostK 0 = boost31`, `boostK (k+1) = langLift (boostK k)`.

At input `n`, the tree is `boostK (n+1)` applied to Contender 32's tree. Like the
language itself, this is structural recursion with a semantic interpreter;
nothing is ever evaluated.
-/

namespace BusyLean.Ordinal

namespace TL

/-- Closed programs of type `tree ⇒ tree` and size `≤ m`, as functions. -/
def funsUpTo (boostF : CTree → CTree) (m : Nat) : List (CTree → CTree) :=
  (rawsUpTo m).filterMap fun r =>
    match infer [] r with
    | some ⟨.arr .tree .tree, t⟩ => some (t.eval boostF ())
    | _ => none

end TL

/-- The whole language over `b`, applied to `t`. -/
def langLift (b : CTree → CTree) (t : CTree) : CTree :=
  .lim fun m => .lim fun i => (((TL.funsUpTo b m)[i]?).map (· t)).getD .zero

/-- Languages stacked `k` times over Contender 31's construction. -/
def boostK : Nat → CTree → CTree
  | 0 => boost31
  | k + 1 => langLift (boostK k)

/-- The tree of input `n`: the `(n+1)`-fold stacked language applied to Contender 32's tree. -/
def stackedTree (n : Nat) : CTree :=
  .lim fun i => if i = 0 then languageTree n else boostK (n + 1) (languageTree n)

end BusyLean.Ordinal
