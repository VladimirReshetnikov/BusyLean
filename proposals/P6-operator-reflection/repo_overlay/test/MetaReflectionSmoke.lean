import BusyLean.MetaReflection

open BusyLean
open BusyLean.W
open BigNumber (WTree)

/-- A tiny executable transformer used only for smoke testing the recursion. -/
def plusOneTransformer : Transformer :=
  fun seed _ n => seed 0 n + 1

private def seed : Family := fun i n => i + n
private def oneNode : WTree Nat := .node fun _ => .leaf

#eval runTransformer plusOneTransformer seed .leaf 0 2
#eval runTransformer plusOneTransformer seed oneNode 0 2

example : runTransformer plusOneTransformer seed .leaf 0 2 = 3 := rfl
example : runTransformer plusOneTransformer seed oneNode 0 2 = 4 := rfl
