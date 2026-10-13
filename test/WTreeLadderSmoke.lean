import BusyLean.Ordinal.WTreeLadder

open BigNumber (WTree)
open BusyLean.Ordinal

private def tinyTree : WTree Nat :=
  .node fun i =>
    match i with
    | 0 => .node (fun _ => .leaf)
    | _ + 1 => .leaf

#eval TreePath.valid tinyTree .root
#eval TreePath.valid tinyTree (.child .root 0)
#eval TreePath.valid tinyTree (.child (.child .root 0) 37)
#eval TreePath.childLt tinyTree (.child .root 0) .root
#eval TreePath.childLt tinyTree (.child (.child .root 0) 37) (.child .root 0)
#eval TreePath.childLt tinyTree .root .root

#check @TreePath.childLt_wf
#check @wLevel_wf
#check @follow_tree12
