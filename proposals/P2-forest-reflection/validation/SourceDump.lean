import Original

/- Small source-interpreter trace for the independent Python comparison. -/
def main : IO Unit := do
  for n in [0, 1, 2, 3, 4] do
    let ts := Original.termsUpTo n
    IO.println s!"T {n} {(Original.typesUpTo n).length}"
    IO.println s!"L {n} {ts.length}"
    IO.println s!"M {n} {Original.largestSTLCNatRecNatOfDepth n}"
    let mut index := 0
    for t in ts do
      IO.println s!"V {n} {index} {Original.eval t}"
      index := index + 1
