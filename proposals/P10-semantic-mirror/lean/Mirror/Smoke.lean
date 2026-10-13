import Mirror.Comparison

namespace BusyLean.Mirror

-- Only tiny primitive values and the short compiler syntax are reduced.
-- Never add #eval contender_7, #eval finalNumber, or #eval programMax.
example : termRank indexProgram = 14 := by decide
example : termRank numberProgram = 16 := by decide
example : termRank boostProgram = 17 := by decide
example : boost 0 = 3 := by decide
example : boost 1 = 18 := by decide

-- This is a theorem check, not numerical evaluation of either side.
example : boostIter 44 BusyLean.contender_6 < BusyLean.contender_7 :=
  BusyLean.contender_7_tower_margin

end BusyLean.Mirror
