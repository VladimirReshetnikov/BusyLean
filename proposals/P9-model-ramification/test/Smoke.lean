import BusyLean7

example : BusyLean7.theta 0 = 2 := by decide
example : BusyLean7.theta 1 = 16 := by decide
example : BusyLean7.termRank (BusyLean7.amplifiedCall .zero) = 11 := by decide
example : BusyLean7.termRank (BusyLean7.amplifiedCall (.var 1)) = 11 := by decide
example : (BigNumber.allTerms 3).length = 308 := by decide
-- No #eval, #reduce, or decide is applied to either contender.
