-- Optional: run only after copying BusyLean7 into the FULL pinned BusyLean repo.
-- This is not part of the minimal vendored standalone project.
import BusyLean.Comparison
import BusyLean7.Comparison

namespace BusyLean

theorem contender_5_lt_contender_7 : contender_5 < contender_7 :=
  Nat.lt_trans contender_5_lt_contender_6 contender_6_lt_contender_7

theorem p5_lt_contender_7 : BigNumber.contender_6 < contender_7 :=
  Nat.lt_trans p5_lt_contender_6 contender_6_lt_contender_7

end BusyLean
