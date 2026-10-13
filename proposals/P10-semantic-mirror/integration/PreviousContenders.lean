-- Optional: run inside the complete BusyLean repository, after installing
-- Mirror/*.lean and BusyLean/Contender7.lean. Not part of the standalone build.
import BusyLean.Comparison
import Mirror.Comparison

namespace BusyLean

theorem contender_5_lt_contender_7 : contender_5 < contender_7 :=
  Nat.lt_trans contender_5_lt_contender_6 contender_6_lt_contender_7

theorem p5_lt_contender_7 : BigNumber.contender_6 < contender_7 :=
  Nat.lt_trans p5_lt_contender_6 contender_6_lt_contender_7

end BusyLean
