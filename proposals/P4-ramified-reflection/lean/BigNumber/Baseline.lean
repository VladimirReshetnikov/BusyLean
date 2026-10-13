import BigNumber.Legacy

/-! This module is NOT in the definition's dependency closure. -/
namespace BigNumber.Legacy

def contender_5_term : Tm :=
  BigNumber.Lists.maxBy value 0 Tm.zero (terms 42)

def contender_5 : Nat := value contender_5_term

end BigNumber.Legacy
