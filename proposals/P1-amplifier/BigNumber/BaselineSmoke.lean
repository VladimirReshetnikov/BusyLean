import BigNumber.Baseline

/-!
Optional executable smoke tests. This module is deliberately not imported by
the submitted definition/proof modules. It evaluates only depths zero to four.
-/

open BigNumber.Baseline

/- Rows are (depth, number of types, number of raw terms, maximum value). -/
#eval (List.range 5).map fun n =>
  (n, (typesUpTo n).length, (termsUpTo n).length, envelope n)

/- Selected representatives allow a second check of the maxBy tie rule. -/
#eval (List.range 5).map largestOfDepth

#print axioms BigNumber.Baseline.contender_5
#print axioms BigNumber.Baseline.envelope
#print axioms BigNumber.Baseline.eval_maxBy
#print axioms BigNumber.Baseline.contender_5_eq_envelope
#print axioms BigNumber.Baseline.initial_le_foldMax
#print axioms BigNumber.Baseline.envelope_bound
