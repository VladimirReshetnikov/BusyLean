import BigNumber.Language

/-! Only small terminating computations. Never evaluate contender_5 or contender_6. -/
open BigNumber

example : Lists.lookup [10, 11, 12] 0 = some 12 := rfl
example : Lists.lookup [10, 11, 12] 2 = some 10 := rfl
example : Lists.lookup [10, 11, 12] 3 = none := rfl
example : Legacy.value (.app .succ (.app .succ .zero)) = 2 := rfl
example : Legacy.value (.app .zero .succ) = 0 := rfl
example : Legacy.value (.app .succ .succ) = 1 := rfl
example : Language.value (fun i n => i + n) (Language.oracleWitness 2 3) = 6 := rfl
example : Language.value (fun _ _ => 0) (.app .succ .treeZero) = 1 := rfl
example : Language.value (fun _ _ => 0) (.quote (.app .succ .zero)) = 1 := rfl
