import BusyLeanNext

open BusyLean.V7

-- Only small primitive arithmetic is evaluated; never a complete world.
example : exp2 0 = 1 := rfl
example : exp2 4 = 16 := rfl
example : tower 0 = 0 := rfl
example : tower 1 = 2 := rfl
example : tower 2 = 16 := rfl

#check contender_7
#check contender_6_lt_contender_7
#check towerOrbit_contender6_lt_contender7
#check lower_language_eventually_lt
#check no_programTree_eq_index
#check fixed_level_lt_diagonal
