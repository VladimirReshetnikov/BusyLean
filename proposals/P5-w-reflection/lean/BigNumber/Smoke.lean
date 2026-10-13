import BigNumber.Definitions
open BigNumber
-- Shallow, optional tests only. Do not replace 3 by 42.
#eval (oldTerms 3).length
#eval (allTerms 3).length
#eval oldMaximum 3
#eval wMaximum 3
#eval (lookup [10, 11, 12] 0)
#eval (lookup [10, 11, 12] 2)
#eval (lookup [10, 11, 12] 3)
#eval rows (fun n => n+1) 1 4
#eval rows (fun n => n+1) 2 1
