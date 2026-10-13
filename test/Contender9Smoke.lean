import BusyLean.Contender9
open BusyLean
-- The pairing code 2^i (2m+1) decodes back to (i, m).
#eval [(0,0),(1,0),(0,3),(3,5),(7,2)].map fun (i, m) => unpair2 (2 ^ i * (2 * m + 1))
-- Small Fω reflections over a toy family fs i x = 10 i + x.
#eval (List.range 4).map (reflect9 (fun i x => 10 * i + x))
#eval (List.range 3).map (stage9 (fun i x => 10 * i + x) (.node fun _ => .leaf))
