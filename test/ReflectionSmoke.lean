import BusyLean.Reflection
open BusyLean.W BigNumber

def num : Nat → Term
  | 0 => .zero
  | n + 1 => .app .succ (num n)

def fam : Family := fun i x => 100 * i + x

-- `var 0` is the oracle family at top level: fam 3 4 = 304.
#eval evalWith fam (.app (.app (.var 0) (num 3)) (num 4))
-- ... and still the oracle under a binder (oldest-first levels):
-- (fun y : ℕ => var0 y y) 5 = fam 5 5 = 505; `var 1` is the binder.
#eval evalWith fam (.app (.lam .nat .nat (.app (.app (.var 0) (.var 1)) (.var 1))) (num 5))
-- Without the oracle environment (P5's own semantics) the same term gives 0.
#eval evaluate (.app (.app (.var 0) (num 3)) (num 4))
-- Small reflections are computable.
#eval (List.range 3).map (reflect (fun _ x => x + 1))
#eval (List.range 3).map (stage (fun _ x => x + 1) (.node fun _ => .leaf))
