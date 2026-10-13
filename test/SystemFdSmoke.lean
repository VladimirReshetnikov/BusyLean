import BusyLean.Contender13
open BusyLean.Fd Ty

def body : Nat → CTm
  | 0 => .var 0
  | k + 1 => .app (.var 1) (body k)
def cnum (n : Nat) : CTm :=
  .tlam .star (.lam (arr (tvar 0) (tvar 0)) (.lam (tvar 0) (body n)))

/-- `(λx : unpack ★ (pack ★ nat). x) 3̄`: typechecks only via `unpack (pack A) ≡ A`. -/
def viaDyn : CTm := .app (.lam (unpack .star (pack .star Ty.nat)) (.var 0)) (cnum 3)

/-- Level-1 kind polymorphism, used at the kind `dyn`:
`(Λκ₁. ΛF:κ₁. λx:nat. x) [dyn] [pack ★ nat] 5̄`. -/
def atDyn : CTm :=
  .app (.tapp (.kapp1 (.klam1 (.tlam (.dvar 0) (.lam Ty.nat (.var 0)))) .dyn)
    (pack .star Ty.nat)) (cnum 5)

/-- Level-0 kind variables cannot be instantiated with `dyn` (rejected, 0). -/
def badLevel : CTm :=
  .app (.tapp (.kapp0 (.klam0 (.tlam (.kvar 0) (.lam Ty.nat (.var 0)))) .dyn)
    (pack .star Ty.nat)) (cnum 5)

/-- `pack` at a non-dyn-free kind is ill-kinded (rejected, 0). -/
def badPack : CTm := .app (.lam (unpack .dyn (pack .dyn (pack .star Ty.nat))) (.var 0)) (cnum 2)

#eval fvalue id 10 viaDyn       -- 3
#eval fvalue id 0 viaDyn        -- 0: the conversion needs fuel
#eval fvalue id 10 atDyn        -- 5
#eval fvalue id 10 badLevel     -- 0
#eval fvalue id 10 badPack      -- 0
#eval fvalue (· + 7) 10 (.app .orc (cnum 3))  -- 10
#eval (List.range 4).map fun n => (ctmsUpTo n).length
