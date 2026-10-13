import BusyLean.Comparison52

open BusyLean.Ordinal

/-- The old universe-relative collapse is represented exactly. -/
example (J : CTree → CTree) (T : CTree) :
    (UL.oldBoostTerm.eval J T UL.emptyEnv).down = boost31J J T := rfl

/-- The universe-language jump retains its input on branch zero. -/
example (J : CTree → CTree) (T : CTree) (n : Nat) :
    universeLanguageLift J T n =
      .lim (fun i => if i = 0 then T else universeProgramTree J T n) := rfl

/-- The new tree applies the universe language to Contender 51's tree. -/
example (N : Nat) :
    BusyLean.universeTree52 N =
      universeLanguageLift (BusyLean.closeU N (BusyLean.metaJump N))
        (BusyLean.primTree N) N := rfl
