import BusyLean.Comparison51

open BusyLean.Ordinal

/-- The old universe-relative collapse is represented exactly. -/
example (J : CTree → CTree) (T : CTree) :
    (UL.oldBoostTerm.eval J T UL.emptyEnv).down = boost31J J T := rfl

/-- The universe-language jump retains its input on branch zero. -/
example (J : CTree → CTree) (T : CTree) (n : Nat) :
    universeLanguageLift J T n =
      .lim (fun i => if i = 0 then T else universeProgramTree J T n) := rfl

/-- The candidate's new closure retains the previous closure on branch zero. -/
example (N : Nat) (J : CTree → CTree) (T : CTree) :
    BusyLean.close51 N J T =
      .lim (fun i => if i = 0 then BusyLean.closeU N J T
        else universeLanguageLift J T N) := rfl
