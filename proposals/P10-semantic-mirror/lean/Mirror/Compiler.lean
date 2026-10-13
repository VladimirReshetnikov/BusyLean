import Mirror.Model

/-! A fixed object-program compiler. These terms are proof witnesses only:
they are NOT inserted into the maximum's enumeration by special cases. -/
namespace BusyLean.Mirror

open BigNumber (Ty Term)

/-- Exact cost matching BigNumber.allTypes. -/
def typeRank : Ty → Nat
  | .nat => 1
  | .arr a b => Nat.max (typeRank a) (typeRank b) + 1
  | .wt a => typeRank a + 1

/-- Exact sufficient enumeration rank, including type and variable costs. -/
def termRank : Term → Nat
  | .var i => i + 2
  | .lam a b t => Nat.max (Nat.max (typeRank a) (typeRank b)) (termRank t) + 1
  | .app t u => Nat.max (termRank t) (termRank u) + 1
  | .zero | .succ => 1
  | .natrec a | .wzero a | .wnode a => typeRank a + 1
  | .wrec a b => Nat.max (typeRank a) (typeRank b) + 1

/-- With six ambient bindings, the two new binders have oldest-first levels 6,7.
This denotes node (fun k => node (fun i => generator k i)). -/
def indexProgram : Term :=
  .app (.wnode .nat)
    (.lam .nat treeTy
      (.app (.wnode .nat)
        (.lam .nat treeTy
          (.app (.app (.var 1) (.var 6)) (.var 7)))))

/-- Generic use of a hierarchy, seed, generated index, and input. -/
def numberProgram : Term :=
  .app (.app (.app (.var 0) (.var 2)) indexProgram) (.var 3)

/-- Generic amplification of that result. Enumeration rank: exactly 17. -/
def boostProgram : Term := .app (.var 4) numberProgram

end BusyLean.Mirror
