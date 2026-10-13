import BusyLean.Ordinal.UniversalLanguage

namespace BusyLean.Ordinal.UTL

-- An ordinary untyped identity closure.
example (L : (CTree → CTree) → CTree → CTree) (b : CTree → CTree) (t : CTree) :
    denote L b 3 (.lam (.var 0)) t = t := rfl

-- The base transformer is callable as a dynamic primitive.
example (L : (CTree → CTree) → CTree → CTree) (b : CTree → CTree) (t : CTree) :
    denote L b 4 (.lam (.boost (.var 0))) t = b t := rfl

-- Quoted code can be evaluated and applied.
example (L : (CTree → CTree) → CTree → CTree) (b : CTree → CTree) (t : CTree) :
    denote L b 8
      (.lam (.app (.eval (.quote (.lam (.var 0)))) (.var 0))) t = t := rfl

-- The intensional constructors and dynamic closure representation are present.
#check Val.clos
#check Tm.self
#check Tm.eval
#check Tm.codeSize

end BusyLean.Ordinal.UTL
