import BusyLean.Ordinal.TreeLanguage

/-!
# Collapsing universes of codes relative to a jump

Contender 31's operator `boost31 Λ` builds a universe of level codes with the
universe operators and closure functionals of Contenders 27–31. It then
collapses `ε_{Ω_top+1}` of the next universe with `U2.DN`, whose successor
step is "the next ε-number" at every level.

`U2.DNJ J` is `DN` with the successor step at the countable level `.zero`
replaced by `lim (ε⁺ x, J (ε⁺ x))`. The level-`.zero` trees of the next
universe are exactly the countable trees. Every diagonal step ends at level
0, so `J` acts throughout the collapse. `boost31J J Λ` is Contender 31's whole
construction collapsed relative to `J`.
-/

namespace BusyLean.Ordinal

namespace U2

variable (U : Univ)

/-- The successor step at level `a`: `J` after ε⁺ at the countable level, ε⁺ above it. -/
def jStepN (J : CTree → CTree) : (a : NCode U) → NLev U a → NLev U a
  | .zero, x => Tre.lim fun i => if i = 0 then Tre.epsNext x else J (Tre.epsNext x)
  | _, x => Tre.epsNext x

/-- **Collapsing in the next universe relative to `J`**, by structural recursion. -/
def DNJ (J : CTree → CTree) : (a : NCode U) → NArg U → NLev U a
  | a, .zero => nOmega U a
  | a, .succ t => jStepN U J a (DNJ J a t)
  | a, .lim f => .lim fun n => DNJ J a (f n)
  | a, .supAt c g =>
      match c, g with
      | .succ c', g =>
          let seq : Nat → NLev U c' := fun k =>
            Nat.rec (motive := fun _ => NLev U c') (nOmega U c') (fun _ x => DNJ J c' (g (.inr x))) k
          .lim fun k => DNJ J a (g (.inr (seq k)))
      | .lim f, g =>
          .lim fun i =>
            let seq : Nat → NLev U (f i) := fun k =>
              Nat.rec (motive := fun _ => NLev U (f i)) (nOmega U (f i))
                (fun _ x => DNJ J (f i) (g ⟨i, .inr x⟩)) k
            .lim fun k => DNJ J a (g ⟨i, .inr (seq k)⟩)
      | .supAt c0 h, g =>
          .lim fun m =>
            match U.sample c0 m with
            | some b =>
                let seq : Nat → NLev U (h b) := fun k =>
                  Nat.rec (motive := fun _ => NLev U (h b)) (nOmega U (h b))
                    (fun _ x => DNJ J (h b) (g ⟨b, .inr x⟩)) k
                .lim fun k => DNJ J a (g ⟨b, .inr (seq k)⟩)
            | none => nOmega U a
      | .zero, _ => nOmega U a

/-- Collapse `ε_{Ω_top + 1}` of the universe after `U` relative to `J`. -/
def universeTreeJ (J : CTree → CTree) : CTree :=
  DNJ U J .zero (NArg.epsNext U (.succ (nToArg U (ntop U) (nOmega U (ntop U)))))

end U2

/-- Contender 31's construction over the index `Λ`, collapsed relative to `J`. -/
def boost31J (J : CTree → CTree) (Λ : CTree) : CTree :=
  U2.universeTreeJ (U2.transTypeUniv (U2.ΦT Λ) Λ) J

end BusyLean.Ordinal
