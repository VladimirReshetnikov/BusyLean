import BusyLean.Ordinal.TreeUniverses

/-!
# Universes of level codes along tree ordinals

`TreeUniverses` stacks universes of level codes along the natural numbers.
Here a universe carries a *sequence* of large codes (`tops`) instead of one. So
the union of a sequence of universes is again a universe, with codes
`Σ i, (F i).Code`. Universes can therefore be indexed by countable tree
ordinals, by structural recursion: `univT 0 = base`,
`univT (a+1) = next (univT a)`, `univT (lim f) = union (univT ∘ f)`.

The number of stacked universes can itself be a collapsed tree. `roundTree`
iterates `Λ ↦ collapse in the universe after univT Λ`, starting from Contender
27's tree. Collapsing inside a universe is unchanged from `TreeUniverses`.
-/

namespace BusyLean.Ordinal

namespace U2

/-- A universe of level codes. -/
structure Univ : Type 1 where
  Code : Type
  Low : Code → Type
  /-- Sample elements of the lower parts, for diagonals. -/
  sample : (c : Code) → Nat → Option (Low c)
  /-- A sequence of large codes. -/
  tops : Nat → Code

/-- Codes of the next universe. -/
inductive NCode (U : Univ) : Type where
  | zero : NCode U
  | succ : NCode U → NCode U
  | lim : (Nat → NCode U) → NCode U
  | supAt : (c : U.Code) → (U.Low c → NCode U) → NCode U

/-- Everything below a code of the next universe. -/
def NLow (U : Univ) : NCode U → Type
  | .zero => Empty
  | .succ t => NLow U t ⊕ Tre (NLow U t) Empty
  | .lim f => Σ i, (NLow U (f i) ⊕ Tre (NLow U (f i)) Empty)
  | .supAt c h => Σ b : U.Low c, (NLow U (h b) ⊕ Tre (NLow U (h b)) Empty)

/-- Level-`a` trees of the next universe. -/
abbrev NLev (U : Univ) (a : NCode U) : Type := Tre (NLow U a) Empty

def nsample (U : Univ) : (c : NCode U) → Nat → Option (NLow U c)
  | .zero, _ => none
  | .succ _, m => some (.inr (Tre.nat m))
  | .lim _, m => some ⟨m, .inr (Tre.nat m)⟩
  | .supAt c _, m => (U.sample c m).map fun b => ⟨b, .inr (Tre.nat m)⟩

/-- A large code: the limit of levels indexed by the old tops. -/
def ntop (U : Univ) : NCode U := .lim fun m => .supAt (U.tops m) fun _ => .zero

/-- Large codes of the next universe: finite successors above `ntop`. -/
def ntops (U : Univ) (m : Nat) : NCode U :=
  Nat.rec (motive := fun _ => NCode U) (ntop U) (fun _ t => .succ t) m

/-- The next universe. -/
def Univ.next (U : Univ) : Univ where
  Code := NCode U
  Low := NLow U
  sample := nsample U
  tops := ntops U

/-- The trivial universe: one code with nothing below it. -/
def Univ.base : Univ where
  Code := Unit
  Low := fun _ => Empty
  sample := fun _ _ => none
  tops := fun _ => ()

/-- The union of a sequence of universes. -/
def Univ.union (F : Nat → Univ) : Univ where
  Code := Σ i, (F i).Code
  Low := fun p => (F p.1).Low p.2
  sample := fun p m => (F p.1).sample p.2 m
  tops := fun m => ⟨m, (F m).tops m⟩

/-- Universes along a countable tree ordinal. -/
def univT : CTree → Univ
  | .zero => Univ.base
  | .succ a => (univT a).next
  | .lim f => Univ.union fun i => univT (f i)
  | .supL _ => Univ.base
  | .supH _ => Univ.base

/-! ## Collapsing inside the next universe -/

variable (U : Univ)

/-- One level up, extending suprema by zero. -/
def nUpSucc (a : NCode U) : NLev U a → NLev U (.succ a) :=
  Tre.embed (fun h => .supL fun c => match c with | .inl b => h b | .inr _ => .zero) (fun h => .supH h)

def nUpLim (f : Nat → NCode U) (i : Nat) : NLev U (f i) → NLev U (.lim f) :=
  Tre.embed (fun h => .supL fun p =>
      if hj : p.1 = i then
        match (hj ▸ p.2 : NLow U (f i) ⊕ Tre (NLow U (f i)) Empty) with
        | .inl b => h b
        | .inr _ => .zero
      else .zero)
    (fun h => .supH h)

/-- Lower elements as level elements (zero where the index type has no decidable equality). -/
def nEmbedLow : (a : NCode U) → NLow U a → NLev U a
  | .zero, b => b.elim
  | .succ a, .inl b => nUpSucc U a (nEmbedLow a b)
  | .succ a, .inr e => nUpSucc U a e
  | .lim f, ⟨i, .inl b⟩ => nUpLim U f i (nEmbedLow (f i) b)
  | .lim f, ⟨i, .inr e⟩ => nUpLim U f i e
  | .supAt _ _, _ => .zero

/-- `Ω_a` in the next universe. -/
def nOmega (a : NCode U) : NLev U a :=
  .lim fun m => if m = 0 then .supL (nEmbedLow U a) else Tre.nat m

/-- Arguments: suprema carry their level code. -/
inductive NArg (U : Univ) : Type where
  | zero : NArg U
  | succ : NArg U → NArg U
  | lim : (Nat → NArg U) → NArg U
  | supAt : (c : NCode U) → (NLow U c → NArg U) → NArg U

namespace NArg

def nat : Nat → NArg U
  | 0 => .zero
  | n + 1 => .succ (nat n)

def add (a : NArg U) : NArg U → NArg U
  | .zero => a
  | .succ t => .succ (add a t)
  | .lim f => .lim fun n => add a (f n)
  | .supAt c g => .supAt c fun x => add a (g x)

def mul (a : NArg U) : NArg U → NArg U
  | .zero => .zero
  | .succ t => add U (mul a t) a
  | .lim f => .lim fun n => mul a (f n)
  | .supAt c g => .supAt c fun x => mul a (g x)

def expo : NArg U → NArg U
  | .zero => .succ .zero
  | .succ t => .lim fun n => mul U (expo t) (nat U n)
  | .lim f => .lim fun n => expo (f n)
  | .supAt c g => .supAt c fun x => expo (g x)

def tower : Nat → NArg U → NArg U
  | 0, x => x
  | k + 1, x => expo U (tower k x)

def epsNext (x : NArg U) : NArg U := .lim fun k => tower U k (.succ x)

end NArg

/-- Level elements as arguments. -/
def nToArg (a : NCode U) : NLev U a → NArg U
  | .zero => .zero
  | .succ t => .succ (nToArg a t)
  | .lim f => .lim fun n => nToArg a (f n)
  | .supL h => .supAt a fun b => nToArg a (h b)
  | .supH _ => .zero

/-- **Collapsing in the next universe**, by structural recursion. -/
def DN : (a : NCode U) → NArg U → NLev U a
  | a, .zero => nOmega U a
  | a, .succ t => Tre.epsNext (DN a t)
  | a, .lim f => .lim fun n => DN a (f n)
  | a, .supAt c g =>
      match c, g with
      | .succ c', g =>
          let seq : Nat → NLev U c' := fun k =>
            Nat.rec (motive := fun _ => NLev U c') (nOmega U c') (fun _ x => DN c' (g (.inr x))) k
          .lim fun k => DN a (g (.inr (seq k)))
      | .lim f, g =>
          .lim fun i =>
            let seq : Nat → NLev U (f i) := fun k =>
              Nat.rec (motive := fun _ => NLev U (f i)) (nOmega U (f i))
                (fun _ x => DN (f i) (g ⟨i, .inr x⟩)) k
            .lim fun k => DN a (g ⟨i, .inr (seq k)⟩)
      | .supAt c0 h, g =>
          .lim fun m =>
            match U.sample c0 m with
            | some b =>
                let seq : Nat → NLev U (h b) := fun k =>
                  Nat.rec (motive := fun _ => NLev U (h b)) (nOmega U (h b))
                    (fun _ x => DN (h b) (g ⟨b, .inr x⟩)) k
                .lim fun k => DN a (g ⟨b, .inr (seq k)⟩)
            | none => nOmega U a
      | .zero, _ => nOmega U a

/-- Collapse `ε_{Ω_top + 1}` of the universe after `U` to a countable tree. -/
def universeTree (U : Univ) : CTree :=
  DN U .zero (NArg.epsNext U (.succ (nToArg U (ntop U) (nOmega U (ntop U)))))

/-- One round: collapse in the universe after `univT Λ`. -/
def nextRound (Λ : CTree) : CTree := universeTree (univT Λ)

/-- `k` rounds above Contender 27's tree. -/
def rounds (n : Nat) : Nat → CTree
  | 0 => universeLadderTree n
  | k + 1 => nextRound (rounds n k)

end U2

/-- The tree of input `n`: `n+1` rounds of universes along trees. -/
def roundTree (n : Nat) : CTree := U2.rounds n (n + 1)

end BusyLean.Ordinal
