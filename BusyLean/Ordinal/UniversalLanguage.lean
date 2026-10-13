import BusyLean.Ordinal.TreeLanguage4

/-!
# A fuel-bounded universal higher-order language over tree ordinals

`TreeLanguage4` is a strongly normalizing, simply typed metalanguage.  This
module adds a qualitatively different closure mechanism: an *untyped* higher-
order tree machine with explicit fuel, quotation, and evaluation.

Untyped self-application is safe here because every call of the interpreter
uses strictly smaller fuel.  Thus every individual run is total and executable.
The whole-language closure ranges over every finite fuel, every finite syntax
depth, and every term at that depth.  No halting oracle, minimization over
termination, or Busy-Beaver function is used.

The dynamic values are closures rather than Lean functions.  This keeps the
value datatype strictly positive.  A separate `natFun` constructor represents
the branch functions supplied to a tree recursor; `Nat -> Val` is a positive
occurrence of `Val`.
-/

namespace BusyLean.Ordinal

namespace UTL

/-- Untyped terms for the universal tree machine. -/
inductive Tm where
  | var : Nat → Tm
  | lam : Tm → Tm
  | app : Tm → Tm → Tm
  | zero : Tm
  | succ : Tm → Tm
  | natRec : Tm → Tm → Tm → Tm
  | tzero : Tm
  | tsucc : Tm → Tm
  | tlim : Tm → Tm
  | treeRec : Tm → Tm → Tm → Tm → Tm
  | boost : Tm → Tm
  | lift : Tm → Tm → Tm
  | quote : Tm → Tm
  | eval : Tm → Tm
  | self : Tm
  | codeSize : Tm → Tm
  deriving DecidableEq, Repr

/-- Syntactic size.  Quoted syntax counts: quotation is compression only when
constructed or selected dynamically, not an exemption from the enumeration. -/
def Tm.size : Tm → Nat
  | .var _ | .zero | .tzero | .self => 1
  | .lam t | .succ t | .tsucc t | .tlim t | .boost t |
      .quote t | .eval t | .codeSize t => t.size + 1
  | .app t u | .lift t u => t.size + u.size + 1
  | .natRec z s n => z.size + s.size + n.size + 1
  | .treeRec z s l t => z.size + s.size + l.size + t.size + 1

/-- Dynamic values.  Closures remember the root program so that `self` remains
lexically scoped even after a quoted program is evaluated. -/
inductive Val where
  | nat : Nat → Val
  | tree : CTree → Val
  | clos : Tm → Tm → List Val → Val
  | natFun : (Nat → Val) → Val
  | code : Tm → Val

/-- The uniform error/default value. -/
def junk : Val := .tree .zero

/-- Dynamic projections use harmless defaults on a tag mismatch. -/
def Val.asNat : Val → Nat
  | .nat n => n
  | _ => 0

/-- Dynamic tree projection. -/
def Val.asTree : Val → CTree
  | .tree t => t
  | _ => .zero

/-- Dynamic code projection. -/
def Val.asCode : Val → Tm
  | .code t => t
  | _ => .zero

/-- Reversed de Bruijn lookup with a total default. -/
def lookup (ρ : List Val) (n : Nat) : Val := (ρ[n]?).getD junk

/--
The universal interpreter.  The recursion argument is *fuel*, not syntax.
Every subevaluation, closure call, and evaluation of quoted code receives
strictly smaller fuel.  Consequently even `eval self` is a total computation.
-/
def run
    (liftF : (CTree → CTree) → CTree → CTree)
    (boostF : CTree → CTree) : Nat → Tm → List Val → Tm → Val
  | 0, _, _, _ => junk
  | fuel + 1, root, ρ, term =>
      let appVal : Val → Val → Val := fun f a =>
        match f with
        | .clos closureRoot body closureEnv =>
            run liftF boostF fuel closureRoot (a :: closureEnv) body
        | .natFun g => g a.asNat
        | _ => junk
      match term with
      | .var n => lookup ρ n
      | .lam body => .clos root body ρ
      | .app f a =>
          appVal (run liftF boostF fuel root ρ f)
            (run liftF boostF fuel root ρ a)
      | .zero => .nat 0
      | .succ n => .nat (run liftF boostF fuel root ρ n).asNat.succ
      | .natRec z s n =>
          let vz := run liftF boostF fuel root ρ z
          let vs := run liftF boostF fuel root ρ s
          let vn := (run liftF boostF fuel root ρ n).asNat
          Nat.rec vz (fun _ acc => appVal vs acc) vn
      | .tzero => .tree .zero
      | .tsucc t => .tree (.succ (run liftF boostF fuel root ρ t).asTree)
      | .tlim f =>
          let vf := run liftF boostF fuel root ρ f
          .tree (.lim fun i => (appVal vf (.nat i)).asTree)
      | .treeRec z s l t =>
          let vz := run liftF boostF fuel root ρ z
          let vs := run liftF boostF fuel root ρ s
          let vl := run liftF boostF fuel root ρ l
          let vt := (run liftF boostF fuel root ρ t).asTree
          TL.treeIter vz (fun x => appVal vs x)
            (fun xs => appVal vl (.natFun xs)) vt
      | .boost t =>
          .tree (boostF (run liftF boostF fuel root ρ t).asTree)
      | .lift b t =>
          let vb := run liftF boostF fuel root ρ b
          let vt := (run liftF boostF fuel root ρ t).asTree
          .tree (liftF (fun x => (appVal vb (.tree x)).asTree) vt)
      | .quote q => .code q
      | .eval c =>
          let q := (run liftF boostF fuel root ρ c).asCode
          run liftF boostF fuel q [] q
      | .self => .code root
      | .codeSize c =>
          .nat (run liftF boostF fuel root ρ c).asCode.size

/-- A term denotes a total tree transformer: run it as a closed value and
apply the resulting closure to the input tree. -/
def denote
    (liftF : (CTree → CTree) → CTree → CTree)
    (boostF : CTree → CTree) (fuel : Nat) (p : Tm) (t : CTree) : CTree :=
  let vf := run liftF boostF fuel p [] p
  match fuel, vf with
  | k + 1, .clos closureRoot body closureEnv =>
      (run liftF boostF k closureRoot (.tree t :: closureEnv) body).asTree
  | _, _ => .zero

/-! ## Effective enumeration -/

/-- Untyped programs of constructor depth at most `n`, with variables below
`n`.  Quotation and evaluation are ordinary constructors in the enumeration. -/
def termsUpTo : Nat → List Tm
  | 0 => []
  | n + 1 =>
      let es := termsUpTo n
      (List.range n).map .var ++ [.zero, .tzero, .self] ++
      es.map .lam ++
      es.flatMap (fun f => es.map fun a => .app f a) ++
      es.map .succ ++ es.map .tsucc ++ es.map .tlim ++ es.map .boost ++
      es.map .quote ++ es.map .eval ++ es.map .codeSize ++
      es.flatMap (fun b => es.map fun t => .lift b t) ++
      es.flatMap (fun z => es.flatMap fun s => es.map fun k => .natRec z s k) ++
      es.flatMap (fun z =>
        es.flatMap fun s => es.flatMap fun l => es.map fun t => .treeRec z s l t)

/-- All transformers denoted by programs of depth at most `m`, at a fixed
fuel.  There is deliberately no type filter: malformed uses take the explicit
`junk` branch, exactly as a total untyped machine should. -/
def funsUpTo
    (liftF : (CTree → CTree) → CTree → CTree)
    (boostF : CTree → CTree) (fuel m : Nat) : List (CTree → CTree) :=
  (termsUpTo m).map fun p => denote liftF boostF fuel p

/-- The identity and quotation/evaluation smoke facts are definitional. -/
theorem denote_id
    (liftF : (CTree → CTree) → CTree → CTree)
    (boostF : CTree → CTree) (t : CTree) :
    denote liftF boostF 3 (.lam (.var 0)) t = t := rfl

theorem denote_boost
    (liftF : (CTree → CTree) → CTree → CTree)
    (boostF : CTree → CTree) (t : CTree) :
    denote liftF boostF 4 (.lam (.boost (.var 0))) t = boostF t := rfl

theorem denote_quote_eval_id
    (liftF : (CTree → CTree) → CTree → CTree)
    (boostF : CTree → CTree) (t : CTree) :
    denote liftF boostF 8
      (.lam (.app (.eval (.quote (.lam (.var 0)))) (.var 0))) t = t := rfl

end UTL

/--
The whole fuel-bounded universal language over a lower closure operator and a
base transformer.  The three limits enumerate fuel, syntax depth, and program
index.  Each selected branch is an ordinary terminating Lean computation.
-/
def universalLangLift
    (liftF : (CTree → CTree) → CTree → CTree)
    (b : CTree → CTree) (t : CTree) : CTree :=
  .lim fun fuel => .lim fun m => .lim fun i =>
    (((UTL.funsUpTo liftF b fuel m)[i]?).map fun p => p t).getD .zero

/--
Universal-reflection languages stacked along a countable tree.  At a successor,
the previous whole-language closure is the `lift` primitive of an untyped,
self-interpreting machine.  Limits remain pointwise, preserving totality.
-/
def universalBoostT : CTree → (CTree → CTree) → CTree → CTree
  | .zero => langLift
  | .succ a => universalLangLift (universalBoostT a)
  | .lim f => fun b t => .lim fun i => universalBoostT (f i) b t
  | .supL _ => langLift
  | .supH _ => langLift

end BusyLean.Ordinal
