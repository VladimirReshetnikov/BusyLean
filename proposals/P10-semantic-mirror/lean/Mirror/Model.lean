import BusyLean.Contender6

/-!
Semantic reflection over complete hierarchy operators.

The import supplies the shared language and helper functions. No definition in
this module depends on BusyLean.contender_6, BusyLean.finalFamily, BusyLean.index,
or either proposal-level contender constant. See the dependency audit.

Do not evaluate any concrete model-number or reflection maximum.
-/
namespace BusyLean.Mirror

open BigNumber (Ty Term Env WTree)
open BusyLean.W (Family prefixMax)

abbrev Tree := WTree Nat
abbrev Reflector := Family → Nat → Nat
abbrev Generator := Nat → Nat → Tree
abbrev Hierarchy := Family → Tree → Nat → Nat

/-- An executable semantic library, not a natural-number seed. -/
structure Model where
  reflection : Reflector
  trees : Generator

/-- Structural recursion on the tree, with a variable reflection algebra. -/
def walk (r : Reflector) (s : Family) : Tree → Nat → Nat
  | .leaf => r s
  | .node f => r (fun i => walk r s (f i))

/-- The unguarded two-level join used to measure a model. -/
def rawIndex (m : Model) : Tree :=
  .node (fun k => .node (fun i => m.trees k i))

/-- The common P5 seed is retained; no assembled predecessor number is a seed. -/
def number (m : Model) (n : Nat) : Nat :=
  walk m.reflection BusyLean.p5Family (rawIndex m) n

/-- Height-h binary exponential tower with top argument x. -/
def tower : Nat → Nat → Nat
  | 0, x => x
  | h + 1, x => BigNumber.pow2 (tower h x)

/-- A transparent quantitative certificate, independent of every contender. -/
def boost (x : Nat) : Nat := x + 1 + tower (x + 1) (x + 1)

def boostIter : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => boost (boostIter k x)

abbrev treeTy : Ty := .wt .nat
abbrev unaryTy : Ty := .arr .nat .nat
abbrev familyTy : Ty := .arr .nat unaryTy
abbrev generatorTy : Ty := .arr .nat (.arr .nat treeTy)
abbrev hierarchyTy : Ty := .arr familyTy (.arr treeTy unaryTy)

/-- Oldest-first levels: 0=hierarchy, 1=generator, 2=seed, 3=input,
4=amplifier, 5=relative oracle. The actual list is newest-first. -/
def environment (h : Hierarchy) (g : Generator) (s : Family)
    (n : Nat) (a : Nat → Nat) (fs : Family) : Env :=
  [⟨familyTy, fs⟩, ⟨unaryTy, a⟩, ⟨.nat, n⟩,
   ⟨familyTy, s⟩, ⟨generatorTy, g⟩, ⟨hierarchyTy, h⟩]

def libraryEnv (m : Model) (fs : Family) (n : Nat) : Env :=
  environment (walk m.reflection) m.trees BusyLean.p5Family n boost fs

def zeroFamily : Family := fun _ _ => 0

def numericValue (env : Env) (t : Term) : Nat :=
  match BigNumber.interpret env t with
  | ⟨.nat, n⟩ => n
  | ⟨.arr _ _, _⟩ => 0
  | ⟨.wt _, _⟩ => 0

def score (m : Model) (fs : Family) (n : Nat) (t : Term) : Nat :=
  numericValue (libraryEnv m fs n) t

/-- The offset is the exact rank of the fixed comparison compiler's output. -/
def budget (n : Nat) : Nat := n + 17

def programMax (m : Model) (fs : Family) (n : Nat) : Nat :=
  BigNumber.maximum (score m fs n) (BigNumber.allTerms (budget n))

/-- Keep closed and relative semantics separately. No oracle monotonicity is used. -/
def libraryBound (m : Model) (fs : Family) (n : Nat) : Nat :=
  BigNumber.maxN (programMax m zeroFamily n) (programMax m fs n)

/-- Reflect over the whole library of each visible child model. -/
def joinReflect (ms : Nat → Model) (fs : Family) (n : Nat) : Nat :=
  n + 1 + BigNumber.maxN (BusyLean.W.reflect fs n)
    (prefixMax (fun i => libraryBound (ms i) fs n) n)

/-- A tree program is interpreted with the complete older semantic library. -/
def treeValue (m : Model) (k : Nat) (t : Term) : Tree :=
  BigNumber.castValue treeTy (BigNumber.interpret (libraryEnv m zeroFamily k) t).2

/-- All child libraries are retained, as separate branches, in the tree generator. -/
def joinTrees (ms : Nat → Model) (k i : Nat) : Tree :=
  .node (fun j => treeValue (ms j) k
    (BusyLean.nthD (BigNumber.allTerms k) i .zero))

def join (ms : Nat → Model) : Model :=
  ⟨joinReflect ms, joinTrees ms⟩

/-- Structural recursion whose results are entire executable semantic libraries. -/
def foldModels (m : Model) : Tree → Model
  | .leaf => m
  | .node f => join (fun i => foldModels m (f i))

/-- Branch zero retains the whole previous model, not its assembled number.
The remaining branches range over the model's generated tree universe. -/
def guardedIndex (m : Model) : Tree :=
  .node (fun
    | 0 => .leaf
    | k + 1 => .node (fun i => m.trees k i))

def bootstrap (m : Model) : Model := foldModels m (guardedIndex m)

def rounds (m : Model) : Nat → Model
  | 0 => m
  | k + 1 => bootstrap (rounds m k)

/-- Reconstruction from the old language's generic reflection and enumeration
operations, with no reference to the old index or old winner functions. -/
def initialModel : Model :=
  ⟨BusyLean.W.reflect,
   fun k i => BusyLean.defTree
     (BusyLean.nthD (BigNumber.allTerms k) i .zero)⟩

/-- A countable join of all finite self-generated semantic bootstrap rounds. -/
def limitModel : Model := join (rounds initialModel)

/-- One further bootstrap through the limit model's own tree universe. -/
def finalModel : Model := bootstrap limitModel

def finalNumber (n : Nat) : Nat := number finalModel n

end BusyLean.Mirror
