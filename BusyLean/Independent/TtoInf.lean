import BusyLean.Independent.TEmbedding
import BusyLean.Independent.CutElim

/-!
# Contender 5's terms as infinitary terms

`trI Γ w` translates a raw Contender 5 term (ill-typed ones included) into an
infinitary typed term of its static type. As in `TEmbedding.lean`, casts
between different types become default values. Natural recursion becomes
Tait's case tree:

  `natRec r ↦ λa f n. case n (a, f 0 a, f 1 (f 0 a), …)`,

η-expanded so that the case distinction always has type `nat`.

`eval_trI` shows that the translation has Contender 5's value.
-/

namespace BusyLean.Indep.Inf

open BusyLean.C5 (Ty den Term Value lookup nthError interp castImpl recursion error)
open BusyLean.Indep.Emb (stype tys typeEqb_eq castImpl_ne lookup_map interp_fst lookup_some)

/-! ## Combinators -/

def varAt : (Γ : List Ty) → (i : Nat) → {a : Ty} → nthError Γ i = some a → Var Γ a
  | [], _, _, h => nomatch h
  | b :: _, 0, _, h => by cases h; exact .here
  | _ :: Γ, i + 1, _, h => .there (varAt Γ i h)

/-- Default values. -/
def errT {Γ : List Ty} : (σ : Ty) → Tm Γ σ
  | .nat => .zero
  | .arr _ b => .lam (errT b)

/-- Casts: the identity between equal types, the default value otherwise. -/
def castT {Γ : List Ty} (src dst : Ty) (t : Tm Γ src) : Tm Γ dst :=
  match h : C5.typeEqb src dst with
  | true => typeEqb_eq h ▸ t
  | false => errT dst

/-- The numeral `succᵏ zero`. -/
def numT {Γ : List Ty} : Nat → Tm Γ .nat
  | 0 => .zero
  | k + 1 => .succ (numT k)

def weaken {Γ : List Ty} {τ σ : Ty} (t : Tm Γ σ) : Tm (τ :: Γ) σ := rename (fun _ v => .there v) t

/-- A case distinction at any type, η-expanded down to `nat`. -/
def caseAt {Γ : List Ty} : (r : Ty) → Tm Γ .nat → (Nat → Tm Γ r) → Tm Γ r
  | .nat, n, g => .case n g
  | .arr _ β, n, g => .lam (caseAt β (weaken n) fun k => .app (weaken (g k)) (.var .here))

/-- `f (k-1) (… (f 0 a))`. -/
def iterT {Γ : List Ty} {r : Ty} (a : Tm Γ r) (f : Tm Γ (.arr .nat (.arr r r))) : Nat → Tm Γ r
  | 0 => a
  | k + 1 => .app (.app f (numT k)) (iterT a f k)

/-- Natural recursion as a case tree. -/
def recT {Γ : List Ty} (r : Ty) : Tm Γ (.arr r (.arr (.arr .nat (.arr r r)) (.arr .nat r))) :=
  .lam (.lam (.lam (caseAt r (.var .here) (iterT (.var (.there (.there .here))) (.var (.there .here))))))

/-! ## Their values -/

theorem eval_errT {Γ : List Ty} (e : Env Γ) : ∀ σ : Ty, eval (errT σ : Tm Γ σ) e = error σ
  | .nat => rfl
  | .arr _ b => by funext x; exact eval_errT (Env.cons x e) b

theorem eval_castT {Γ : List Ty} (src dst : Ty) (t : Tm Γ src) (e : Env Γ) :
    eval (castT src dst t) e = (castImpl src dst).1 (eval t e) := by
  unfold castT
  split
  · next h =>
      have he := typeEqb_eq h
      subst he
      rw [(castImpl_same src).1]
  · next h => rw [castImpl_ne h, eval_errT]

theorem eval_numT {Γ : List Ty} (e : Env Γ) : ∀ k, (eval (numT k : Tm Γ .nat) e : Nat) = k
  | 0 => rfl
  | k + 1 => congrArg Nat.succ (eval_numT e k)

theorem eval_weaken {Γ : List Ty} {τ σ : Ty} (t : Tm Γ σ) (x : den τ) (e : Env Γ) :
    eval (weaken (τ := τ) t) (Env.cons x e) = eval t e := by
  unfold weaken; rw [eval_rename]; rfl

theorem eval_caseAt {Γ : List Ty} : ∀ (r : Ty) (n : Tm Γ .nat) (g : Nat → Tm Γ r) (e : Env Γ),
    eval (caseAt r n g) e = eval (g (eval n e)) e
  | .nat, _, _, _ => rfl
  | .arr _ β, n, g, e => by
      funext x
      show eval (caseAt β (weaken n) _) (Env.cons x e) = _
      rw [eval_caseAt β]
      show eval (weaken (g (eval (weaken n) (Env.cons x e)))) (Env.cons x e) x = _
      rw [eval_weaken, eval_weaken]

theorem eval_iterT {Γ : List Ty} {r : Ty} (a : Tm Γ r) (f : Tm Γ (.arr .nat (.arr r r)))
    (e : Env Γ) : ∀ k, eval (iterT a f k) e = recursion (eval a e) (eval f e) k
  | 0 => rfl
  | k + 1 => by
      show eval f e (eval (numT k) e) (eval (iterT a f k) e) = _
      rw [eval_iterT a f e k, eval_numT]
      rfl

theorem eval_recT {Γ : List Ty} (r : Ty) (e : Env Γ) :
    eval (recT r : Tm Γ _) e = recursion := by
  funext a f n
  show eval (caseAt r _ _) _ = _
  rw [eval_caseAt]
  exact eval_iterT _ _ _ n

/-! ## The translation -/

/-- The type of a looked-up variable (`nat` if unbound). -/
def optTy : Option Ty → Ty
  | some a => a
  | none => .nat

/-- The result type of an application whose function has type `T`. -/
def codTy : Ty → Ty
  | .nat => .nat
  | .arr _ b => b

def trVarAux {Γ : List Ty} (x : Nat) : (o : Option Ty) → lookup Γ x = o → Tm Γ (optTy o)
  | some _, h => .var (varAt Γ _ (lookup_some h))
  | none, _ => .zero

def trApp {Γ : List Ty} : (T : Ty) → Tm Γ T → (U : Ty) → Tm Γ U → Tm Γ (codTy T)
  | .nat, _, _, _ => .zero
  | .arr a _, tt, U, uu => .app tt (castT U a uu)

/-- The translation of a raw term in an environment of types `Γ`. -/
def trI : (Γ : List Ty) → (w : Term) → Tm Γ (stype Γ w)
  | Γ, .var x => trVarAux x (lookup Γ x) rfl
  | Γ, .lam a b t => .lam (castT (stype (a :: Γ) t) b (trI (a :: Γ) t))
  | Γ, .app t u => trApp (stype Γ t) (trI Γ t) (stype Γ u) (trI Γ u)
  | _, .zero => .zero
  | _, .succ => .lam (.succ (.var .here))
  | _, .natRec r => recT r

/-! ## Correctness -/

/-- The environment of values, as an environment of the typed terms. -/
def envOf : (e : List Value) → Env (tys e)
  | [] => fun _ v => nomatch v
  | ⟨_, x⟩ :: e => Env.cons x (envOf e)

theorem nthError_envOf : ∀ (e : List Value) (i : Nat) {a : Ty} (h : nthError (tys e) i = some a),
    nthError e i = some ⟨a, envOf e a (varAt (tys e) i h)⟩
  | [], _, _, h => nomatch h
  | ⟨b, x⟩ :: e, 0, a, h => by
      cases h
      rfl
  | ⟨b, x⟩ :: e, i + 1, a, h => nthError_envOf e i h

theorem lookup_envOf (e : List Value) (x : Nat) {a : Ty} (h : lookup (tys e) x = some a) :
    lookup e x = some ⟨a, envOf e a (varAt (tys e) _ (lookup_some h))⟩ := by
  have hb : Nat.ble (tys e).length x = false := by
    cases hb : Nat.ble (tys e).length x with
    | false => rfl
    | true =>
        have : lookup (tys e) x = none := by
          show (match Nat.ble (tys e).length x with
            | true => none
            | false => nthError (tys e) ((tys e).length - (x + 1))) = none
          rw [hb]
        rw [this] at h; cases h
  show (match Nat.ble e.length x with
    | true => none
    | false => nthError e (e.length - (x + 1))) = _
  rw [show e.length = (tys e).length from (List.length_map _).symm, hb]
  exact nthError_envOf e _ (lookup_some h)

theorem eval_trVarAux (e : List Value) (x : Nat) : ∀ (o : Option Ty) (h : lookup (tys e) x = o),
    interp e (.var x) = (⟨optTy o, eval (trVarAux x o h) (envOf e)⟩ : Value)
  | some a, h => by
      show (match lookup e x with
        | some r => r
        | none => (⟨.nat, error .nat⟩ : Value)) = _
      rw [lookup_envOf e x h]
      rfl
  | none, h => by
      show (match lookup e x with
        | some r => r
        | none => (⟨.nat, error .nat⟩ : Value)) = _
      have : lookup e x = none := by
        rw [lookup_map] at h
        cases hl : lookup e x with
        | none => rfl
        | some v => rw [hl] at h; cases h
      rw [this]
      rfl

theorem eval_trApp {Γ : List Ty} (ρ : Env Γ) : ∀ (T : Ty) (tt : Tm Γ T) (U : Ty) (uu : Tm Γ U),
    (match (⟨T, eval tt ρ⟩ : Value), (⟨U, eval uu ρ⟩ : Value) with
      | ⟨.nat, _⟩, _ => (⟨.nat, error .nat⟩ : Value)
      | ⟨.arr a _, r₁⟩, ⟨_, r₂⟩ => ⟨_, r₁ (C5.cast a r₂)⟩) =
    ⟨codTy T, eval (trApp T tt U uu) ρ⟩
  | .nat, _, _, _ => rfl
  | .arr a _, tt, U, uu => by
      show (⟨_, eval tt ρ (C5.cast a (eval uu ρ))⟩ : Value) =
        ⟨_, eval tt ρ (eval (castT U a uu) ρ)⟩
      rw [eval_castT]
      rfl

/-- **The translation has Contender 5's value.** -/
theorem eval_trI : ∀ (w : Term) (e : List Value),
    interp e w = (⟨stype (tys e) w, eval (trI (tys e) w) (envOf e)⟩ : Value)
  | .var x, e => eval_trVarAux e x _ rfl
  | .lam a b t, e => by
      show (⟨.arr a b, fun x => C5.cast b (interp (⟨a, x⟩ :: e) t).2⟩ : Value) =
        ⟨.arr a b, fun x => eval (castT (stype (a :: tys e) t) b (trI (a :: tys e) t))
          (Env.cons x (envOf e))⟩
      refine congrArg (Sigma.mk _) (funext fun x => ?_)
      rw [eval_trI t (⟨a, x⟩ :: e), eval_castT]
      rfl
  | .app t u, e => by
      show (match interp e t, interp e u with
        | ⟨.nat, _⟩, _ => (⟨.nat, error .nat⟩ : Value)
        | ⟨.arr a _, r₁⟩, ⟨_, r₂⟩ => ⟨_, r₁ (C5.cast a r₂)⟩) = _
      rw [eval_trI t e, eval_trI u e]
      exact eval_trApp (envOf e) _ _ _ _
  | .zero, _ => rfl
  | .succ, _ => rfl
  | .natRec r, e => by
      show interp e (.natRec r) = ⟨_, eval (recT r) (envOf e)⟩
      rw [eval_recT]
      rfl

/-- A closed term of static type `nat`, as a closed infinitary program. -/
def progOf (w : Term) (hs : stype [] w = .nat) : Tm [] .nat := hs ▸ trI [] w

theorem value_cast (T : Ty) (tt : Tm [] T) (hs : T = .nat) :
    value (hs ▸ tt) = (match (⟨T, eval tt (envOf [])⟩ : Value) with
      | ⟨.nat, n⟩ => (n : Nat)
      | ⟨.arr _ _, _⟩ => 0) := by
  subst hs
  show eval tt env0 = eval tt (envOf [])
  congr 1

theorem value_progOf (w : Term) (hs : stype [] w = .nat) : value (progOf w hs) = C5.eval w := by
  unfold progOf C5.eval
  rw [eval_trI w []]
  exact value_cast _ _ hs

end BusyLean.Indep.Inf
