import BusyLean7.Enumeration

/-! Self-casts and the oracle-independent depth-11 comparison program. -/
namespace BusyLean7
open BigNumber (Ty Term WTree)

@[simp] theorem eqb_self (a : Ty) : BigNumber.eqb a a = true := by
  induction a with
  | nat => rfl
  | arr a b ia ib => simp [BigNumber.eqb, ia, ib]
  | wt a ia => simp [BigNumber.eqb, ia]

theorem wmap_identity {A : Type} (w : WTree A) :
    BigNumber.wmap (fun x : A => x) w = w := by
  induction w with
  | leaf => rfl
  | node f ih =>
      change WTree.node (fun x => BigNumber.wmap (fun y : A => y) (f x)) =
        WTree.node f
      exact congrArg WTree.node (funext ih)

@[simp] theorem wmap_identity_function {A : Type} :
    BigNumber.wmap (fun x : A => x) = (fun w : WTree A => w) :=
  funext wmap_identity

@[simp] theorem castPair_self (a : Ty) :
    BigNumber.castPair a a = ((fun x => x), (fun x => x)) := by
  induction a with
  | nat => rfl
  | arr a b ia ib => simp [BigNumber.castPair, ia, ib]
  | wt a ia => simp [BigNumber.castPair, ia]

@[simp] theorem castValue_self {a : Ty} (x : BigNumber.den a) :
    BigNumber.castValue a x = x := by
  simp [BigNumber.castValue]

theorem interpret_app_exact {env : BigNumber.Env} {a b : Ty}
    {t u : Term} {f : BigNumber.den a → BigNumber.den b} {x : BigNumber.den a}
    (ht : BigNumber.interpret env t = ⟨.arr a b, f⟩)
    (hu : BigNumber.interpret env u = ⟨a, x⟩) :
    BigNumber.interpret env (.app t u) = ⟨b, f x⟩ := by
  simp only [BigNumber.interpret, ht, hu, castValue_self]

theorem interpret_input (M : Model) (fs : Family) (n : Nat) :
    BigNumber.interpret (modelEnv M fs n) (.var 1) = ⟨.nat, n⟩ := rfl

theorem interpret_seed (M : Model) (fs : Family) (n : Nat) :
    BigNumber.interpret (modelEnv M fs n) (.var 2) =
      ⟨familyTy, BusyLean.p5Family⟩ := rfl

theorem interpret_forests (M : Model) (fs : Family) (n : Nat) :
    BigNumber.interpret (modelEnv M fs n) (.var 4) =
      ⟨.arr .nat stageTy, M.lowerStage⟩ := rfl

theorem interpret_trees (M : Model) (fs : Family) (n : Nat) :
    BigNumber.interpret (modelEnv M fs n) (.var 5) =
      ⟨.arr .nat treeTy, M.lowerTree⟩ := rfl

theorem interpret_theta (M : Model) (fs : Family) (n : Nat) :
    BigNumber.interpret (modelEnv M fs n) (.var 6) =
      ⟨numFnTy, theta⟩ := rfl

/-- This calculation does not inspect the oracle fs, nor assume it monotone. -/
theorem interpret_call (M : Model) (fs : Family) (n k : Nat) (s : Term)
    (hs : BigNumber.interpret (modelEnv M fs n) s = ⟨.nat, k⟩) :
    BigNumber.interpret (modelEnv M fs n) (callAt s) =
      ⟨.nat, M.lowerStage k BusyLean.p5Family (M.lowerTree k) n⟩ := by
  have h0 := interpret_app_exact (interpret_forests M fs n) hs
  have h1 := interpret_app_exact h0 (interpret_seed M fs n)
  have ht := interpret_app_exact (interpret_trees M fs n) hs
  have h2 := interpret_app_exact h1 ht
  exact interpret_app_exact h2 (interpret_input M fs n)

theorem interpret_amplified (M : Model) (fs : Family) (n k : Nat) (s : Term)
    (hs : BigNumber.interpret (modelEnv M fs n) s = ⟨.nat, k⟩) :
    BigNumber.interpret (modelEnv M fs n) (amplifiedCall s) =
      ⟨.nat, theta (M.lowerStage k BusyLean.p5Family (M.lowerTree k) n)⟩ :=
  interpret_app_exact (interpret_theta M fs n) (interpret_call M fs n k s hs)

theorem eval_amplified_zero (M : Model) (fs : Family) (n : Nat) :
    eval M fs n (amplifiedCall .zero) =
      theta (M.lowerStage 0 BusyLean.p5Family (M.lowerTree 0) n) :=
  congrArg score (interpret_amplified M fs n 0 .zero rfl)

theorem eval_amplified_input (M : Model) (fs : Family) (n : Nat) :
    eval M fs n (amplifiedCall (.var 1)) =
      theta (M.lowerStage n BusyLean.p5Family (M.lowerTree n) n) :=
  congrArg score (interpret_amplified M fs n n (.var 1) (interpret_input M fs n))

end BusyLean7
