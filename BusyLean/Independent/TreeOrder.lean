import BusyLean.Independent.EpsilonHardy

/-!
# Hardy functions and a structural order on Brouwer trees

Facts about `Eps.hardy` that hold for **every** tree (thanks to the maximum at
limits): monotonicity, `H_a(y) ≥ y`, strictness, and the composition law
`H_{a+b} = H_a ∘ H_b`.

`Le n a b` (written `a ⊑ₙ b`) is a structural simulation order: `b` is
obtained from `a` by enlarging subtrees, and every limit step that picks a
single element of a fundamental sequence uses an index `≤ n`. It is sound for
the Hardy functions at every argument `≥ n`, and it is preserved by addition
and by `ω`-exponentiation.
-/

namespace BusyLean.Indep.Eps

open BTree

/-! ## Maxima -/

theorem le_maxUpTo (g : Nat → Nat) : ∀ {i y : Nat}, i ≤ y → g i ≤ maxUpTo g y
  | i, 0, h => by rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | i, y + 1, h => by
      show g i ≤ max (maxUpTo g y) (g (y + 1))
      by_cases e : i = y + 1
      · subst e; exact Nat.le_max_right _ _
      · exact Nat.le_trans (le_maxUpTo g (by omega)) (Nat.le_max_left _ _)

theorem maxUpTo_le {g : Nat → Nat} {B : Nat} : ∀ {y : Nat}, (∀ i, i ≤ y → g i ≤ B) →
    maxUpTo g y ≤ B
  | 0, h => h 0 (Nat.le_refl 0)
  | y + 1, h => Nat.max_le.mpr ⟨maxUpTo_le fun i hi => h i (by omega), h _ (Nat.le_refl _)⟩

theorem maxUpTo_mono {g g' : Nat → Nat} {y y' : Nat} (hy : y ≤ y')
    (hg : ∀ i, i ≤ y → g i ≤ g' i) : maxUpTo g y ≤ maxUpTo g' y' :=
  maxUpTo_le fun i hi => Nat.le_trans (hg i hi) (le_maxUpTo g' (Nat.le_trans hi hy))

theorem maxUpTo_comp {h : Nat → Nat} (hm : ∀ {a b}, a ≤ b → h a ≤ h b) (g : Nat → Nat) :
    ∀ y, maxUpTo (fun i => h (g i)) y = h (maxUpTo g y)
  | 0 => rfl
  | y + 1 => by
      show max (maxUpTo (fun i => h (g i)) y) (h (g (y + 1))) = h (max (maxUpTo g y) (g (y + 1)))
      rw [maxUpTo_comp hm g y]
      rcases Nat.le_total (maxUpTo g y) (g (y + 1)) with e | e
      · rw [Nat.max_eq_right e, Nat.max_eq_right (hm e)]
      · rw [Nat.max_eq_left e, Nat.max_eq_left (hm e)]

/-! ## Hardy functions -/

theorem hardy_mono : ∀ (a : BTree) {y y' : Nat}, y ≤ y' → hardy a y ≤ hardy a y'
  | .zero, _, _, h => h
  | .succ a, _, _, h => hardy_mono a (Nat.succ_le_succ h)
  | .lim f, _, _, h => maxUpTo_mono h fun i _ => hardy_mono (f i) h

theorem le_hardy : ∀ (a : BTree) (y : Nat), y ≤ hardy a y
  | .zero, _ => Nat.le_refl _
  | .succ a, y => Nat.le_trans (Nat.le_succ y) (le_hardy a (y + 1))
  | .lim f, y => Nat.le_trans (le_hardy (f 0) y) (le_maxUpTo (fun i => hardy (f i) y) (Nat.zero_le y))

theorem hardy_lt_succ : ∀ (a : BTree) (y : Nat), hardy a y + 1 ≤ hardy a (y + 1)
  | .zero, _ => Nat.le_refl _
  | .succ a, y => hardy_lt_succ a (y + 1)
  | .lim f, y => by
      show maxUpTo (fun i => hardy (f i) y) y + 1 ≤ maxUpTo (fun i => hardy (f i) (y + 1)) (y + 1)
      have h : maxUpTo (fun i => hardy (f i) y) y ≤ maxUpTo (fun i => hardy (f i) (y + 1) - 1) y :=
        maxUpTo_mono (Nat.le_refl y) fun i _ => by have := hardy_lt_succ (f i) y; omega
      have h2 : maxUpTo (fun i => hardy (f i) (y + 1) - 1) y + 1 ≤
          maxUpTo (fun i => hardy (f i) (y + 1)) (y + 1) := by
        have := maxUpTo_le (g := fun i => hardy (f i) (y + 1) - 1) (y := y)
          (B := maxUpTo (fun i => hardy (f i) (y + 1)) (y + 1) - 1) fun i hi => by
            have := le_maxUpTo (fun i => hardy (f i) (y + 1)) (i := i) (y := y + 1) (by omega)
            omega
        have hpos : 1 ≤ maxUpTo (fun i => hardy (f i) (y + 1)) (y + 1) :=
          Nat.le_trans (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le y)) (le_hardy (f 0) (y + 1)))
            (le_maxUpTo (fun i => hardy (f i) (y + 1)) (Nat.zero_le _))
        omega
      omega

theorem hardy_add (a : BTree) : ∀ (b : BTree) (y : Nat), hardy (add a b) y = hardy a (hardy b y)
  | .zero, _ => rfl
  | .succ b, y => hardy_add a b (y + 1)
  | .lim f, y => by
      show maxUpTo (fun i => hardy (add a (f i)) y) y = hardy a (maxUpTo (fun i => hardy (f i) y) y)
      rw [← maxUpTo_comp (hardy_mono a)]
      congr 1
      funext i
      exact hardy_add a (f i) y

/-! ## The structural order -/

/-- `Le n a b`: `a ⊑ₙ b`. -/
inductive Le (n : Nat) : BTree → BTree → Prop where
  | zero (b : BTree) : Le n .zero b
  | succ {a b : BTree} : Le n a b → Le n (.succ a) (.succ b)
  | succR {a b : BTree} : Le n a b → Le n a (.succ b)
  | limL {f : Nat → BTree} {b : BTree} : (∀ i, Le n (f i) b) → Le n (.lim f) b
  | limR {a : BTree} {g : Nat → BTree} (i : Nat) : i ≤ n → Le n a (g i) → Le n a (.lim g)
  | lim {f g : Nat → BTree} : (∀ i, Le n (f i) (g i)) → Le n (.lim f) (.lim g)

theorem Le.hardy_le {n : Nat} {a b : BTree} (h : Le n a b) : ∀ {y : Nat}, n ≤ y → hardy a y ≤ hardy b y := by
  induction h with
  | zero b => intro y _; exact le_hardy b y
  | succ _ ih => intro y hy; exact ih (Nat.le_succ_of_le hy)
  | @succR a b _ ih =>
      intro y hy; exact Nat.le_trans (ih hy) (hardy_mono b (Nat.le_succ y))
  | limL _ ih => intro y hy; exact maxUpTo_le fun i _ => ih i hy
  | @limR a g i hi _ ih =>
      intro y hy
      exact Nat.le_trans (ih hy) (le_maxUpTo (fun j => hardy (g j) y) (Nat.le_trans hi hy))
  | lim _ ih => intro y hy; exact maxUpTo_mono (Nat.le_refl y) fun i _ => ih i hy

theorem Le.refl (n : Nat) : ∀ a : BTree, Le n a a
  | .zero => .zero _
  | .succ a => .succ (Le.refl n a)
  | .lim f => .lim fun i => Le.refl n (f i)

theorem Le.mono {n m : Nat} (hnm : n ≤ m) {a b : BTree} (h : Le n a b) : Le m a b := by
  induction h with
  | zero b => exact .zero b
  | succ _ ih => exact .succ ih
  | succR _ ih => exact .succR ih
  | limL _ ih => exact .limL ih
  | limR i hi _ ih => exact .limR i (Nat.le_trans hi hnm) ih
  | lim _ ih => exact .lim ih

/-- Inversion: what lies below a successor lies below its predecessor's successor. -/
theorem Le.of_succ_left {n : Nat} {a b : BTree} (h : Le n (.succ a) b) : Le n a b := by
  generalize e : BTree.succ a = s at h
  induction h generalizing a with
  | zero => cases e
  | succ h _ => cases e; exact .succR h
  | succR _ ih => exact .succR (ih e)
  | limL => cases e
  | limR i hi _ ih => exact .limR i hi (ih e)
  | lim => cases e

/-- What lies below `lim g` lies below its `i`-th element's upper bounds. -/
theorem Le.of_lim_left {n : Nat} {g : Nat → BTree} {c : BTree} (h : Le n (.lim g) c) (i : Nat) :
    ∀ {a : BTree}, (∀ c', Le n (g i) c' → Le n a c') → i ≤ n → Le n a c := by
  generalize e : BTree.lim g = l at h
  induction h with
  | zero => cases e
  | succ => cases e
  | succR _ ih => intro a ha hi; exact .succR (ih e ha hi)
  | limL hall => cases e; intro a ha _; exact ha _ (hall i)
  | limR k hk _ ih => intro a ha hi; exact .limR k hk (ih e ha hi)
  | @lim f' h' hall =>
      cases e
      intro a ha hi
      exact .limR i hi (ha _ (hall i))

theorem Le.trans {n : Nat} {a b c : BTree} (hab : Le n a b) (hbc : Le n b c) : Le n a c := by
  induction hab generalizing c with
  | zero => exact .zero c
  | limL _ ih => exact .limL fun j => ih j hbc
  | succR _ ih => exact ih hbc.of_succ_left
  | @succ a b _ ih =>
      generalize e : BTree.succ b = s at hbc
      induction hbc with
      | zero => cases e
      | succ h => cases e; exact .succ (ih h)
      | succR _ ih' => exact .succR (ih' e)
      | limL => cases e
      | limR k hk _ ih' => exact .limR k hk (ih' e)
      | lim => cases e
  | @limR a g i hi _ ih => exact hbc.of_lim_left i (fun c' h => ih h) hi
  | @lim f g _ ih =>
      generalize e : BTree.lim g = l at hbc
      induction hbc with
      | zero => cases e
      | succ => cases e
      | succR _ ih' => exact .succR (ih' e)
      | limL hall => cases e; exact .limL fun j => ih j (hall j)
      | limR k hk _ ih' => exact .limR k hk (ih' e)
      | lim hall => cases e; exact .lim fun j => ih j (hall j)

/-! ## Arithmetic is monotone -/

theorem le_add_right {n : Nat} (a : BTree) : ∀ b : BTree, Le n a (add a b)
  | .zero => Le.refl n a
  | .succ b => .succR (le_add_right a b)
  | .lim f => .limR 0 (Nat.zero_le n) (le_add_right a (f 0))

theorem le_add_left {n : Nat} (a : BTree) : ∀ b : BTree, Le n b (add a b)
  | .zero => .zero a
  | .succ b => .succ (le_add_left a b)
  | .lim f => .lim fun i => le_add_left a (f i)

theorem add_mono_right {n : Nat} (a : BTree) {b b' : BTree} (h : Le n b b') :
    Le n (add a b) (add a b') := by
  induction h with
  | zero b' => exact le_add_right a b'
  | succ _ ih => exact .succ ih
  | succR _ ih => exact .succR ih
  | limL _ ih => exact .limL ih
  | limR i hi _ ih => exact .limR i hi ih
  | lim _ ih => exact .lim ih

theorem add_mono_left {n : Nat} {a a' : BTree} (h : Le n a a') : ∀ b : BTree,
    Le n (add a b) (add a' b)
  | .zero => h
  | .succ b => .succ (add_mono_left h b)
  | .lim f => .lim fun i => add_mono_left h (f i)

theorem add_mono {n : Nat} {a a' b b' : BTree} (ha : Le n a a') (hb : Le n b b') :
    Le n (add a b) (add a' b') :=
  (add_mono_left ha b).trans (add_mono_right a' hb)

theorem mulNat_mono {n : Nat} {a a' : BTree} (h : Le n a a') : ∀ i, Le n (mulNat a i) (mulNat a' i)
  | 0 => Le.refl n _
  | i + 1 => add_mono (mulNat_mono h i) h

theorem one_le_opow {n : Nat} (hn : 1 ≤ n) : ∀ b : BTree, Le n (.succ .zero) (opow b)
  | .zero => Le.refl n _
  | .succ b => .limR 1 hn ((one_le_opow hn b).trans (le_add_left _ _))
  | .lim f => .limR 0 (Nat.zero_le n) (one_le_opow hn (f 0))

theorem opow_mono {n : Nat} (hn : 1 ≤ n) {a b : BTree} (h : Le n a b) : Le n (opow a) (opow b) := by
  induction h with
  | zero b => exact one_le_opow hn b
  | succ _ ih => exact .lim fun i => mulNat_mono ih i
  | succR _ ih => exact .limR 1 hn (ih.trans (le_add_left _ _))
  | limL _ ih => exact .limL ih
  | limR i hi _ ih => exact .limR i hi ih
  | lim _ ih => exact .lim ih

/-! ## Joins and the key inequalities -/

/-- An upper bound of two trees: the limit of `a, b, b, …`. -/
def join (a b : BTree) : BTree := .lim fun i => if i = 0 then a else b

theorem le_join_left {n : Nat} (a b : BTree) : Le n a (join a b) :=
  .limR 0 (Nat.zero_le n) (Le.refl n a)

theorem le_join_right {n : Nat} (hn : 1 ≤ n) (a b : BTree) : Le n b (join a b) :=
  .limR 1 hn (Le.refl n b)

theorem join_le {n : Nat} {a b c : BTree} (ha : Le n a c) (hb : Le n b c) : Le n (join a b) c :=
  .limL fun i => by
    by_cases e : i = 0
    · simp only [e, ite_true]; exact ha
    · simp only [e, ite_false]; exact hb

theorem join_mono {n : Nat} {a a' b b' : BTree} (ha : Le n a a') (hb : Le n b b') :
    Le n (join a b) (join a' b') :=
  .lim fun i => by
    by_cases e : i = 0
    · simp only [e, ite_true]; exact ha
    · simp only [e, ite_false]; exact hb

/-- `ω^a + ω^a ⊑ ω^{a+1}`. -/
theorem opow_add_self_le {n : Nat} (hn : 2 ≤ n) (a : BTree) :
    Le n (add (opow a) (opow a)) (opow (.succ a)) :=
  .limR 2 hn (add_mono_left (le_add_left .zero (opow a)) (opow a))

theorem succ_le_add_self {n : Nat} {x : BTree} (h : Le n (.succ .zero) x) :
    Le n (.succ x) (add x x) :=
  add_mono_right x h

/-- `ω^a + ω^b ⊑ ω^{(a ∨ b) + 1}`. -/
theorem opow_add_opow_le {n : Nat} (hn : 2 ≤ n) (a b : BTree) :
    Le n (add (opow a) (opow b)) (opow (.succ (join a b))) :=
  (add_mono (opow_mono (by omega) (le_join_left a b))
    (opow_mono (by omega) (le_join_right (by omega) a b))).trans (opow_add_self_le hn _)

/-- `(ω^a) + 1 ⊑ ω^{a+1}`. -/
theorem succ_opow_le {n : Nat} (hn : 2 ≤ n) (a : BTree) :
    Le n (.succ (opow a)) (opow (.succ a)) :=
  (succ_le_add_self (one_le_opow (by omega) a)).trans (opow_add_self_le hn a)

end BusyLean.Indep.Eps
