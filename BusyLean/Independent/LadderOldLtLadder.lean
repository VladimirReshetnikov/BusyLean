import BusyLean.Independent.Ladder

/-!
# The previous rung 4 is smaller than rung 4

Rung 4 incorporates its previous version (`LadderOld.lean`, the self-building
transfinite ladder of `SystemFLT`): every value `readMax g T n` of the current
rung exceeds `oldMax n`, the running maximum of `LadderOld.F4` up to `n`. So
`F4 n > LadderOld.F4 k` for every `k ≤ n`, and

  `LadderOld.contender_4 = LadderOld.F4 (LadderOld.F4 42)`
  `  ≤ oldMax (F4 42) < F4 (F4 42) = contender_4`,

because `LadderOld.F4 42 ≤ oldMax 42 < F4 42`. The previous version is then
dropped from the hierarchy: rung 4 is the ladder with universe levels.
-/

namespace BusyLean.Indep

open Ladder (listMax natsUpTo oldMax readMax)

theorem le_listMax_of_mem {A : Type} (score : A → Nat) {x : A} :
    ∀ {l : List A}, x ∈ l → score x ≤ listMax score l
  | _ :: _, .head _ => Nat.le_max_left _ _
  | _ :: _, .tail _ h => Nat.le_trans (le_listMax_of_mem score h) (Nat.le_max_right _ _)

theorem mem_natsUpTo_of_lt : ∀ {m n : Nat}, n < m → n ∈ natsUpTo m
  | m + 1, n, h => by
      by_cases e : n = m
      · subst e; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_natsUpTo_of_lt (by omega))

/-- The previous rung's function, at any `k ≤ n`, is at most `oldMax n`. -/
theorem F4old_le_oldMax {k n : Nat} (h : k ≤ n) : LadderOld.F4 k ≤ oldMax n :=
  le_listMax_of_mem LadderOld.F4 (mem_natsUpTo_of_lt (Nat.lt_succ_of_le h))

/-- Every value of rung 4 exceeds the running maximum of the previous rung 4. -/
theorem oldMax_lt_F4 (n : Nat) : oldMax n < F4 n :=
  Ladder.oldMax_lt_readMax _ _ n

/-- **The previous rung 4 < rung 4.** -/
theorem contender_4_old_lt_contender_4 : LadderOld.contender_4 < contender_4 := by
  show LadderOld.F4 (LadderOld.F4 42) < F4 (F4 42)
  have h42 : LadderOld.F4 42 ≤ F4 42 :=
    Nat.le_of_lt (Nat.lt_of_le_of_lt (F4old_le_oldMax (Nat.le_refl 42)) (oldMax_lt_F4 42))
  exact Nat.lt_of_le_of_lt (F4old_le_oldMax h42) (oldMax_lt_F4 (F4 42))

end BusyLean.Indep
