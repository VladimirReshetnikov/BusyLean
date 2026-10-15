import BusyLean.Independent.TFBSem
import BusyLean.Independent.SystemTLtLadder
import BusyLean.Independent.FwCheckV

/-!
# Rung 3 < rung 4: the Hardy hierarchy at `ψ_0(ε_{Ω_ω+1})` < the self-building ladder with universe levels

The ordinal rung is computed by one Fω program, `tfbProgramW`: the
translation of the `TT` shell `tfbShell = λθ. H_θ(H_θ(42))` applied to
`TFB.thetaW`, which computes the Takeuti–Feferman–Buchholz ordinal
`ψ_0(ε_{Ω_ω+1})` as a Brouwer tree (`TFBProg.lean`). The program has depth
`153`, the verified checker gives it type `nat` at fuel `5` (`check_tfbProgram`),
and it reduces to the Church numeral of `F3 (F3 42)` under any oracle
(`steps_rungProgram`, from `TFB.rel_thetaW`).

**Through the readers of rung 4.** Wrapped as `ΛX. λ rec x. tfbProgram`, the
program is a numeric reader of the ladder with universe levels, which ignores
its input tree (`readerProgramW`, depth `≤ 156`). Its type checks with
`FLV.infer` (`checkW_soundV`), it is enumerated (`mem_vctmsUpTo`), and its
value is `F3 (F3 42)` whatever the oracle and the tree (`readNat_readerProgram`):
after the two wrapper steps, System FT2's normal-order reduction of the
included program is System F's (`FT2.nf_embF`). So every `readMax` with a
budget of at least `156` exceeds the ordinal rung (`contender_3_lt_readMax`).
Every reflection step of rung 4 is a `readMax` (`F4_eq`), and `F4 42 ≥ 1067`.

The same program, as a ladder program of `ladderMax`, gives the comparison
through the ladder of universes as well (`contender_3_lt_ladderMax`).

The comparison is a simulation: impredicative Church encodings of Brouwer trees,
of Buchholz's trees of every level and of the trees of level `ω`, with
type-level evidence for induction over the levels, carry out the transfinite
recursion that defines the collapse and the hierarchy.
-/

namespace BusyLean.Indep

open BusyLean.FL
open BusyLean.Indep.FW
open BusyLean.Indep.TFB (natW treeW thetaW trTL rel_thetaW)
open BusyLean.Indep.Ladder (fvalue ladderUpTo ladderMax listMax readNat readMax vctmsUpTo)
open BusyLean.Ordinal (CTree Addr addrUpTo)

/-- The shell `λθ. H_θ(H_θ(42))`, in Fω. -/
def tfbShellW : FTm := trTL (fun _ => natW) (fun _ => natW) TT.tfbShell

/-- **The ordinal rung as one Fω program.** -/
def tfbProgramW : FTm := .app tfbShellW thetaW

theorem check_tfbProgram : checkW 5 [] [] tfbProgramW = some natW := by decide +kernel

theorem cdepth_tfbProgram : cdepthF tfbProgramW ≤ 153 := by decide +kernel

/-- The rung as a ladder program at level `m`. -/
def rungProgram (m : Nat) : CTm (Atom m) := embC tfbProgramW

theorem infer_rungProgram {m : Nat} (hm : 5 ≤ m) : infer m [] [] (rungProgram m) = some FL.Ty.nat :=
  infer_embC check_tfbProgram hm [] []

/-- The rung program reduces to the numeral of the ordinal rung, under any oracle. -/
theorem steps_rungProgram (g : Nat → Nat) (m : Nat) :
    F.Steps g (erase (rungProgram m)) (F.Tm.num (F3 (F3 42))) := by
  show F.Steps g (FL.erase (embC tfbProgramW : CTm (Atom m))) _
  rw [erase_embC]
  show F.Steps g (F.Tm.app (eraseF tfbShellW) (eraseF thetaW)) _
  rw [show eraseF tfbShellW = TT.utrT TT.tfbShell from TFB.eraseF_trTL _ _ _]
  have h := TT.rel_utrT0 (f := g) TT.tfbShell (eraseF thetaW) Buch.thetaTFB rel_thetaW
  rw [TT.eval_tfbShell] at h
  exact h

/-- Every ladder maximum with budget `≥ 153` exceeds the ordinal rung, whatever the oracle. -/
theorem contender_3_lt_ladderMax (g : Nat → Nat) {m : Nat} (hm : 153 ≤ m) :
    contender_3 < ladderMax g m := by
  have hmem : rungProgram m ∈ ladderUpTo m :=
    FW.mem_ctmsUpTo (Atom.all m) tfbProgramW (Nat.le_trans cdepth_tfbProgram hm)
  have hv := fvalue_eq (ℓ := m) (infer_rungProgram (by omega)) (steps_rungProgram g m)
  have hle := le_listMax (fvalue m g m) hmem
  rw [hv] at hle
  unfold contender_3 ladderMax
  generalize listMax (fvalue m g m) (ladderUpTo m) = L at hle ⊢
  generalize F3 (F3 42) = V at hle ⊢
  omega

/-! ## The ordinal rung as a reader program of the ladder with levels -/

/-- The recursor type of the readers, in Fω. -/
def recTyW : FTy :=
  .all .star (.arr (.tvar 0) (.arr (.arr (.tvar 0) (.tvar 0))
    (.arr (.arr (.arr natW (.tvar 0)) (.tvar 0)) (.arr (.tvar 1) (.tvar 0)))))

/-- The ordinal rung as a numeric reader that ignores its input tree:
`ΛX. λ rec x. tfbProgram`. -/
def readerProgramW : FTm := .tlam .star (.lam recTyW (.lam (.tvar 0) tfbProgramW))

theorem cdepth_readerProgram : cdepthF readerProgramW ≤ 156 := by
  have h := cdepth_tfbProgram
  have e : cdepthF readerProgramW =
      max 1 (max 11 (max 2 (cdepthF tfbProgramW) + 1) + 1) + 1 := rfl
  rw [e]
  generalize cdepthF tfbProgramW = D at h ⊢
  have h1 : max 2 D ≤ 153 := Nat.max_le.2 ⟨by omega, h⟩
  have h2 : max 11 (max 2 D + 1) ≤ 154 := Nat.max_le.2 ⟨by omega, by omega⟩
  have h3 : max 1 (max 11 (max 2 D + 1) + 1) ≤ 155 := Nat.max_le.2 ⟨by omega, by omega⟩
  omega

section Reader

variable {α : Type} [DecidableEq α] [AtomOrder α]

theorem inferV_lam {fuel : Nat} {Λ : List (FLV.Lvl α)} {Δ : List (FLV.Kind α)}
    {Γ : List (FLV.Ty α)} {A B : FLV.Ty α} {b : FLV.CTm α}
    (hk : FLV.inferKind Λ Δ A = some .star) (hb : FLV.infer fuel Λ Δ (A :: Γ) b = some B) :
    FLV.infer fuel Λ Δ Γ (.lam A b) = some (.arr A B) := by
  show (match FLV.inferKind Λ Δ A with
    | some .star => (FLV.infer fuel Λ Δ (A :: Γ) b).map (FLV.Ty.arr A)
    | _ => none) = _
  rw [hk, hb]
  rfl

theorem inferV_tlam {fuel : Nat} {Λ : List (FLV.Lvl α)} {Δ : List (FLV.Kind α)}
    {k : FLV.Kind α} {B : FLV.Ty α} {b : FLV.CTm α}
    (hb : FLV.infer fuel Λ (k :: Δ) [] b = some B) :
    FLV.infer fuel Λ Δ [] (.tlam k b) = some (.all k B) := by
  show (FLV.infer fuel Λ (k :: Δ) ([].map (FLV.Ty.tren Nat.succ)) b).map (FLV.Ty.all k) = _
  rw [show ([] : List (FLV.Ty α)).map (FLV.Ty.tren Nat.succ) = [] from rfl, hb]
  rfl

/-- The wrapped program is a numeric reader of the ladder with levels. -/
theorem infer_readerProgram {fuel : Nat} (hF : 5 ≤ fuel) :
    FLV.infer fuel [] [] [] (embCV readerProgramW : FLV.CTm α) = some FLV.natReaderTy := by
  have h := checkW_soundV (α := α) 5 tfbProgramW check_tfbProgram hF []
    [FLV.Kind.star] [FLV.Ty.tvar 0, FLV.recTy]
  have hk1 : FLV.inferKind [] [FLV.Kind.star] (FLV.recTy : FLV.Ty α) = some .star := rfl
  have hk2 : FLV.inferKind [] [FLV.Kind.star] (FLV.Ty.tvar 0 : FLV.Ty α) = some .star := rfl
  exact inferV_tlam (inferV_lam hk1 (inferV_lam hk2 h))

end Reader

/-- The value of a numeric reader program, from its type and the numeral its
normal form denotes. -/
theorem readNat_eq {g : Nat → Nat} {T : CTree} {fuel n : Nat} {p : FLV.CTm (Addr T)}
    (h : FLV.infer fuel [] [] [] p = some FLV.natReaderTy)
    (hv : ∀ hs : FT2.SN ⟨g, T⟩ (FLT2.applyNatReader (FLV.erase p)),
      FT2.decode (FT2.nf ⟨g, T⟩ ⟨_, hs⟩) = n) :
    readNat g T fuel p = n := by
  unfold readNat
  split
  · next A hA =>
      have e : A = FLV.natReaderTy := by rw [h] at hA; cases hA; rfl
      subst e
      rw [dite_eq_left rfl]
      exact hv _
  · next hA => rw [h] at hA; cases hA

/-- The two steps of a reader that ignores its arguments. -/
theorem nstep_reader1 (f : FT2.Orc) (E : FT2.Tm) :
    FT2.nstep f (FLT2.applyNatReader (.lam (.lam E))) =
      some (.app (.lam (FT2.Tm.subst (FT2.Tm.up (FT2.Tm.cons .trec .var)) E)) (.tsub [])) := rfl

theorem nstep_reader2 (f : FT2.Orc) (E : FT2.Tm) :
    FT2.nstep f (.app (.lam (FT2.Tm.subst (FT2.Tm.up (FT2.Tm.cons .trec .var)) E)) (.tsub [])) =
      some (FT2.Tm.subst (FT2.Tm.cons (.tsub []) .var)
        (FT2.Tm.subst (FT2.Tm.up (FT2.Tm.cons .trec .var)) E)) := rfl

theorem subst_reader {E : FT2.Tm} (hE : FT2.closedB 0 E = true) :
    FT2.Tm.subst (FT2.Tm.cons (.tsub []) .var)
      (FT2.Tm.subst (FT2.Tm.up (FT2.Tm.cons .trec .var)) E) = E := by
  rw [FT2.subst_closed E hE (fun i hi => absurd hi (Nat.not_lt_zero i)),
    FT2.subst_closed E hE (fun i hi => absurd hi (Nat.not_lt_zero i))]

theorem sn_of_reader {f : FT2.Orc} {E : FT2.Tm} (hE : FT2.closedB 0 E = true)
    (hs : FT2.SN f (FLT2.applyNatReader (.lam (.lam E)))) : FT2.SN f E := by
  have h := (hs.step (FT2.nstep_sound (nstep_reader1 f E))).step
    (FT2.nstep_sound (nstep_reader2 f E))
  rwa [subst_reader hE] at h

/-- A reader that ignores its arguments has the normal form of its body. -/
theorem nf_reader {f : FT2.Orc} {E : FT2.Tm} (hE : FT2.closedB 0 E = true)
    (hs : FT2.SN f (FLT2.applyNatReader (.lam (.lam E)))) (hE' : FT2.SN f E) :
    FT2.nf f ⟨_, hs⟩ = FT2.nf f ⟨E, hE'⟩ := by
  rw [FT2.nf_of_nstep f hs (nstep_reader1 f E), FT2.nf_of_nstep f _ (nstep_reader2 f E)]
  exact FT2.nf_congr f (subst_reader hE) _ _

/-- **The wrapped ordinal rung computes `F3 (F3 42)`**, for every oracle and tree. -/
theorem readNat_readerProgram (g : Nat → Nat) (T : CTree) {m : Nat} (hm : 5 ≤ m) :
    readNat g T m (embCV readerProgramW) = F3 (F3 42) := by
  refine readNat_eq (infer_readerProgram hm) fun hs => ?_
  have eE : FLV.erase (embCV readerProgramW : FLV.CTm (Addr T)) =
      .lam (.lam (FT2.embF (eraseF tfbProgramW))) := erase_embCV _
  have hE : FT2.closedB 0 (FT2.embF (eraseF tfbProgramW)) = true :=
    closedB_eraseF tfbProgramW check_tfbProgram
  have hs' : FT2.SN ⟨g, T⟩ (FLT2.applyNatReader (.lam (.lam (FT2.embF (eraseF tfbProgramW))))) :=
    eE ▸ hs
  rw [FT2.nf_congr _ (congrArg FLT2.applyNatReader eE) hs hs']
  have hE' := sn_of_reader hE hs'
  rw [nf_reader hE hs' hE']
  have hsn : F.SN g (eraseF tfbProgramW) := by
    have h := Ladder.sn_erase (f := g) m (infer_rungProgram hm)
    rwa [show FL.erase (rungProgram m) = eraseF tfbProgramW from erase_embC _] at h
  have hst : F.Steps g (eraseF tfbProgramW) (F.Tm.num (F3 (F3 42))) := by
    have h := steps_rungProgram g m
    rwa [show FL.erase (rungProgram m) = eraseF tfbProgramW from erase_embC _] at h
  rw [FT2.nf_embF ⟨g, T⟩ ⟨eraseF tfbProgramW, hsn⟩ hE', FT2.decode_embF]
  exact F.decode_nf_of_steps _ hst

/-- Every `readMax` with budget `≥ 156` exceeds the ordinal rung, whatever the
oracle and the tree: the wrapped program is one of its readers. -/
theorem contender_3_lt_readMax (g : Nat → Nat) (T : CTree) {m : Nat} (hm : 156 ≤ m) :
    contender_3 < readMax g T m := by
  have hmem : (embCV readerProgramW : FLV.CTm (Addr T)) ∈ vctmsUpTo (addrUpTo T m) m :=
    mem_vctmsUpTo _ readerProgramW (Nat.le_trans cdepth_readerProgram hm)
  have hle := le_listMax (readNat g T m) hmem
  rw [readNat_readerProgram g T (m := m) (by omega)] at hle
  have hR := Nat.le_trans hle (Nat.le_trans
    (Nat.le_max_right (listMax (fvalue m g m) (ladderUpTo m))
      (listMax (readNat g T m) (vctmsUpTo (addrUpTo T m) m)))
    (Nat.le_max_right (Ladder.oldMax m) _))
  unfold contender_3 readMax
  generalize max (Ladder.oldMax m) (max (listMax (fvalue m g m) (ladderUpTo m))
    (listMax (readNat g T m) (vctmsUpTo (addrUpTo T m) m))) = M at hR ⊢
  generalize F3 (F3 42) = V at hR ⊢
  omega

/-- **Rung 3 < rung 4**: the ordinal rung < the self-building ladder with universe
levels, through its reader programs. -/
theorem contender_3_lt_contender_4 : contender_3 < contender_4 := by
  have h42 := F4_42_ge
  have h := contender_3_lt_readMax (orc4 (F4 42)) (tree4 (F4 42)) (m := F4 42)
    (by generalize F4 42 = M at h42; omega)
  exact Nat.lt_of_lt_of_le h (Nat.le_of_eq (F4_eq (F4 42)).symm)

end BusyLean.Indep
