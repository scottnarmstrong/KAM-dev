/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAL1Q

/-!
# The rational mirror of an isoenergetic run with the ℓ¹ entry (package C6L1)

Stage `0` is the entry (`V2/RouteAL1Q.lean`), every later stage C6's `StepQ`:

* `stCE`, `stRate`, `stCD`, `stCp`: the constants of stage `s`;
* `xL1`: the normalised errors, `x_{s+1} = 2^{4τ} C_{E,s} x_s²`;
* `okL1`: (J0)–(J3) of `KAM.Iso.Sharp2.L1.routeAOkIL1` as one Boolean, with `ei ≥ 0.3679`;
* `okL1_sound`: its soundness; the conditions are downward closed and the errors and the cap sums
  are monotone in the constants, so the bounds `le_*` of the entry suffice;
* `c2L1`, `c3L1`, `c2_le`, `c3_le`: upper bounds of `c2IL1`, `c3IL1`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.L1

open KAM.Sharp2.RouteA KAM.Iso.Sharp2.RouteA KAM.Sharp.Engine KAM.Sharp2.L1
open KAM.Iso.Sharp2.L1 (stageIL1 xIL1 routeAOkIL1 entryStageIA entryStageIA_rate_nonneg c2IL1
  c3IL1)
open KAM.Sharp2.Examples (EntryQ)

variable (Q : NumQ) (E : EntryQ)

/-- The error constant of stage `s` (the entry at `s = 0`). -/
def stCE (s : ℕ) : ℚ := if s = 0 then eCE (Q.inp 0) E else (Q.inp s).CE

/-- The rates of stage `s`. -/
def stRate (s : ℕ) (i : Fin 9) : ℚ := if s = 0 then erate (Q.inp 0) E i else (Q.inp s).rateQ i

/-- The closeness constant of stage `s`. -/
def stCD (s : ℕ) : ℚ := if s = 0 then eCDK (Q.inp 0) E else (Q.inp s).CDK

/-- The frequency constant of stage `s`. -/
def stCp (s : ℕ) : ℚ := if s = 0 then eCDw (Q.inp 0) E else (Q.inp s).CDw

/-- `x₀ = X⋆`, `x_{s+1} = 2^{4τ} C_{E,s} x_s²`, with the entry at `s = 0`. -/
def xL1 (Xs : ℚ) : ℕ → ℚ
  | 0 => Xs
  | s + 1 => 2 ^ (2 * (2 * Q.τ)) * stCE Q E s * xL1 Xs s ^ 2

/-- (J0)–(J3) with the ℓ¹ entry, as one Boolean. -/
def okL1 (σ m₀ : Fin 9 → ℚ) (Xs : ℚ) : Bool :=
  decide (0 ≤ Xs) && decide (1 ≤ Q.kp) && E.wfB && decide (3679 / 10000 ≤ E.ei) &&
    econd (Q.inp 0) E Xs &&
    (List.range Q.kp).all (fun s => decide (s = 0) || (Q.inp s).condB (xL1 Q E Xs s)) &&
    (Q.inp Q.kp).condB (xL1 Q E Xs Q.kp) &&
    decide (2 ^ (2 * (2 * Q.τ)) * (Q.inp Q.kp).CE * xL1 Q E Xs Q.kp ≤ 1) &&
    (List.finRange 9).all fun i =>
      decide (m₀ i + Q.sumQ Q.γb (xL1 Q E Xs) (fun s => stRate Q E s i) (2 * Q.τ - jI i) ≤ σ i)

/-- The rational upper bound of `c2IL1`. -/
def c2L1 (Xs : ℚ) : ℚ :=
  Q.ρ ^ (2 * Q.τ) * Q.sumQ 1 (xL1 Q E Xs) (stCD Q E) (2 * Q.τ) / (Xs * Q.δ0 ^ (4 * Q.τ))

/-- The rational upper bound of `c3IL1`. -/
def c3L1 (Xs : ℚ) : ℚ :=
  Q.ρ ^ (2 * Q.τ) * Q.sumQ 1 (xL1 Q E Xs) (stCp Q E) (2 * Q.τ) / (Xs * Q.δ0 ^ (4 * Q.τ))

variable {Q E}

theorem pos_inp (hQ : Q.toNum.Wf) (s : ℕ) : (Q.inp s).toStep.Pos := by
  rw [NumQ.toStep_inp]; exact hQ.pos s

/-- The real stage constants against their mirrors. -/
theorem stage_bounds (hQ : Q.toNum.Wf) (hτ : 1 ≤ Q.τ) (hE : E.toA.Wf)
    (hei : Ent.einv ≤ (E.ei : ℝ)) (s : ℕ) :
    (0 ≤ (stageIL1 Q.toNum E.toA s).CE ∧ (stageIL1 Q.toNum E.toA s).CE ≤ (stCE Q E s : ℝ)) ∧
    (∀ i, 0 ≤ (stageIL1 Q.toNum E.toA s).rate i ∧
      (stageIL1 Q.toNum E.toA s).rate i ≤ (stRate Q E s i : ℝ)) ∧
    (stageIL1 Q.toNum E.toA s).CD = (stCD Q E s : ℝ) ∧
    (stageIL1 Q.toNum E.toA s).Cp = (stCp Q E s : ℝ) := by
  have hp0 := pos_inp hQ 0
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    have hst : stageIL1 Q.toNum E.toA 0 = entryStageIA (Q.inp 0).toStep E.toA := by
      simp [stageIL1, NumQ.toStep_inp]
    have hk := Ent.nonneg hp0 hE
    rw [hst]
    refine ⟨⟨?_, ?_⟩, fun i => ⟨entryStageIA_rate_nonneg hp0 hE i, ?_⟩, ?_, ?_⟩
    · simp only [entryStageIA, Ent.CE_eq]; exact hk.CE
    · simp only [entryStageIA, Ent.CE_eq, stCE, ite_true]; exact le_CE hp0 hE hei
    · simp only [stRate, ite_true]; exact le_erate hp0 hE hei i
    · simp only [entryStageIA, Ent.CDK_eq, stCD, ite_true]; exact ecast_CDK _ _
    · simp only [entryStageIA, Ent.CDw_eq, stCp, ite_true]; exact ecast_CDw _ _
  · have hs0 : s ≠ 0 := hs.ne'
    have hst : stageIL1 Q.toNum E.toA s = stageI Q.toNum s := by simp [stageIL1, hs0]
    rw [hst]
    refine ⟨⟨(hQ.pos s).CE, ?_⟩, fun i => ⟨rateI_nonneg (hQ.pos s) i, ?_⟩, ?_, ?_⟩
    · show (Q.toNum.inp s).CE ≤ _
      simp only [stCE, hs0, ite_false]
      rw [NumQ.cast_CE hτ]
    · simp only [stRate, hs0, ite_false]
      rw [NumQ.cast_rate_at]
    · show (Q.toNum.inp s).CDK = _
      simp only [stCD, hs0, ite_false]
      rw [← NumQ.toStep_inp, StepQ.cast_CDK]
    · show (Q.toNum.inp s).CDw = _
      simp only [stCp, hs0, ite_false]
      rw [← NumQ.toStep_inp, StepQ.cast_CDw]

theorem four_rpow (τ : ℕ) : (2 : ℝ) ^ (2 * (2 * (τ : ℝ))) = ((2 ^ (2 * (2 * τ)) : ℚ) : ℝ) := by
  rw [show (2 * (2 * (τ : ℝ))) = ((2 * (2 * τ) : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  push_cast; rfl

/-- The real errors are bounded by their mirrors. -/
theorem x_bounds (hQ : Q.toNum.Wf) (hτ : 1 ≤ Q.τ) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ))
    {Xs : ℚ} (hX : 0 ≤ Xs) (s : ℕ) :
    0 ≤ xIL1 Q.toNum E.toA (Xs : ℝ) s ∧ xIL1 Q.toNum E.toA (Xs : ℝ) s ≤ (xL1 Q E Xs s : ℝ) := by
  induction s with
  | zero =>
    refine ⟨?_, ?_⟩
    · show (0 : ℝ) ≤ (Xs : ℝ)
      exact_mod_cast hX
    · show (Xs : ℝ) ≤ ((xL1 Q E Xs 0 : ℚ) : ℝ)
      simp [xL1]
  | succ s ih =>
    obtain ⟨⟨hc0, hc⟩, -, -⟩ := stage_bounds hQ hτ hE hei s
    have e1 : xIL1 Q.toNum E.toA (Xs : ℝ) (s + 1) = (2 : ℝ) ^ (2 * (2 * (Q.τ : ℝ))) *
        (stageIL1 Q.toNum E.toA s).CE * xIL1 Q.toNum E.toA (Xs : ℝ) s ^ 2 := rfl
    rw [e1, four_rpow]
    have e2 : ((xL1 Q E Xs (s + 1) : ℚ) : ℝ) =
        ((2 ^ (2 * (2 * Q.τ)) : ℚ) : ℝ) * (stCE Q E s : ℝ) * (xL1 Q E Xs s : ℝ) ^ 2 := by
      simp [xL1]
    rw [e2]
    have h2 : (0 : ℝ) ≤ ((2 ^ (2 * (2 * Q.τ)) : ℚ) : ℝ) := by positivity
    refine ⟨by have := ih.1; positivity, ?_⟩
    have h1 : (stageIL1 Q.toNum E.toA s).CE * xIL1 Q.toNum E.toA (Xs : ℝ) s ^ 2 ≤
        (stCE Q E s : ℝ) * (xL1 Q E Xs s : ℝ) ^ 2 :=
      mul_le_mul hc (pow_le_pow_left₀ ih.1 ih.2 2) (by positivity) (hc0.trans hc)
    calc ((2 ^ (2 * (2 * Q.τ)) : ℚ) : ℝ) * (stageIL1 Q.toNum E.toA s).CE *
          xIL1 Q.toNum E.toA (Xs : ℝ) s ^ 2
        = ((2 ^ (2 * (2 * Q.τ)) : ℚ) : ℝ) * ((stageIL1 Q.toNum E.toA s).CE *
          xIL1 Q.toNum E.toA (Xs : ℝ) s ^ 2) := by ring
      _ ≤ ((2 ^ (2 * (2 * Q.τ)) : ℚ) : ℝ) * ((stCE Q E s : ℝ) * (xL1 Q E Xs s : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = _ := by ring

/-- The sums of (J3) and of the closeness estimates, against their mirrors. -/
theorem sumA_le (hQ : Q.toNum.Wf) (hτ : 1 ≤ Q.τ) (hE : E.toA.Wf)
    (hei : Ent.einv ≤ (E.ei : ℝ)) {Xs : ℚ} (hX : 0 ≤ Xs) (γ : ℚ) {c' : ℕ → ℝ} {c : ℕ → ℚ}
    (hc : ∀ t, 0 ≤ c' t ∧ c' t ≤ (c t : ℝ)) {b : ℝ} {e : ℕ}
    (hb : 2 * (2 * (Q.τ : ℝ)) - b = e) :
    sumA (2 * (Q.τ : ℝ)) 3 Q.ρ Q.ρinf γ (xIL1 Q.toNum E.toA (Xs : ℝ)) c' b Q.kp ≤
      (Q.sumQ γ (xL1 Q E Xs) c e : ℝ) := by
  have hd : ∀ t, 0 ≤ deltaSeq 3 (Q.ρ : ℝ) Q.ρinf t := fun t => (hQ.δ_pos t).le
  have hle := KAM.Sharp2.Examples.NumQ.l1_sumA_le (a := 2 * (Q.τ : ℝ)) (γb := (γ : ℝ)) (b := b)
    (kp := Q.kp) hd hc (x' := fun t => (xL1 Q E Xs t : ℝ)) (x_bounds hQ hτ hE hei hX)
  refine hle.trans (le_of_eq ?_)
  exact NumQ.cast_sumA γ (fun _ => rfl) (fun _ => rfl) hb

/-- **Soundness of the rational check of a run with the ℓ¹ entry.** -/
theorem okL1_sound (hQ : Q.toNum.Wf) (hτ : 1 ≤ Q.τ) {σ m₀ : Fin 9 → ℚ} {Xs : ℚ}
    (h : okL1 Q E σ m₀ Xs = true) :
    E.toA.Wf ∧ Ent.einv ≤ (E.ei : ℝ) ∧
      routeAOkIL1 Q.toNum E.toA (fun i => (σ i : ℝ)) (fun i => (m₀ i : ℝ)) (Xs : ℝ) := by
  simp only [okL1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, List.mem_finRange, true_implies] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, hkp⟩, hwf⟩, hei0⟩, hJ0⟩, hJ1⟩, hJ1t⟩, hJ2⟩, hJ3⟩ := h
  obtain ⟨hE, -⟩ := EntryQ.wf_of hwf
  have hei : Ent.einv ≤ (E.ei : ℝ) :=
    einv_le.trans (by exact_mod_cast hei0)
  have hp0 := pos_inp hQ 0
  have hx := x_bounds hQ hτ hE hei h0
  refine ⟨hE, hei, ⟨hkp, by exact_mod_cast h0, ?_, fun s hs1 hs => ?_, ?_, ?_, fun i => ?_⟩⟩
  · rw [← NumQ.toStep_inp]
    exact econd_sound hp0 hE hei h0 hJ0
  · have hc : (Q.inp s).condB (xL1 Q E Xs s) = true := by
      rcases hJ1 s hs with h1 | h1
      · omega
      · exact h1
    have := StepQ.condB_sound hτ hc
    rw [NumQ.toStep_inp] at this
    exact this.down (hQ.pos s) (hx s).2
  · have := StepQ.condB_sound hτ hJ1t
    rw [NumQ.toStep_inp] at this
    exact this.down (hQ.pos _) (hx _).2
  · show (2 : ℝ) ^ (2 * (2 * (Q.τ : ℝ))) * (Q.toNum.inp Q.kp).CE *
      xIL1 Q.toNum E.toA (Xs : ℝ) Q.kp ≤ 1
    rw [four_rpow, NumQ.cast_CE hτ]
    have h3 : ((2 ^ (2 * (2 * Q.τ)) * (Q.inp Q.kp).CE * xL1 Q E Xs Q.kp : ℚ) : ℝ) ≤
        ((1 : ℚ) : ℝ) := Rat.cast_le.mpr hJ2
    push_cast at h3 ⊢
    have hCE0 : (0 : ℝ) ≤ (Q.inp Q.kp).CE := by
      rw [← NumQ.cast_CE hτ]; exact (hQ.pos _).CE
    refine le_trans ?_ h3
    exact mul_le_mul_of_nonneg_left (hx _).2 (by positivity)
  · have hj : (jI i : ℕ) ≤ 1 := by fin_cases i <;> simp [jI]
    have hb : 2 * (2 * (Q.τ : ℝ)) - (2 * (Q.τ : ℝ) + (jI i : ℝ)) =
        ((2 * Q.τ - jI i : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hle := sumA_le hQ hτ hE hei h0 Q.γb
      (c' := fun s => (stageIL1 Q.toNum E.toA s).rate i) (c := fun s => stRate Q E s i)
      (fun t => (stage_bounds hQ hτ hE hei t).2.1 i) hb
    have h4 : ((m₀ i + Q.sumQ Q.γb (xL1 Q E Xs) (fun s => stRate Q E s i) (2 * Q.τ - jI i) :
        ℚ) : ℝ) ≤ (σ i : ℝ) := Rat.cast_le.mpr (hJ3 i)
    push_cast at h4
    exact (add_le_add le_rfl hle).trans h4

/-- The closeness constant of the entry branch, in rational form. -/
theorem c2_le (hQ : Q.toNum.Wf) (hτ : 1 ≤ Q.τ) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ))
    {Xs : ℚ} (hX : 0 < Xs) : c2IL1 Q.toNum E.toA (Xs : ℝ) ≤ (c2L1 Q E Xs : ℝ) := by
  have hb : 2 * (2 * (Q.τ : ℝ)) - 2 * (Q.τ : ℝ) = ((2 * Q.τ : ℕ) : ℝ) := by push_cast; ring
  have hs := sumA_le hQ hτ hE hei hX.le 1 (c' := fun s => (stageIL1 Q.toNum E.toA s).CD)
    (c := stCD Q E) (fun t => by
      rw [(stage_bounds hQ hτ hE hei t).2.2.1]
      refine ⟨?_, le_rfl⟩
      rw [← (stage_bounds hQ hτ hE hei t).2.2.1]
      rcases Nat.eq_zero_or_pos t with ht | ht
      · subst ht
        have hp0 := pos_inp hQ 0
        have hst : stageIL1 Q.toNum E.toA 0 = entryStageIA (Q.inp 0).toStep E.toA := by
          simp [stageIL1, NumQ.toStep_inp]
        rw [hst]
        simp only [entryStageIA, Ent.CDK_eq]
        exact (Ent.nonneg hp0 hE).CDK
      · have hst : stageIL1 Q.toNum E.toA t = stageI Q.toNum t := by simp [stageIL1, ht.ne']
        rw [hst]
        exact (hQ.pos t).CDK) hb
  have e1 : ((1 : ℚ) : ℝ) = 1 := Rat.cast_one
  rw [e1] at hs
  have e2 : (2 * (Q.τ : ℝ)) = ((2 * Q.τ : ℕ) : ℝ) := by push_cast; ring
  have e4 : (4 * (Q.τ : ℝ)) = ((4 * Q.τ : ℕ) : ℝ) := by push_cast; ring
  have hX' : (0 : ℝ) < Xs := by exact_mod_cast hX
  have hρ0 : (0 : ℝ) < Q.ρ := hQ.ρinf_pos.trans hQ.ρinf_lt
  have hd0 : (0 : ℝ) < Q.δ0 := by
    rw [← NumQ.cast_δ0]; exact delta0_pos (by norm_num) hQ.ρinf_lt
  show (Q.ρ : ℝ) ^ (2 * (Q.τ : ℝ)) * sumA (2 * (Q.τ : ℝ)) 3 Q.ρ Q.ρinf 1
    (xIL1 Q.toNum E.toA (Xs : ℝ)) (fun s => (stageIL1 Q.toNum E.toA s).CD) (2 * (Q.τ : ℝ)) Q.kp /
    ((Xs : ℝ) * delta0 3 (Q.ρ : ℝ) Q.ρinf ^ (4 * (Q.τ : ℝ))) ≤ _
  rw [NumQ.cast_δ0, e4, Real.rpow_natCast, e2, Real.rpow_natCast]
  simp only [c2L1]
  push_cast
  gcongr

/-- The frequency constant of the entry branch, in rational form. -/
theorem c3_le (hQ : Q.toNum.Wf) (hτ : 1 ≤ Q.τ) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ))
    {Xs : ℚ} (hX : 0 < Xs) : c3IL1 Q.toNum E.toA (Xs : ℝ) ≤ (c3L1 Q E Xs : ℝ) := by
  have hb : 2 * (2 * (Q.τ : ℝ)) - 2 * (Q.τ : ℝ) = ((2 * Q.τ : ℕ) : ℝ) := by push_cast; ring
  have hs := sumA_le hQ hτ hE hei hX.le 1 (c' := fun s => (stageIL1 Q.toNum E.toA s).Cp)
    (c := stCp Q E) (fun t => by
      rw [(stage_bounds hQ hτ hE hei t).2.2.2]
      refine ⟨?_, le_rfl⟩
      rw [← (stage_bounds hQ hτ hE hei t).2.2.2]
      rcases Nat.eq_zero_or_pos t with ht | ht
      · subst ht
        have hp0 := pos_inp hQ 0
        have hst : stageIL1 Q.toNum E.toA 0 = entryStageIA (Q.inp 0).toStep E.toA := by
          simp [stageIL1, NumQ.toStep_inp]
        rw [hst]
        simp only [entryStageIA, Ent.CDw_eq]
        exact (Ent.nonneg hp0 hE).CDw
      · have hst : stageIL1 Q.toNum E.toA t = stageI Q.toNum t := by simp [stageIL1, ht.ne']
        rw [hst]
        exact (hQ.pos t).CDw) hb
  have e1 : ((1 : ℚ) : ℝ) = 1 := Rat.cast_one
  rw [e1] at hs
  have e2 : (2 * (Q.τ : ℝ)) = ((2 * Q.τ : ℕ) : ℝ) := by push_cast; ring
  have e4 : (4 * (Q.τ : ℝ)) = ((4 * Q.τ : ℕ) : ℝ) := by push_cast; ring
  have hX' : (0 : ℝ) < Xs := by exact_mod_cast hX
  have hρ0 : (0 : ℝ) < Q.ρ := hQ.ρinf_pos.trans hQ.ρinf_lt
  have hd0 : (0 : ℝ) < Q.δ0 := by
    rw [← NumQ.cast_δ0]; exact delta0_pos (by norm_num) hQ.ρinf_lt
  show (Q.ρ : ℝ) ^ (2 * (Q.τ : ℝ)) * sumA (2 * (Q.τ : ℝ)) 3 Q.ρ Q.ρinf 1
    (xIL1 Q.toNum E.toA (Xs : ℝ)) (fun s => (stageIL1 Q.toNum E.toA s).Cp) (2 * (Q.τ : ℝ)) Q.kp /
    ((Xs : ℝ) * delta0 3 (Q.ρ : ℝ) Q.ρinf ^ (4 * (Q.τ : ℝ))) ≤ _
  rw [NumQ.cast_δ0, e4, Real.rpow_natCast, e2, Real.rpow_natCast]
  simp only [c3L1]
  push_cast
  gcongr

end KAM.CertificateSharp.V2.L1

end
