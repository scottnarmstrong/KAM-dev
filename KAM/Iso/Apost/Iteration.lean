/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Apost.Step
public import KAM.Iso.Apost.Schedule
public import KAM.Iso.Apost.Standing
import KAM.Iso.Apost.ConstantsArith
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Part 2 (isoenergetic iteration): the induction of the iteration

Blueprint node `bpI:p2:iteration`
(`KAM.Iso.Apost.iteration`). The sequence of pairs `(K_j, s_j)` is the explicit
`KAM.Iso.Apost.isoSeq` of `KAM/Iso/Apost/Defs.lean`: `(K₀, s₀) = (K, s₀)` and
`(K_{j+1}, s_{j+1}) = (K̄_j, s̄_j)`, the isoenergetic Newton map on `T_{r_j - 2δ_j}` and the new
ray parameter. The schedule `δ_j, r_j` is that of `KAM.Apost`, `ε_j, d_j` are `isoEpsSeq`, `isoDSeq`
(`KAM/Iso/Apost/Schedule.lean`). The hypotheses are exactly `IterHyp` (rule 6).

The proof mirrors `KAM/Apost/Iteration.lean` (`Stage`, `stage_zero`, `stage_succ`).

* `step:p2:it-sums`: `iso_sums_le` bounds the partial sums `D_j`, `∑ n d_i/δ_i`,
  `∑ C_B d_i/δ_i`, `∑ 2𝔪² C_{Δ𝖳} d_i/δ_i²` by comparison with the sums of `iso_error_decay` and
  the constant inequalities `Arith.iso_iteration_sums`; in addition `D_j ≤ ν/2`.
* `step:p2:it-stepsmall`: `iso_stepsmall_seq` is the smallness hypothesis of `step` at stage `j`.
* `step:p2:it-base`: `iso_stage_zero`.
* `step:p2:it-step`: `iso_stage_succ` applies `step` at the stage `j` and carries the induction
  hypotheses `IsoStage` to `j + 1`. The ray facts `1 < s_j < σ_ω` and `ν - D_j ≤ ν(s_j)` are not
  carried: they follow from `‖s_j ω* - s₀ ω*‖ ≤ D_j ≤ ν/2` by `ray` (`iso_ray_step`).

`T_r` is `complexStrip n r`; matrix norms are the operator norms of
`open scoped Matrix.Norms.Operator`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.Iso.Apost

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear

/-! ### The sequence -/

section Seq

variable {n : ℕ} (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
  (ωstar : Fin n → ℝ) (E₀ s₀ ρ ρinf : ℝ)

@[simp] theorem isoSeq_zero : isoSeq H K ωstar E₀ s₀ ρ ρinf 0 = (K, s₀) := rfl

@[simp] theorem isoSeq_succ_fst (j : ℕ) :
    (isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).1 =
      isoNewtonMap H (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 ωstar E₀
        (isoSeq H K ωstar E₀ s₀ ρ ρinf j).2 (rSeq ρ ρinf j - 2 * deltaSeq ρ ρinf j) := rfl

@[simp] theorem isoSeq_succ_snd (j : ℕ) :
    (isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).2 =
      isoNewS H (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 ωstar E₀
        (isoSeq H K ωstar E₀ s₀ ρ ρinf j).2 := rfl

end Seq

/-! ### The partial sums `D_j` and their weighted versions -/

section Sums

variable (n τ M σK σB σT) in
/-- `D_j = ∑_{i<j} d_i`. -/
def isoSumD (ρ ρinf γ e : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, isoDSeq n τ M σK σB σT ρ ρinf γ e i

variable (n τ M σK σB σT) in
/-- `∑_{i<j} n d_i / δ_i`, the accumulated change of `DK`. -/
def isoSumDK (ρ ρinf γ e : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, n * isoDSeq n τ M σK σB σT ρ ρinf γ e i / deltaSeq ρ ρinf i

variable (n τ M σK σB σT) in
/-- `∑_{i<j} C_B d_i / δ_i`, the accumulated change of `B`. -/
def isoSumB (ρ ρinf γ e : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j,
    C_B n M σK σB σT * isoDSeq n τ M σK σB σT ρ ρinf γ e i / deltaSeq ρ ρinf i

variable (n τ M σK σB σT) in
/-- `∑_{i<j} 2𝔪² C_{Δ𝖳} d_i / δ_i²`, the accumulated change of `⟨𝖳⟩⁻¹`. -/
def isoSumT (ρ ρinf γ e : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, 2 * mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT *
    isoDSeq n τ M σK σB σT ρ ρinf γ e i / deltaSeq ρ ρinf i ^ 2

variable {n : ℕ} {τ M σK σB σT : ℝ} {γ ρ ρinf e : ℝ}

theorem isoSumD_zero : isoSumD n τ M σK σB σT ρ ρinf γ e 0 = 0 := by simp [isoSumD]

theorem isoSumDK_zero : isoSumDK n τ M σK σB σT ρ ρinf γ e 0 = 0 := by simp [isoSumDK]

theorem isoSumB_zero : isoSumB n τ M σK σB σT ρ ρinf γ e 0 = 0 := by simp [isoSumB]

theorem isoSumT_zero : isoSumT n τ M σK σB σT ρ ρinf γ e 0 = 0 := by simp [isoSumT]

theorem isoSumD_succ (j : ℕ) : isoSumD n τ M σK σB σT ρ ρinf γ e (j + 1) =
    isoSumD n τ M σK σB σT ρ ρinf γ e j + isoDSeq n τ M σK σB σT ρ ρinf γ e j := by
  simp only [isoSumD, Finset.sum_range_succ]

theorem isoSumDK_succ (j : ℕ) : isoSumDK n τ M σK σB σT ρ ρinf γ e (j + 1) =
    isoSumDK n τ M σK σB σT ρ ρinf γ e j +
      n * isoDSeq n τ M σK σB σT ρ ρinf γ e j / deltaSeq ρ ρinf j := by
  simp only [isoSumDK, Finset.sum_range_succ]

theorem isoSumB_succ (j : ℕ) : isoSumB n τ M σK σB σT ρ ρinf γ e (j + 1) =
    isoSumB n τ M σK σB σT ρ ρinf γ e j +
      C_B n M σK σB σT * isoDSeq n τ M σK σB σT ρ ρinf γ e j / deltaSeq ρ ρinf j := by
  simp only [isoSumB, Finset.sum_range_succ]

theorem isoSumT_succ (j : ℕ) : isoSumT n τ M σK σB σT ρ ρinf γ e (j + 1) =
    isoSumT n τ M σK σB σT ρ ρinf γ e j + 2 * mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT *
      isoDSeq n τ M σK σB σT ρ ρinf γ e j / deltaSeq ρ ρinf j ^ 2 := by
  simp only [isoSumT, Finset.sum_range_succ]

/-- `n d_i / δ_i = (n Ĉ_Δ/γ²) · ε_i/δ_i^{a+1}`. -/
theorem isoDK_term_eq (hρ : ρinf < ρ) (hγ : 0 < γ) (i : ℕ) :
    n * isoDSeq n τ M σK σB σT ρ ρinf γ e i / deltaSeq ρ ρinf i =
      n * hatCDelta n τ M σK σB σT / γ ^ 2 *
        (isoEpsSeq n τ M σK σB σT ρ ρinf γ e i / deltaSeq ρ ρinf i ^ (aExp n τ + 1)) := by
  have hδ := deltaSeq_pos hρ i
  have hp : deltaSeq ρ ρinf i ^ aExp n τ ≠ 0 := (Real.rpow_pos_of_pos hδ _).ne'
  have hγ' : γ ≠ 0 := hγ.ne'
  rw [Real.rpow_add_one hδ.ne']
  unfold isoDSeq dStep
  field_simp

/-- `C_B d_i / δ_i = (C_B Ĉ_Δ/γ²) · ε_i/δ_i^{a+1}`. -/
theorem isoB_term_eq (hρ : ρinf < ρ) (hγ : 0 < γ) (i : ℕ) :
    C_B n M σK σB σT * isoDSeq n τ M σK σB σT ρ ρinf γ e i / deltaSeq ρ ρinf i =
      C_B n M σK σB σT * hatCDelta n τ M σK σB σT / γ ^ 2 *
        (isoEpsSeq n τ M σK σB σT ρ ρinf γ e i / deltaSeq ρ ρinf i ^ (aExp n τ + 1)) := by
  have hδ := deltaSeq_pos hρ i
  have hp : deltaSeq ρ ρinf i ^ aExp n τ ≠ 0 := (Real.rpow_pos_of_pos hδ _).ne'
  have hγ' : γ ≠ 0 := hγ.ne'
  rw [Real.rpow_add_one hδ.ne']
  unfold isoDSeq dStep
  field_simp

/-- `2𝔪² C_{Δ𝖳} d_i / δ_i² = (2𝔪² C_{Δ𝖳} Ĉ_Δ/γ²) · ε_i/δ_i^{a+2}`. -/
theorem isoT_term_eq (hρ : ρinf < ρ) (hγ : 0 < γ) (i : ℕ) :
    2 * mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT * isoDSeq n τ M σK σB σT ρ ρinf γ e i /
        deltaSeq ρ ρinf i ^ 2 =
      2 * mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT * hatCDelta n τ M σK σB σT / γ ^ 2 *
        (isoEpsSeq n τ M σK σB σT ρ ρinf γ e i / deltaSeq ρ ρinf i ^ (aExp n τ + 2)) := by
  have hδ := deltaSeq_pos hρ i
  have hp : deltaSeq ρ ρinf i ^ aExp n τ ≠ 0 := (Real.rpow_pos_of_pos hδ _).ne'
  have hγ' : γ ≠ 0 := hγ.ne'
  rw [Real.rpow_add hδ, Real.rpow_two]
  unfold isoDSeq dStep
  field_simp

/-- Step `it-sums`: the five summed bounds, for every `j`, from `ĉ_* e/(γ⁴ δ₀^{2a}) ≤ 1` and
`γ ≤ Θ`. -/
theorem iso_sums_le (hP : Params n τ M σK σB σT) {μ ν : ℝ} (hρ : ρinf < ρ) (hγ : 0 < γ)
    (hγΘ : γ ≤ Theta n M σK σB σT) (he : 0 ≤ e) (hμ : 0 < μ) (hν : 0 < ν)
    (hsmall : hatcStar n τ M σK σB σT μ ν * e / (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) ≤ 1)
    (j : ℕ) :
    isoSumD n τ M σK σB σT ρ ρinf γ e j ≤ μ / 4 ∧ isoSumD n τ M σK σB σT ρ ρinf γ e j ≤ ν / 2 ∧
      isoSumDK n τ M σK σB σT ρ ρinf γ e j ≤ μ / 4 ∧
      isoSumB n τ M σK σB σT ρ ρinf γ e j ≤ μ / 4 ∧
      isoSumT n τ M σK σB σT ρ ρinf γ e j ≤ μ / 2 := by
  have hd0 := delta0_pos hρ
  have hq := Arith.iso_error_decay_hyp hγ hd0 he hsmall
  have hi := Arith.iso_iteration_sums hP hγ hγΘ hd0 (delta0_le_one ρ ρinf) he hμ hν hsmall
  have ha := eight_le_aExp hP
  have hn := zero_le_one.trans hP.one_le_cast
  have hΔ := zero_le_one.trans (one_le_hatCDelta hP)
  have hCB := zero_le_one.trans (one_le_C_B hP)
  have hCT := zero_le_one.trans (one_le_CDTbord hP)
  have hm := zero_le_one.trans (one_le_mSize (M := M) (σK := σK) (σB := σB) (σT := σT))
  have hX0 : 0 ≤ hatCDelta n τ M σK σB σT / γ ^ 2 := by positivity
  have hD : isoSumD n τ M σK σB σT ρ ρinf γ e j ≤
      hatCDelta n τ M σK σB σT / γ ^ 2 * (2 * e / delta0 ρ ρinf ^ aExp n τ) := by
    have h := isoEps_partial_sum_le hP hρ hγ he hq (j := aExp n τ) (by linarith) hX0 j
    have h' : isoSumD n τ M σK σB σT ρ ρinf γ e j =
        ∑ i ∈ Finset.range j, hatCDelta n τ M σK σB σT / γ ^ 2 *
          (isoEpsSeq n τ M σK σB σT ρ ρinf γ e i / deltaSeq ρ ρinf i ^ aExp n τ) :=
      Finset.sum_congr rfl fun i _ => isoDSeq_eq i
    rw [h']
    exact h
  have hDK : isoSumDK n τ M σK σB σT ρ ρinf γ e j ≤
      (n : ℝ) * hatCDelta n τ M σK σB σT / γ ^ 2 * (2 * e / delta0 ρ ρinf ^ (aExp n τ + 1)) := by
    have hX : 0 ≤ (n : ℝ) * hatCDelta n τ M σK σB σT / γ ^ 2 := by positivity
    have h := isoEps_partial_sum_le hP hρ hγ he hq (j := aExp n τ + 1) (by linarith) hX j
    have h' : isoSumDK n τ M σK σB σT ρ ρinf γ e j =
        ∑ i ∈ Finset.range j, (n : ℝ) * hatCDelta n τ M σK σB σT / γ ^ 2 *
          (isoEpsSeq n τ M σK σB σT ρ ρinf γ e i / deltaSeq ρ ρinf i ^ (aExp n τ + 1)) :=
      Finset.sum_congr rfl fun i _ => isoDK_term_eq hρ hγ i
    rw [h']
    exact h
  have hB : isoSumB n τ M σK σB σT ρ ρinf γ e j ≤
      C_B n M σK σB σT * hatCDelta n τ M σK σB σT / γ ^ 2 *
        (2 * e / delta0 ρ ρinf ^ (aExp n τ + 1)) := by
    have hX : 0 ≤ C_B n M σK σB σT * hatCDelta n τ M σK σB σT / γ ^ 2 := by positivity
    have h := isoEps_partial_sum_le hP hρ hγ he hq (j := aExp n τ + 1) (by linarith) hX j
    have h' : isoSumB n τ M σK σB σT ρ ρinf γ e j =
        ∑ i ∈ Finset.range j, C_B n M σK σB σT * hatCDelta n τ M σK σB σT / γ ^ 2 *
          (isoEpsSeq n τ M σK σB σT ρ ρinf γ e i / deltaSeq ρ ρinf i ^ (aExp n τ + 1)) :=
      Finset.sum_congr rfl fun i _ => isoB_term_eq hρ hγ i
    rw [h']
    exact h
  have hT : isoSumT n τ M σK σB σT ρ ρinf γ e j ≤
      2 * mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT * hatCDelta n τ M σK σB σT / γ ^ 2 *
        (2 * e / delta0 ρ ρinf ^ (aExp n τ + 2)) := by
    have hX : 0 ≤ 2 * mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT *
        hatCDelta n τ M σK σB σT / γ ^ 2 := by positivity
    have h := isoEps_partial_sum_le hP hρ hγ he hq (j := aExp n τ + 2) (by linarith) hX j
    have h' : isoSumT n τ M σK σB σT ρ ρinf γ e j =
        ∑ i ∈ Finset.range j, 2 * mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT *
          hatCDelta n τ M σK σB σT / γ ^ 2 *
          (isoEpsSeq n τ M σK σB σT ρ ρinf γ e i / deltaSeq ρ ρinf i ^ (aExp n τ + 2)) :=
      Finset.sum_congr rfl fun i _ => isoT_term_eq hρ hγ i
    rw [h']
    exact h
  exact ⟨hD.trans hi.1, hD.trans hi.2.1, hDK.trans hi.2.2.1, hB.trans hi.2.2.2.1,
    hT.trans hi.2.2.2.2⟩

/-- Step `it-stepsmall`: `ĉ_step ε_j/(γ⁴ δ_j^{2a}) ≤ min {1, μ/2}` at every stage. -/
theorem iso_stepsmall_seq (hP : Params n τ M σK σB σT) {μ ν : ℝ} (hρ : ρinf < ρ) (hγ : 0 < γ)
    (he : 0 ≤ e) (hμ : 0 < μ)
    (hsmall : hatcStar n τ M σK σB σT μ ν * e / (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) ≤ 1)
    (j : ℕ) :
    hatcStep n τ M σK σB σT * isoEpsSeq n τ M σK σB σT ρ ρinf γ e j /
      (γ ^ 4 * deltaSeq ρ ρinf j ^ (2 * aExp n τ)) ≤ min 1 (μ / 2) := by
  have hq := Arith.iso_error_decay_hyp hγ (delta0_pos hρ) he hsmall
  have hstep := Arith.iso_iteration_step_small hP hγ (delta0_pos hρ) he hμ hsmall
  have hc0 := zero_le_one.trans (one_le_hatcStep hP)
  have hb := isoEps_div_le hP hρ hγ he hq (le_refl (2 * aExp n τ)) j
  refine le_trans ?_ hstep
  rw [mul_div_mul_comm, mul_div_mul_comm (hatcStep n τ M σK σB σT) e]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

end Sums

/-! ### The ray -/

section Ray

variable {n : ℕ} {τ M σK σB σT σω ν γ : ℝ} {ωstar : Fin n → ℝ}
  {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

/-- A parameter within `d ≤ ν/2` of one with margin at least `ν` is on the open ray, with margin
at least `ν - d` (the "in particular" clause of `ray`). -/
theorem iso_ray_step (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ) {s₀ s' d : ℝ}
    (hm : ν ≤ rayMargin σω ωstar s₀) (hd : ‖s' • ωstar - s₀ • ωstar‖ ≤ d) (hdν : d ≤ ν / 2) :
    1 < s' ∧ s' < σω ∧ ν - d ≤ rayMargin σω ωstar s' :=
  (ray (σω := σω) hS.dio).2.2.2.2.2 s₀ s' ν d hm hd (by linarith [hS.ν_pos])

end Ray

/-! ### The induction hypothesis -/

/-- The induction hypothesis at stage `j`: the part of (i)--(vi) of `bpI:p2:iteration` that is
carried from `j` to `j + 1`. The bounds on the sums themselves (`D_j ≤ μ/4` and so on) and
`ε_j ≤ e ≤ 1` do not depend on the induction (`iso_sums_le`, `isoEps_le`), and the ray facts
`1 < s_j < σ_ω`, `ν - D_j ≤ ν(s_j)` follow from `sdist` (`iso_ray_step`). -/
structure IsoStage (n : ℕ) (τ M σK σB σT : ℝ) (D : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ωstar : Fin n → ℝ) (E₀ γ ρ ρinf μ e s₀ : ℝ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (j : ℕ) : Prop where
  adm : IsoAdmissible σK σB σT D H ωstar E₀ (rSeq ρ ρinf j)
    (μ - isoSumD n τ M σK σB σT ρ ρinf γ e j) (isoEpsSeq n τ M σK σB σT ρ ρinf γ e j)
    (isoSeq H K ωstar E₀ s₀ ρ ρinf j).2 (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1
  dist : ∀ θ ∈ complexStrip n (rSeq ρ ρinf j),
    ‖(isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ - K θ‖ ≤ isoSumD n τ M σK σB σT ρ ρinf γ e j
  sdist : ‖(isoSeq H K ωstar E₀ s₀ ρ ρinf j).2 • ωstar - s₀ • ωstar‖ ≤
    isoSumD n τ M σK σB σT ρ ρinf γ e j
  dk : ∀ θ ∈ complexStrip n (rSeq ρ ρinf j),
    ‖fderiv ℂ (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ‖ ≤
      σK - μ + isoSumDK n τ M σK σB σT ρ ρinf γ e j
  gb : ∀ θ ∈ complexStrip n (rSeq ρ ρinf j),
    ‖(gramMatrix (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ)⁻¹‖ ≤
      σB - μ + isoSumB n τ M σK σB σT ρ ρinf γ e j
  tb : ‖(KAM.Iso.extendedTorsionAverage H (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1
      ((isoSeq H K ωstar E₀ s₀ ρ ρinf j).2 • ωstar))⁻¹‖ ≤
    σT - μ + isoSumT n τ M σK σB σT ρ ρinf γ e j

section Induction

variable {n : ℕ} {τ M σK σB σT σω ν γ : ℝ} {ωstar : Fin n → ℝ}
  {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {E₀ ρ ρinf μ e s₀ : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

/-- Step `it-base`: `(K₀, s₀) = (K, s₀)` is `(ρ, μ, e)`-admissible, and the bounds hold with empty
sums. -/
theorem iso_stage_zero (hρ0 : 0 < ρ) (hμ : 0 < μ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hK : IterHyp σK σB σT σω ν D H ωstar E₀ ρ μ e s₀ K) :
    IsoStage n τ M σK σB σT D H ωstar E₀ γ ρ ρinf μ e s₀ K 0 := by
  have hk0 : (isoSeq H K ωstar E₀ s₀ ρ ρinf 0).1 = K := rfl
  have hs0 : (isoSeq H K ωstar E₀ s₀ ρ ρinf 0).2 = s₀ := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk0, hs0, rSeq_zero, isoSumD_zero, isoEpsSeq_zero, sub_zero]
    exact
      { r_pos := hρ0
        β_pos := hμ
        ε_nonneg := he0
        ε_le_one := he1
        holo := hK.holo
        primary := hK.primary
        real := hK.real
        ball_sub := hK.ball_sub
        deriv_le := fun θ hθ => (hK.deriv_le θ hθ).trans (by linarith)
        gram := fun θ hθ => ⟨(hK.gram θ hθ).1, (hK.gram θ hθ).2.trans (by linarith)⟩
        error_le := hK.error_le
        s_gt := hK.s_gt
        twist := ⟨hK.twist.1, hK.twist.2.trans (by linarith)⟩
        energy_le := hK.energy_le }
  · intro θ _
    rw [hk0, sub_self, norm_zero, isoSumD_zero]
  · rw [hs0, sub_self, norm_zero, isoSumD_zero]
  · intro θ hθ
    rw [rSeq_zero] at hθ
    rw [hk0, isoSumDK_zero, add_zero]
    exact hK.deriv_le θ hθ
  · intro θ hθ
    rw [rSeq_zero] at hθ
    rw [hk0, isoSumB_zero, add_zero]
    exact (hK.gram θ hθ).2
  · rw [hk0, hs0, isoSumT_zero, add_zero]
    exact hK.twist.2

/-- Step `it-step`: `step` applied at the stage `j` carries the induction hypothesis to `j + 1` and
gives (vi) at `j`. -/
theorem iso_stage_succ (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ) (hρinf : 0 < ρinf)
    (hρ : ρinf < ρ) (hμ : 0 < μ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hm : ν ≤ rayMargin σω ωstar s₀)
    (heps : ∀ j, isoEpsSeq n τ M σK σB σT ρ ρinf γ e j ≤ e)
    (hsm : ∀ j, hatcStep n τ M σK σB σT * isoEpsSeq n τ M σK σB σT ρ ρinf γ e j /
      (γ ^ 4 * deltaSeq ρ ρinf j ^ (2 * aExp n τ)) ≤ min 1 (μ / 2))
    (hsum : ∀ j, isoSumD n τ M σK σB σT ρ ρinf γ e j ≤ μ / 4 ∧
      isoSumD n τ M σK σB σT ρ ρinf γ e j ≤ ν / 2 ∧
      isoSumDK n τ M σK σB σT ρ ρinf γ e j ≤ μ / 4 ∧
      isoSumB n τ M σK σB σT ρ ρinf γ e j ≤ μ / 4 ∧
      isoSumT n τ M σK σB σT ρ ρinf γ e j ≤ μ / 2) {j : ℕ}
    (st : IsoStage n τ M σK σB σT D H ωstar E₀ γ ρ ρinf μ e s₀ K j) :
    IsoStage n τ M σK σB σT D H ωstar E₀ γ ρ ρinf μ e s₀ K (j + 1) ∧
      ((∀ θ ∈ complexStrip n (rSeq ρ ρinf (j + 1)),
        ‖(isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).1 θ - (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ‖ ≤
            isoDSeq n τ M σK σB σT ρ ρinf γ e j ∧
          ‖fderiv ℂ (isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).1 θ -
              fderiv ℂ (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ‖ ≤
            n * isoDSeq n τ M σK σB σT ρ ρinf γ e j / deltaSeq ρ ρinf j) ∧
        ‖(isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).2 • ωstar -
            (isoSeq H K ωstar E₀ s₀ ρ ρinf j).2 • ωstar‖ ≤
          isoDSeq n τ M σK σB σT ρ ρinf γ e j) := by
  have hP := hS.toParams
  obtain ⟨hD0, -, -, -, -⟩ := hsum j
  obtain ⟨hD1, hD1ν, hDK1, hB1, hT1⟩ := hsum (j + 1)
  obtain ⟨hr1, -, hδ1, h4δ⟩ := (schedule hρinf hρ).2.2 j
  obtain ⟨-, hrlow, -, -⟩ := (schedule hρinf hρ).2.2 (j + 1)
  have hρlow := (schedule hρinf hρ).2.1
  have hδ := deltaSeq_pos hρ j
  have hsm' : hatcStep n τ M σK σB σT * isoEpsSeq n τ M σK σB σT ρ ρinf γ e j /
      (γ ^ 4 * deltaSeq ρ ρinf j ^ (2 * aExp n τ)) ≤
      min 1 (μ - isoSumD n τ M σK σB σT ρ ρinf γ e j) :=
    (hsm j).trans (min_le_min le_rfl (by linarith))
  have hstep := step hS st.adm hδ hδ1 h4δ hsm'
  have hk := isoSeq_succ_fst H K ωstar E₀ s₀ ρ ρinf j
  have hs := isoSeq_succ_snd H K ωstar E₀ s₀ ρ ρinf j
  have hd : isoDSeq n τ M σK σB σT ρ ρinf γ e j =
      dStep n τ M σK σB σT γ (isoEpsSeq n τ M σK σB σT ρ ρinf γ e j) (deltaSeq ρ ρinf j) := rfl
  have hε := isoEpsSeq_succ (n := n) (τ := τ) (M := M) (σK := σK) (σB := σB) (σT := σT)
    (ρ := ρ) (ρinf := ρinf) (γ := γ) (e := e) j
  rw [← hk, ← hs, ← hd, ← hε] at hstep
  obtain ⟨⟨hdiff, hprim, hreal⟩, ⟨hdist, -, hball, hsdist⟩, ⟨herr, hEn⟩, hfr,
    ⟨htunit, htinv⟩⟩ := hstep
  -- the strips
  have hs20 : complexStrip n (rSeq ρ ρinf (j + 1)) ⊆ complexStrip n (rSeq ρ ρinf j) :=
    Triangular.strip_mono (by rw [hr1]; linarith)
  have hs22 : complexStrip n (rSeq ρ ρinf (j + 1)) ⊆
      complexStrip n (rSeq ρ ρinf j - 2 * deltaSeq ρ ρinf j) :=
    Triangular.strip_mono (by rw [hr1]; linarith)
  have hs23 : complexStrip n (rSeq ρ ρinf (j + 1)) ⊆
      complexStrip n (rSeq ρ ρinf j - 3 * deltaSeq ρ ρinf j) :=
    Triangular.strip_mono (by rw [hr1]; linarith)
  -- the new bounds
  have hdist' : ∀ θ ∈ complexStrip n (rSeq ρ ρinf (j + 1)),
      ‖(isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).1 θ - K θ‖ ≤
        isoSumD n τ M σK σB σT ρ ρinf γ e (j + 1) := by
    intro θ hθ
    have h1 := norm_sub_le_norm_sub_add_norm_sub
      ((isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).1 θ) ((isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ) (K θ)
    have h2 := st.dist θ (hs20 hθ)
    have h3 := hdist θ (hs22 hθ)
    rw [isoSumD_succ]
    linarith
  have hsdist' : ‖(isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).2 • ωstar - s₀ • ωstar‖ ≤
      isoSumD n τ M σK σB σT ρ ρinf γ e (j + 1) := by
    have h1 := norm_sub_le_norm_sub_add_norm_sub
      ((isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).2 • ωstar)
      ((isoSeq H K ωstar E₀ s₀ ρ ρinf j).2 • ωstar) (s₀ • ωstar)
    have h2 := st.sdist
    rw [isoSumD_succ]
    linarith
  have hdk' : ∀ θ ∈ complexStrip n (rSeq ρ ρinf (j + 1)),
      ‖fderiv ℂ (isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).1 θ‖ ≤
        σK - μ + isoSumDK n τ M σK σB σT ρ ρinf γ e (j + 1) := by
    intro θ hθ
    have h1 := norm_le_norm_add_norm_sub' (fderiv ℂ (isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).1 θ)
      (fderiv ℂ (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ)
    have h2 := st.dk θ (hs20 hθ)
    have h3 := (hfr θ (hs23 hθ)).1
    rw [isoSumDK_succ]
    linarith
  have hgb' : ∀ θ ∈ complexStrip n (rSeq ρ ρinf (j + 1)),
      ‖(gramMatrix (isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).1 θ)⁻¹‖ ≤
        σB - μ + isoSumB n τ M σK σB σT ρ ρinf γ e (j + 1) := by
    intro θ hθ
    have h1 := norm_le_norm_add_norm_sub'
      (gramMatrix (isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).1 θ)⁻¹
      (gramMatrix (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ)⁻¹
    have h2 := st.gb θ (hs20 hθ)
    have h3 := (hfr θ (hs23 hθ)).2.2
    rw [isoSumB_succ]
    linarith
  have htb' : ‖(KAM.Iso.extendedTorsionAverage H (isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).1
        ((isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).2 • ωstar))⁻¹‖ ≤
      σT - μ + isoSumT n τ M σK σB σT ρ ρinf γ e (j + 1) := by
    have h1 := norm_le_norm_add_norm_sub'
      (KAM.Iso.extendedTorsionAverage H (isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).1
        ((isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).2 • ωstar))⁻¹
      (KAM.Iso.extendedTorsionAverage H (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1
        ((isoSeq H K ωstar E₀ s₀ ρ ρinf j).2 • ωstar))⁻¹
    have h2 := st.tb
    rw [isoSumT_succ]
    linarith
  have hβ : μ - isoSumD n τ M σK σB σT ρ ρinf γ e (j + 1) =
      μ - isoSumD n τ M σK σB σT ρ ρinf γ e j - isoDSeq n τ M σK σB σT ρ ρinf γ e j := by
    rw [isoSumD_succ]
    ring
  obtain ⟨hs1, -, -⟩ := iso_ray_step hS hm hsdist' hD1ν
  have hadm : IsoAdmissible σK σB σT D H ωstar E₀ (rSeq ρ ρinf (j + 1))
      (μ - isoSumD n τ M σK σB σT ρ ρinf γ e (j + 1))
      (isoEpsSeq n τ M σK σB σT ρ ρinf γ e (j + 1))
      (isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).2 (isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).1 :=
      { r_pos := by linarith
        β_pos := by linarith
        ε_nonneg := isoEpsSeq_nonneg hP hρ he0 _
        ε_le_one := (heps _).trans he1
        holo := hdiff.mono hs22
        primary := fun θ hθ k => hprim θ (hs22 hθ) k
        real := hreal
        ball_sub := fun θ hθ => by
          rw [hβ]
          exact hball θ (hs22 hθ)
        deriv_le := fun θ hθ => (hdk' θ hθ).trans (by linarith)
        gram := fun θ hθ => ⟨(hfr θ (hs23 hθ)).2.1, (hgb' θ hθ).trans (by linarith)⟩
        error_le := fun θ hθ => herr θ (hs22 hθ)
        s_gt := hs1
        twist := ⟨htunit, htb'.trans (by linarith)⟩
        energy_le := hEn }
  exact ⟨⟨hadm, hdist', hsdist', hdk', hgb', htb'⟩,
    fun θ hθ => ⟨hdist θ (hs22 hθ), (hfr θ (hs23 hθ)).1⟩, hsdist⟩

end Induction

section Iteration

variable {n : ℕ} {τ M σK σB σT σω ν γ : ℝ} {ωstar : Fin n → ℝ}
  {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

/-- `bpI:p2:iteration` (i)–(vi), `D_j = ∑_{i<j} d_i`. -/
theorem iteration (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ) {E₀ ρ ρinf μ e s₀ : ℝ}
    (hρinf : 0 < ρinf) (hρ : ρinf < ρ) (hμ : 0 < μ) {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : IterHyp σK σB σT σω ν D H ωstar E₀ ρ μ e s₀ K) (he1 : e ≤ 1)
    (hsmall : hatcStar n τ M σK σB σT μ ν * e / (γ ^ 4 * delta0 ρ ρinf ^ (2 * aExp n τ)) ≤ 1) :
    isoSeq H K ωstar E₀ s₀ ρ ρinf 0 = (K, s₀) ∧ ∀ j : ℕ,
      (IsoAdmissible σK σB σT D H ωstar E₀ (rSeq ρ ρinf j)
          (μ - ∑ i ∈ Finset.range j, isoDSeq n τ M σK σB σT ρ ρinf γ e i)
          (isoEpsSeq n τ M σK σB σT ρ ρinf γ e j) (isoSeq H K ωstar E₀ s₀ ρ ρinf j).2
          (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 ∧
        isoEpsSeq n τ M σK σB σT ρ ρinf γ e j ≤ e) ∧
      (∑ i ∈ Finset.range j, isoDSeq n τ M σK σB σT ρ ρinf γ e i ≤ μ / 4 ∧
        ∑ i ∈ Finset.range j, isoDSeq n τ M σK σB σT ρ ρinf γ e i ≤ ν / 2 ∧
        (∀ θ ∈ complexStrip n (rSeq ρ ρinf j), ‖(isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ - K θ‖ ≤
          ∑ i ∈ Finset.range j, isoDSeq n τ M σK σB σT ρ ρinf γ e i) ∧
        ‖(isoSeq H K ωstar E₀ s₀ ρ ρinf j).2 • ωstar - s₀ • ωstar‖ ≤
          ∑ i ∈ Finset.range j, isoDSeq n τ M σK σB σT ρ ρinf γ e i ∧
        ν - ∑ i ∈ Finset.range j, isoDSeq n τ M σK σB σT ρ ρinf γ e i ≤
          rayMargin σω ωstar (isoSeq H K ωstar E₀ s₀ ρ ρinf j).2 ∧
        1 < (isoSeq H K ωstar E₀ s₀ ρ ρinf j).2 ∧ (isoSeq H K ωstar E₀ s₀ ρ ρinf j).2 < σω) ∧
      ((∀ θ ∈ complexStrip n (rSeq ρ ρinf j), ‖fderiv ℂ (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ‖ ≤
          σK - μ + ∑ i ∈ Finset.range j,
            n * isoDSeq n τ M σK σB σT ρ ρinf γ e i / deltaSeq ρ ρinf i) ∧
        σK - μ + ∑ i ∈ Finset.range j,
          n * isoDSeq n τ M σK σB σT ρ ρinf γ e i / deltaSeq ρ ρinf i ≤ σK - μ / 2) ∧
      ((∀ θ ∈ complexStrip n (rSeq ρ ρinf j),
          ‖(gramMatrix (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ)⁻¹‖ ≤ σB - μ + ∑ i ∈ Finset.range j,
            C_B n M σK σB σT * isoDSeq n τ M σK σB σT ρ ρinf γ e i / deltaSeq ρ ρinf i) ∧
        σB - μ + ∑ i ∈ Finset.range j,
          C_B n M σK σB σT * isoDSeq n τ M σK σB σT ρ ρinf γ e i / deltaSeq ρ ρinf i ≤ σB - μ / 2) ∧
      (‖(KAM.Iso.extendedTorsionAverage H (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1
            ((isoSeq H K ωstar E₀ s₀ ρ ρinf j).2 • ωstar))⁻¹‖ ≤
          σT - μ + ∑ i ∈ Finset.range j, 2 * mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT *
            isoDSeq n τ M σK σB σT ρ ρinf γ e i / deltaSeq ρ ρinf i ^ 2 ∧
        σT - μ + ∑ i ∈ Finset.range j, 2 * mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT *
          isoDSeq n τ M σK σB σT ρ ρinf γ e i / deltaSeq ρ ρinf i ^ 2 ≤ σT - μ / 2) ∧
      ((∀ θ ∈ complexStrip n (rSeq ρ ρinf (j + 1)),
          ‖(isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).1 θ - (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ‖ ≤
            isoDSeq n τ M σK σB σT ρ ρinf γ e j ∧
          ‖fderiv ℂ (isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).1 θ -
              fderiv ℂ (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 θ‖ ≤
            n * isoDSeq n τ M σK σB σT ρ ρinf γ e j / deltaSeq ρ ρinf j) ∧
        ‖(isoSeq H K ωstar E₀ s₀ ρ ρinf (j + 1)).2 • ωstar -
            (isoSeq H K ωstar E₀ s₀ ρ ρinf j).2 • ωstar‖ ≤
          isoDSeq n τ M σK σB σT ρ ρinf γ e j) := by
  have hP := hS.toParams
  have hγ := hS.gamma_pos
  have hν := hS.ν_pos
  have hρ0 : 0 < ρ := hρinf.trans hρ
  have h00 : (0 : Fin n → ℂ) ∈ complexStrip n ρ := fun i => by simpa using hρ0
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hK.error_le 0 h00)
  have st0 : IsoStage n τ M σK σB σT D H ωstar E₀ γ ρ ρinf μ e s₀ K 0 :=
    iso_stage_zero hρ0 hμ he0 he1 hK
  -- `γ ≤ Θ`, from the frequency estimate for `(K, s₀)`
  obtain ⟨hγω, hω⟩ := st0.adm.freq hS
  have hγΘ : γ ≤ Theta n M σK σB σT := hγω.trans hω
  have hq := Arith.iso_error_decay_hyp hγ (delta0_pos hρ) he0 hsmall
  have hsums := fun j => iso_sums_le hP hρ hγ hγΘ he0 hμ hν hsmall j
  have heps := fun j => isoEps_le hP hρ hγ he0 hq j
  have hsm := fun j => iso_stepsmall_seq hP hρ hγ he0 hμ hsmall j
  have hall : ∀ j : ℕ, IsoStage n τ M σK σB σT D H ωstar E₀ γ ρ ρinf μ e s₀ K j := by
    intro j
    induction j with
    | zero => exact st0
    | succ j ih => exact (iso_stage_succ hS hρinf hρ hμ he0 he1 hK.margin heps hsm hsums ih).1
  refine ⟨rfl, fun j => ?_⟩
  obtain ⟨hD, hDν, hDK, hB, hT⟩ := hsums j
  have st := hall j
  obtain ⟨hs1, hs2, hs3⟩ := iso_ray_step hS hK.margin st.sdist hDν
  have hv := (iso_stage_succ hS hρinf hρ hμ he0 he1 hK.margin heps hsm hsums st).2
  unfold isoSumD at hD hDν
  unfold isoSumDK at hDK
  unfold isoSumB at hB
  unfold isoSumT at hT
  exact ⟨⟨st.adm, heps j⟩, ⟨hD, hDν, st.dist, st.sdist, hs3, hs1, hs2⟩, ⟨st.dk, by linarith⟩,
    ⟨st.gb, by linarith⟩, ⟨st.tb, by linarith⟩, hv⟩

end Iteration

end KAM.Iso.Apost

end
