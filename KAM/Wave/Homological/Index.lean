/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Seq.Transport
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Normal modes, P96-K index and the weighted pairing (blueprint-W `bpW:w4:index`)

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still being built.

Normal sequences `z = (z_j)_{j ≥ 1}` (`ℕ+ → ℂ`, P96-K index `j`, wave index `J = j + 2`) with the
weights `ω_{a,q}(j+2)`:

* `homWt a q j = ω_{a,q}(j+2) = (j+2)^q e^{a(j+2)}`;
* `HomNormal a q z`: `z ∈ ℓ^N_{a,q}` (`∑ ω_{a,q}(j+2)² |z_j|² < ∞`), with the norm `homNorm a q z`
  (the `ℓ²`-norm of the weighted sequence `homNormLp`);
* `homPair x x' = ∑_j x_j x'_j` (no conjugation) and the Cauchy–Schwarz bound
  `|⟨x,x'⟩₀| ≤ ‖x‖_{a,q} ‖x'‖_{a,q'}` for `q + q' ≥ 0` (`bpW:w4:pairing`, `norm_homPair_le`);
* the multiplier bound `homNormal_mul` (a sequence `μ` with `|μ_j| ≤ M (j+2)` maps `ℓ^N_{a,q}` to
  `ℓ^N_{a,q-1}` with norm `≤ M`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open scoped InnerProductSpace

/-- The weight `ω_{a,q}(j+2)` of the P96-K normal index `j` (wave index `J = j + 2`). -/
noncomputable def homWt (a q : ℝ) (j : ℕ+) : ℝ := ellWeight a q (j + 2)

theorem homWt_pos (a q : ℝ) (j : ℕ+) : 0 < homWt a q j := ellWeight_pos a q (j + 2)

theorem ellWeight_succ_exponent' (a p : ℝ) (J : ℕ+) :
    ellWeight a (p + 1) J = (J : ℝ) * ellWeight a p J := by
  unfold ellWeight
  rw [Real.rpow_add_one (by exact_mod_cast J.ne_zero)]
  ring

theorem homWt_succ (a q : ℝ) (j : ℕ+) : homWt a (q + 1) j = ((j : ℝ) + 2) * homWt a q j := by
  unfold homWt
  rw [ellWeight_succ_exponent']
  push_cast
  ring

/-- `z ∈ ℓ^N_{a,q}`: the weighted sequence `ω_{a,q}(j+2) z_j` is square summable. -/
def HomNormal (a q : ℝ) (z : ℕ+ → ℂ) : Prop :=
  Memℓp (fun j => (homWt a q j : ℂ) * z j) 2

/-- The weighted sequence of `z ∈ ℓ^N_{a,q}` as an element of `ℓ²`. -/
def homNormLp {a q : ℝ} {z : ℕ+ → ℂ} (hz : HomNormal a q z) : lp (fun _ : ℕ+ => ℂ) 2 :=
  ⟨fun j => (homWt a q j : ℂ) * z j, hz⟩

/-- The norm `‖z‖_{a,q}` on `ℓ^N_{a,q}`. -/
noncomputable def homNorm {a q : ℝ} {z : ℕ+ → ℂ} (hz : HomNormal a q z) : ℝ := ‖homNormLp hz‖

theorem homNorm_nonneg {a q : ℝ} {z : ℕ+ → ℂ} (hz : HomNormal a q z) : 0 ≤ homNorm hz :=
  norm_nonneg _

theorem norm_homNormLp_apply {a q : ℝ} {z : ℕ+ → ℂ} (hz : HomNormal a q z) (j : ℕ+) :
    ‖homNormLp hz j‖ = homWt a q j * ‖z j‖ := by
  simp [homNormLp, abs_of_pos (homWt_pos a q j)]

theorem homNorm_hasSum {a q : ℝ} {z : ℕ+ → ℂ} (hz : HomNormal a q z) :
    HasSum (fun j => (homWt a q j * ‖z j‖) ^ 2) (homNorm hz ^ 2) := by
  have := lp_two_hasSum_sq (homNormLp hz)
  unfold homNorm
  simpa only [norm_homNormLp_apply] using this


/-- Cauchy–Schwarz for nonnegative square-summable sequences. -/
theorem summable_tsum_mul_le {A B : ℕ+ → ℝ} {a b : ℝ} (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : HasSum (fun j => A j ^ 2) (a ^ 2))
    (hb : HasSum (fun j => B j ^ 2) (b ^ 2)) :
    Summable (fun j => A j * B j) ∧ ∑' j, A j * B j ≤ a * b := by
  have hA' : Summable fun j => A j ^ (2 : ℝ) := by
    simpa only [Real.rpow_two] using ha.summable
  have hB' : Summable fun j => B j ^ (2 : ℝ) := by
    simpa only [Real.rpow_two] using hb.summable
  obtain ⟨h1, h2⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two hA hB hA' hB'
  refine ⟨h1, h2.trans ?_⟩
  simp only [Real.rpow_two] at h2 ⊢
  rw [ha.tsum_eq, hb.tsum_eq]
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq ha0, Real.sqrt_sq hb0]


/-- The product of weights is at least one when `a ≥ 0` and `q + q' ≥ 0` (`J = j + 2 ≥ 1`). -/
theorem one_le_homWt_mul {a q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') (j : ℕ+) :
    1 ≤ homWt a q j * homWt a q' j := by
  unfold homWt ellWeight
  have hJ : (1 : ℝ) ≤ ((j + 2 : ℕ+) : ℝ) := by exact_mod_cast one_le (j + 2)
  have hJ0 : (0 : ℝ) ≤ ((j + 2 : ℕ+) : ℝ) := by linarith
  have h1 : (1 : ℝ) ≤ ((j + 2 : ℕ+) : ℝ) ^ (q + q') := Real.one_le_rpow hJ hqq'
  have h2 : (1 : ℝ) ≤ Real.exp (2 * a * ((j + 2 : ℕ+) : ℝ)) := Real.one_le_exp (by positivity)
  calc (1 : ℝ) ≤ ((j + 2 : ℕ+) : ℝ) ^ (q + q') * Real.exp (2 * a * ((j + 2 : ℕ+) : ℝ)) :=
        one_le_mul_of_one_le_of_one_le h1 h2
    _ = _ := by
      rw [Real.rpow_add (by linarith)]
      have : Real.exp (2 * a * ((j + 2 : ℕ+) : ℝ)) =
          Real.exp (a * ((j + 2 : ℕ+) : ℝ)) * Real.exp (a * ((j + 2 : ℕ+) : ℝ)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]; ring

/-- **The weighted pairing** (blueprint `bpW:w4:pairing`): for `a ≥ 0`, `q + q' ≥ 0`,
`∑_j |x_j x'_j| ≤ ‖x‖_{a,q} ‖x'‖_{a,q'}`; in particular `|⟨x,x'⟩₀| ≤ ‖x‖_{a,q}‖x'‖_{a,q'}`. -/
theorem homPair_le {a q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') {x x' : ℕ+ → ℂ}
    (hx : HomNormal a q x) (hx' : HomNormal a q' x') :
    Summable (fun j => ‖x j * x' j‖) ∧ ∑' j, ‖x j * x' j‖ ≤ homNorm hx * homNorm hx' := by
  obtain ⟨hs, hle⟩ := summable_tsum_mul_le
    (A := fun j => homWt a q j * ‖x j‖) (B := fun j => homWt a q' j * ‖x' j‖)
    (fun j => by have := homWt_pos a q j; positivity)
    (fun j => by have := homWt_pos a q' j; positivity)
    (homNorm_nonneg hx) (homNorm_nonneg hx') (homNorm_hasSum hx) (homNorm_hasSum hx')
  have hb : ∀ j, ‖x j * x' j‖ ≤ (homWt a q j * ‖x j‖) * (homWt a q' j * ‖x' j‖) := by
    intro j
    have h1 := one_le_homWt_mul ha hqq' j
    rw [norm_mul]
    have : (homWt a q j * ‖x j‖) * (homWt a q' j * ‖x' j‖) =
        (homWt a q j * homWt a q' j) * (‖x j‖ * ‖x' j‖) := by ring
    rw [this]
    exact le_mul_of_one_le_left (by positivity) h1
  have hsum : Summable (fun j => ‖x j * x' j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hb hs
  exact ⟨hsum, (hsum.tsum_le_tsum hb hs).trans hle⟩

theorem norm_homPair_le {a q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') {x x' : ℕ+ → ℂ}
    (hx : HomNormal a q x) (hx' : HomNormal a q' x') :
    ‖∑' j, x j * x' j‖ ≤ homNorm hx * homNorm hx' :=
  (norm_tsum_le_tsum_norm (homPair_le ha hqq' hx hx').1).trans (homPair_le ha hqq' hx hx').2


/-- **Multipliers lower the weight by one** (blueprint `bpW:w4:lie` (i), step *Bounds*): if
`|μ_j| ≤ M (j+2)` then `z ∈ ℓ^N_{a,q}` gives `μ z ∈ ℓ^N_{a,q-1}` with `‖μ z‖_{a,q-1} ≤ M ‖z‖_{a,q}`. -/
theorem homNormal_mul {a q M : ℝ} (hM : 0 ≤ M) {μ z : ℕ+ → ℂ}
    (hμ : ∀ j, ‖μ j‖ ≤ M * ((j : ℝ) + 2)) (hz : HomNormal a q z) :
    ∃ hy : HomNormal a (q - 1) (fun j => μ j * z j), homNorm hy ≤ M * homNorm hz := by
  have hterm : ∀ j, homWt a (q - 1) j * ‖μ j * z j‖ ≤ M * (homWt a q j * ‖z j‖) := by
    intro j
    have hw : homWt a q j = ((j : ℝ) + 2) * homWt a (q - 1) j := by
      have := homWt_succ a (q - 1) j
      rwa [sub_add_cancel] at this
    rw [norm_mul, hw]
    have h0 := homWt_pos a (q - 1) j
    calc homWt a (q - 1) j * (‖μ j‖ * ‖z j‖)
        ≤ homWt a (q - 1) j * (M * ((j : ℝ) + 2) * ‖z j‖) := by
          gcongr
          exact hμ j
      _ = _ := by ring
  have hmem : HomNormal a (q - 1) (fun j => μ j * z j) := by
    unfold HomNormal
    refine memℓp_gen ?_
    have hs : Summable fun j => M ^ 2 * (homWt a q j * ‖z j‖) ^ 2 :=
      ((homNorm_hasSum hz).summable).mul_left _
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hs
    have := pow_le_pow_left₀ (by have := homWt_pos a (q - 1) j; positivity) (hterm j) 2
    rw [norm_mul] at this
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (homWt_pos a (q - 1) j)]
    nlinarith [this]
  refine ⟨hmem, ?_⟩
  have hs := homNorm_hasSum hmem
  have hs2 := (homNorm_hasSum hz).mul_left (M ^ 2)
  have hle := hasSum_le (fun j => ?_) hs hs2
  · have h0 := homNorm_nonneg hmem
    have h1 := homNorm_nonneg hz
    nlinarith [sq_nonneg (homNorm hmem - M * homNorm hz), mul_nonneg hM h1]
  · calc (homWt a (q - 1) j * ‖μ j * z j‖) ^ 2 ≤ (M * (homWt a q j * ‖z j‖)) ^ 2 :=
        pow_le_pow_left₀ (by have := homWt_pos a (q - 1) j; positivity) (hterm j) 2
      _ = _ := by ring

end KAM.Wave
