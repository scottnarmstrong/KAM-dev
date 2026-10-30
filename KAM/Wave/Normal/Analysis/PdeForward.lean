/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import KAM.Wave.Normal.Analysis.PdeForce

/-!
# Coefficient system `⇒` PDE (blueprint `bpW:w0n:pde-equiv` (i))

Infrastructure used by several nodes; the dependency graph is still being built.

If `q, p` are curves in `ℓ^{1,1}`, continuously differentiable into `ℓ^{1,0}`, satisfying
`q̇ = λ p`, `ṗ = -λ q - 𝒢(q)` in `ℓ^{1,0}`, then `u = U_m(q)` is a classical solution on `I` with
`u_t = V_m(p)` (`KAM.Wave.wave_coeff_to_pde`).

All series appearing are written as inner products `⟨Ψ(x), Y(t)⟩` of an analytic sine feature
`Ψ` (`KAM.Wave.sineFeatureR`, with `a = 1`, `p = 0`, multiplier `λ^{∓1/2}`) with the `ℓ²`
coordinates `Y(t) = waveEllToLp 1 0 (q t)`; this gives joint continuity and the time derivatives.
-/

@[expose] public noncomputable section

open Real
open scoped ENNReal

namespace KAM.Wave

lemma waveEll_neg {a p : ℝ} {c : ℕ+ → ℝ} (h : WaveEll a p c) : WaveEll a p (fun j => -c j) :=
  (show Summable _ from h).congr fun j => by ring

lemma sineModeIter_two (j : ℕ+) (x : ℝ) :
    sineModeIter 2 j x = -((j : ℝ) ^ 2 * sineMode j x) := by
  unfold sineModeIter sineMode
  have : (j : ℝ) * x + ((2 : ℕ) : ℝ) * π / 2 = (j : ℝ) * x + π := by push_cast; ring
  rw [this, Real.sin_add_pi]
  ring

lemma sqrt_lam_inv_mul_lam (m : ℝ) (hm : 0 < m) (j : ℕ+) :
    (Real.sqrt (lam m hm j))⁻¹ * lam m hm j = Real.sqrt (lam m hm j) := by
  have h := sqrt_lam_pos m hm j
  have h2 : Real.sqrt (lam m hm j) * Real.sqrt (lam m hm j) = lam m hm j :=
    Real.mul_self_sqrt (lt_of_lt_of_le one_pos (one_le_lam m hm j)).le
  field_simp
  linarith

section Feature

variable {β : ℕ+ → ℝ} {B ν : ℝ}

lemma waveSeries_eq_inner (hβ : PolyBounded β B ν) (k : ℕ) (x : ℝ) {c : ℕ+ → ℝ}
    (hc : WaveEll 1 0 c) :
    ∑' j, β j * c j * sineModeIter k j x =
      inner ℝ (sineFeatureR 1 0 β one_pos hβ k x) (waveEllToLp 1 0 c) := by
  have h := hasSum_inner_sineFeatureR 1 0 β one_pos hβ k x (waveEllToLp 1 0 c)
  simp only [waveEllToLp_apply_div hc] at h
  exact h.tsum_eq

lemma continuous_waveFeature (hβ : PolyBounded β B ν) (k : ℕ) :
    Continuous (sineFeatureR 1 0 β one_pos hβ k) :=
  continuous_iff_continuousAt.2 fun x => (sineFeatureR_analyticAt 1 0 β one_pos hβ k x).continuousAt

lemma waveSeries_hasDerivAt (hβ : PolyBounded β B ν) (k : ℕ) (x : ℝ) {I : Set ℝ}
    (hI : IsOpen I) {c : ℝ → ℕ+ → ℝ} (hc : ∀ s ∈ I, WaveEll 1 0 (c s)) {t : ℝ} (ht : t ∈ I)
    {Y' : lp (fun _ : ℕ+ => ℝ) 2}
    (hY : HasDerivAt (fun s => waveEllToLp 1 0 (c s)) Y' t) :
    HasDerivAt (fun s => ∑' j, β j * c s j * sineModeIter k j x)
      (inner ℝ (sineFeatureR 1 0 β one_pos hβ k x) Y') t := by
  have h1 := (innerSL ℝ (sineFeatureR 1 0 β one_pos hβ k x)).hasFDerivAt.comp_hasDerivAt t hY
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hI.mem_nhds ht] with s hs
  simp [waveSeries_eq_inner hβ k x (hc s hs)]

lemma waveSeries_continuousOn (hβ : PolyBounded β B ν) (k : ℕ) {I : Set ℝ}
    {Y : ℝ → lp (fun _ : ℕ+ => ℝ) 2} (hY : ContinuousOn Y I) :
    ContinuousOn (fun z : ℝ × ℝ => inner ℝ (sineFeatureR 1 0 β one_pos hβ k z.2) (Y z.1))
      (I ×ˢ Set.Icc 0 π) :=
  ContinuousOn.inner ((continuous_waveFeature hβ k).comp continuous_snd).continuousOn
    (hY.comp continuousOn_fst (fun z hz => hz.1))

end Feature

/-- The identity `u_tt = u_xx - m u - u³` in series form. -/
theorem wave_pde_identity (m : ℝ) (hm : 0 < m) {c : ℕ+ → ℝ} (hc : WaveEll 1 1 c) (x : ℝ)
    (hx : x ∈ Set.Icc 0 π) :
    waveSineSeries 0 (fun j => Real.sqrt (lam m hm j) *
        (-(lam m hm j * c j) - waveCubic m hm c j)) x =
      waveSineSeries 2 (waveHat m hm c) x - m * waveU m hm c x - waveU m hm c x ^ 3 := by
  have hhat := waveEll_waveHat m hm hc
  have hsA : Summable fun j : ℕ+ => waveHat m hm c j * sineModeIter 2 j x :=
    summable_waveSineSeries (waveEll_summable_pow_mul one_pos hhat 2) x
  have hsB : Summable fun j : ℕ+ => waveHat m hm c j * sineModeIter 0 j x :=
    summable_waveSineSeries (by simpa using waveEll_summable_pow_mul one_pos hhat 0) x
  have hsC : Summable fun j : ℕ+ =>
      (Real.sqrt (lam m hm j) * waveCubic m hm c j) * sineModeIter 0 j x :=
    summable_waveSineSeries (by simpa using summable_abs_sqrtLam_waveCubic m hm hc) x
  rw [wave_force_identity m hm hc x hx, waveU_eq_series]
  unfold waveSineSeries
  rw [← tsum_mul_left, ← hsA.tsum_sub (hsB.mul_left m), ← (hsA.sub (hsB.mul_left m)).tsum_sub hsC]
  refine tsum_congr fun j => ?_
  have hl := sqrt_lam_pos m hm j
  have h2 : Real.sqrt (lam m hm j) * Real.sqrt (lam m hm j) = lam m hm j :=
    Real.mul_self_sqrt (lt_of_lt_of_le one_pos (one_le_lam m hm j)).le
  have h3 : lam m hm j ^ 2 = (j : ℝ) ^ 2 + m := by
    unfold lam; rw [Real.sq_sqrt (by positivity)]
  have h4 : (j : ℝ) ^ 2 = (Real.sqrt (lam m hm j)) ^ 4 - m := by
    nlinarith [h2, h3]
  simp only [waveHat, sineModeIter_two, sineModeIter_zero]
  generalize Real.sqrt (lam m hm j) = s at hl h2 h4 ⊢
  rw [h4, ← h2]
  field_simp
  ring

lemma waveU_eq_betaU_series (m : ℝ) (hm : 0 < m) (c : ℕ+ → ℝ) (k : ℕ) (x : ℝ) :
    waveSineSeries k (waveHat m hm c) x = ∑' j, betaU m hm j * c j * sineModeIter k j x := by
  unfold waveSineSeries waveHat betaU
  exact tsum_congr fun j => by rw [div_eq_inv_mul]

lemma waveV_eq_betaV_series (m : ℝ) (hm : 0 < m) (c : ℕ+ → ℝ) (x : ℝ) :
    waveV m hm c x = ∑' j, betaV m hm j * c j * sineModeIter 0 j x := by
  unfold waveV betaV
  exact tsum_congr fun j => by rw [sineModeIter_zero]

/-- `bpW:w0n:pde-equiv` (i): the coefficient system gives a classical solution with
`u_t = V_m(p)`. The continuity of `q, p` into `ℓ^{1,1}` is not needed in the proof; it is part
of the blueprint hypothesis. -/
theorem wave_coeff_to_pde (m : ℝ) (hm : 0 < m) {I : Set ℝ} (hI : IsOpen I)
    {q p : ℝ → ℕ+ → ℝ}
    (hq : ∀ t ∈ I, WaveEll 1 1 (q t)) (hp : ∀ t ∈ I, WaveEll 1 1 (p t))
    (_hqc : ContinuousOn (fun t => waveEllToLp 1 1 (q t)) I)
    (_hpc : ContinuousOn (fun t => waveEllToLp 1 1 (p t)) I)
    (hqd : ContDiffOn ℝ 1 (fun t => waveEllToLp 1 0 (q t)) I)
    (hpd : ContDiffOn ℝ 1 (fun t => waveEllToLp 1 0 (p t)) I)
    (hqe : ∀ t ∈ I, deriv (fun s => waveEllToLp 1 0 (q s)) t =
      waveEllToLp 1 0 (fun j => lam m hm j * p t j))
    (hpe : ∀ t ∈ I, deriv (fun s => waveEllToLp 1 0 (p s)) t =
      waveEllToLp 1 0 (fun j => -(lam m hm j * q t j) - waveCubic m hm (q t) j)) :
    ∃ ut ux utt uxx : ℝ → ℝ → ℝ,
      IsClassicalSolutionWith m (fun t x => waveU m hm (q t) x) ut ux utt uxx I ∧
      ∀ t ∈ I, ∀ x ∈ Set.Icc 0 π, ut t x = waveV m hm (p t) x := by
  have hq0 : ∀ t ∈ I, WaveEll 1 0 (q t) := fun t ht => waveEll_mono (by norm_num) (hq t ht)
  have hp0 : ∀ t ∈ I, WaveEll 1 0 (p t) := fun t ht => waveEll_mono (by norm_num) (hp t ht)
  have hlq : ∀ t ∈ I, WaveEll 1 0 (fun j => lam m hm j * q t j) := fun t ht => by
    simpa using waveEll_lam_mul m hm (hq t ht)
  have hlp : ∀ t ∈ I, WaveEll 1 0 (fun j => lam m hm j * p t j) := fun t ht => by
    simpa using waveEll_lam_mul m hm (hp t ht)
  have hR : ∀ t ∈ I, WaveEll 1 0
      (fun j => -(lam m hm j * q t j) - waveCubic m hm (q t) j) := fun t ht =>
    waveEll_sub (waveEll_neg (hlq t ht))
      (waveEll_mono (by norm_num) (waveEll_waveCubic m hm (hq t ht)))
  have hYq : ∀ t ∈ I, HasDerivAt (fun s => waveEllToLp 1 0 (q s))
      (deriv (fun s => waveEllToLp 1 0 (q s)) t) t := fun t ht =>
    ((hqd.differentiableOn (by norm_num)).differentiableAt (hI.mem_nhds ht)).hasDerivAt
  have hYp : ∀ t ∈ I, HasDerivAt (fun s => waveEllToLp 1 0 (p s))
      (deriv (fun s => waveEllToLp 1 0 (p s)) t) t := fun t ht =>
    ((hpd.differentiableOn (by norm_num)).differentiableAt (hI.mem_nhds ht)).hasDerivAt
  have hdYpc : ContinuousOn (deriv fun s => waveEllToLp 1 0 (p s)) I :=
    hpd.continuousOn_deriv_of_isOpen hI le_rfl
  have eU : ∀ t ∈ I, ∀ (k : ℕ) (x : ℝ), waveSineSeries k (waveHat m hm (q t)) x =
      inner ℝ (sineFeatureR 1 0 (betaU m hm) one_pos (polyBounded_betaU m hm) k x)
        (waveEllToLp 1 0 (q t)) := fun t ht k x => by
    rw [waveU_eq_betaU_series]
    exact waveSeries_eq_inner (polyBounded_betaU m hm) k x (hq0 t ht)
  have eV : ∀ t ∈ I, ∀ x : ℝ, waveV m hm (p t) x =
      inner ℝ (sineFeatureR 1 0 (betaV m hm) one_pos (polyBounded_betaV m hm) 0 x)
        (waveEllToLp 1 0 (p t)) := fun t ht x => by
    rw [waveV_eq_betaV_series]
    exact waveSeries_eq_inner (polyBounded_betaV m hm) 0 x (hp0 t ht)
  have eT : ∀ t ∈ I, ∀ x : ℝ, waveSineSeries 0 (fun j => Real.sqrt (lam m hm j) *
      (-(lam m hm j * q t j) - waveCubic m hm (q t) j)) x =
      inner ℝ (sineFeatureR 1 0 (betaV m hm) one_pos (polyBounded_betaV m hm) 0 x)
        (deriv (fun s => waveEllToLp 1 0 (p s)) t) := fun t ht x => by
    rw [hpe t ht]
    exact waveSeries_eq_inner (polyBounded_betaV m hm) 0 x (hR t ht)
  refine ⟨fun t x => waveV m hm (p t) x,
    fun t x => waveSineSeries 1 (waveHat m hm (q t)) x,
    fun t x => waveSineSeries 0 (fun j => Real.sqrt (lam m hm j) *
      (-(lam m hm j * q t j) - waveCubic m hm (q t) j)) x,
    fun t x => waveSineSeries 2 (waveHat m hm (q t)) x, ⟨?_, ?_, ?_⟩, fun t _ x _ => rfl⟩
  · intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · refine (waveSeries_continuousOn (polyBounded_betaU m hm) 0 hqd.continuousOn).congr ?_
      intro z hz
      show waveU m hm (q z.1) z.2 = _
      rw [waveU_eq_series]; exact eU z.1 hz.1 0 z.2
    · refine (waveSeries_continuousOn (polyBounded_betaV m hm) 0 hpd.continuousOn).congr ?_
      intro z hz
      exact eV z.1 hz.1 z.2
    · refine (waveSeries_continuousOn (polyBounded_betaU m hm) 1 hqd.continuousOn).congr ?_
      intro z hz
      exact eU z.1 hz.1 1 z.2
    · refine (waveSeries_continuousOn (polyBounded_betaV m hm) 0 hdYpc).congr ?_
      intro z hz
      exact eT z.1 hz.1 z.2
    · refine (waveSeries_continuousOn (polyBounded_betaU m hm) 2 hqd.continuousOn).congr ?_
      intro z hz
      exact eU z.1 hz.1 2 z.2
  · intro t ht x hx
    have hhat := waveEll_waveHat m hm (hq t ht)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have h := waveSeries_hasDerivAt (polyBounded_betaU m hm) 0 x hI (c := q) hq0 ht (hYq t ht)
      rw [hqe t ht, ← waveSeries_eq_inner (polyBounded_betaU m hm) 0 x (hlp t ht)] at h
      have e1 : (fun s => waveU m hm (q s) x) =
          fun s => ∑' j, betaU m hm j * q s j * sineModeIter 0 j x :=
        funext fun s => by rw [waveU_eq_series, waveU_eq_betaU_series]
      have e2 : ∑' j, betaU m hm j * (lam m hm j * p t j) * sineModeIter 0 j x =
          waveV m hm (p t) x := by
        rw [waveV_eq_betaV_series]
        refine tsum_congr fun j => ?_
        simp only [betaU, betaV]
        rw [← mul_assoc, sqrt_lam_inv_mul_lam]
      rw [e1]; rwa [e2] at h
    · have h := waveSeries_hasDerivAt (polyBounded_betaV m hm) 0 x hI (c := p) hp0 ht (hYp t ht)
      rw [hpe t ht, ← waveSeries_eq_inner (polyBounded_betaV m hm) 0 x (hR t ht)] at h
      have e1 : (fun s => waveV m hm (p s) x) =
          fun s => ∑' j, betaV m hm j * p s j * sineModeIter 0 j x :=
        funext fun s => waveV_eq_betaV_series m hm (p s) x
      rw [e1]; exact h
    · show HasDerivWithinAt (waveU m hm (q t)) _ _ x
      rw [waveU_eq_series]
      exact (hasDerivAt_waveSineSeries (k := 0) (waveEll_summable_pow_mul one_pos hhat 1)
        x).hasDerivWithinAt
    · exact (hasDerivAt_waveSineSeries (k := 1) (waveEll_summable_pow_mul one_pos hhat 2)
        x).hasDerivWithinAt
    · exact wave_pde_identity m hm (hq t ht) x hx
  · intro t ht
    show waveU m hm (q t) 0 = 0 ∧ waveU m hm (q t) π = 0
    rw [waveU_eq_series]
    exact ⟨waveSineSeries_zero_apply _, waveSineSeries_pi _⟩

end KAM.Wave

end
