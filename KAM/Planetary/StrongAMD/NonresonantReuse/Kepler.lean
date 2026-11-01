/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Exponential.KeplerData
public import KAM.Planetary.StrongAMD.NonresonantScale

/-!
# Period-one Kepler data (package LP-NRR, item 1)

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
Package LP-NRR, MAIN Lemma 13 (`LP:MAIN L13 (429–464)`), track LP, non-frozen.

`lpKepler ν I = planetaryKeplerC ν I / (2π)` is the Kepler part in the period-one convention.
On `polyNbhd {I⁰} ρ` with `ρ ≤ I_min/2` (`I_min > 0` a lower bound of the coordinates of the real
centre `I⁰`) it is holomorphic, real on real points, has frequency `ω(I⁰)/(2π)` at the centre
(`ω_i = ν_i³/I_i³`) and a frequency Lipschitz constant `lpKeplerLip ν I_min` which does not depend
on `I⁰`.  Item 2 (nonresonance of the centre from (5)) is also here.
-/

@[expose] public noncomputable section

open KAM KAM.Planetary KAM.Weighted KAM.NormalForm Set

namespace KAM.Planetary.StrongAMD

variable {n : ℕ}

/-- The period-one Kepler data `h(I) = planetaryKeplerC ν I / (2π)`. -/
def lpKepler (ν : Fin n → ℝ) (I : Fin n → ℂ) : ℂ :=
  planetaryKeplerC ν I / ((2 * Real.pi : ℝ) : ℂ)

/-- A Lipschitz constant for the frequency of `lpKepler`, uniform in the centre. -/
def lpKeplerLip (ν : Fin n → ℝ) (Imin : ℝ) : ℝ :=
  ∑ i, 3 * ν i ^ 3 / (2 * Real.pi * (Imin / 2) ^ 4)

theorem lpKeplerLip_nonneg {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (Imin : ℝ) :
    0 ≤ lpKeplerLip ν Imin :=
  Finset.sum_nonneg fun i _ => by
    have := hν i
    positivity

/-- Points within `ρ ≤ I_min/2` of a centre with coordinates `≥ I_min` have real part
`≥ I_min/2`. -/
theorem lp_re_ge_of_mem_polyNbhd {I0 : Fin n → ℝ} {Imin ρ : ℝ} (hI : ∀ i, Imin ≤ I0 i)
    (hρ : ρ ≤ Imin / 2) {z : Fin n → ℂ}
    (hz : z ∈ polyNbhd {KAM.realInclusion n I0} ρ) (i : Fin n) : Imin / 2 ≤ (z i).re := by
  obtain ⟨I', hI', hlt⟩ := hz
  rw [Set.mem_singleton_iff] at hI'
  subst hI'
  have h1 : ‖z i - (I0 i : ℂ)‖ ≤ ‖z - KAM.realInclusion n I0‖ := by
    simpa using norm_le_pi_norm (z - KAM.realInclusion n I0) i
  have h2 : |(z i).re - I0 i| ≤ ‖z i - (I0 i : ℂ)‖ := by
    simpa using Complex.abs_re_le_norm (z i - (I0 i : ℂ))
  have := abs_le.1 (h2.trans (h1.trans hlt.le))
  linarith [hI i, this.1]

theorem lp_norm_ge_of_mem_polyNbhd {I0 : Fin n → ℝ} {Imin ρ : ℝ} (hI : ∀ i, Imin ≤ I0 i)
    (hρ : ρ ≤ Imin / 2) {z : Fin n → ℂ}
    (hz : z ∈ polyNbhd {KAM.realInclusion n I0} ρ) (i : Fin n) : Imin / 2 ≤ ‖z i‖ :=
  (lp_re_ge_of_mem_polyNbhd hI hρ hz i).trans (Complex.re_le_norm _)

theorem lp_ne_zero_of_mem_polyNbhd {I0 : Fin n → ℝ} {Imin ρ : ℝ} (hImin : 0 < Imin)
    (hI : ∀ i, Imin ≤ I0 i) (hρ : ρ ≤ Imin / 2) {z : Fin n → ℂ}
    (hz : z ∈ polyNbhd {KAM.realInclusion n I0} ρ) (i : Fin n) : z i ≠ 0 := fun h0 => by
  have := lp_norm_ge_of_mem_polyNbhd hI hρ hz i
  rw [h0, norm_zero] at this
  linarith

/-- Item 1, holomorphy. -/
theorem lpKepler_differentiableOn {ν : Fin n → ℝ} {I0 : Fin n → ℝ} {Imin ρ : ℝ}
    (hImin : 0 < Imin) (hI : ∀ i, Imin ≤ I0 i) (hρ : ρ ≤ Imin / 2) :
    DifferentiableOn ℂ (lpKepler ν) (polyNbhd {KAM.realInclusion n I0} ρ) := by
  have h1 : DifferentiableOn ℂ (keplerSumGen ℂ ν) {z : Fin n → ℂ | ∀ i, z i ≠ 0} :=
    (keplerSumGen_contDiffOn (𝕜 := ℂ) ν 1).differentiableOn (by norm_num)
  have h2 := (h1.mono fun z hz => lp_ne_zero_of_mem_polyNbhd hImin hI hρ hz).const_smul
    (((2 * Real.pi : ℝ) : ℂ)⁻¹)
  refine h2.congr fun x _ => ?_
  simp [lpKepler, planetaryKeplerC_eq, div_eq_inv_mul]

/-- Item 1, reality on real points. -/
theorem lpKepler_real (ν : Fin n → ℝ) (I : Fin n → ℝ) :
    (lpKepler ν (KAM.realInclusion n I)).im = 0 := by
  have : KAM.realInclusion n I = fun i => (I i : ℂ) := by
    funext i; simp
  rw [this, lpKepler, planetaryKeplerC_ofReal, ← Complex.ofReal_div]
  exact Complex.ofReal_im _

/-- The frequency of `lpKepler` at a point with nonzero coordinates. -/
theorem lpKepler_freq {ν : Fin n → ℝ} {z : Fin n → ℂ} (hz : ∀ i, z i ≠ 0) (i : Fin n) :
    freq (lpKepler ν) z i = (ν i : ℂ) ^ 3 / z i ^ 3 / (2 * Real.pi) := by
  have h : HasFDerivAt (fun x => ((2 * Real.pi : ℝ) : ℂ)⁻¹ • keplerSumGen ℂ ν x) _ z :=
    (keplerSumGen_hasFDerivAt (𝕜 := ℂ) ν hz).const_smul (((2 * Real.pi : ℝ) : ℂ)⁻¹)
  have e : lpKepler ν = fun x => ((2 * Real.pi : ℝ) : ℂ)⁻¹ • keplerSumGen ℂ ν x := by
    funext x; simp [lpKepler, planetaryKeplerC_eq, div_eq_inv_mul]
  unfold freq
  rw [e, h.fderiv]
  simp [keplerSumGenD, Pi.single_apply, div_eq_inv_mul, mul_comm]

/-- Item 1, the frequency at the centre: `freq lpKepler I⁰ = ω(I⁰)/(2π)`. -/
theorem lpKepler_freq_real {ν : Fin n → ℝ} {I0 : Fin n → ℝ} (hI : ∀ i, I0 i ≠ 0) (i : Fin n) :
    freq (lpKepler ν) (KAM.realInclusion n I0) i =
      ((ν i ^ 3 / I0 i ^ 3 / (2 * Real.pi) : ℝ) : ℂ) := by
  rw [lpKepler_freq (fun j => by simpa using hI j)]
  simp

/-- Item 1, the uniform Lipschitz bound for the frequency (`FreqLipschitz`). -/
theorem lpKepler_freqLipschitz {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {I0 : Fin n → ℝ}
    {Imin ρ : ℝ} (hImin : 0 < Imin) (hI : ∀ i, Imin ≤ I0 i) (hρ : ρ ≤ Imin / 2) :
    FreqLipschitz {KAM.realInclusion n I0} ρ (lpKeplerLip ν Imin) (lpKepler ν) := by
  intro I₀ hI₀ I hIm hlt
  rw [Set.mem_singleton_iff] at hI₀
  subst hI₀
  have hρ0 : 0 < ρ ∨ ρ ≤ 0 := lt_or_ge 0 ρ
  have hLn := lpKeplerLip_nonneg hν Imin
  have hnorm : 0 ≤ ‖I - KAM.realInclusion n I0‖ := norm_nonneg _
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  -- the one-variable mean value estimate on the ball around the centre coordinate
  set c : ℂ := (ν i : ℂ) ^ 3 / (2 * Real.pi) with hc
  set g : ℂ → ℂ := fun x => c / x ^ 3 with hg
  have hball : ∀ x ∈ Metric.ball ((I0 i : ℝ) : ℂ) ρ, Imin / 2 ≤ ‖x‖ := by
    intro x hx
    have hx' : ‖x - (I0 i : ℂ)‖ < ρ := by simpa [dist_eq_norm] using hx
    have h2 : |x.re - I0 i| ≤ ‖x - (I0 i : ℂ)‖ := by
      simpa using Complex.abs_re_le_norm (x - (I0 i : ℂ))
    have := abs_le.1 (h2.trans hx'.le)
    exact (by linarith [hI i, this.1] : Imin / 2 ≤ x.re).trans (Complex.re_le_norm _)
  have hder : ∀ x ∈ Metric.ball ((I0 i : ℝ) : ℂ) ρ,
      HasDerivWithinAt g (-3 * c / x ^ 4) (Metric.ball ((I0 i : ℝ) : ℂ) ρ) x := by
    intro x hx
    have hx0 : x ≠ 0 := fun h0 => by
      have := hball x hx
      rw [h0, norm_zero] at this
      linarith
    have h := (hasDerivAt_const x c).div (hasDerivAt_pow 3 x) (pow_ne_zero 3 hx0)
    refine (h.hasDerivWithinAt).congr_deriv ?_
    field_simp
    ring
  have hbd : ∀ x ∈ Metric.ball ((I0 i : ℝ) : ℂ) ρ,
      ‖-3 * c / x ^ 4‖ ≤ 3 * ν i ^ 3 / (2 * Real.pi * (Imin / 2) ^ 4) := by
    intro x hx
    have hxn := hball x hx
    have hνi := hν i
    have hpi := Real.pi_pos
    have hn3 : ‖-3 * c / x ^ 4‖ = 3 * (ν i ^ 3 / (2 * Real.pi)) / ‖x‖ ^ 4 := by
      simp [hc, norm_pow, abs_of_pos hνi, abs_of_pos hpi]
    rw [hn3]
    have hpos : 0 < Imin / 2 := by linarith
    calc 3 * (ν i ^ 3 / (2 * Real.pi)) / ‖x‖ ^ 4
        ≤ 3 * (ν i ^ 3 / (2 * Real.pi)) / (Imin / 2) ^ 4 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact pow_le_pow_left₀ hpos.le hxn 4
      _ = _ := by field_simp
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (convex_ball _ ρ)
    (Metric.mem_ball_self (lt_of_le_of_lt hnorm hlt))
    (show I i ∈ Metric.ball ((I0 i : ℝ) : ℂ) ρ by
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_le_of_lt (by simpa using norm_le_pi_norm (I - KAM.realInclusion n I0) i) hlt)
  have hI1 : ∀ j, I j ≠ 0 := fun j => lp_ne_zero_of_mem_polyNbhd hImin hI hρ hIm j
  have hfi : freq (lpKepler ν) I i = g (I i) := by
    rw [lpKepler_freq hI1, hg, hc]; ring
  have hf0 : freq (lpKepler ν) (KAM.realInclusion n I0) i = g (I0 i : ℂ) := by
    rw [lpKepler_freq (fun j => by simpa using (hImin.trans_le (hI j)).ne'), hg, hc]
    simp only [KAM.realInclusion_apply]; ring
  have hlin : ‖I i - (I0 i : ℂ)‖ ≤ ‖I - KAM.realInclusion n I0‖ := by
    simpa using norm_le_pi_norm (I - KAM.realInclusion n I0) i
  have hLi : 3 * ν i ^ 3 / (2 * Real.pi * (Imin / 2) ^ 4) ≤ lpKeplerLip ν Imin := by
    unfold lpKeplerLip
    exact Finset.single_le_sum (f := fun j => 3 * ν j ^ 3 / (2 * Real.pi * (Imin / 2) ^ 4))
      (fun j _ => by have := hν j; positivity) (Finset.mem_univ i)
  have hmv' : ‖g (I i) - g (I0 i : ℂ)‖ ≤ 3 * ν i ^ 3 / (2 * Real.pi * (Imin / 2) ^ 4) *
      ‖I i - (I0 i : ℂ)‖ := hmv
  have : ‖(freq (lpKepler ν) I - freq (lpKepler ν) (KAM.realInclusion n I0)) i‖ =
      ‖g (I i) - g (I0 i : ℂ)‖ := by
    simp only [Pi.sub_apply, hfi, hf0]
  rw [this]
  refine hmv'.trans ?_
  calc 3 * ν i ^ 3 / (2 * Real.pi * (Imin / 2) ^ 4) * ‖I i - (I0 i : ℂ)‖
      ≤ lpKeplerLip ν Imin * ‖I i - (I0 i : ℂ)‖ :=
        mul_le_mul_of_nonneg_right hLi (norm_nonneg _)
    _ ≤ lpKeplerLip ν Imin * ‖I - KAM.realInclusion n I0‖ :=
        mul_le_mul_of_nonneg_left hlin hLn

/-- The frequency vector `ω(I⁰)_i = ν_i³/I⁰_i³` (`LP:MAIN (4)`). -/
def lpFrequency (ν I0 : Fin n → ℝ) : Fin n → ℝ := fun i => ν i ^ 3 / I0 i ^ 3

/-- Item 2: nonresonance of the centre from the Diophantine condition (5)
(`|k · ω(I⁰)| ≥ γ |k|₁^{-τ}` for `k ≠ 0`), in the engine's form with `Λ = {0}`. -/
theorem lpKepler_isNonresonant {ν : Fin n → ℝ} {I0 : Fin n → ℝ} (hI : ∀ i, I0 i ≠ 0)
    {γ τ K : ℝ} (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    (hdio : ∀ k : Fin n → ℤ, k ≠ 0 →
      γ * KAM.Fourier.modeSize k ^ (-τ) ≤ |∑ i, (k i : ℝ) * lpFrequency ν I0 i|)
    (hK : 1 ≤ K) :
    IsNonresonant {KAM.realInclusion n I0} K (γ / (2 * Real.pi) * K ^ (-τ)) {0} (lpKepler ν) := by
  intro I hIm k hk
  rw [Set.mem_singleton_iff] at hIm
  subst hIm
  have hk0 : k ≠ 0 := fun h0 => hk.2 (by simpa using h0)
  have key := diophantine_to_period_one hγ hτ (lpFrequency ν I0) hdio hK hk0 hk.1
  have : dotC k (freq (lpKepler ν) (KAM.realInclusion n I0)) =
      ((∑ i, (k i : ℝ) * (lpFrequency ν I0 i / (2 * Real.pi)) : ℝ) : ℂ) := by
    unfold dotC
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lpKepler_freq_real hI i]
    simp [lpFrequency]
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  exact key

end KAM.Planetary.StrongAMD

end
