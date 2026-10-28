/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.IterationBridge

/-! # P11B iteration: the increments on the whole collar

`stepP:p11a:il-inc`: the increments `Δh = ⟨R_{*0}⟩`, `Δω = ⟨R_{*1}⟩` are formed from the cutoff of
the remainder on the whole collar `B_ν`; they involve no divisor. Holomorphy, the sup bounds
and reality are obtained from the coefficient facts of `p11_cutoff_coeff`, without the divisor
hypothesis of the canonical step.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

theorem p11Error_nonneg {n : ℕ} (hn : 1 ≤ n) {T d : ℝ} (hd : 0 < d) : 0 ≤ p11Error n T d := by
  unfold p11Error
  have := p11C_ge_one hn
  positivity

theorem cutoff_delta {n : ℕ} (hn : 1 ≤ n) {r s T d eps : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hT : 0 ≤ T) (hd : 0 < d) (hdr : d < r)
    (he : 0 ≤ eps) {B : Set (P11CVec n)} (hB : IsOpen B) {R : P11Family n → ℂ}
    (hR : p11Admissible r s B R) (hb : p11Bound (domain_def n r s B) R eps) :
    DifferentiableOn ℂ (p11DeltaH T R) B ∧ DifferentiableOn ℂ (p11DeltaW T R) B ∧
    p11Bound B (p11DeltaH T R) ((1 + p11Error n T d) * eps) ∧
    p11Bound B (p11DeltaW T R) ((1 + p11Error n T d) * eps / s) := by
  obtain ⟨c1, c2, -, -, c5, c6, -⟩ := p11_cutoff_coeff hn hr hs hT hd hdr he hB hR hb
  have hr' : 0 < r - d := by linarith
  have hE := p11Error_nonneg (T := T) hn hd
  have hM : 0 ≤ (1 + p11Error n T d) * eps := by positivity
  refine ⟨differentiableOn_coeff hr' hB c1.1 0,
    differentiableOn_pi.2 fun i => differentiableOn_coeff hr' hB (c2 i).1 0, ?_, ?_⟩
  · intro b hb'
    have := norm_coeff_le hr' c1 c5 hb' 0
    unfold p11DeltaH p11AngleAverage
    simpa [KAM.Fourier.modeSize] using this
  · intro b hb'
    refine (pi_norm_le_iff_of_nonneg (div_nonneg hM hs.le)).2 fun i => ?_
    have c6' : p11Bound (KAM.complexStrip n (r - d) ×ˢ B) (fun z => p11R1 T R z i)
        ((1 + p11Error n T d) * eps / s) := fun z hz => (norm_le_pi_norm _ i).trans (c6 z hz)
    unfold p11DeltaW p11AngleAverage
    simpa [KAM.Fourier.modeSize] using norm_coeff_le hr' (c2 i) c6' hb' 0

theorem cutoff_R1_eq {n : ℕ} (hn : 1 ≤ n) {r s T d eps : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hT : 0 ≤ T) (hd : 0 < d) (hdr : d < r)
    (he : 0 ≤ eps) {B : Set (P11CVec n)} (hB : IsOpen B) {R : P11Family n → ℂ}
    (hR : p11Admissible r s B R) (hb : p11Bound (domain_def n r s B) R eps)
    {b : P11CVec n} (hbB : b ∈ B) (θ : P11CVec n) (i : Fin n) :
    p11R1 T R (θ, b) i = ((2 / s : ℝ) : ℂ) *
      (p11Cutoff T R ((θ, ((s / 2 : ℝ) : ℂ) • Pi.single i 1), b) -
        p11Cutoff T R ((θ, 0), b)) := by
  obtain ⟨-, -, -, -, -, -, c7⟩ := p11_cutoff_coeff hn hr hs hT hd hdr he hB hR hb
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [c7 ((θ, ((s / 2 : ℝ) : ℂ) • Pi.single i 1), b) hbB, c7 ((θ, 0), b) hbB]
  simp [Pi.single_apply]
  field_simp

theorem cutoff_delta_real {n : ℕ} (hn : 1 ≤ n) {r s T d eps : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hT : 0 ≤ T) (hd : 0 < d) (hdr : d < r)
    (he : 0 ≤ eps) {B : Set (P11CVec n)} (hB : IsOpen B) {R : P11Family n → ℂ}
    (hR : p11Admissible r s B R) (hb : p11Bound (domain_def n r s B) R eps)
    (hreal : p11Real (domain_def n r s B) R) {b : P11Vec n}
    (hbB : KAM.realInclusion n b ∈ B) :
    (p11DeltaH T R (KAM.realInclusion n b)).im = 0 ∧
      ∀ i, (p11DeltaW T R (KAM.realInclusion n b) i).im = 0 := by
  obtain ⟨-, -, -, cu4⟩ := p11_cutoff hn hr hs hT hd hdr he (q := 1 / 2) (by norm_num)
    (by norm_num) hB hR hb
  have hc := cu4 hreal
  have hr' : 0 < r - d := by linarith
  have key : ∀ x : P11Vec n,
      (p11R0 T R (KAM.realInclusion n x, KAM.realInclusion n b)).im = 0 ∧
      ∀ i, (p11R1 T R (KAM.realInclusion n x, KAM.realInclusion n b) i).im = 0 := by
    intro x
    have hmem : ∀ y : P11Vec n, ‖KAM.realInclusion n y‖ < s →
        (KAM.realInclusion₂ n (x, y), KAM.realInclusion n b) ∈
          domain_def n (r - d) s B := fun y hy =>
      p11_mem_domain_def.mpr ⟨KAM.ofReal_mem_complexStrip hr' x, hy, hbB⟩
    have h0 : ‖KAM.realInclusion n (0 : P11Vec n)‖ < s := by simpa using hs
    have c0 := hc (x, 0) b (by simpa using hmem 0 h0)
    have e0 : p11R0 T R (KAM.realInclusion n x, KAM.realInclusion n b) =
        p11Cutoff T R (KAM.realInclusion₂ n (x, 0), KAM.realInclusion n b) := by simp [p11R0]
    refine ⟨by rw [e0]; exact c0, fun i => ?_⟩
    set y : P11Vec n := Pi.single i (s / 2) with hy
    have hyc : KAM.realInclusion n y = ((s / 2 : ℝ) : ℂ) • (Pi.single i 1 : P11CVec n) := by
      ext j; by_cases hj : j = i <;> simp [hy, hj]
    have hyn : ‖KAM.realInclusion n y‖ < s := by
      rw [hyc]; exact norm_half_single hs i
    have c1 := hc (x, y) b (hmem y hyn)
    rw [cutoff_R1_eq hn hr hs hT hd hdr he hB hR hb hbB, Complex.im_ofReal_mul, ← hyc]
    have : (p11Cutoff T R ((KAM.realInclusion n x, KAM.realInclusion n y),
        KAM.realInclusion n b) -
        p11Cutoff T R ((KAM.realInclusion n x, 0), KAM.realInclusion n b)).im = 0 := by
      rw [Complex.sub_im]
      simp only [KAM.realInclusion₂_apply, map_zero] at c0 c1
      rw [c1, c0]; simp
    rw [this, mul_zero]
  exact ⟨coeff_zero_real fun x => (key x).1,
    fun i => coeff_zero_real (P := fun z => p11R1 T R z i) fun x => (key x).2 i⟩

end KAM.Planetary

end
