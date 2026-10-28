/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.FourierCutoff
public import KAM.Planetary.MaximalStep.Taylor

/-!
# The cutoff of the remainder (P11A-C4, `bpP:p11a:cutoff`)

`p11Cutoff T R = p11Cut T (p11Taylor R)`: the first-order Taylor part of `R` in the action
(`taylor_cutoff`, `M = ε`) followed by the Fourier truncation (`fourier_cutoff`, `M = 2ε`). The
bounds compose as `2(1+E_T) ε` on `D(r-d,s;B)` and `ε(q²/(1-q) + 2E_T)` for `R - R_*` on
`D(r-d,qs;B)`; reality of `R` on `D(r,s;B)` passes to the Taylor part (the real derivative of a
real-valued slice is real) and then to the truncation.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Metric
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

/-- The first-order Taylor part of a family that is real on the real points of `D(r,s;B)` is real
there. -/
theorem p11_taylor_real {n : ℕ} {r s : ℝ} (hs : 0 < s) {B : Set (P11CVec n)}
    (hB : IsOpen B) {F : P11Family n → ℂ} (hF : p11Admissible r s B F)
    (hreal : p11Real (domain_def n r s B) F) :
    p11Real (domain_def n r s B) (p11Taylor F) := by
  intro x b hxb
  obtain ⟨h1, h2, h3⟩ := p11_mem_domain_def.mp
    (show ((KAM.realInclusion n x.1, KAM.realInclusion n x.2), KAM.realInclusion n b) ∈
      domain_def n r s B from hxb)
  set θ := KAM.realInclusion n x.1 with hθ
  set η := KAM.realInclusion n x.2 with hη
  set b' := KAM.realInclusion n b with hb'
  have hDo := p11_isOpen_domain_def r s hB
  have hmem : ∀ t : ℝ, |t| < 1 → ((θ, (t : ℂ) • η), b') ∈ domain_def n r s B := by
    intro t ht
    refine p11_mem_domain_def.mpr ⟨h1, ?_, h3⟩
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |t| * ‖η‖ ≤ 1 * ‖η‖ := by gcongr
      _ < s := by simpa using h2
  have hsm : ∀ t : ℝ, (t : ℂ) • η = KAM.realInclusion n (t • x.2) := fun t => by
    rw [map_smul, ← Complex.coe_smul]
  have hrealpt : ∀ t : ℝ, |t| < 1 → (F ((θ, (t : ℂ) • η), b')).im = 0 := fun t ht => by
    have := hreal (x.1, t • x.2) b (by have := hmem t ht; rwa [hsm] at this)
    simpa [hsm] using this
  have hF0 : (F ((θ, 0), b')).im = 0 := by
    have := hrealpt 0 (by simp)
    simpa using this
  have hφ : DifferentiableAt ℂ (fun η' => F ((θ, η'), b')) 0 :=
    (p11_slice_differentiableOn hF.1 h1 h3).differentiableAt (ball_mem_nhds _ hs)
  have h1' : HasDerivAt (fun ζ : ℂ => ζ • η) η 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const η
  have h2' : HasDerivAt (fun ζ : ℂ => F ((θ, ζ • η), b'))
      (fderiv ℂ (fun η' => F ((θ, η'), b')) 0 η) ((0 : ℂ)) := by
    have h2 : HasFDerivAt (fun η' => F ((θ, η'), b')) (fderiv ℂ (fun η' => F ((θ, η'), b')) 0)
        ((fun ζ : ℂ => ζ • η) 0) := by simpa using hφ.hasFDerivAt
    exact h2.comp_hasDerivAt 0 h1'
  have h3' : HasDerivAt (fun t : ℝ => F ((θ, (t : ℂ) • η), b'))
      (fderiv ℂ (fun η' => F ((θ, η'), b')) 0 η) 0 := by
    have := HasDerivAt.comp_ofReal (z := 0) (by simpa using h2')
    simpa using this
  have h4 : HasDerivAt (fun t : ℝ => (F ((θ, (t : ℂ) • η), b')).im)
      (fderiv ℂ (fun η' => F ((θ, η'), b')) 0 η).im 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3'
  have h5 : HasDerivAt (fun t : ℝ => (F ((θ, (t : ℂ) • η), b')).im) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq (by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
      exact hrealpt t (by simpa using ht))
  have h6 := h4.unique h5
  show (F ((θ, 0), b') + fderiv ℂ (fun η' => F ((θ, η'), b')) 0 η).im = 0
  rw [Complex.add_im, h6, hF0, add_zero]

/-- `bpP:p11a:cutoff`. -/
theorem cutoff {n : ℕ} (hn : 1 ≤ n) {r s T d eps q : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hT : 0 ≤ T) (hd : 0 < d) (hdr : d < r)
    (he : 0 ≤ eps) (hq : 0 < q) (hq1 : q < 1)
    {B : Set (P11CVec n)} (hB : IsOpen B) {R : P11Family n → ℂ}
    (hR : p11Admissible r s B R) (hb : p11Bound (domain_def n r s B) R eps) :
    p11Admissible (r-d) s B (p11Cutoff T R) ∧
    p11Bound (domain_def n (r-d) s B) (p11Cutoff T R) (2*(1+p11Error n T d)*eps) ∧
    p11Bound (domain_def n (r-d) (q*s) B) (R-p11Cutoff T R)
      (eps*(q^2/(1-q)+2*p11Error n T d)) ∧
    (p11Real (domain_def n r s B) R → p11Real (domain_def n (r-d) s B) (p11Cutoff T R)) := by
  obtain ⟨hta, htb, htc, -⟩ := taylor_cutoff hr hs he hq hq1 hB hR hb
  obtain ⟨-, hfa, hfb, hfc, hfd, -⟩ :=
    fourier_cutoff hn hr hs hT hd hdr hB hta (by linarith) htb
  refine ⟨hfa, ?_, ?_, fun hreal => hfd (p11_taylor_real hs hB hR hreal)⟩
  · intro z hz
    have := hfc z hz
    calc ‖p11Cutoff T R z‖ ≤ (1 + p11Error n T d) * (2 * eps) := this
      _ = 2 * (1 + p11Error n T d) * eps := by ring
  · rintro ⟨⟨θ, η⟩, b⟩ hz
    obtain ⟨h1, h2, h3⟩ := p11_mem_domain_def.mp hz
    have hz1 : ((θ, η), b) ∈ domain_def n r (q * s) B :=
      p11_mem_domain_def.mpr ⟨fun j => (h1 j).trans (by linarith), h2, h3⟩
    have hz2 : ((θ, η), b) ∈ domain_def n (r - d) s B :=
      p11_mem_domain_def.mpr ⟨h1, h2.trans_le (by nlinarith), h3⟩
    have e1 := htc _ hz1
    have e2 := hfb _ hz2
    calc ‖(R - p11Cutoff T R) ((θ, η), b)‖
        = ‖(R - p11Taylor R) ((θ, η), b) + (p11Taylor R - p11Cut T (p11Taylor R)) ((θ, η), b)‖ := by
          simp [p11Cutoff]
      _ ≤ eps * q ^ 2 / (1 - q) + p11Error n T d * (2 * eps) := (norm_add_le _ _).trans (add_le_add e1 e2)
      _ = eps * (q ^ 2 / (1 - q) + 2 * p11Error n T d) := by ring

end KAM.Planetary
