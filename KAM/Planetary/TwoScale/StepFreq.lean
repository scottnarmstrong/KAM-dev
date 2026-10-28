/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.Setting
public import KAM.Nekhoroshev.NormalForm.Setting

/-!
# Two-scale KAM step: frequency-map toolbox

Openness of `actionNbhd`, differentiability of `freq h` on it, reality of the frequency at real
points, the coordinatewise mean value inequality, block versions of `dotC`, and the elementary
consequences of the constants (`rhoHat ≤ ρ`, `rhoHat ≤ γᵢ/(3·M·K^(τ+1))`, `L > 0`).
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-14 (`bpP:p3:step`).
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

theorem isOpen_actionNbhd' {n : ℕ} (D : Set (Fin n → ℝ)) (r : ℝ) :
    IsOpen (KAM.actionNbhd D r) := by
  rw [← (conv_data D r 0).1]; exact isOpen_polyNbhd _ r

theorem actionNbhd_mono {n : ℕ} {D : Set (Fin n → ℝ)} {r r' : ℝ} (h : r' ≤ r) :
    KAM.actionNbhd D r' ⊆ KAM.actionNbhd D r := by
  rw [← (conv_data D r 0).1, ← (conv_data D r' 0).1]; exact polyNbhd_mono h

theorem mem_actionNbhd_of_mem {n : ℕ} {D : Set (Fin n → ℝ)} {r : ℝ} (hr : 0 < r) {I : Fin n → ℝ}
    (hI : I ∈ D) : KAM.realInclusion n I ∈ KAM.actionNbhd D r :=
  ⟨I, hI, by
    show ‖KAM.realInclusion n I - KAM.realInclusion n I‖ < r
    simpa using hr⟩

theorem actionNbhd_ball {n : ℕ} {D : Set (Fin n → ℝ)} {r : ℝ} {J : Fin n → ℝ} (hJ : J ∈ D) :
    ball (KAM.realInclusion n J) r ⊆ KAM.actionNbhd D r := fun I hI =>
  ⟨J, hJ, by
    have h1 : ‖I - KAM.realInclusion n J‖ < r := by simpa [dist_eq_norm] using hI
    exact h1⟩

/-- Reality of the frequency at real points of the neighbourhood. -/
theorem freq_im_zero {n : ℕ} {D : Set (Fin n → ℝ)} {ρ sb : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (KAM.actionNbhd D ρ))
    (hsb : 0 < sb) (hreal : RealOn (coefficientDom D ρ sb) (fun z => h z.2)) {I : Fin n → ℝ}
    (hI : KAM.realInclusion n I ∈ KAM.actionNbhd D ρ) (i : Fin n) :
    (freq h (KAM.realInclusion n I) i).im = 0 := by
  have hopen := isOpen_actionNbhd' D ρ
  have hhd : DifferentiableAt ℂ h (KAM.realInclusion n I) :=
    hh.differentiableAt (hopen.mem_nhds hI)
  have hreal' : ∀ J : Fin n → ℝ, KAM.realInclusion n J ∈ KAM.actionNbhd D ρ →
      (h (KAM.realInclusion n J)).im = 0 := by
    intro J hJ
    have hm : KAM.realInclusion₂ n (0, J) ∈ coefficientDom D ρ sb := by
      refine ⟨fun j => ?_, ?_⟩
      · simpa [KAM.realInclusion₂_apply, geometricWidth] using div_pos hsb (by positivity)
      · simpa [KAM.realInclusion₂_apply] using
          ((conv_data D ρ 0).1.symm ▸ hJ : KAM.realInclusion n J ∈ polyNbhd (realBase D) ρ)
    simpa [KAM.realInclusion₂_apply] using hreal (0, J) hm
  set g : (Fin n → ℝ) → ℝ := fun J => (h (KAM.realInclusion n J)).re with hg
  have h2 : HasFDerivAt (fun J => h (KAM.realInclusion n J))
      (((fderiv ℂ h (KAM.realInclusion n I)).restrictScalars ℝ).comp (KAM.realInclusion n)) I :=
    (hhd.hasFDerivAt.restrictScalars ℝ).comp I ((KAM.realInclusion n).hasFDerivAt)
  have h3 : HasFDerivAt g (Complex.reCLM.comp
      (((fderiv ℂ h (KAM.realInclusion n I)).restrictScalars ℝ).comp (KAM.realInclusion n))) I :=
    Complex.reCLM.hasFDerivAt.comp I h2
  have hev : (fun J => h (KAM.realInclusion n J)) =ᶠ[nhds I] fun J => ((g J : ℝ) : ℂ) := by
    have hopen' : IsOpen ((KAM.realInclusion n) ⁻¹' KAM.actionNbhd D ρ) :=
      hopen.preimage (KAM.realInclusion n).continuous
    filter_upwards [hopen'.mem_nhds hI] with J hJ
    exact Complex.ext (by simp [hg]) (by simpa [hg] using hreal' J hJ)
  have h5 : HasFDerivAt (fun J => ((g J : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ g I)) I :=
    Complex.ofRealCLM.hasFDerivAt.comp I h3.differentiableAt.hasFDerivAt
  have h6 := (h2.congr_of_eventuallyEq hev.symm).unique h5
  have h7 := congrArg (fun L => L (Pi.single i 1)) h6
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    Complex.ofRealCLM_apply] at h7
  rw [KAM.realInclusion_single] at h7
  simp only [freq]
  rw [h7]; simp

theorem freq_realInclusion_eq {n : ℕ} {D : Set (Fin n → ℝ)} {ρ sb : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (KAM.actionNbhd D ρ))
    (hsb : 0 < sb) (hreal : RealOn (coefficientDom D ρ sb) (fun z => h z.2)) {I : Fin n → ℝ}
    (hI : KAM.realInclusion n I ∈ KAM.actionNbhd D ρ) :
    freq h (KAM.realInclusion n I) = KAM.realInclusion n (realFreq h I) := by
  funext i
  have := freq_im_zero hh hsb hreal hI i
  simp only [realFreq, KAM.realInclusion_apply]
  exact Complex.ext (by simp) (by simpa using this)

/-- Coordinatewise mean value inequality on a convex set. -/
theorem coord_mvt {n : ℕ} {s : Set (Fin n → ℂ)} (hs : Convex ℝ s) {F : (Fin n → ℂ) → (Fin n → ℂ)}
    {c : ℝ} (hc0 : 0 ≤ c) (j : Fin n) (hF : ∀ x ∈ s, DifferentiableAt ℂ F x)
    (hc : ∀ x ∈ s, ∀ v, ‖fderiv ℂ F x v j‖ ≤ c * ‖v‖) {x y : Fin n → ℂ} (hx : x ∈ s)
    (hy : y ∈ s) : ‖F x j - F y j‖ ≤ c * ‖x - y‖ := by
  have hd : ∀ z ∈ s, DifferentiableAt ℂ (fun w => F w j) z := fun z hz =>
    (differentiableAt_pi.1 (hF z hz)) j
  have hder : ∀ z ∈ s, ‖fderiv ℂ (fun w => F w j) z‖ ≤ c := by
    intro z hz
    refine ContinuousLinearMap.opNorm_le_bound _ hc0 fun v => ?_
    have : fderiv ℂ (fun w => F w j) z v = fderiv ℂ F z v j := by
      rw [fderiv_pi (fun i => (differentiableAt_pi.1 (hF z hz)) i)]; rfl
    rw [this]; exact hc z hz v
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ) hd hder hs hy hx |>.trans_eq
    (by rw [norm_sub_rev]) |> fun h => by simpa [norm_sub_rev] using h

end KAM.Planetary

end
