/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Interfaces.HoloReal

/-!
# Zero perturbation: the real Hamiltonian and its field on the enlarged domain

Blueprint `bpN:p2:zero-deriv` with receipts `zd-zero`, `zd-diff`, `zd-field`. For an integrable `h`
and a perturbation of size `0`, on the whole enlarged real domain `W_s = ℝⁿ × B(0, R + s)` the real
Hamiltonian equals `h_ℝ ∘ snd`, is differentiable with derivative `Dh_ℝ ∘ snd`, and its Hamiltonian
vector field is `(ω(I), 0)`.
-/

public section

open Set Filter Metric
open scoped Topology

namespace KAM.Nekhoroshev

variable {n : ℕ}

section ZeroField
variable {R s : ℝ} (hR : 0 < R) (hs : 0 < s)
variable {h : (Fin n → ℂ) → ℂ} (hh : IsAnalyticIntegrable R s h)
variable {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
variable (hf : IsAnalyticPerturbation R s 0 f)
include hR hs hh hf

/-- `Wdom`, from Part 1, is the enlarged domain, not just `actionBall n R`. -/
theorem zd_zero : (∀ w ∈ complexDomain n R s, f w = 0) ∧
    (∀ z ∈ Wdom n R s, KAM.realInclusion₂ n z ∈ complexDomain n R s) ∧
    ∀ z ∈ Wdom n R s, KAM.realHamiltonian h f z = realPart h z.2 := by
  have hd : Data n R s 0 h f := ⟨hR, hs, hh, hf⟩
  refine ⟨(holo_real_e hd).1, fun z hz => ?_, (holo_real_e hd).2⟩
  rw [← realInclusion₂_preimage_complexDomain hR hs] at hz
  exact hz

theorem zd_diff (z : (Fin n → ℝ) × (Fin n → ℝ)) (hz : z ∈ Wdom n R s) :
    HasFDerivAt (KAM.realHamiltonian h f)
      ((fderiv ℝ (realPart h) z.2).comp
        (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ))) z := by
  have hz2 : z.2 ∈ realActionDomain n R s := by
    rw [realActionDomain_eq hR hs]; exact hz.2
  have hD : DifferentiableAt ℝ (realPart h) z.2 :=
    ((hh.2.2.2.2).contDiffAt ((isOpen_realActionDomain hR hs).mem_nhds hz2)).differentiableAt
      (by norm_num)
  have h1 : HasFDerivAt (fun w : (Fin n → ℝ) × (Fin n → ℝ) => realPart h w.2)
      ((fderiv ℝ (realPart h) z.2).comp
        (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ))) z :=
    hD.hasFDerivAt.comp z (hasFDerivAt_snd (𝕜 := ℝ) (E := Fin n → ℝ) (F := Fin n → ℝ) (p := z))
  have hev : (fun w : (Fin n → ℝ) × (Fin n → ℝ) => realPart h w.2) =ᶠ[𝓝 z]
      KAM.realHamiltonian h f := by
    filter_upwards [(isOpen_Wdom R s).mem_nhds hz] with w hw
    exact ((zd_zero hR hs hh hf).2.2 w hw).symm
  exact h1.congr_of_eventuallyEq hev.symm

theorem zd_field (z : (Fin n → ℝ) × (Fin n → ℝ)) (hz : z ∈ Wdom n R s) :
    KAM.hamiltonianVectorField (KAM.realHamiltonian h f) z =
      (KAM.frequencyMap h z.2, 0) := by
  unfold KAM.hamiltonianVectorField
  rw [(zd_diff hR hs hh hf z hz).fderiv]
  ext i
  · simp [KAM.frequencyMap]; rfl
  · simp

theorem zero_deriv (z : (Fin n → ℝ) × (Fin n → ℝ)) (hz : z ∈ Wdom n R s) :
    KAM.realHamiltonian h f z = realPart h z.2 ∧
    DifferentiableAt ℝ (KAM.realHamiltonian h f) z ∧
    (∀ a b, fderiv ℝ (KAM.realHamiltonian h f) z (a, b) =
      fderiv ℝ (realPart h) z.2 b) ∧
    KAM.hamiltonianVectorField (KAM.realHamiltonian h f) z =
      (KAM.frequencyMap h z.2, 0) := by
  have hd := zd_diff hR hs hh hf z hz
  exact ⟨(zd_zero hR hs hh hf).2.2 z hz, hd.differentiableAt,
    fun a b => by rw [hd.fderiv]; rfl, zd_field hR hs hh hf z hz⟩

end ZeroField

end KAM.Nekhoroshev
