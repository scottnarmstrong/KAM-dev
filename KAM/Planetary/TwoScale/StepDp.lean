/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.StepNext

/-!
# Two-scale KAM step: the new base set `D₊ = ĩ₊(D)` (`stepP:p3:st-ihat`, `st-const`)

`D₊` is the image of `D` under the real part of `ĩ₊`. Generic facts: `ĩ₊` real on `D` makes
`D₊ ⊆ ℝⁿ` sit in the tube of `D`, the neighbourhood inclusion `(D₊)_{R/16} ⊆ D_{R/8}`, the
frequency image `ω₊(D₊) = ω₀(D)`, and the block constants. Design package P23-14.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

section Generic

variable {n : ℕ} {D : Set (Fin n → ℝ)} {ihat : (Fin n → ℂ) → (Fin n → ℂ)}

theorem realInclusion_re {ι : Type*} [Fintype ι] (v : ι → ℂ) (hv : ∀ i, (v i).im = 0) :
    (fun i => (((v i).re : ℝ) : ℂ)) = v := by
  funext i; exact Complex.ext (by simp) (by simpa using (hv i).symm)

theorem dp_realInclusion (hreal : ∀ I ∈ D, ∀ i, (ihat (KAM.realInclusion n I) i).im = 0)
    {I : Fin n → ℝ} (hI : I ∈ D) :
    KAM.realInclusion n (fun j => (ihat (KAM.realInclusion n I) j).re) =
      ihat (KAM.realInclusion n I) := by
  funext i
  exact congrFun (realInclusion_re _ (hreal I hI)) i

theorem dp_subset_tube {r : ℝ} (hreal : ∀ I ∈ D, ∀ i, (ihat (KAM.realInclusion n I) i).im = 0)
    (hball : ∀ I ∈ D, ihat (KAM.realInclusion n I) ∈ Metric.ball (KAM.realInclusion n I) r) :
    (fun I => fun j => (ihat (KAM.realInclusion n I) j).re) '' D ⊆ realTube D r := by
  rintro _ ⟨I, hI, rfl⟩
  show KAM.realInclusion n _ ∈ KAM.actionNbhd D r
  rw [dp_realInclusion hreal hI]
  have e : KAM.realInclusion n I = fun i => (I i : ℂ) := by funext i; simp
  have := hball I hI
  rw [mem_ball, dist_eq_norm, e] at this
  exact ⟨I, hI, this⟩

theorem dp_nbhd_subset {r r' : ℝ} {Dp : Set (Fin n → ℝ)} (hDp : Dp ⊆ realTube D r) :
    KAM.actionNbhd Dp r' ⊆ KAM.actionNbhd D (r + r') := by
  rintro z ⟨x, hx, hz⟩
  obtain ⟨J, hJ, hxJ⟩ := hDp hx
  refine ⟨J, hJ, ?_⟩
  calc ‖z - fun i => (J i : ℂ)‖ = ‖(z - KAM.realInclusion n x) +
        (KAM.realInclusion n x - fun i => (J i : ℂ))‖ := by congr 1; funext i; simp
    _ ≤ ‖z - KAM.realInclusion n x‖ + ‖KAM.realInclusion n x - fun i => (J i : ℂ)‖ :=
        norm_add_le _ _
    _ < r' + r := add_lt_add hz hxJ
    _ = r + r' := add_comm _ _

theorem dp_freq_image {hp h : (Fin n → ℂ) → ℂ}
    (hreal : ∀ I ∈ D, ∀ i, (ihat (KAM.realInclusion n I) i).im = 0)
    (hfr : ∀ I ∈ D, freq hp (ihat (KAM.realInclusion n I)) = freq h (KAM.realInclusion n I)) :
    realFreq hp '' ((fun I => fun j => (ihat (KAM.realInclusion n I) j).re) '' D) =
      realFreq h '' D := by
  rw [Set.image_image]
  refine Set.image_congr fun I hI => ?_
  funext i
  simp only [realFreq]
  rw [dp_realInclusion hreal hI, hfr I hI]

end Generic

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

namespace KamHyp

/-- Block constants: `10 c E / R ≤ 10 (c / M̄) Ê R` since `M̄ ≤ L`. -/
theorem ihat_const (H : KamHyp D sbar p h f) {c : ℝ} (hc : 0 ≤ c) :
    10 * c * p.E / rhoHat p ≤ 10 * (c / p.Mbar) * eHat p * rhoHat p := by
  have hR := H.R_pos
  have hMb := H.positive.2.2.2.2.2.2.1
  have hLb : p.Mbar ≤ p.L := (le_max_left _ _).trans H.L_bound
  have hE := H.positive.2.2.2.1
  have e : 10 * (c / p.Mbar) * eHat p * rhoHat p = 10 * c * p.E * p.L / (p.Mbar * rhoHat p) := by
    rw [eHat_eq]; field_simp
  rw [e, div_le_div_iff₀ hR (by positivity)]
  have : 0 ≤ 10 * c * p.E := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hLb this]

end KamHyp

end KAM.Planetary

end
