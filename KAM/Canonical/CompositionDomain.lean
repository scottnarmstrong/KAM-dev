/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Canonical.Adjoint
public import KAM.Canonical.Flow
public import KAM.Canonical.VectorField
public import KAM.Weighted.Domains
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Composition with the time-one map: premises and domain (`bpN:p5:composition` (i))

Blueprint-N Part 5, node `bpN:p5:composition` (design `docs/tracks/N/design/PART145-LEAN-DESIGN.md`,
package C5-8).

* `KAM.Canonical.ComposeData`: the source premises `0 < ρ < r ≤ r' - ρ`, `0 < σ < s ≤ s' - σ`,
  `φ ∈ O(r', s')` of finite norm `Φ ≥ 0`, `η = 2Φ/(ρσ) ≤ 1/2`; `.omega` is `Ω = 𝒟_{r'-ρ, s'-σ}`
  and `.gauge` the gauge `ν_{ρ,σ}`;
* `KAM.Canonical.composition_domain`: (i) the size of the field on `Ω`, the `SmallField` hypotheses
  of the flow, the inclusion `𝒟_{r-ρ, s-σ} ⊆ Ω^{1/2}` and the invariance
  `X^t(𝒟_{r-ρ, s-σ}) ⊆ 𝒟_{r, s}`;
* `KAM.Canonical.ComposeData.flow_mem_hat`: the trajectories even stay in the smaller loss
  `𝒟_{r-ρ+ρ/4, s-σ+σ/4}` (used for the remainder of the Lie series).
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Canonical

open KAM.Weighted

variable {n : ℕ}

/-- The source premises of `bpN:p5:composition`: `0<ρ<r≤r'-ρ`, `0<σ<s≤s'-σ`, `φ ∈ Os r' s'` of
finite norm `Φ`, `η = 2Φ/(ρσ) ≤ 1/2`. -/
structure ComposeData (D : Set (Fin n → ℂ)) (r s r' s' ρ σ Φ : ℝ)
    (φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : Prop where
  hρ : 0 < ρ
  hρr : ρ < r
  hr : r ≤ r' - ρ
  hσ : 0 < σ
  hσs : σ < s
  hs : s ≤ s' - σ
  φ_class : InClass D r' s' φ
  Φ_nonneg : 0 ≤ Φ
  φ_bound : WBound D r' s' φ Φ
  eta_le : 2 * Φ / (ρ * σ) ≤ 1 / 2

/-- `Ω = 𝒟_{r'-ρ, s'-σ}` and the gauge `ν_{ρ,σ}` of `bpN:p5:composition`. -/
def ComposeData.omega {D : Set (Fin n → ℂ)} {r s r' s' ρ σ Φ : ℝ}
    {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (_ : ComposeData D r s r' s' ρ σ Φ φ) :
    Set ((Fin n → ℂ) × (Fin n → ℂ)) := Dom n D (r' - ρ) (s' - σ)

def ComposeData.gauge {D : Set (Fin n → ℂ)} {r s r' s' ρ σ Φ : ℝ}
    {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hd : ComposeData D r s r' s' ρ σ Φ φ) :
    ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ)) :=
  scaleCLE ρ σ hd.hρ hd.hσ

/-- A point at scaled distance `≤ c` from `𝒟_{r₀, s₀}` lies in `𝒟_{r₀ + ρ c, s₀ + σ c}`. -/
theorem mem_Dom_of_scaledNorm_le {D : Set (Fin n → ℂ)} {ρ σ c r₀ s₀ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ)
    (hc : 0 < c) (hr₀ : 0 < r₀) (hs₀ : 0 < s₀) {z w : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ Dom n D r₀ s₀) (hw : scaledNorm ρ σ (w - z) ≤ c) :
    w ∈ Dom n D (r₀ + ρ * c) (s₀ + σ * c) := by
  have h1 : ‖w.1 - z.1‖ / σ ≤ c := (le_max_left _ _).trans hw
  have h2 : ‖w.2 - z.2‖ / ρ ≤ c := (le_max_right _ _).trans hw
  refine polydisc_subset_Dom hr₀ (by nlinarith) hs₀ (by nlinarith) hz ⟨?_, ?_⟩
  · rw [div_le_iff₀ hσ] at h1
    linarith
  · rw [div_le_iff₀ hρ] at h2
    linarith

namespace ComposeData

variable {D : Set (Fin n → ℂ)} {r s r' s' ρ σ Φ : ℝ} {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

theorem scaledNorm_field_le (hd : ComposeData D r s r' s' ρ σ Φ φ) :
    ∀ z ∈ hd.omega, scaledNorm ρ σ (KAM.hamiltonianVectorFieldℂ φ z) ≤ Φ / (ρ * σ) := fun z hz =>
  (vf_bound hd.φ_class hd.φ_bound hd.hρ (by linarith [hd.hρ, hd.hρr, hd.hr]) hd.hσ
    (by linarith [hd.hσ, hd.hσs, hd.hs]) z hz).2.2

theorem phi_div_le (hd : ComposeData D r s r' s' ρ σ Φ φ) : Φ / (ρ * σ) ≤ 1 / 4 := by
  have := hd.eta_le
  have h : 2 * Φ / (ρ * σ) = 2 * (Φ / (ρ * σ)) := by ring
  linarith

theorem phi_div_nonneg (hd : ComposeData D r s r' s' ρ σ Φ φ) : 0 ≤ Φ / (ρ * σ) :=
  div_nonneg hd.Φ_nonneg (mul_pos hd.hρ hd.hσ).le

theorem smallField (hd : ComposeData D r s r' s' ρ σ Φ φ) :
    SmallField hd.gauge hd.omega (KAM.hamiltonianVectorFieldℂ φ) (Φ / (ρ * σ)) where
  isOpen := isOpen_Dom _ _ _
  differentiableOn := differentiableOn_hamField (isOpen_Dom _ _ _)
    (hd.φ_class.differentiableOn.mono (Dom_mono (by linarith [hd.hρ]) (by linarith [hd.hσ])))
  eps_nonneg := hd.phi_div_nonneg
  eps_le := hd.phi_div_le.trans (by norm_num)
  bound z hz := by
    have := hd.scaledNorm_field_le z hz
    rwa [ComposeData.gauge, norm_scaleCLE]

/-- The closed gauge ball of radius `1/4` around a point of `𝒟_{r-ρ, s-σ}` lies in the smaller
loss `𝒟_{r-ρ+ρ/4, s-σ+σ/4}`. -/
theorem flow_mem_hat (hd : ComposeData D r s r' s' ρ σ Φ φ) {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ Dom n D (r - ρ) (s - σ)) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z ∈
      Dom n D (r - ρ + ρ * (1 / 4)) (s - σ + σ * (1 / 4)) := by
  have hz1 : z ∈ gaugeInterior hd.gauge hd.omega (1 / 2) := by
    intro w hw
    have hw' : scaledNorm ρ σ (w - z) ≤ 1 / 2 := by
      rwa [ComposeData.gauge, norm_scaleCLE] at hw
    have := mem_Dom_of_scaledNorm_le hd.hρ hd.hσ (by norm_num : (0 : ℝ) < 1 / 2)
      (by linarith [hd.hρr]) (by linarith [hd.hσs]) hz hw'
    exact Dom_mono (by nlinarith [hd.hr, hd.hρ]) (by nlinarith [hd.hs, hd.hσ]) this
  have hb := (flow_a hd.smallField hz1).2.2.2 t ht
  have hle : |t| * (Φ / (ρ * σ)) ≤ 1 / 4 :=
    (mul_le_of_le_one_left hd.phi_div_nonneg (abs_le.2 ht)).trans hd.phi_div_le
  refine mem_Dom_of_scaledNorm_le hd.hρ hd.hσ (by norm_num : (0 : ℝ) < 1 / 4)
    (by linarith [hd.hρr]) (by linarith [hd.hσs]) hz ?_
  rw [ComposeData.gauge, norm_scaleCLE] at hb
  exact hb.trans hle

theorem gaugeInterior_half (hd : ComposeData D r s r' s' ρ σ Φ φ) :
    Dom n D (r - ρ) (s - σ) ⊆ gaugeInterior hd.gauge hd.omega (1 / 2) := by
  intro z hz w hw
  have hw' : scaledNorm ρ σ (w - z) ≤ 1 / 2 := by
    rwa [ComposeData.gauge, norm_scaleCLE] at hw
  have := mem_Dom_of_scaledNorm_le hd.hρ hd.hσ (by norm_num : (0 : ℝ) < 1 / 2)
    (by linarith [hd.hρr]) (by linarith [hd.hσs]) hz hw'
  exact Dom_mono (by nlinarith [hd.hr, hd.hρ]) (by nlinarith [hd.hs, hd.hσ]) this

end ComposeData

/-- `bpN:p5:composition` (i) (`Canonical/Composition.lean`). -/
theorem composition_domain {D : Set (Fin n → ℂ)} {r s r' s' ρ σ Φ : ℝ}
    {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hd : ComposeData D r s r' s' ρ σ Φ φ) :
    (∀ z ∈ hd.omega, scaledNorm ρ σ (KAM.hamiltonianVectorFieldℂ φ z) ≤ (2 * Φ / (ρ * σ)) / 2) ∧
    SmallField hd.gauge hd.omega (KAM.hamiltonianVectorFieldℂ φ) (Φ / (ρ * σ)) ∧
    Dom n D (r - ρ) (s - σ) ⊆ gaugeInterior hd.gauge hd.omega (1 / 2) ∧
    ∀ z ∈ Dom n D (r - ρ) (s - σ), ∀ t ∈ Icc (-1 : ℝ) 1,
      flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z ∈ Dom n D r s := by
  refine ⟨fun z hz => ?_, hd.smallField, hd.gaugeInterior_half, fun z hz t ht => ?_⟩
  · have := hd.scaledNorm_field_le z hz
    have h : (2 * Φ / (ρ * σ)) / 2 = Φ / (ρ * σ) := by ring
    rwa [h]
  · refine Dom_mono ?_ ?_ (hd.flow_mem_hat hz ht)
    · nlinarith [hd.hρ]
    · nlinarith [hd.hσ]

end KAM.Canonical

end
