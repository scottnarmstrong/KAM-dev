/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Linear.Defs
public import KAM.Apost.Geometry
public import KAM.Apost.PerturbationTorsion
import Mathlib.Tactic.Linarith

/-!
# Part 1 (isoenergetic linear step): geometry and perturbation without the twist condition

Blueprint nodes `bpI:p1:geometry-noA5` and `bpI:p1:perturbation-noA5`.

The isoenergetic problem has no (A5) (the Kolmogorov twist condition on `⟨T⟩`); it is replaced
by the bordered twist condition (B5), which lives on the bordered matrix. The geometric and the
perturbative estimates of the Kolmogorov `KAM.Apost` never use (A5) except in the last item of
the perturbation lemma, so they are re-assembled here from its helper lemmas:

* `geometry_noA5` is `KAM.Apost.geometry` (the bounds on `DE`, `∂_ω Ω_K`, `E_red`, `Ω_K`,
  `E_sym`) together with `KAM.Apost.frame_basic` (b)-(d) (the pointwise frame bounds, the bounds
  on `η^L`, `η^N` and, under `‖ω‖ ≤ Θ`, on `X_N` and `T`), for `AdmissibleNoTwist` data.
* `perturbation_noA5` is items (a)-(e) of `KAM.Apost.perturbation` (the domain, the derivative,
  the Gram matrix and normal-frame perturbation, the torsion perturbation), without its twist
  hypothesis `hT` and its item (f).

The standing data is `Setting` (`Setting.toStanding` is `KAM.Apost.Standing`).
-/

@[expose] public section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.Iso.Linear

open KAM KAM.Torus KAM.Apost

variable {n : ℕ}

section Frame

variable {τ M σK σB σT γ : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ}

/-- `bpI:p1:geometry-noA5`: the conclusions of `KAM.Apost.geometry` and of
`KAM.Apost.frame_basic` (b)–(d), without any torsion hypothesis. -/
theorem geometry_noA5 (hS : Setting n τ M σK σB σT D H ω γ) {r β ε δ : ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : AdmissibleNoTwist σK σB D H ω r β ε K)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h2δ : 2 * δ < r) :
    (∀ θ ∈ complexStrip n (r - δ),
      ‖errDerivMat H K ω θ‖ ≤ n * ε / δ ∧ ‖(errDerivMat H K ω θ)ᵀ‖ ≤ 2 * n * ε / δ ∧
      ‖fderiv ℂ (lagrangeMat K) θ (fun l => (ω l : ℂ))‖ ≤
        2 * n * (n + 1) * mSize M σK σB σT * ε / δ ∧
      ‖redDefect H K ω θ‖ ≤ C_red n M σK σB σT * ε / δ) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖lagrangeMat K θ‖ ≤ C_Omega n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) ∧
      ‖symDefect K θ‖ ≤ C_sym n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1))) ∧
    (∀ θ ∈ complexStrip n r, ‖etaL H K ω θ‖ ≤ 2 * n * mSize M σK σB σT ^ 2 * ε ∧
      ‖etaN H K ω θ‖ ≤ 2 * n * mSize M σK σB σT * ε ∧ ‖tangentMat K θ‖ ≤ mSize M σK σB σT ∧
      ‖(gramMatrix K θ)⁻¹‖ ≤ mSize M σK σB σT ∧ ‖normalMat K θ‖ ≤ mSize M σK σB σT ^ 2 ∧
      ‖frameMat K θ‖ ≤ 2 * mSize M σK σB σT ^ 2) ∧
    (‖ω‖ ≤ Theta n M σK σB σT → ∀ θ ∈ complexStrip n (r - δ),
      ‖normalFieldMat H K ω θ‖ ≤ C_X n M σK σB σT / δ ∧
        ‖torsion H K ω θ‖ ≤ C_T n M σK σB σT / δ) := by
  have hSt := hS.toStanding
  have hr := hK.r_pos
  have hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ D := fun θ hθ =>
    hK.ball_sub θ hθ (Metric.mem_ball_self hK.β_pos)
  obtain ⟨hdiff, hper, havg, hbound⟩ := Geometry.geo_omegak_inputs hSt hr hK.holo hK.primary hK𝔅
    hK.deriv_le hK.error_le hδ
  have hΩ : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖lagrangeMat K θ‖ ≤ C_Omega n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) := by
    intro θ hθ
    have hθ' : θ ∈ complexStrip n (r - δ - δ) := by
      have : r - δ - δ = r - 2 * δ := by ring
      rw [this]
      exact hθ
    have hcoh := (KAM.Apost.cohomological hSt (r := r - δ) (δ := δ) (by linarith) hδ
      (by linarith)).2 (lagrangeMat K) _ hdiff hper havg hbound θ hθ'
    rwa [Geometry.geo_omegak_arith hSt.gamma_pos hδ] at hcoh
  obtain ⟨-, hnorms, hη, hXT⟩ := frame_basic hSt hr hK.β_pos hK.holo hK.ball_sub hK.deriv_le hK.gram
  refine ⟨fun θ hθ => ?_, fun θ hθ => ?_, fun θ hθ => ?_, fun hω θ hθ => ?_⟩
  · obtain ⟨h1, h2⟩ := Geometry.geo_de hSt hK.holo hK𝔅 hK.error_le hδ θ hθ
    exact ⟨h1, h2, hbound θ hθ, Geometry.geo_ered hSt hK.holo hK𝔅 hK.deriv_le
      (fun θ hθ => (hK.gram θ hθ).2) hK.error_le hδ θ hθ⟩
  · have hθr : θ ∈ complexStrip n r := fun i => lt_of_lt_of_le (hθ i) (by linarith)
    refine ⟨hΩ θ hθ, ?_⟩
    calc ‖symDefect K θ‖ ≤ mSize M σK σB σT ^ 2 * ‖lagrangeMat K θ‖ :=
          Geometry.geo_esym_le (hK.gram θ hθr).1 (hK.gram θ hθr).2
      _ ≤ mSize M σK σB σT ^ 2 *
            (C_Omega n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1))) :=
          mul_le_mul_of_nonneg_left (hΩ θ hθ) (by positivity)
      _ = C_sym n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) := Geometry.geo_esym_arith
  · obtain ⟨hL, -, hG, hN, -, hP, -⟩ := hnorms θ hθ
    obtain ⟨hηL, hηN⟩ := hη ε hK.error_le θ hθ
    exact ⟨hηL, hηN, hL, hG, hN, hP⟩
  · exact hXT hω δ hδ hδ1 (by linarith) θ hθ

/-- `bpI:p1:perturbation-noA5` (a)–(e): `KAM.Apost.perturbation` without `hT` and item (f). -/
theorem perturbation_noA5 (hS : Setting n τ M σK σB σT D H ω γ) {r δ β d : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h2δ : 2 * δ < r) (hω : ‖ω‖ ≤ Theta n M σK σB σT)
    {K K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hball : ∀ θ ∈ complexStrip n r, Metric.ball (K θ) β ⊆ D)
    (hDK : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ σK)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ σB)
    (hK' : DifferentiableOn ℂ K' (complexStrip n r)) (hd : ∀ θ ∈ complexStrip n r, ‖K' θ - K θ‖ ≤ d)
    (hdβ : d < β) (hsmall : 2 * mSize M σK σB σT * C_DT n M σK σB σT * d / δ ^ 2 ≤ 1) :
    (∀ θ ∈ complexStrip n r, Metric.ball (K' θ) (β - d) ⊆ D ∧
      ‖linMat H K' θ - linMat H K θ‖ ≤ mSize M σK σB σT * d) ∧
    (∀ θ ∈ complexStrip n (r - δ), ‖fderiv ℂ K' θ - fderiv ℂ K θ‖ ≤ n * d / δ) ∧
    (∀ θ ∈ complexStrip n (r - δ), IsUnit (gramMatrix K' θ).det ∧
      ‖(gramMatrix K' θ)⁻¹‖ ≤ 2 * mSize M σK σB σT ∧
      ‖(gramMatrix K' θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤ C_B n M σK σB σT * d / δ) ∧
    (∀ θ ∈ complexStrip n (r - δ), ‖normalMat K' θ - normalMat K θ‖ ≤ C_DN n M σK σB σT * d / δ ∧
      ‖normalMat K' θ‖ ≤ 2 * mSize M σK σB σT ^ 2 ∧
      ‖(normalMat K' θ)ᵀ‖ ≤ 4 * n * mSize M σK σB σT ^ 2) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖torsion H K' ω θ - torsion H K ω θ‖ ≤ C_DT n M σK σB σT * d / δ ^ 2) := by
  -- `2 * δ < r` is part of the blueprint statement; only item (f) of K's lemma uses it.
  have _h2δ : 2 * δ < r := h2δ
  have hSt := hS.toStanding
  have hP := hSt.toParams
  have h0 : (0 : Fin n → ℂ) ∈ complexStrip n r := fun i => by simpa using hr
  have hd0 : 0 ≤ d := (norm_nonneg _).trans (hd 0 h0)
  have hβ : 0 < β := lt_of_le_of_lt hd0 hdβ
  have hsub : complexStrip n (r - δ) ⊆ complexStrip n r :=
    PerturbationAux.complexStrip_mono (by linarith)
  have ha : ∀ θ ∈ complexStrip n r, Metric.ball (K' θ) (β - d) ⊆ D := fun θ hθ =>
    PerturbationAux.ball_subset_of_close (hball θ hθ) (hd θ hθ)
  obtain ⟨hb, hc, hdN⟩ := PerturbationAux.frame_items hP hδ hδ1 hd0 hK hDK hG hK' hd hsmall
  have hG' : ∀ θ ∈ complexStrip n (r - δ), IsUnit (gramMatrix K' θ).det :=
    fun θ hθ => (hc θ hθ).1
  have hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ D := fun θ hθ => hball θ hθ (Metric.mem_ball_self hβ)
  have hAb : ∀ θ ∈ complexStrip n r, ‖linMat H K θ‖ ≤ mSize M σK σB σT := fun θ hθ =>
    FrameAux.norm_linMat_le hSt (hK𝔅 θ hθ)
  have hXX := PerturbationAux.norm_normalField_sub_le_strip hSt hδ hδ1 hd0 hω hK hball
    (fun θ hθ => (hG θ hθ).1) hK' hd hdβ hG' hdN hAb
  have he := PerturbationAux.norm_torsion_sub_le hSt hδ hδ1 hω hK hK𝔅 hDK hG hK' hG' hdN hXX
  refine ⟨fun θ hθ => ⟨ha θ hθ, PerturbationAux.norm_linMat_sub_le hSt (hball θ hθ) (hd θ hθ) hdβ⟩,
    hb, hc, fun θ hθ => ⟨(hdN θ hθ).1, (hdN θ hθ).2, ?_⟩, he⟩
  calc ‖(normalMat K' θ)ᵀ‖ ≤ 2 * n * ‖normalMat K' θ‖ := FrameAux.norm_transpose_le_two_mul _
    _ ≤ 2 * n * (2 * mSize M σK σB σT ^ 2) := by
        gcongr
        exact (hdN θ hθ).2
    _ = 4 * n * mSize M σK σB σT ^ 2 := by ring

end Frame

end KAM.Iso.Linear
