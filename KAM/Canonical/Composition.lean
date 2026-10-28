/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Canonical.CompositionSeries
public import KAM.Canonical.FlowInverse
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Composition with the time-one map (`bpN:p5:composition`)

Blueprint-N Part 5, node `bpN:p5:composition` (design `docs/tracks/N/design/PART145-LEAN-DESIGN.md`,
package C5-8). Declarations in this facade:

* `KAM.Canonical.ComposeData` and `composition_domain` (i) are in `Canonical/CompositionDomain`,
  the engine of (ii) in `Canonical/CompositionSeries` (`lieSeries_*`, `series_eq`);
* `KAM.Canonical.composition_series` (ii): the Lie series converges in `|·|_{r-ρ,s-σ}` to
  `u ∘ X¹_φ`, with the bound `(1 - eη/4)⁻¹ |u| ≤ (1 - η)⁻¹ |u|`;
* `KAM.Canonical.composition_t` (iii): the same for `X^t`, `|t| ≤ 1`, with `η` replaced by `|t| η`
  (`X^t_φ = X¹_{tφ}` by uniqueness of the flow);
* `KAM.Canonical.composition_real` (iv): reality.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Canonical

open KAM.Weighted

variable {n : ℕ} {D : Set (Fin n → ℂ)} {r s r' s' ρ σ Φ U : ℝ} {φ u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

/-- `bpN:p5:composition` (ii): the Lie series converges in `|·|_{r-ρ,s-σ}` to `u ∘ X¹_φ`, with the
bound `(1 - eη/4)⁻¹ |u| ≤ (1 - η)⁻¹ |u|`, `η = 2Φ/(ρσ)`. -/
theorem composition_series {D : Set (Fin n → ℂ)} {r s r' s' ρ σ Φ U : ℝ}
    {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hd : ComposeData D r s r' s' ρ σ Φ φ)
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hu : InClass D r s u) (hb : WBound D r s u U) :
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' ≥ N, WBound D (r - ρ) (s - σ)
      (fun z => (∑' j : ℕ, ((j.factorial : ℂ)⁻¹) * adPow φ j u z) -
        ∑ j ∈ Finset.range N', ((j.factorial : ℂ)⁻¹) * adPow φ j u z) ε) ∧
    InClass D (r - ρ) (s - σ) (fun z => ∑' j : ℕ, ((j.factorial : ℂ)⁻¹) * adPow φ j u z) ∧
    WBound D (r - ρ) (s - σ) (fun z => ∑' j : ℕ, ((j.factorial : ℂ)⁻¹) * adPow φ j u z)
      ((1 - Real.exp 1 * (2 * Φ / (ρ * σ)) / 4)⁻¹ * U) ∧
    (∀ z ∈ Dom n D (r - ρ) (s - σ), u (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 z) =
      ∑' j : ℕ, ((j.factorial : ℂ)⁻¹) * adPow φ j u z) ∧
    InClass D (r - ρ) (s - σ) (fun z => u (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 z)) ∧
    WBound D (r - ρ) (s - σ) (fun z => u (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 z))
      ((1 - 2 * Φ / (ρ * σ))⁻¹ * U) := by
  have heq : EqOn (fun z => ∑' j : ℕ, ((j.factorial : ℂ)⁻¹) * adPow φ j u z)
      (fun z => u (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 z))
      (Dom n D (r - ρ) (s - σ)) := fun z hz => (series_eq hd hu hb hz).symm
  have hcl := lieSeries_class hd hu hb
  have hbd := lieSeries_bound hd hu hb
  refine ⟨lieSeries_tail hd hu hb, hcl, hbd, fun z hz => series_eq hd hu hb hz,
    inClass_congr heq hcl, ?_⟩
  by_cases hU : U < 0
  · exact wbound_of_neg hb hU (by linarith [hd.hρ])
  · replace hU := not_lt.1 hU
    obtain ⟨-, hqη, -⟩ := q_facts (η := 2 * Φ / (ρ * σ)) hd.eta_nonneg
      (hd.eta_le.trans (by norm_num))
    have hpos : 0 < 1 - 2 * Φ / (ρ * σ) := by linarith [hd.eta_le]
    refine wbound_congr (by linarith [hd.hσs]) heq (hbd.mono le_rfl le_rfl ?_)
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hpos (by linarith)) hU

/-! ### The flow of `tφ` -/

/-- The premises for `t φ`, `|t| ≤ 1`: `Φ` becomes `|t| Φ`. -/
theorem ComposeData.smul (hd : ComposeData D r s r' s' ρ σ Φ φ) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ComposeData D r s r' s' ρ σ (|t| * Φ) (fun z => (t : ℂ) * φ z) where
  hρ := hd.hρ
  hρr := hd.hρr
  hr := hd.hr
  hσ := hd.hσ
  hσs := hd.hσs
  hs := hd.hs
  φ_class := inClass_const_mul _ hd.φ_class
  Φ_nonneg := mul_nonneg (abs_nonneg t) hd.Φ_nonneg
  φ_bound := by
    have := wbound_const_mul (t : ℂ) hd.φ_bound
    simpa [Complex.norm_real, Real.norm_eq_abs] using this
  eta_le := by
    have h1 : 2 * (|t| * Φ) / (ρ * σ) = |t| * (2 * Φ / (ρ * σ)) := by ring
    rw [h1]
    exact (mul_le_of_le_one_left hd.eta_nonneg (abs_le.2 ht)).trans hd.eta_le

theorem ham_const_mul {c : ℂ} {w : (Fin n → ℂ) × (Fin n → ℂ)} (hw : DifferentiableAt ℂ φ w) :
    KAM.hamiltonianVectorFieldℂ (fun z => c * φ z) w = c • KAM.hamiltonianVectorFieldℂ φ w := by
  unfold KAM.hamiltonianVectorFieldℂ
  rw [fderiv_const_mul hw]
  refine Prod.ext (funext fun i => by simp) (funext fun i => by simp [mul_neg])

/-- `X^t_φ = X¹_{tφ}` on `𝒟_{r-ρ, s-σ}` (uniqueness of the flow). -/
theorem flow_smul (hd : ComposeData D r s r' s' ρ σ Φ φ) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ Dom n D (r - ρ) (s - σ)) :
    flow (KAM.hamiltonianVectorFieldℂ (fun z => (t : ℂ) * φ z)) (hd.smul ht).omega 1 z =
      flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z := by
  have hz1 := hd.gaugeInterior_half hz
  have hz2 := (hd.smul ht).gaugeInterior_half hz
  obtain ⟨h0, hsol, -, -⟩ := flow_a hd.smallField hz1
  have hγ : KAM.ODE.IsSolutionIn (KAM.hamiltonianVectorFieldℂ (fun z => (t : ℂ) * φ z))
      (hd.smul ht).omega (Icc (-1) 1)
      (fun τ => flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega (t * τ) z) := by
    intro τ hτ
    have hts : t * τ ∈ Icc (-1 : ℝ) 1 := by
      rw [mem_Icc, ← abs_le, abs_mul]
      exact (mul_le_mul (abs_le.2 ht) (abs_le.2 hτ) (abs_nonneg _) zero_le_one).trans_eq
        (one_mul 1)
    obtain ⟨hmem, hder⟩ := hsol (t * τ) hts
    refine ⟨hmem, ?_⟩
    have hdiff : DifferentiableAt ℂ φ (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega (t * τ) z) :=
      (hd.φ_class.differentiableOn.mono
        (Dom_mono (by linarith [hd.hρ]) (by linarith [hd.hσ]))).differentiableAt
        ((isOpen_Dom _ _ _).mem_nhds hmem)
    have := hder.scomp τ ((hasDerivAt_id τ).const_mul t)
    rw [ham_const_mul hdiff, Complex.coe_smul]
    simpa [Function.comp_def] using this
  have h00 : (fun τ => flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega (t * τ) z) 0 = z := by
    simpa using h0
  have := (flow_a (hd.smul ht).smallField hz2).2.2.1 (Icc (-1) 1) ordConnected_Icc
    ⟨by norm_num, by norm_num⟩ _ hγ h00 1 ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
  simpa using this.symm

/-- `bpN:p5:composition` (iii): `X^t`, `|t| ≤ 1`, with `η` replaced by `|t| η`. -/
theorem composition_t {D : Set (Fin n → ℂ)} {r s r' s' ρ σ Φ U : ℝ}
    {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hd : ComposeData D r s r' s' ρ σ Φ φ)
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hu : InClass D r s u) (hb : WBound D r s u U) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    InClass D (r - ρ) (s - σ) (fun z => u (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z)) ∧
    WBound D (r - ρ) (s - σ) (fun z => u (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z))
      ((1 - |t| * (2 * Φ / (ρ * σ)))⁻¹ * U) := by
  obtain ⟨-, -, -, -, h5, h6⟩ := composition_series (hd.smul ht) hu hb
  have heq : EqOn (fun z => u (flow (KAM.hamiltonianVectorFieldℂ (fun z => (t : ℂ) * φ z))
        (hd.smul ht).omega 1 z)) (fun z => u (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z))
      (Dom n D (r - ρ) (s - σ)) := fun z hz => by
    beta_reduce
    rw [flow_smul hd ht hz]
  refine ⟨inClass_congr heq h5, wbound_congr (by linarith [hd.hσs]) heq ?_⟩
  have h : 2 * (|t| * Φ) / (ρ * σ) = |t| * (2 * Φ / (ρ * σ)) := by ring
  rwa [h] at h6

/-- `bpN:p5:composition` (iv): reality. -/
theorem composition_real {D : Set (Fin n → ℂ)} {r s r' s' ρ σ Φ : ℝ}
    {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hd : ComposeData D r s r' s' ρ σ Φ φ)
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hur : RealOn (Dom n D r s) u)
    (hφr : RealOn (Dom n D r' s') φ) :
    RealOn (Dom n D (r - ρ) (s - σ))
      (fun z => u (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 z)) := by
  intro x hx
  have hsub : Dom n D (r' - ρ) (s' - σ) ⊆ Dom n D r' s' :=
    Dom_mono (by linarith [hd.hρ]) (by linarith [hd.hσ])
  have hreal : ∀ w ∈ hd.omega, w ∈ range (KAM.realInclusion₂ n) →
      KAM.hamiltonianVectorFieldℂ φ w ∈ range (KAM.realInclusion₂ n) := by
    rintro w hw ⟨y, rfl⟩
    have hV : IsOpen (Dom n D r' s') := isOpen_Dom _ _ _
    obtain ⟨⟨-, h2⟩, -⟩ := KAM.hamiltonian_real hV hd.φ_class.differentiableOn
      (fun y hy => hφr y hy) (z := y) (hsub hw) (H := fun y' => (φ (KAM.realInclusion₂ n y')).re)
      (Filter.Eventually.of_forall fun _ => rfl)
    exact ⟨_, h2⟩
  obtain ⟨y, hy⟩ := flow_e hd.smallField hreal _ (hd.gaugeInterior_half hx) ⟨x, rfl⟩ 1
    ⟨by norm_num, le_rfl⟩
  have hmem := (composition_domain hd).2.2.2 _ hx 1 ⟨by norm_num, le_rfl⟩
  simp only []
  rw [← hy] at hmem ⊢
  exact hur y hmem

end KAM.Canonical

end
