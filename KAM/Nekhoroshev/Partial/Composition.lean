/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.CompositionCoeff
public import KAM.Nekhoroshev.Partial.Adjoint
public import KAM.Nekhoroshev.Partial.Lie
public import KAM.Nekhoroshev.Partial.VectorField
public import KAM.Nekhoroshev.Partial.Flow
public import KAM.Nekhoroshev.Partial.ExtFlow
public import KAM.Nekhoroshev.Partial.RealSystem
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Module.Equiv.Prod

/-!
# Composition with the extended time-one map (`bpN:p11:composition`, Part 11, package N11-F1)

For `ExtCompose b R' s' R s ρ σ V φ` (the source premises `0 < ρ < R`, `R + ρ ≤ R'`, `0 < σ < s`,
`s + σ ≤ s'`, `φ ∈ 𝒪_{R',s'}` of norm `≤ V`, `η = 2V/(ρσ) ≤ 1/2`, `(SL)_{ρ,σ}`) and `X^t = extFlow`
the flow of the weighted field `X^c_φ = wfield c φ` on `Ω = 𝒟_{R'-ρ,s'-σ}`:

* `composition_domain` (step `co-field`): the field has `ν_{ρ,σ}`-size `≤ V/(ρσ)` and `X^t` maps
  `𝒟_{R-ρ,s-σ}` into the smaller tube `𝒟_{R-(1-V/(ρσ))ρ, s-(1-V/(ρσ))σ}`;
* `composition` (steps `co-series`, `co-remainder` and the norm convergence): the Lie series of
  `u ∘ X^t` converges pointwise and in `|·|_{R-ρ,s-σ}`, with the bound
  `(1 - |t| η)⁻¹ |u|_{R,s}` for `u ∘ X^t`;
* `composition_real`: reality of `u ∘ X¹`.

The engine is the Part 5 one (`KAM.Canonical.CompositionSeries`) on the unequal product `EC n k`,
with the adjoint constant `e² η/8` of `adjoint` (so `q ≤ η`).
-/

@[expose] public noncomputable section

open Set Metric Filter Finset
open scoped Topology BigOperators

namespace KAM.Nekhoroshev

open KAM.Weighted

variable {n k : ℕ}

/-- Source assumptions for B.5, including explicit norm bounds. -/
structure ExtCompose (b : PartialBlock n k) (R' s' R s ρ σ V : ℝ) (φ : EC n k → ℂ) : Prop where
  rho_pos : 0 < ρ
  rho_lt : ρ < R
  sig_pos : 0 < σ
  sig_lt : σ < s
  radii : R+ρ ≤ R'
  widths : s+σ ≤ s'
  bound_nonneg : 0 ≤ V
  hol : InClass b.base R' s' φ
  bound : WBound b.base R' s' φ V
  small : 2*V/(ρ*σ) ≤ 1/2
  slow : slowLoss b.c ρ σ k

/-! ### The gauge `ν_{ρ,σ}` -/

/-- The gauge `diag(σ⁻¹, ρ⁻¹)` of `scaled ρ σ`. -/
def extComposeGauge {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) : EC n k ≃L[ℂ] EC n k :=
  (ContinuousLinearEquiv.smulLeft (Units.mk0 ((σ : ℂ)⁻¹) (by simpa using hσ.ne'))).prodCongr
    (ContinuousLinearEquiv.smulLeft (Units.mk0 ((ρ : ℂ)⁻¹) (by simpa using hρ.ne')))

theorem norm_extComposeGauge {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (z : EC n k) :
    ‖extComposeGauge hρ hσ z‖ = scaled ρ σ z := by
  simp [extComposeGauge, scaled, Prod.norm_def, norm_smul, abs_of_pos hρ, abs_of_pos hσ,
    div_eq_inv_mul]

/-- A point at scaled distance `≤ c` from `𝒟_{r₀,s₀}` lies in `𝒟_{r₀+ρc, s₀+σc}`. -/
theorem mem_Dom_of_scaled_le {m : ℕ} {D : Set (Fin m → ℂ)} {ρ σ c r₀ s₀ : ℝ} (hρ : 0 < ρ)
    (hσ : 0 < σ)
    {z w : (Fin n → ℂ) × (Fin m → ℂ)} (hz : z ∈ Dom n D r₀ s₀)
    (hw : max (‖w.1 - z.1‖ / σ) (‖w.2 - z.2‖ / ρ) ≤ c) :
    w ∈ Dom n D (r₀ + ρ * c) (s₀ + σ * c) := by
  have h1 : ‖w.1 - z.1‖ ≤ σ * c := by
    have := (le_max_left _ _).trans hw
    rwa [div_le_iff₀ hσ, mul_comm] at this
  have h2 : ‖w.2 - z.2‖ ≤ ρ * c := by
    have := (le_max_right _ _).trans hw
    rwa [div_le_iff₀ hρ, mul_comm] at this
  obtain ⟨hz1, I', hI', hz2⟩ := hz
  refine ⟨fun i => ?_, I', hI', ?_⟩
  · have h3 : |(w.1 i).im - (z.1 i).im| ≤ σ * c := by
      have := (norm_le_pi_norm (w.1 - z.1) i).trans h1
      calc |(w.1 i).im - (z.1 i).im| = |((w.1 - z.1) i).im| := by simp
        _ ≤ ‖(w.1 - z.1) i‖ := Complex.abs_im_le_norm _
        _ ≤ σ * c := this
    have h4 : |(w.1 i).im| ≤ |(z.1 i).im| + |(w.1 i).im - (z.1 i).im| := by
      calc |(w.1 i).im| = |(z.1 i).im + ((w.1 i).im - (z.1 i).im)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have := hz1 i
    linarith
  · calc ‖w.2 - I'‖ = ‖(w.2 - z.2) + (z.2 - I')‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖w.2 - z.2‖ + ‖z.2 - I'‖ := norm_add_le _ _
      _ < ρ * c + r₀ := add_lt_add_of_le_of_lt h2 hz2
      _ = r₀ + ρ * c := by ring

private theorem differentiableOn_wfield' {Ω : Set (EC n k)} (hΩ : IsOpen Ω) (c : ℝ)
    {φ : EC n k → ℂ} (hφ : DifferentiableOn ℂ φ Ω) : DifferentiableOn ℂ (wfield c φ) Ω := by
  have hd : ∀ v : EC n k, DifferentiableOn ℂ (fun z => fderiv ℂ φ z v) Ω := fun v =>
    (KAM.holomorphic_regularity_of_finiteDimensional hΩ hφ).1.clm_apply (differentiableOn_const v)
  refine DifferentiableOn.prodMk (differentiableOn_pi.2 fun i => hd _)
    (differentiableOn_pi.2 fun j => ?_)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Fin.append_left]
    exact (hd _).neg
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_right, Fin.append_left]
      exact (differentiableOn_const _).mul (hd _)
    · simp only [Fin.append_right, neg_mul]
      exact ((differentiableOn_const _).mul (hd _)).neg

private theorem exp_one_bounds : 0 < Real.exp 1 ∧ Real.exp 1 < 2.7182818286 :=
  ⟨Real.exp_pos 1, Real.exp_one_lt_d9⟩

/-- `q = e²η/8` for `0 ≤ η ≤ 1`: `0 ≤ q ≤ η` and `q < 1`. -/
theorem q_facts_ext {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    0 ≤ Real.exp 1 ^ 2 * η / 8 ∧ Real.exp 1 ^ 2 * η / 8 ≤ η ∧ Real.exp 1 ^ 2 * η / 8 < 1 := by
  obtain ⟨he0, he1⟩ := exp_one_bounds
  have he2 : Real.exp 1 ^ 2 < 7.4 := by nlinarith
  refine ⟨by positivity, ?_, ?_⟩ <;> nlinarith

namespace ExtCompose

variable {b : PartialBlock n k} {R' s' R s ρ σ V : ℝ} {φ : EC n k → ℂ}

theorem eta_half (hc : ExtCompose b R' s' R s ρ σ V φ) : V / (ρ * σ) ≤ 1 / 4 := by
  have := hc.small
  have h : 2 * V / (ρ * σ) = 2 * (V / (ρ * σ)) := by ring
  linarith

theorem div_nonneg' (hc : ExtCompose b R' s' R s ρ σ V φ) : 0 ≤ V / (ρ * σ) :=
  div_nonneg hc.bound_nonneg (mul_pos hc.rho_pos hc.sig_pos).le

theorem ext_eta_nonneg (hc : ExtCompose b R' s' R s ρ σ V φ) : 0 ≤ 2 * V / (ρ * σ) :=
  div_nonneg (by linarith [hc.bound_nonneg]) (mul_pos hc.rho_pos hc.sig_pos).le

theorem rho_lt' (hc : ExtCompose b R' s' R s ρ σ V φ) : ρ < R' := by
  linarith [hc.rho_lt, hc.radii, hc.rho_pos]

theorem sig_lt' (hc : ExtCompose b R' s' R s ρ σ V φ) : σ < s' := by
  linarith [hc.sig_lt, hc.widths, hc.sig_pos]

theorem dom_sub (hc : ExtCompose b R' s' R s ρ σ V φ) :
    Dom n b.base (R' - ρ) (s' - σ) ⊆ Dom n b.base R' s' :=
  Dom_mono (by linarith [hc.rho_pos]) (by linarith [hc.sig_pos])

private theorem field_bound (hc : ExtCompose b R' s' R s ρ σ V φ) (hk : 1 ≤ k) :
    ∀ z ∈ Dom n b.base (R' - ρ) (s' - σ), scaled ρ σ (wfield b.c φ z) ≤ V / (ρ * σ) :=
  fun z hz => (vf b hk hc.rho_pos hc.rho_lt' hc.sig_pos hc.sig_lt' hc.slow hc.bound_nonneg
    hc.hol hc.bound z hz).1

theorem extSmallField (hc : ExtCompose b R' s' R s ρ σ V φ) (hk : 1 ≤ k) :
    KAM.Canonical.SmallField (extComposeGauge hc.rho_pos hc.sig_pos)
      (Dom n b.base (R' - ρ) (s' - σ))
      (wfield b.c φ) (V / (ρ * σ)) where
  isOpen := isOpen_Dom _ _ _
  differentiableOn := differentiableOn_wfield' (isOpen_Dom _ _ _) _
    (hc.hol.differentiableOn.mono hc.dom_sub)
  eps_nonneg := hc.div_nonneg'
  eps_le := hc.eta_half.trans (by norm_num)
  bound z hz := by
    rw [norm_extComposeGauge]
    exact hc.field_bound hk z hz

theorem ext_gaugeInterior_half (hc : ExtCompose b R' s' R s ρ σ V φ) :
    Dom n b.base (R - ρ) (s - σ) ⊆
      KAM.Canonical.gaugeInterior (extComposeGauge hc.rho_pos hc.sig_pos)
        (Dom n b.base (R' - ρ) (s' - σ)) (1 / 2) := by
  intro z hz w hw
  rw [norm_extComposeGauge] at hw
  have := mem_Dom_of_scaled_le (c := 1 / 2) hc.rho_pos hc.sig_pos hz (by simpa [scaled] using hw)
  exact Dom_mono (by nlinarith [hc.radii, hc.rho_pos]) (by nlinarith [hc.widths, hc.sig_pos]) this

end ExtCompose

/-- B.5(i) keeps its smaller image tube, used by the integral remainder. -/
theorem composition_domain (b : PartialBlock n k) (hk : 1 ≤ k) {R' s' R s ρ σ V : ℝ}
    {φ : EC n k → ℂ} (hc : ExtCompose b R' s' R s ρ σ V φ) :
    (∀ z ∈ Dom n b.base (R'-ρ) (s'-σ), scaled ρ σ (wfield b.c φ z) ≤ V/(ρ*σ)) ∧
    (∀ t : ℝ, |t| ≤ 1 → MapsTo (extFlow b R' s' ρ σ φ t)
      (Dom n b.base (R-ρ) (s-σ))
      (Dom n b.base (R-(1-V/(ρ*σ))*ρ) (s-(1-V/(ρ*σ))*σ))) := by
  refine ⟨hc.field_bound hk, fun t ht z hz => ?_⟩
  have hb := (KAM.Canonical.flow_a (hc.extSmallField hk) (hc.ext_gaugeInterior_half hz)).2.2.2 t
    (abs_le.1 ht)
  rw [norm_extComposeGauge] at hb
  have hle : scaled ρ σ (extFlow b R' s' ρ σ φ t z - z) ≤ V / (ρ * σ) :=
    hb.trans (mul_le_of_le_one_left hc.div_nonneg' ht)
  have := mem_Dom_of_scaled_le hc.rho_pos hc.sig_pos hz (by simpa [scaled] using hle)
  have e1 : R - (1 - V / (ρ * σ)) * ρ = R - ρ + ρ * (V / (ρ * σ)) := by ring
  have e2 : s - (1 - V / (ρ * σ)) * σ = s - σ + σ * (V / (ρ * σ)) := by ring
  rw [e1, e2]
  exact this

theorem ExtCompose.tube_sub {b : PartialBlock n k} {R' s' R s ρ σ V : ℝ} {φ : EC n k → ℂ}
    (hc : ExtCompose b R' s' R s ρ σ V φ) :
    Dom n b.base (R-(1-V/(ρ*σ))*ρ) (s-(1-V/(ρ*σ))*σ) ⊆ Dom n b.base R s := by
  have h1 : 0 ≤ 1 - V / (ρ * σ) := by linarith [hc.eta_half]
  exact Dom_mono (by nlinarith [mul_nonneg h1 hc.rho_pos.le])
    (by nlinarith [mul_nonneg h1 hc.sig_pos.le])

/-! ### The terms and the sum of the Lie series -/

namespace ExtCompose

variable {b : PartialBlock n k} {R' s' R s ρ σ V U : ℝ} {φ u : EC n k → ℂ}

theorem extLieTerm_bound (hc : ExtCompose b R' s' R s ρ σ V φ) (hU : 0 ≤ U)
    (hu : InClass b.base R s u) (hb : WBound b.base R s u U) (j : ℕ) :
    InClass b.base (R-ρ) (s-σ) (fun z => ((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z) ∧
    WBound b.base (R-ρ) (s-σ) (fun z => ((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z)
      ((Real.exp 1 ^ 2 * (2 * V / (ρ * σ)) / 8) ^ j * U) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hcl : InClass b.base (R-ρ) (s-σ) u :=
      ⟨hu.differentiableOn.mono (Dom_mono (by linarith [hc.rho_pos]) (by linarith [hc.sig_pos])),
        fun j z hz => hu.periodic j z
          (Dom_mono (by linarith [hc.rho_pos]) (by linarith [hc.sig_pos]) hz)⟩
    have heq : EqOn u (fun z => (((0 : ℕ).factorial : ℂ)⁻¹) * extAd b.c φ 0 u z)
        (Dom n b.base (R-ρ) (s-σ)) := fun z _ => by simp [extAd]
    refine ⟨inClass_congr_ext heq hcl, wbound_congr_ext (by linarith [hc.sig_lt]) heq ?_⟩
    simpa using hb.mono (by linarith [hc.rho_pos]) (by linarith [hc.sig_pos]) le_rfl
  · obtain ⟨h1, h3⟩ := adjoint b hc.rho_pos hc.rho_lt hc.sig_pos hc.sig_lt hc.radii hc.widths
      hc.slow hU hc.bound_nonneg hc.hol hu hc.bound hb j hj
    exact ⟨inClass_const_mul_ext _ h1, h3⟩

variable (hc : ExtCompose b R' s' R s ρ σ V φ) (hU : 0 ≤ U)
  (hu : InClass b.base R s u) (hb : WBound b.base R s u U)

include hc in
theorem extLieSeries_summable : Summable fun j : ℕ =>
    (Real.exp 1 ^ 2 * (2 * V / (ρ * σ)) / 8) ^ j * U := by
  obtain ⟨h0, -, hq⟩ := q_facts_ext (η := 2 * V / (ρ * σ)) hc.ext_eta_nonneg
    (hc.small.trans (by norm_num))
  exact (summable_geometric_of_lt_one h0 hq).mul_right U

include hc hU hu hb

private theorem lieSeries_class : InClass b.base (R-ρ) (s-σ)
    (fun z => ∑' j : ℕ, ((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z) := by
  have hterm := hc.extLieTerm_bound hU hu hb
  have hbd : ∀ j, ∀ z ∈ Dom n b.base (R-ρ) (s-σ),
      ‖((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z‖ ≤
        (Real.exp 1 ^ 2 * (2 * V / (ρ * σ)) / 8) ^ j * U := fun j =>
    sup_le_wbound (hterm j).1 (hterm j).2
  refine ⟨?_, fun j z hz => ?_⟩
  · refine (uniform_limit_holomorphic (isOpen_Dom _ _ _) (K := fun N z =>
      ∑ j ∈ range N, ((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z)
      (fun N => ?_) (tendstoUniformlyOn_tsum_nat hc.extLieSeries_summable hbd)).1
    exact DifferentiableOn.fun_sum fun j _ => (hterm j).1.differentiableOn
  · exact tsum_congr fun i => by rw [(hterm i).1.periodic j z hz]

private theorem lieSeries_bound : WBound b.base (R-ρ) (s-σ)
    (fun z => ∑' j : ℕ, ((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z)
    ((1 - Real.exp 1 ^ 2 * (2 * V / (ρ * σ)) / 8)⁻¹ * U) := by
  have hterm := hc.extLieTerm_bound hU hu hb
  have h := wbound_tsum_ext (by linarith [hc.sig_lt]) (fun j => (hterm j).1)
    (fun j => (hterm j).2) hc.extLieSeries_summable
  obtain ⟨h0, -, hq⟩ := q_facts_ext (η := 2 * V / (ρ * σ)) hc.ext_eta_nonneg
    (hc.small.trans (by norm_num))
  rwa [tsum_mul_right, tsum_geometric_of_lt_one h0 hq] at h

private theorem lieSeries_tail : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' ≥ N, WBound b.base (R-ρ) (s-σ)
    (fun z => (∑' j : ℕ, ((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z) -
      ∑ j ∈ range N', ((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z) ε := by
  intro ε hε
  obtain ⟨h0, -, hq⟩ := q_facts_ext (η := 2 * V / (ρ * σ)) hc.ext_eta_nonneg
    (hc.small.trans (by norm_num))
  set q := Real.exp 1 ^ 2 * (2 * V / (ρ * σ)) / 8 with hqdef
  have hterm := hc.extLieTerm_bound hU hu hb
  have hlim : Tendsto (fun N : ℕ => q ^ N * ((1 - q)⁻¹ * U)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0 hq).mul_const ((1 - q)⁻¹ * U)
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  refine ⟨N, fun N' hN' => ?_⟩
  have h := wbound_tsum_ext (by linarith [hc.sig_lt]) (fun j => (hterm (j + N')).1)
    (fun j => (hterm (j + N')).2) ((summable_nat_add_iff N').2 hc.extLieSeries_summable)
  have hsum : ∑' j : ℕ, q ^ (j + N') * U = q ^ N' * ((1 - q)⁻¹ * U) := by
    simp_rw [pow_add]
    rw [tsum_mul_right, tsum_mul_right, tsum_geometric_of_lt_one h0 hq]
    ring
  rw [hsum] at h
  refine wbound_congr_ext (by linarith [hc.sig_lt]) (fun z hz => ?_)
    (h.mono le_rfl le_rfl (hN N' hN').le)
  have hs' : Summable fun j : ℕ => ((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z :=
    Summable.of_norm_bounded hc.extLieSeries_summable fun j =>
      sup_le_wbound (hterm j).1 (hterm j).2 z hz
  rw [← hs'.sum_add_tsum_nat_add N', add_sub_cancel_left]

end ExtCompose

/-! ### Identification with `u ∘ X¹` -/

namespace ExtCompose

variable {b : PartialBlock n k} {R' s' R s ρ σ V U : ℝ} {φ u : EC n k → ℂ}

private theorem hat_eta {ρ σ V : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) :
    2 * V / (ρ * (3 / 4) * (σ * (3 / 4))) = 16 / 9 * (2 * V / (ρ * σ)) := by
  field_simp
  ring

variable (hc : ExtCompose b R' s' R s ρ σ V φ) (hk : 1 ≤ k) (hU : 0 ≤ U)
  (hu : InClass b.base R s u) (hb : WBound b.base R s u U)
include hc hk hU hu hb

/-- On the trajectories from `𝒟_{R-ρ,s-σ}`, the iterates `ad_φ^N u / N!` are `≤ q̂^N U`, where
`q̂` is the constant of the loss `(3ρ/4, 3σ/4)`. -/
theorem extAd_traj_bound {N : ℕ} (hN : 1 ≤ N) {z : EC n k}
    (hz : z ∈ Dom n b.base (R-ρ) (s-σ)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖extAd b.c φ N u (extFlow b R' s' ρ σ φ t z)‖ ≤
      (N.factorial : ℝ) *
        ((Real.exp 1 ^ 2 * (2 * V / (ρ * (3 / 4) * (σ * (3 / 4)))) / 8) ^ N * U) := by
  have hρ' : 0 < ρ * (3 / 4) := by have := hc.rho_pos; positivity
  have hσ' : 0 < σ * (3 / 4) := by have := hc.sig_pos; positivity
  have hSL' : slowLoss b.c (ρ * (3 / 4)) (σ * (3 / 4)) k := by
    have := hc.slow
    unfold slowLoss at this ⊢
    linarith
  obtain ⟨h1, h3⟩ := adjoint b hρ' (by linarith [hc.rho_pos, hc.rho_lt]) hσ'
    (by linarith [hc.sig_pos, hc.sig_lt]) (by linarith [hc.radii, hc.rho_pos])
    (by linarith [hc.widths, hc.sig_pos]) hSL' hU hc.bound_nonneg hc.hol hu hc.bound hb N hN
  have hmem : extFlow b R' s' ρ σ φ t z ∈
      Dom n b.base (R - ρ * (3 / 4)) (s - σ * (3 / 4)) := by
    have := (composition_domain b hk hc).2 t (abs_le.2 ⟨by linarith [ht.1], ht.2⟩) hz
    refine Dom_mono ?_ ?_ this
    · have := mul_le_mul_of_nonneg_left hc.eta_half hc.rho_pos.le
      nlinarith [hc.rho_pos]
    · have := mul_le_mul_of_nonneg_left hc.eta_half hc.sig_pos.le
      nlinarith [hc.sig_pos]
  have h4 := sup_le_wbound (inClass_const_mul_ext ((N.factorial : ℂ)⁻¹) h1) h3 _ hmem
  have hf : (0 : ℝ) < N.factorial := Nat.cast_pos.2 (Nat.factorial_pos N)
  calc _ = (N.factorial : ℝ) * ‖((N.factorial : ℂ)⁻¹) * extAd b.c φ N u
          (extFlow b R' s' ρ σ φ t z)‖ := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 hf.le

/-- On `𝒟_{R-ρ,s-σ}` the Lie series is `u ∘ X¹_φ`. -/
theorem ext_series_eq {z : EC n k} (hz : z ∈ Dom n b.base (R-ρ) (s-σ)) :
    u (extFlow b R' s' ρ σ φ 1 z) =
      ∑' j : ℕ, ((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z := by
  have hterm := hc.extLieTerm_bound hU hu hb
  have hs' : Summable fun j : ℕ => ((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z :=
    Summable.of_norm_bounded hc.extLieSeries_summable fun j =>
      sup_le_wbound (hterm j).1 (hterm j).2 z hz
  have hlim1 := hs'.hasSum.tendsto_sum_nat
  have hη := hc.small
  have hη0 := hc.ext_eta_nonneg
  have hq := q_facts_ext (η := 16 / 9 * (2 * V / (ρ * σ))) (by positivity) (by linarith)
  rw [← hat_eta (V := V) hc.rho_pos hc.sig_pos] at hq
  obtain ⟨hq0, -, hq1⟩ := hq
  have hz1 := hc.ext_gaugeInterior_half hz
  have hΩ : IsOpen (Dom n b.base R s) := isOpen_Dom _ _ _
  have hsub : Dom n b.base R s ⊆ Dom n b.base (R' - ρ) (s' - σ) :=
    Dom_mono (by linarith [hc.radii]) (by linarith [hc.widths])
  have hφd : DifferentiableOn ℂ φ (Dom n b.base R s) :=
    hc.hol.differentiableOn.mono (hsub.trans hc.dom_sub)
  have hud : DifferentiableOn ℂ u (Dom n b.base R s) := hu.differentiableOn
  obtain ⟨h0, hsol, -, -⟩ := KAM.Canonical.flow_a (hc.extSmallField hk) hz1
  have hγ : KAM.ODE.IsSolutionIn (wfield b.c φ) (Dom n b.base R s) (Icc 0 1)
      (fun t => extFlow b R' s' ρ σ φ t z) := fun t ht => by
    refine ⟨?_, (hsol t ⟨by linarith [ht.1], ht.2⟩).2⟩
    have := (composition_domain b hk hc).2 t (abs_le.2 ⟨by linarith [ht.1], ht.2⟩) hz
    exact hc.tube_sub this
  have htaylor : ∀ N : ℕ, 1 ≤ N → ‖∑ j ∈ range N, ((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z -
      u (extFlow b R' s' ρ σ φ 1 z)‖ ≤
      (Real.exp 1 ^ 2 * (2 * V / (ρ * (3 / 4) * (σ * (3 / 4)))) / 8) ^ N * U := fun N hN => by
    have h1 := ext_taylor hΩ hφd hud hγ N hN
    have hB := ext_taylor_bound hΩ hφd hud hγ N hN _ fun t ht =>
      hc.extAd_traj_bound hk hU hu hb hN hz ht
    have hf : (0 : ℝ) < N.factorial := Nat.cast_pos.2 (Nat.factorial_pos N)
    have h1' : u (extFlow b R' s' ρ σ φ 1 z) = _ := h1
    have h00 : extFlow b R' s' ρ σ φ 0 z = z := h0
    simp only [h00] at h1'
    rw [h1', sub_add_cancel_left, norm_neg]
    refine hB.trans_eq ?_
    field_simp
  have hlim2 : Tendsto (fun N : ℕ => ∑ j ∈ range N, ((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z)
      atTop (𝓝 (u (extFlow b R' s' ρ σ φ 1 z))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      ((eventually_ge_atTop 1).mono fun N hN => htaylor N hN) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const U
  exact tendsto_nhds_unique hlim2 hlim1

end ExtCompose

/-! ### The flow of `tφ` -/

private theorem wfield_smul_real (c t : ℝ) {φ : EC n k → ℂ} {w : EC n k}
    (hw : DifferentiableAt ℂ φ w) :
    wfield c (fun z => (t : ℂ) * φ z) w = (t : ℂ) • wfield c φ w := by
  have hf : fderiv ℂ (fun z => (t : ℂ) * φ z) w = (t : ℂ) • fderiv ℂ φ w :=
    fderiv_const_mul hw _
  unfold wfield
  simp only [hf, smul_apply, smul_eq_mul]
  refine Prod.ext (funext fun i => by simp) (funext fun j => ?_)
  simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Fin.append_left]
    ring
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_right, Fin.append_left]
      ring
    · simp only [Fin.append_right]
      ring

namespace ExtCompose

variable {b : PartialBlock n k} {R' s' R s ρ σ V U : ℝ} {φ u : EC n k → ℂ}

/-- The premises for `tφ`, `|t| ≤ 1`: `V` becomes `|t| V`. -/
theorem smul_ext (hc : ExtCompose b R' s' R s ρ σ V φ) {t : ℝ} (ht : |t| ≤ 1) :
    ExtCompose b R' s' R s ρ σ (|t| * V) (fun z => (t : ℂ) * φ z) where
  rho_pos := hc.rho_pos
  rho_lt := hc.rho_lt
  sig_pos := hc.sig_pos
  sig_lt := hc.sig_lt
  radii := hc.radii
  widths := hc.widths
  bound_nonneg := mul_nonneg (abs_nonneg t) hc.bound_nonneg
  hol := inClass_const_mul_ext _ hc.hol
  bound := by
    have := wbound_const_mul_ext (t : ℂ) hc.bound
    simpa [Complex.norm_real, Real.norm_eq_abs] using this
  small := by
    have h1 : 2 * (|t| * V) / (ρ * σ) = |t| * (2 * V / (ρ * σ)) := by ring
    rw [h1]
    exact (mul_le_of_le_one_left hc.ext_eta_nonneg ht).trans hc.small
  slow := hc.slow

/-- `X^t_φ = X¹_{tφ}` on `𝒟_{R-ρ,s-σ}` (uniqueness of the flow). -/
theorem extCompose_flow_smul (hc : ExtCompose b R' s' R s ρ σ V φ) (hk : 1 ≤ k) {t : ℝ}
    (ht : |t| ≤ 1)
    {z : EC n k} (hz : z ∈ Dom n b.base (R-ρ) (s-σ)) :
    extFlow b R' s' ρ σ (fun z => (t : ℂ) * φ z) 1 z = extFlow b R' s' ρ σ φ t z := by
  have hz1 := hc.ext_gaugeInterior_half hz
  have hz2 := (hc.smul_ext ht).ext_gaugeInterior_half hz
  obtain ⟨h0, hsol, -, -⟩ := KAM.Canonical.flow_a (hc.extSmallField hk) hz1
  have hγ : KAM.ODE.IsSolutionIn (wfield b.c fun z => (t : ℂ) * φ z)
      (Dom n b.base (R' - ρ) (s' - σ)) (Icc (-1) 1)
      (fun τ => extFlow b R' s' ρ σ φ (t * τ) z) := by
    intro τ hτ
    have hts : t * τ ∈ Icc (-1 : ℝ) 1 := by
      rw [Set.mem_Icc, ← abs_le, abs_mul]
      exact (mul_le_mul ht (abs_le.2 hτ) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    obtain ⟨hmem, hder⟩ := hsol (t * τ) hts
    refine ⟨hmem, ?_⟩
    have hdiff : DifferentiableAt ℂ φ (extFlow b R' s' ρ σ φ (t * τ) z) :=
      (hc.hol.differentiableOn.mono hc.dom_sub).differentiableAt
        ((isOpen_Dom _ _ _).mem_nhds hmem)
    have := hder.scomp τ ((hasDerivAt_id τ).const_mul t)
    rw [wfield_smul_real _ _ hdiff, Complex.coe_smul]
    simpa [extFlow, Function.comp_def] using this
  have h00 : (fun τ => extFlow b R' s' ρ σ φ (t * τ) z) 0 = z := by simpa [extFlow] using h0
  have := (KAM.Canonical.flow_a ((hc.smul_ext ht).extSmallField hk) hz2).2.2.1 (Icc (-1) 1)
    ordConnected_Icc ⟨by norm_num, by norm_num⟩ _ hγ h00 1
    ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
  simpa [extFlow] using this.symm

variable (hc : ExtCompose b R' s' R s ρ σ V φ) (hk : 1 ≤ k) (hU : 0 ≤ U)
  (hu : InClass b.base R s u) (hb : WBound b.base R s u U)
include hc hk hU hu hb

theorem hasSum_pt {z : EC n k} (hz : z ∈ Dom n b.base (R-ρ) (s-σ)) :
    HasSum (fun j : ℕ => ((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z)
      (u (extFlow b R' s' ρ σ φ 1 z)) := by
  have hterm := hc.extLieTerm_bound hU hu hb
  have hs' : Summable fun j : ℕ => ((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z :=
    Summable.of_norm_bounded hc.extLieSeries_summable fun j =>
      sup_le_wbound (hterm j).1 (hterm j).2 z hz
  rw [hc.ext_series_eq hk hU hu hb hz]
  exact hs'.hasSum

/-- Class and norm of `u ∘ X¹_φ`. -/
theorem comp_one_class_bound :
    InClass b.base (R-ρ) (s-σ) (fun z => u (extFlow b R' s' ρ σ φ 1 z)) ∧
    WBound b.base (R-ρ) (s-σ) (fun z => u (extFlow b R' s' ρ σ φ 1 z))
      ((1 - 2 * V / (ρ * σ))⁻¹ * U) := by
  have heq : EqOn (fun z => ∑' j : ℕ, ((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z)
      (fun z => u (extFlow b R' s' ρ σ φ 1 z)) (Dom n b.base (R-ρ) (s-σ)) :=
    fun z hz => (hc.ext_series_eq hk hU hu hb hz).symm
  refine ⟨inClass_congr_ext heq (hc.lieSeries_class hU hu hb), ?_⟩
  have hbd := hc.lieSeries_bound hU hu hb
  obtain ⟨-, hqη, -⟩ := q_facts_ext (η := 2 * V / (ρ * σ)) hc.ext_eta_nonneg
    (hc.small.trans (by norm_num))
  have hpos : 0 < 1 - 2 * V / (ρ * σ) := by linarith [hc.small]
  refine wbound_congr_ext (by linarith [hc.sig_lt]) heq (hbd.mono le_rfl le_rfl ?_)
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hpos (by linarith)) hU

end ExtCompose

namespace ExtCompose

variable {b : PartialBlock n k} {R' s' R s ρ σ V U : ℝ} {φ u : EC n k → ℂ}

/-- `X^t`, `|t| ≤ 1`, with `η` replaced by `|t| η`. -/
theorem comp_t_class_bound (hc : ExtCompose b R' s' R s ρ σ V φ) (hk : 1 ≤ k) (hU : 0 ≤ U)
    (hu : InClass b.base R s u) (hb : WBound b.base R s u U) {t : ℝ} (ht : |t| ≤ 1) :
    InClass b.base (R-ρ) (s-σ) (u ∘ extFlow b R' s' ρ σ φ t) ∧
    WBound b.base (R-ρ) (s-σ) (u ∘ extFlow b R' s' ρ σ φ t)
      ((1 - |t| * (2 * V / (ρ * σ)))⁻¹ * U) := by
  obtain ⟨h5, h6⟩ := (hc.smul_ext ht).comp_one_class_bound hk hU hu hb
  have heq : EqOn (fun z => u (extFlow b R' s' ρ σ (fun z => (t : ℂ) * φ z) 1 z))
      (u ∘ extFlow b R' s' ρ σ φ t) (Dom n b.base (R-ρ) (s-σ)) := fun z hz => by
    beta_reduce
    rw [hc.extCompose_flow_smul hk ht hz]
    rfl
  refine ⟨inClass_congr_ext heq h5, wbound_congr_ext (by linarith [hc.sig_lt]) heq ?_⟩
  have h : 2 * (|t| * V) / (ρ * σ) = |t| * (2 * V / (ρ * σ)) := by ring
  rwa [h] at h6

end ExtCompose

theorem composition (b : PartialBlock n k) (hk : 1 ≤ k) {R' s' R s ρ σ V U : ℝ}
    {φ u : EC n k → ℂ} (hc : ExtCompose b R' s' R s ρ σ V φ)
    (hU : 0 ≤ U) (hu : InClass b.base R s u) (hub : WBound b.base R s u U) :
    let X := extFlow b R' s' ρ σ φ
    (∀ t : ℝ, |t| ≤ 1 → MapsTo (X t) (Dom n b.base (R-ρ) (s-σ)) (Dom n b.base R s)) ∧
    (∀ t : ℝ, |t| ≤ 1 → InClass b.base (R-ρ) (s-σ) (u ∘ X t) ∧
      WBound b.base (R-ρ) (s-σ) (u ∘ X t) ((1-|t| *(2*V/(ρ*σ)))⁻¹*U)) ∧
    (∀ z ∈ Dom n b.base (R-ρ) (s-σ),
      HasSum (fun j : ℕ => ((j.factorial:ℂ)⁻¹)*extAd b.c φ j u z) (u (X 1 z))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' ≥ N,
      WBound b.base (R-ρ) (s-σ)
        (fun z => u (X 1 z)-∑ j ∈ Finset.range N', ((j.factorial:ℂ)⁻¹)*extAd b.c φ j u z) ε) := by
  intro X
  refine ⟨fun t ht z hz => hc.tube_sub ((composition_domain b hk hc).2 t ht hz),
    fun t ht => hc.comp_t_class_bound hk hU hu hub ht,
    fun z hz => hc.hasSum_pt hk hU hu hub hz, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hc.lieSeries_tail hU hu hub ε hε
  refine ⟨N, fun N' hN' => ?_⟩
  refine wbound_congr_ext (by linarith [hc.sig_lt]) (fun z hz => ?_) (hN N' hN')
  rw [hc.ext_series_eq hk hU hu hub hz]

/-! ### Reality -/

private theorem extRe_extCx (z : ER n k) : extRe (extCx z) = z := by
  ext i <;> simp [extRe, extCx]

private theorem extCx_eq' (z : ER n k) :
    extCx z = (KAM.realInclusion n z.1, KAM.realInclusion (n+(k+k)) z.2) := by
  ext i <;> simp [extCx]

theorem composition_real (b : PartialBlock n k) (hk : 1 ≤ k) {R' s' R s ρ σ V : ℝ}
    {φ u : EC n k → ℂ} (hc : ExtCompose b R' s' R s ρ σ V φ)
    (hφ : extReal (Dom n b.base R' s') φ) (hu : extReal (Dom n b.base R s) u) :
    extReal (Dom n b.base (R-ρ) (s-σ)) (u ∘ extFlow b R' s' ρ σ φ 1) := by
  have hR' : 0 < R' := by linarith [hc.rho_pos, hc.rho_lt, hc.radii]
  have hs' : 0 < s' := by linarith [hc.sig_pos, hc.sig_lt, hc.widths]
  have hext : ext_class b R' s' φ := ⟨hc.hol, hφ⟩
  have hreal : ∀ y : ER n k, extCx y ∈ Dom n b.base (R' - ρ) (s' - σ) →
      extCx (extRe (wfield b.c φ (extCx y))) = wfield b.c φ (extCx y) := by
    intro y hy
    have hyR : y ∈ b.realDom R' := by
      refine ⟨KAM.ofReal_mem_complexStrip one_pos y.1, ?_⟩
      exact polyNbhd_mono (by linarith [hc.rho_pos]) hy.2
    have := (real_system b hR' hs' hext).2.2.1 y hyR
    rw [← this, extRe_extCx]
  intro x hx
  have hx' : extCx x ∈ Dom n b.base (R - ρ) (s - σ) := by
    rw [extCx_eq']
    exact hx
  have hxg := hc.ext_gaugeInterior_half hx'
  have hrl := flow_real (extComposeGauge hc.rho_pos hc.sig_pos) (hc.extSmallField hk) hreal hxg
    (t := 1) (by norm_num)
  have hmem := hc.tube_sub ((composition_domain b hk hc).2 1 (by norm_num) hx')
  have hrel : extCx (extRe (extFlow b R' s' ρ σ φ 1 (extCx x))) =
      extFlow b R' s' ρ σ φ 1 (extCx x) := hrl
  set y : ER n k := extRe (extFlow b R' s' ρ σ φ 1 (extCx x)) with hydef
  have hy : (KAM.realInclusion n y.1, KAM.realInclusion (n+(k+k)) y.2) =
      extFlow b R' s' ρ σ φ 1 (extCx x) := by
    rw [← extCx_eq']
    exact hrel
  have h1 := hu y (by rw [hy]; exact hmem)
  rw [hy] at h1
  have hxe : (KAM.realInclusion n x.1, KAM.realInclusion (n+(k+k)) x.2) = extCx x :=
    (extCx_eq' x).symm
  show (u (extFlow b R' s' ρ σ φ 1 (KAM.realInclusion n x.1,
    KAM.realInclusion (n+(k+k)) x.2))).im = 0
  rw [hxe]
  exact h1

end KAM.Nekhoroshev

end
