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

def extFlow (b : PartialBlock n k) (R s ρ σ : ℝ) (φ : EC n k → ℂ) (t : ℝ) : EC n k → EC n k :=
  KAM.Canonical.flow (wfield b.c φ) (Dom n b.base (R-ρ) (s-σ)) t

/-! ### The gauge `ν_{ρ,σ}` -/

/-- The gauge `diag(σ⁻¹, ρ⁻¹)` of `scaled ρ σ`. -/
def extGauge {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) : EC n k ≃L[ℂ] EC n k :=
  (ContinuousLinearEquiv.smulLeft (Units.mk0 ((σ : ℂ)⁻¹) (by simpa using hσ.ne'))).prodCongr
    (ContinuousLinearEquiv.smulLeft (Units.mk0 ((ρ : ℂ)⁻¹) (by simpa using hρ.ne')))

theorem norm_extGauge {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (z : EC n k) :
    ‖extGauge hρ hσ z‖ = scaled ρ σ z := by
  simp [extGauge, scaled, Prod.norm_def, norm_smul, abs_of_pos hρ, abs_of_pos hσ,
    div_eq_inv_mul]

/-- A point at scaled distance `≤ c` from `𝒟_{r₀,s₀}` lies in `𝒟_{r₀+ρc, s₀+σc}`. -/
theorem mem_Dom_of_scaled_le {m : ℕ} {D : Set (Fin m → ℂ)} {ρ σ c r₀ s₀ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ)
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

theorem eta_nonneg (hc : ExtCompose b R' s' R s ρ σ V φ) : 0 ≤ 2 * V / (ρ * σ) :=
  div_nonneg (by linarith [hc.bound_nonneg]) (mul_pos hc.rho_pos hc.sig_pos).le

theorem rho_lt' (hc : ExtCompose b R' s' R s ρ σ V φ) : ρ < R' := by
  linarith [hc.rho_lt, hc.radii, hc.rho_pos]

theorem sig_lt' (hc : ExtCompose b R' s' R s ρ σ V φ) : σ < s' := by
  linarith [hc.sig_lt, hc.widths, hc.sig_pos]

theorem dom_sub (hc : ExtCompose b R' s' R s ρ σ V φ) :
    Dom n b.base (R' - ρ) (s' - σ) ⊆ Dom n b.base R' s' :=
  Dom_mono (by linarith [hc.rho_pos]) (by linarith [hc.sig_pos])

theorem field_bound (hc : ExtCompose b R' s' R s ρ σ V φ) (hk : 1 ≤ k) :
    ∀ z ∈ Dom n b.base (R' - ρ) (s' - σ), scaled ρ σ (wfield b.c φ z) ≤ V / (ρ * σ) :=
  fun z hz => (vf b hk hc.rho_pos hc.rho_lt' hc.sig_pos hc.sig_lt' hc.slow hc.bound_nonneg
    hc.hol hc.bound z hz).1

theorem smallField (hc : ExtCompose b R' s' R s ρ σ V φ) (hk : 1 ≤ k) :
    KAM.Canonical.SmallField (extGauge hc.rho_pos hc.sig_pos) (Dom n b.base (R' - ρ) (s' - σ))
      (wfield b.c φ) (V / (ρ * σ)) where
  isOpen := isOpen_Dom _ _ _
  differentiableOn := differentiableOn_wfield' (isOpen_Dom _ _ _) _
    (hc.hol.differentiableOn.mono hc.dom_sub)
  eps_nonneg := hc.div_nonneg'
  eps_le := hc.eta_half.trans (by norm_num)
  bound z hz := by
    rw [norm_extGauge]
    exact hc.field_bound hk z hz

theorem gaugeInterior_half (hc : ExtCompose b R' s' R s ρ σ V φ) :
    Dom n b.base (R - ρ) (s - σ) ⊆
      KAM.Canonical.gaugeInterior (extGauge hc.rho_pos hc.sig_pos)
        (Dom n b.base (R' - ρ) (s' - σ)) (1 / 2) := by
  intro z hz w hw
  rw [norm_extGauge] at hw
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
  have hb := (KAM.Canonical.flow_a (hc.smallField hk) (hc.gaugeInterior_half hz)).2.2.2 t
    (abs_le.1 ht)
  rw [norm_extGauge] at hb
  have hle : scaled ρ σ (extFlow b R' s' ρ σ φ t z - z) ≤ V / (ρ * σ) :=
    hb.trans (mul_le_of_le_one_left hc.div_nonneg' ht)
  have := mem_Dom_of_scaled_le hc.rho_pos hc.sig_pos hz (by simpa [scaled] using hle)
  have e1 : R - (1 - V / (ρ * σ)) * ρ = R - ρ + ρ * (V / (ρ * σ)) := by ring
  have e2 : s - (1 - V / (ρ * σ)) * σ = s - σ + σ * (V / (ρ * σ)) := by ring
  rw [e1, e2]
  exact this

/-! ### The terms and the sum of the Lie series -/

namespace ExtCompose

variable {b : PartialBlock n k} {R' s' R s ρ σ V U : ℝ} {φ u : EC n k → ℂ}

theorem lieTerm_bound (hc : ExtCompose b R' s' R s ρ σ V φ) (hU : 0 ≤ U)
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
theorem lieSeries_summable : Summable fun j : ℕ =>
    (Real.exp 1 ^ 2 * (2 * V / (ρ * σ)) / 8) ^ j * U := by
  obtain ⟨h0, -, hq⟩ := q_facts_ext (η := 2 * V / (ρ * σ)) hc.eta_nonneg
    (hc.small.trans (by norm_num))
  exact (summable_geometric_of_lt_one h0 hq).mul_right U

include hc hU hu hb

theorem lieSeries_class : InClass b.base (R-ρ) (s-σ)
    (fun z => ∑' j : ℕ, ((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z) := by
  have hterm := hc.lieTerm_bound hU hu hb
  have hbd : ∀ j, ∀ z ∈ Dom n b.base (R-ρ) (s-σ),
      ‖((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z‖ ≤
        (Real.exp 1 ^ 2 * (2 * V / (ρ * σ)) / 8) ^ j * U := fun j =>
    sup_le_wbound (hterm j).1 (hterm j).2
  refine ⟨?_, fun j z hz => ?_⟩
  · refine (uniform_limit_holomorphic (isOpen_Dom _ _ _) (K := fun N z =>
      ∑ j ∈ range N, ((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z)
      (fun N => ?_) (tendstoUniformlyOn_tsum_nat hc.lieSeries_summable hbd)).1
    exact DifferentiableOn.fun_sum fun j _ => (hterm j).1.differentiableOn
  · exact tsum_congr fun i => by rw [(hterm i).1.periodic j z hz]

theorem lieSeries_bound : WBound b.base (R-ρ) (s-σ)
    (fun z => ∑' j : ℕ, ((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z)
    ((1 - Real.exp 1 ^ 2 * (2 * V / (ρ * σ)) / 8)⁻¹ * U) := by
  have hterm := hc.lieTerm_bound hU hu hb
  have h := wbound_tsum_ext (by linarith [hc.sig_lt]) (fun j => (hterm j).1)
    (fun j => (hterm j).2) hc.lieSeries_summable
  obtain ⟨h0, -, hq⟩ := q_facts_ext (η := 2 * V / (ρ * σ)) hc.eta_nonneg
    (hc.small.trans (by norm_num))
  rwa [tsum_mul_right, tsum_geometric_of_lt_one h0 hq] at h

theorem lieSeries_tail : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' ≥ N, WBound b.base (R-ρ) (s-σ)
    (fun z => (∑' j : ℕ, ((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z) -
      ∑ j ∈ range N', ((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z) ε := by
  intro ε hε
  obtain ⟨h0, -, hq⟩ := q_facts_ext (η := 2 * V / (ρ * σ)) hc.eta_nonneg
    (hc.small.trans (by norm_num))
  set q := Real.exp 1 ^ 2 * (2 * V / (ρ * σ)) / 8 with hqdef
  have hterm := hc.lieTerm_bound hU hu hb
  have hlim : Tendsto (fun N : ℕ => q ^ N * ((1 - q)⁻¹ * U)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0 hq).mul_const ((1 - q)⁻¹ * U)
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  refine ⟨N, fun N' hN' => ?_⟩
  have h := wbound_tsum_ext (by linarith [hc.sig_lt]) (fun j => (hterm (j + N')).1)
    (fun j => (hterm (j + N')).2) ((summable_nat_add_iff N').2 hc.lieSeries_summable)
  have hsum : ∑' j : ℕ, q ^ (j + N') * U = q ^ N' * ((1 - q)⁻¹ * U) := by
    simp_rw [pow_add]
    rw [tsum_mul_right, tsum_mul_right, tsum_geometric_of_lt_one h0 hq]
    ring
  rw [hsum] at h
  refine wbound_congr_ext (by linarith [hc.sig_lt]) (fun z hz => ?_)
    (h.mono le_rfl le_rfl (hN N' hN').le)
  have hs' : Summable fun j : ℕ => ((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z :=
    Summable.of_norm_bounded hc.lieSeries_summable fun j =>
      sup_le_wbound (hterm j).1 (hterm j).2 z hz
  rw [← hs'.sum_add_tsum_nat_add N', add_sub_cancel_left]

end ExtCompose

end KAM.Nekhoroshev

end
