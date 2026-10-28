/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.FiniteMeasureHyp
public import KAM.Planetary.WeakKAM.FiniteMeasureExt

/-! # P11B finite-stage measure (`finite-measure`)

`finite_measure` (`bpP:p11a:finite-measure`): for a retained prefix of length `ν`, one cutoff
sequence `χ` (chosen here, coherently for every shorter prefix, `selection_coherent_cutoffs`)
gives the extended frequencies `ω̃_j`; the set `H` of parameters passing every shell test
`|k·ω̃_{ν(k)}| ≥ 2γ|k|₁^{-τ}` for `|k|₁ ≤ T_ν` is compact, lies in the retained set, and has measure
at least `meas K - loss`.

* `stepP:p11a:fm-close`: `selection_stage_close` (every stage stays `θ_max`-close to `ω`);
* `stepP:p11a:fm-family`: `selection_family_measure` (the family `ω̃_{min{ν(k),ν}}` and the
  power law with `2γ`);
* `stepP:p11a:fm-incl`: `selection_retained_of_tests` (induction on the stage).
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ}

theorem selectionT_mono (a : SelectionSchedule n) (hT : 0 < a.T₀) {i j : ℕ} (h : i ≤ j) :
    selectionT a i ≤ selectionT a j := by
  unfold selectionT
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) h) hT.le

/-- A mode of the `j`-th shell has stage `j`. -/
theorem selectionModeStage_eq_of_mem_shell (a : SelectionSchedule n) (hT : 1 ≤ a.T₀)
    {k : Fin n → ℤ} {j : ℕ} (hk : k ∈ selectionShell a j) : selectionModeStage a k = j := by
  have hle : selectionModeStage a k ≤ j := selectionModeStage_le a hT hk.1 hk.2.1
  by_contra hne
  have hlt : selectionModeStage a k < j := lt_of_le_of_ne hle hne
  have hm := selectionModeStage_mem_shell a hT hk.1
  rcases hk.2.2 with h0 | hj
  · omega
  · have := selectionT_mono a (by linarith) (show selectionModeStage a k ≤ j - 1 by omega)
    linarith [hm.2.1]

theorem isCompact_selection_tests {K : Set (SelectionR n)} (hK : IsCompact K)
    (F : (Fin n → ℤ) → SelectionR n → SelectionR n) (hF : ∀ k, ContinuousOn (F k) K) (T : ℝ)
    (r : (Fin n → ℤ) → ℝ) :
    IsCompact {b ∈ K | ∀ k : Fin n → ℤ, 0 < selectionModeLength k → selectionModeLength k ≤ T →
      r k ≤ |∑ i, (k i : ℝ) * F k b i|} := by
  set S : Set (Fin n → ℤ) := {k | 0 < selectionModeLength k ∧ selectionModeLength k ≤ T} with hS
  have hg : ∀ k, ContinuousOn (fun b => |∑ i, (k i : ℝ) * F k b i|) K := fun k =>
    (continuousOn_finsetSum _ fun i _ =>
      continuousOn_const.mul ((continuous_apply i).comp_continuousOn (hF k))).abs
  have hcl : IsClosed (K ∩ ⋂ k ∈ S, (K ∩ (fun b => |∑ i, (k i : ℝ) * F k b i|) ⁻¹' Ici (r k))) :=
    hK.isClosed.inter (isClosed_biInter fun k _ =>
      (hg k).preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici)
  refine hK.of_isClosed_subset ?_ (fun b hb => hb.1)
  convert hcl using 1
  ext b
  simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_preimage, mem_Ici, hS]
  constructor
  · rintro ⟨hb, h⟩
    exact ⟨hb, fun k hk => ⟨hb, h k hk.1 hk.2⟩⟩
  · rintro ⟨hb, h⟩
    exact ⟨hb, fun k h1 h2 => (h k ⟨h1, h2⟩).2⟩

theorem abs_sum_re_le (k : Fin n → ℤ) (z : SelectionC n) :
    |∑ i, (k i : ℝ) * selectionRe z i| ≤ ‖∑ i, (k i : ℂ) * z i‖ := by
  have : (∑ i, (k i : ℂ) * z i).re = ∑ i, (k i : ℝ) * selectionRe z i := by
    simp [Complex.re_sum, selectionRe]
  rw [← this]
  exact Complex.abs_re_le_norm _

theorem selectionCDio_eq (d : SelectionData n) :
    p11CDio n n d.ρ d.μ (Metric.diam d.K) d.ϑ d.β d.M d.τ = selectionCDio d := by
  have hβ := d.beta_pos
  have h : d.β ^ (-1 - (d.μ : ℝ)⁻¹) = d.β⁻¹ * d.β ^ (-((d.μ : ℝ)⁻¹)) := by
    rw [show -1 - (d.μ : ℝ)⁻¹ = -1 + -(d.μ : ℝ)⁻¹ by ring, Real.rpow_add hβ, Real.rpow_neg_one]
  unfold p11CDio p11Csub selectionCDio selectionChat
  dsimp only
  rw [h, div_eq_mul_inv]
  ring

/-- `stepP:p11a:fm-family`: the power law with `2γ` for a `θ_max`-close smooth family. -/
theorem selection_family_measure (d : SelectionData n)
    (wt : (Fin n → ℤ) → SelectionR n → SelectionR n)
    (hreg : ∀ k, k ≠ 0 → ContDiffOn ℝ d.μ (wt k) (selectionV d))
    (hclose : ∀ k, k ≠ 0 → ∀ j ≤ d.μ, ∀ y ∈ selectionThick d.K d.ϑ,
      selectionDGVector j (wt k - frequencyMap d.h) y ≤ selectionThetaMax d) :
    volume d.K - ENNReal.ofReal d.loss ≤ volume {y ∈ d.K | ∀ k : Fin n → ℤ, k ≠ 0 →
      2 * selectionGamma d * KAM.Fourier.modeSize k ^ (-d.τ) ≤ |p11dotZ k (wt k y)|} := by
  have H := selectionDioHyp d wt hreg hclose
  have hn : (0 : ℝ) < n := by exact_mod_cast d.n_pos
  have hρ : d.ρ ≠ 0 := by rcases d.rho_mem with h | h <;> simp [h]
  have hβ := d.beta_pos
  set A : ℝ := (1 / 2 : ℝ) * (Real.sqrt n)⁻¹ * (d.β / 4) ^ ((d.ρ : ℝ)⁻¹) with hA
  set B : ℝ := (d.loss / selectionCDio d) ^ ((d.μ : ℝ) / d.ρ) with hB
  have hg2 : 2 * selectionGamma d = min A B := by unfold selectionGamma; ring
  have hγ := selectionGamma_pos d
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hsmall : (Real.sqrt n * (2 * selectionGamma d)) ^ d.ρ < d.β / 4 := by
    have h1 : Real.sqrt n * (2 * selectionGamma d) ≤ 1 / 2 * (d.β / 4) ^ ((d.ρ : ℝ)⁻¹) := by
      rw [hg2]
      calc Real.sqrt n * min A B ≤ Real.sqrt n * A := by gcongr; exact min_le_left _ _
        _ = _ := by rw [hA]; field_simp
    have hx : ((d.β / 4) ^ ((d.ρ : ℝ)⁻¹)) ^ d.ρ = d.β / 4 :=
      Real.rpow_inv_natCast_pow (by positivity) hρ
    calc (Real.sqrt n * (2 * selectionGamma d)) ^ d.ρ
        ≤ (1 / 2 * (d.β / 4) ^ ((d.ρ : ℝ)⁻¹)) ^ d.ρ :=
          pow_le_pow_left₀ (by positivity) h1 _
      _ = (1 / 2) ^ d.ρ * (d.β / 4) := by rw [mul_pow, hx]
      _ < d.β / 4 := by
          have : (1 / 2 : ℝ) ^ d.ρ ≤ 1 / 2 := pow_le_of_le_one (by norm_num) (by norm_num) hρ
          nlinarith
  obtain ⟨-, -, hmeas⟩ := power_law (m := n) (P := selectionPatch d) H d.tau_gap
    (by positivity : 0 < 2 * selectionGamma d) hsmall
  refine hmeas d.loss d.loss_pos d.loss_lt ?_
  show 2 * selectionGamma d ≤ p11GammaStar n d.ρ d.μ d.β
    (p11CDio n n d.ρ d.μ (Metric.diam d.K) d.ϑ d.β d.M d.τ) d.loss
  rw [selectionCDio_eq, hg2]
  unfold p11GammaStar
  refine min_le_min (le_of_eq ?_) le_rfl
  rw [hA, Real.rpow_neg hn.le, ← Real.sqrt_eq_rpow]

/-- Scalar facts of the adapted schedule used by `finite_measure`. -/
theorem selection_adm_facts (d : SelectionData n) (ε : ℝ) (he : 0 ≤ ε)
    (hsmall : ε ≤ selectionAdmissible d) :
    SelectionAdmissibility d (adm_params d ε) ∧ (adm_params d ε).t₀ ≤ 1 ∧
      0 < (adm_params d ε).s₀ ∧ 0 < (adm_params d ε).ε₀ := by
  obtain ⟨-, hA, -⟩ := adm_choice d ε he hsmall
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast d.n_pos
  have hC : 0 < d.C₁ := by linarith [d.hessian_normalized]
  have hsq : 1 ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn
  have hs : 0 < (adm_params d ε).s₀ := by
    have hL := selectionLambdaMax_pos d
    show 0 < selectionLambdaMax d / (n * d.C₁)
    positivity
  refine ⟨hA, ?_, hs, ?_⟩
  · exact (hA.t_le.trans (div_le_self d.theta_pos.le hsq)).trans d.theta_le
  · show 0 < ε + n / 2 * d.C₁ * (adm_params d ε).s₀ ^ 2
    positivity

/-- `stepP:p11a:fm-close`: every stage `j ≤ ν` is smooth, agrees with `ω_j` on `K_j`, and stays
`θ_max`-close to `ω`. -/
theorem selection_stage_close (d : SelectionData n) (ε : ℝ) (he : 0 ≤ ε)
    (hsmall : ε ≤ selectionAdmissible d) (c : SelectionChain n) (ν : ℕ)
    (hc : SelectionExtensionChain d (adm_params d ε) c ν) (χ : ℕ → SelectionR n → ℝ)
    (hχ : ∀ j < ν, ContDiff ℝ d.μ (χ j) ∧
      (∀ y, 0 ≤ χ j y ∧ χ j y ≤ 1) ∧ (∀ y ∈ c.K j, χ j y = 1) ∧
      tsupport (χ j) ⊆ {y | Metric.infDist y (c.K j) ≤
        selectiont (adm_params d ε) j / 2} ∧
      ∀ k ≤ d.μ, ∀ y, ∀ a' : Fin k → SelectionR n, (∀ i, ‖a' i‖ ≤ 1) →
        |iteratedFDeriv ℝ k (χ j) y a'| ≤
          selectionCutoffC n d.μ k * (4 / selectiont (adm_params d ε) j) ^ k)
    {j : ℕ} (hj : j ≤ ν) :
    ContDiffOn ℝ d.μ (selectionExtendedFrequency d c χ j) (selectionV d) ∧
      (∀ b ∈ c.K j, selectionExtendedFrequency d c χ j b =
        selectionRe (selectionFrequency d c j (selectionReal b))) ∧
      ∀ i ≤ d.μ, ∀ y ∈ selectionThick d.K d.ϑ,
        selectionDGVector i (selectionExtendedFrequency d c χ j - frequencyMap d.h) y ≤
          selectionThetaMax d := by
  obtain ⟨hA, ht1, hs, he0⟩ := selection_adm_facts d ε he hsmall
  set a := adm_params d ε with ha
  have hT : 1 ≤ a.T₀ := hA.cutoff_ge
  obtain ⟨h1, h2, h3⟩ := selection_stage_of_cutoffs d a c j (hc.mono hj) hA.t_pos ht1
    d.tau_nonneg χ fun i hi => hχ i (lt_of_lt_of_le hi hj)
  refine ⟨h1, h2, fun i hi y hy => (h3 i hi y hy).trans ?_⟩
  have hC : 0 < d.C₁ := by linarith [d.hessian_normalized]
  have hγ : 0 < a.γ := selectionGamma_pos d
  have hcol := hA.collar
  have hinc := hA.increment
  have hlam : 0 ≤ a.ε₀ / a.s₀ := by positivity
  have hprops := schedule_props (C₁ := d.C₁) a d.n_pos d.μ_pos d.tau_nonneg hγ hT hA.t_pos hs
    he0 d.strip_pos d.hessian_normalized (by nlinarith [mul_pos hC hA.t_pos]) hinc hcol j 0
  have hsum := hprops.2.2.2.2.2.2.2.2.2.2.1
  have hE := selectionExtensionC_pos d.n_pos d.μ
  have hsum' : ∑ i ∈ Finset.range j, selectionell a i / selectiont a i ^ d.μ ≤
      4 * (a.ε₀ / a.s₀) / a.t₀ ^ d.μ := hsum
  calc selectionExtensionC n d.μ * ∑ i ∈ Finset.range j, selectionell a i / selectiont a i ^ d.μ
      ≤ selectionExtensionC n d.μ * (4 * (a.ε₀ / a.s₀) / a.t₀ ^ d.μ) :=
        mul_le_mul_of_nonneg_left hsum' hE.le
    _ = 4 * selectionExtensionC n d.μ * (a.ε₀ / a.s₀) / a.t₀ ^ d.μ := by ring
    _ ≤ selectionThetaMax d := hA.closeness

/-- `stepP:p11a:fm-incl`: points passing the tests lie in every retained set up to stage `ν`. -/
theorem selection_retained_of_tests (d : SelectionData n) (a : SelectionSchedule n)
    (c : SelectionChain n) (ν : ℕ) (hc : SelectionFiniteChain d a c ν) (hT : 1 ≤ a.T₀)
    (χ : ℕ → SelectionR n → ℝ)
    (hext : ∀ j ≤ ν, ∀ b ∈ c.K j, selectionExtendedFrequency d c χ j b =
      selectionRe (selectionFrequency d c j (selectionReal b)))
    {b : SelectionR n} (hb0 : b ∈ d.K)
    (htest : ∀ k : Fin n → ℤ, 0 < selectionModeLength k → selectionModeLength k ≤ selectionT a ν →
      2 * a.γ / selectionModeLength k ^ a.τ ≤
        |∑ i, (k i : ℝ) * selectionExtendedFrequency d c χ (selectionModeStage a k) b i|) :
    b ∈ selectionRetained a d c ν := by
  have key : ∀ j ≤ ν, b ∈ c.K j → ∀ k ∈ selectionShell a j,
      2 * a.γ / selectionModeLength k ^ a.τ ≤
        ‖∑ i, (k i : ℂ) * selectionFrequency d c j (selectionReal b) i‖ := by
    intro j hj hbj k hk
    have hkj := selectionModeStage_eq_of_mem_shell a hT hk
    have hle : selectionModeLength k ≤ selectionT a ν :=
      hk.2.1.trans (selectionT_mono a (by linarith) hj)
    have := htest k hk.1 hle
    rw [hkj, hext j hj b hbj] at this
    exact this.trans (abs_sum_re_le k _)
  have hmem : ∀ j ≤ ν, b ∈ c.K j := by
    intro j
    induction j with
    | zero => intro _; rw [hc.initial]; exact hb0
    | succ j ih =>
      intro hj
      have hbj := ih (by omega)
      rw [hc.retained j (by omega)]
      exact ⟨hbj, key j (by omega) hbj⟩
  exact ⟨hmem ν le_rfl, key ν le_rfl (hmem ν le_rfl)⟩

/-- Full finite-stage measure lemma; extensions are outputs, never a supplied good family. -/
theorem finite_measure (d : SelectionData n) (ε : ℝ) (he : 0 ≤ ε)
    (hsmall : ε ≤ selectionAdmissible d) (c : SelectionChain n) (ν : ℕ)
    (hc : SelectionFiniteChain d (adm_params d ε) c ν) :
    ∃ χ : ℕ → SelectionR n → ℝ,
      (∀ j ≤ ν, ContDiffOn ℝ d.μ (selectionExtendedFrequency d c χ j)
        {y | selectionReal y ∈ actionNbhd d.K (2 * d.ϑ)} ∧
        ∀ b ∈ c.K j, selectionExtendedFrequency d c χ j b =
          selectionRe (selectionFrequency d c j (selectionReal b))) ∧
      let a := adm_params d ε
      let H := {b ∈ d.K | ∀ k : Fin n → ℤ,
        0 < selectionModeLength k → selectionModeLength k ≤ selectionT a ν →
        2 * a.γ / selectionModeLength k ^ a.τ ≤
          |∑ i, (k i : ℝ) * selectionExtendedFrequency d c χ (selectionModeStage a k) b i|}
      IsCompact H ∧ H ⊆ selectionRetained a d c ν ∧
        volume d.K - ENNReal.ofReal d.loss ≤ volume H ∧ H.Nonempty := by
  obtain ⟨hA, ht1, hs, he0⟩ := selection_adm_facts d ε he hsmall
  set a := adm_params d ε with ha
  have hT : 1 ≤ a.T₀ := hA.cutoff_ge
  obtain ⟨χ, hχ⟩ := selection_coherent_cutoffs d a c ν hc.toSelectionExtensionChain hA.t_pos ht1
    d.tau_nonneg
  have hstage := fun (j : ℕ) (hj : j ≤ ν) =>
    selection_stage_close d ε he hsmall c ν hc.toSelectionExtensionChain χ hχ hj
  have hext : ∀ j ≤ ν, ∀ b ∈ c.K j, selectionExtendedFrequency d c χ j b =
      selectionRe (selectionFrequency d c j (selectionReal b)) := fun j hj => (hstage j hj).2.1
  set wt : (Fin n → ℤ) → SelectionR n → SelectionR n :=
    fun k => selectionExtendedFrequency d c χ (min (selectionModeStage a k) ν) with hwt
  have hG := selection_family_measure d wt (fun k _ => (hstage _ (min_le_right _ _)).1)
    (fun k _ j hj y hy => (hstage _ (min_le_right _ _)).2.2 j hj y hy)
  set Hs := {b ∈ d.K | ∀ k : Fin n → ℤ,
        0 < selectionModeLength k → selectionModeLength k ≤ selectionT a ν →
        2 * a.γ / selectionModeLength k ^ a.τ ≤
          |∑ i, (k i : ℝ) * selectionExtendedFrequency d c χ (selectionModeStage a k) b i|}
    with hHs
  have hGH : {y ∈ d.K | ∀ k : Fin n → ℤ, k ≠ 0 →
      2 * selectionGamma d * KAM.Fourier.modeSize k ^ (-d.τ) ≤ |p11dotZ k (wt k y)|} ⊆ Hs := by
    rintro b ⟨hbK, hb⟩
    refine ⟨hbK, fun k hk hkT => ?_⟩
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp [selectionModeLength] at hk
    have h1 := hb k hk0
    have hst : selectionModeStage a k ≤ ν := selectionModeStage_le a hT hk hkT
    simp only [wt, min_eq_left hst] at h1
    have e : 2 * selectionGamma d * KAM.Fourier.modeSize k ^ (-d.τ) =
        2 * a.γ / selectionModeLength k ^ a.τ := by
      rw [Real.rpow_neg (KAM.Fourier.modeSize_nonneg k), div_eq_mul_inv]
      rfl
    rw [← e]
    exact h1
  have hKV : d.K ⊆ selectionV d := fun x hx =>
    selectionThick_subset_V d (K_subset_selectionThick d.K d.theta_pos.le hx)
  have hHeq : Hs = {b ∈ d.K | ∀ k : Fin n → ℤ, 0 < selectionModeLength k →
      selectionModeLength k ≤ selectionT a ν → 2 * a.γ / selectionModeLength k ^ a.τ ≤
        |∑ i, (k i : ℝ) * wt k b i|} := by
    ext b
    refine and_congr_right fun _ => forall_congr' fun k => forall_congr' fun hk =>
      forall_congr' fun hkT => ?_
    simp only [wt, min_eq_left (selectionModeStage_le a hT hk hkT)]
  have hcomp : IsCompact Hs := by
    rw [hHeq]
    exact isCompact_selection_tests d.compact wt
      (fun k => (hstage _ (min_le_right _ _)).1.continuousOn.mono hKV) _ _
  have hmeas : volume d.K - ENNReal.ofReal d.loss ≤ volume Hs := hG.trans (measure_mono hGH)
  have hne : Hs.Nonempty := by
    refine nonempty_of_measure_ne_zero (μ := volume) ?_
    intro h0
    rw [h0, nonpos_iff_eq_zero, tsub_eq_zero_iff_le] at hmeas
    exact absurd d.loss_lt (not_lt.2 hmeas)
  refine ⟨χ, fun j hj => ⟨(hstage j hj).1, (hstage j hj).2.1⟩, ?_⟩
  exact ⟨hcomp, fun b hb => selection_retained_of_tests d a c ν hc hT χ hext hb.1 hb.2, hmeas,
    hne⟩

end KAM.Planetary
