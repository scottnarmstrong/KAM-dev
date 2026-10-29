/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Quantitative.Assembly
public import KAM.Planetary.Quantitative.AssemblyK6
public import KAM.Planetary.WeakKAM.ExtensionNorm

/-! # GAP-P11a-SQ: literal node exports of the quantitative-theorem steps

* `sel_data_gamma` (`bpP:p11a:sel-data`): the loss `γ = γ_*(ε*)/2` of the selection data, i.e.
  `2γ = γ_*(ε*)` with `γ_*` the power-law constant `p11GammaStar` for `m = N`.
* `qt_order` (`stepP:p11a:qt-order`): positivity of `γ`, `ε_adm`, `meas K`, `diam K`, and
  `K_ϑ ⊆ V` (Euclidean distance `≤ ϑ` implies max-distance `< 2ϑ`).
* `qt_reduce` (`stepP:p11a:qt-reduce`): the reduction of `(𝔡, h, f)` to the standing data of
  `sel-data`, with `γ(𝔡') = γ(𝔡)` and `ε_adm^♭(𝔡) ≤ ε_adm^{(3)}(𝔡')`.

Only source premises are assumed; every derived quantity is constructed in the proofs.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology
namespace KAM.Planetary
open KAM KAM.Kepler KAM.ODE

/-- `bpP:p11a:sel-data`: the loss `γ := γ_*(ε*)/2` of the standing data, so `2γ ≤ γ_*(ε*)`,
with `γ_*` the constant of Corollary `power-law` for `m = N`. -/
theorem sel_data_gamma {n : ℕ} (d : SelectionData n) :
    2 * selectionGamma d = p11GammaStar n d.ρ d.μ d.β
      (p11CDio n n d.ρ d.μ (Metric.diam d.K) d.ϑ d.β d.M d.τ) d.loss ∧
    2 * selectionGamma d ≤ p11GammaStar n d.ρ d.μ d.β
      (p11CDio n n d.ρ d.μ (Metric.diam d.K) d.ϑ d.β d.M d.τ) d.loss := by
  have hb := d.beta_pos
  have h1 := p11c_zero_two_gamma (qbcOfSelection d 0)
  have h2 := p11c_zero_cDio_eq (qbcOfSelection d 0)
  rw [← h2] at h1
  rw [← qbc_gamma_sel d 0 hb]
  exact ⟨h1, h1.le⟩

/-- `stepP:p11a:qt-order`: `γ`, `ε_adm`, `meas K`, `diam K` are positive, and `K_ϑ ⊆ V`. -/
theorem qt_order {N : ℕ} (d : QuantitativeData N) (hd : d.Valid) :
    0 < d.gamma ∧ 0 < thresholds d ∧ 0 < volume d.K ∧ 0 < d.diameter ∧
    {y : Fin N → ℝ | ∃ x ∈ d.K, KAM.Nekhoroshev.euclid (y - x) ≤ d.vartheta} ⊆
      {y : Fin N → ℝ | realInclusion N y ∈ actionNbhd d.K (2 * d.vartheta)} := by
  have hn := hd.1
  refine ⟨p11c_zero_gamma_pos d hn, qbc_thresholds_pos hn, ?_, qbPoly_diameter_pos d hn, ?_⟩
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hl0, hlK⟩ := hn
    exact (ENNReal.ofReal_pos.2 hl0).trans hlK
  · rintro y ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    have e : (realInclusion N y - fun i => (x i : ℂ)) = selectionReal (y - x) := by
      funext i; simp [selectionReal, realInclusion]
    rw [e, norm_selectionReal]
    rw [p11c_euclid_eq] at hxy
    exact lt_of_le_of_lt ((norm_le_selectionLength _).trans hxy) (by linarith [hn.2.2.2.2.2.1])

/-- `stepP:p11a:qt-reduce`: the reduction to the standing data of `sel-data`. -/
theorem qt_reduce {N : ℕ} (d : QuantitativeData N) (hd : d.Valid) (h : (Fin N → ℂ) → ℂ)
    (f : (Fin N → ℂ) × (Fin N → ℂ) → ℂ) (hh : QuantitativeInput d h f) :
    ∃ (ds : SelectionData N) (m0 : ℝ), ds.h = h ∧ qbcOfSelection ds m0 = d ∧
      selectionM₀ ds ≤ m0 ∧
      (∀ ε : ℝ, 0 < ε →
        (∀ z ∈ complexStrip N d.s ×ˢ actionNbhd d.K (2 * d.vartheta), ‖f z‖ ≤ ε) →
        SelectionPerturbation ds f ε) ∧
      selectionGamma ds = d.gamma ∧ thresholds d ≤ selectionAdmissible ds := by
  obtain ⟨ds, m0, rfl, rfl, hM⟩ := p11c_selData_exists d hd.1 h f hh
  obtain ⟨-, hfhol, hper, -, hfreal, -⟩ := hh
  exact ⟨ds, m0, rfl, rfl, hM, fun ε _ hf => ⟨hfhol, hper, fun z hz => hfreal z hz, hf⟩,
    qbc_gamma_sel ds m0 ds.beta_pos, polyBudget_threshold_le hd.1 hM⟩

end KAM.Planetary

end
