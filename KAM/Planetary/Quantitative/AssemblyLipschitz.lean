/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Quantitative.Assembly

/-!
# Quantitative weak KAM: the family with its defect Lipschitz bound

`weak_kam_quantitative_lip` is `weak_kam_quantitative` with one more exported clause,
`QuantitativeFamily.DefectLipschitz`: the defect `u_b(θ) = K_b(θ) - (θ, b)` is `2⁻¹⁰`-Lipschitz in
the pair `(θ, b)` on `ℝᴺ × good` (max norm). This is the internal clause
`SelectionLipschitz.lipschitz_joint` (`bpP:p11a:lipschitz-family`), which the evaluation output
already carries; in the case `ε = 0` the defect vanishes (`zero_case`). The proof repeats the
repackaging of `Assembly.lean` (`p11c_asm_family`, `p11c_asm_zero_family`) with the extra clause.
Additive: no existing declaration changes.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
namespace KAM.Planetary
open KAM KAM.Kepler KAM.ODE

variable {N : ℕ}

/-- The defect `u_b(θ) = K_b(θ) - (θ, b)` of a family is `2⁻¹⁰`-Lipschitz in `(θ, b)` on
`ℝᴺ × good` (`bpP:p11a:lipschitz-family`). -/
def QuantitativeFamily.DefectLipschitz {d : QuantitativeData N} {H : Phase N → ℝ}
    {cDelta eps : ℝ} (Q : QuantitativeFamily d H cDelta eps) : Prop :=
  ∀ b ∈ Q.good, ∀ b' ∈ Q.good, ∀ θ θ' : Fin N → ℝ,
    ‖(Q.torus b θ - (θ, b)) - (Q.torus b' θ' - (θ', b'))‖ ≤
      (2 : ℝ) ^ (-10 : ℤ) * ‖((θ, b) : Phase N) - (θ', b')‖

/-- Positive branch at selection level, with the defect Lipschitz bound. -/
theorem p11c_asm_family_lip (ds : SelectionData N) (m0 : ℝ)
    (hv : (qbcOfSelection ds m0).NumericalValid) (hM : selectionM₀ ds ≤ m0)
    (f : SelectionPhaseC N → ℂ) (ε : ℝ) (he : 0 < ε)
    (hth : ε ≤ thresholds (qbcOfSelection ds m0)) (hpert : SelectionPerturbation ds f ε) :
    ∃ Q : QuantitativeFamily (qbcOfSelection ds m0) (realHamiltonian ds.h f)
      (selectionCDelta ds) ε, Q.DefectLipschitz := by
  have hsmall : ε ≤ selectionAdmissible ds := hth.trans (polyBudget_threshold_le hv hM)
  obtain ⟨o⟩ := evaluation_bilipschitz ds ε he hsmall f hpert
  have hg : (qbcOfSelection ds m0).gamma = selectionGamma ds := qbc_gamma_sel ds m0 ds.beta_pos
  have hHK : ∀ b ∈ o.Hinf, b ∈ ds.K := fun b hb => by
    rw [o.Hinf_eq] at hb; exact hb.1
  have hbK : ∀ b ∈ o.Hinf, b ∈ o.Kinf := fun b hb => o.H_subset hb
  have hsel : ∀ (b θ : Fin N → ℝ), selectionEvaluation o.defect b θ - (θ, b) = o.defect b θ :=
    fun b θ => by simp [selectionEvaluation]
  refine ⟨QuantitativeFamily.mk o.Hinf (selectionEvaluation o.defect) o.ωstar o.compact_H hHK ?_
    (fun b hb => p11c_asm_lattice ds m0 ε he hsmall f hpert o (hbK b hb) (hHK b hb))
    (fun b hb => ?_) (fun b hb θ => ?_) (fun b hb b' hb' θ θ' => ?_)
    (fun b hb b' hb' θ θ' => ?_) ?_ ?_ ?_, fun b hb b' hb' θ θ' => ?_⟩
  · exact tsub_le_iff_right.1 o.measure_H
  · rw [hg]
    exact o.diophantine b hb
  · rw [hsel, p11c_displacement, hg]
    refine le_min ?_ ?_
    · rw [p11c_asm_zpow18]; exact o.delta_absolute.trans' (o.displacement b (hbK b hb) θ)
    · exact (o.displacement b (hbK b hb) θ).trans o.delta_power
  · rw [p11c_asm_zpow10]; exact (o.bilipschitz b (hbK b hb) b' (hbK b' hb') θ θ').1
  · rw [p11c_asm_zpow10]; exact (o.bilipschitz b (hbK b hb) b' (hbK b' hb') θ θ').2
  · show MeasurableSet ((fun z : Phase N => selectionEvaluation o.defect z.2 z.1) ''
      (unitCube N ×ˢ o.Hinf))
    rw [p11c_asm_cell]
    exact o.image_measurable _ o.compact_H o.H_subset
  · show ENNReal.ofReal ((2 : ℝ) ^ (-(2 * N : ℤ))) * volume o.Hinf ≤ volume
      ((fun z : Phase N => selectionEvaluation o.defect z.2 z.1) '' (unitCube N ×ˢ o.Hinf))
    rw [p11c_asm_cell, p11c_asm_zpow2N]
    exact o.measure_coarse _ o.compact_H o.H_subset
  · show IsCompact ((fun z : Phase N => selectionEvaluation o.defect z.2 z.1) ''
      ((Set.pi univ fun _ => Icc (0 : ℝ) 1) ×ˢ o.Hinf))
    rw [p11c_asm_closed_cell]
    exact o.closed_image_compact _ o.compact_H o.H_subset
  · show ‖(selectionEvaluation o.defect b θ - (θ, b)) -
      (selectionEvaluation o.defect b' θ' - (θ', b'))‖ ≤ _
    rw [hsel, hsel, p11c_asm_zpow10]
    exact o.lipschitz_joint b (hbK b hb) b' (hbK b' hb') θ θ'

/-- The case `eps = 0`, with the (vanishing) defect Lipschitz bound. -/
theorem p11c_asm_zero_family_lip (d : QuantitativeData N) (hd : d.Valid)
    (h : (Fin N → ℂ) → ℂ) (f : (Fin N → ℂ) × (Fin N → ℂ) → ℂ) (hh : QuantitativeInput d h f)
    (cDelta : ℝ) (hf : ∀ z ∈ complexStrip N d.s ×ˢ actionNbhd d.K (2 * d.vartheta), ‖f z‖ ≤ 0) :
    ∃ Q : QuantitativeFamily d (realHamiltonian h f) cDelta 0, Q.DefectLipschitz := by
  have hs : 0 < d.s := hd.1.2.2.2.2.2.2.2.1
  have hh0 : QuantitativeInput d h 0 := by
    obtain ⟨hhol, -, -, hreal, -, hfin, htop, hhess, hM0b⟩ := hh
    exact ⟨hhol, differentiableOn_const 0, fun _ _ _ => rfl, hreal, fun _ _ => by simp, hfin,
      htop, hhess, hM0b⟩
  obtain ⟨Q, -, hQt, -⟩ := zero_case d hd h hh0 cDelta
  have hGG : ∀ z ∈ p11c_realDomain d, realHamiltonian h f z = realHamiltonian h 0 z := by
    intro z hz
    have hmem : realInclusion₂ N z ∈ complexStrip N d.s ×ˢ actionNbhd d.K (2 * d.vartheta) :=
      ⟨realInclusion_mem_complexStrip hs _, hz⟩
    have h0 : f (realInclusion₂ N z) = 0 := norm_le_zero_iff.1 (hf _ hmem)
    have e : realHamiltonian h f z = (h (realInclusion N z.2) + f (realInclusion₂ N z)).re := rfl
    rw [e, h0]
    simp only [realHamiltonian, Pi.zero_apply, add_zero]
    rfl
  refine ⟨QuantitativeFamily.mk Q.good Q.torus Q.freq Q.compact Q.subset Q.measure
    (fun b hb => p11c_asm_transfer (p11c_asm_isOpen_domain d) hGG (Q.lattice b hb)) Q.dio
    Q.displacement Q.lower Q.upper Q.borel Q.cell_lower Q.compact_closed,
    fun b _ b' _ θ θ' => ?_⟩
  show ‖(Q.torus b θ - (θ, b)) - (Q.torus b' θ' - (θ', b'))‖ ≤ _
  rw [hQt]
  simp only [sub_self, norm_zero]
  positivity

/-- **Quantitative weak KAM with the defect Lipschitz bound.** `weak_kam_quantitative`, whose
family moreover satisfies `QuantitativeFamily.DefectLipschitz`. -/
theorem weak_kam_quantitative_lip (N mu : ℕ) (tau s C1 : ℝ) :
    ∃ cDelta : ℝ, 0 < cDelta ∧ ∀ d : QuantitativeData N,
      d.Valid → d.mu = mu → d.tau = tau → d.s = s → d.C1 = C1 →
      ∀ h f, QuantitativeInput d h f → ∀ eps : ℝ, 0 ≤ eps → eps ≤ thresholds d →
      (∀ z ∈ complexStrip N d.s ×ˢ actionNbhd d.K (2 * d.vartheta), ‖f z‖ ≤ eps) →
      ∃ Q : QuantitativeFamily d (realHamiltonian h f) cDelta eps, Q.DefectLipschitz := by
  by_cases hpos : 1 ≤ N ∧ 0 < s ∧ 1 ≤ C1
  · refine ⟨p11c_cDelta N mu tau s C1, p11c_cDelta_pos hpos.1 hpos.2.1 hpos.2.2, ?_⟩
    intro d hd hmu htau hs hC1 h f hh eps he0 heps hf
    rcases he0.eq_or_lt with h0 | hpos'
    · subst h0
      exact p11c_asm_zero_family_lip d hd h f hh _ hf
    · obtain ⟨ds, m0, rfl, rfl, hM⟩ := p11c_selData_exists d hd.1 h f hh
      obtain ⟨hhol, hfhol, hper, hreal, hfreal, -⟩ := hh
      have e : p11c_cDelta N mu tau s C1 = selectionCDelta ds := by
        rw [← hmu, ← htau, ← hs, ← hC1]; rfl
      rw [e]
      exact p11c_asm_family_lip ds m0 hd.1 hM f eps hpos' heps
        ⟨hfhol, hper, fun z hz => hfreal z hz, hf⟩
  · refine ⟨1, one_pos, fun d hd hmu htau hs hC1 => ?_⟩
    exfalso
    obtain ⟨hN, -, -, -, -, -, -, hs0, -, hC, -⟩ := hd.1
    exact hpos ⟨hN, hs ▸ hs0, hC1 ▸ hC⟩

end KAM.Planetary

end
