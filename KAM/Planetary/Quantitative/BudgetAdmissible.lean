/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Quantitative.BudgetCompare
public import KAM.Planetary.WeakKAM.Admissible

/-!
# Quantitative budget: identification with the upstream admissibility threshold (P11C-Q2)

Reconciliation `stepP:p11a:qb-comp` / `bpP:p11a:budget` with the delivered File 11a-3 threshold:
the local old-threshold projection `p11c_oldThreshold` and the mollifier constants equal the
upstream `selectionAdmissible`, the threshold of `adm_params`, under the data correspondence
`qbcOfSelection`.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology
namespace KAM.Planetary

/-- Data correspondence: quantitative data read off from upstream selection data, with an
independent upper bound `m0` in place of the upstream derivative supremum. -/
def qbcOfSelection {n : ℕ} (d : SelectionData n) (m0 : ℝ) : QuantitativeData n where
  mu := d.μ
  rho := d.ρ
  tau := d.τ
  vartheta := d.ϑ
  s := d.strip
  beta := d.β
  M := d.M
  M0 := m0
  C1 := d.C₁
  epsLoss := d.loss
  K := d.K

theorem qbc_bump_eq (mu : ℕ) : p11c_mollifier mu = selectionBump mu := by
  funext x
  simp only [p11c_mollifier, selectionBump, p11c_bump, selectionBumpRaw, max_comm]

theorem qbc_cutoffConstant_eq (n mu : ℕ) :
    p11c_cutoffConstant n mu = selectionExtensionC n mu := by
  have h1 : ∀ j, p11c_mollifierMass mu j = selectionBumpL1 mu j := by
    intro j
    simp only [p11c_mollifierMass, selectionBumpL1, qbc_bump_eq]
  have h2 : ∀ k, p11c_cutoffDerivative n mu k = selectionCutoffC n mu k := by
    intro k
    simp only [p11c_cutoffDerivative, selectionCutoffC, h1]
  simp only [p11c_cutoffConstant, selectionExtensionC, h2]

theorem qbc_varpi_sel {n : ℕ} (d : SelectionData n) (m0 : ℝ) :
    (qbcOfSelection d m0).varpi = selectionVarpi n d.μ d.τ := by
  unfold QuantitativeData.varpi selectionVarpi selectionExponent
  simp only [qbcOfSelection]
  rw [← neg_mul]

theorem qbc_A0_sel {n : ℕ} (d : SelectionData n) (m0 : ℝ) :
    (qbcOfSelection d m0).A0 = Real.log (16 * selectionCN n / selectionVarpi n d.μ d.τ) := by
  unfold QuantitativeData.A0
  rw [qbc_varpi_sel]
  rfl

theorem qbc_oldT_sel {n : ℕ} (d : SelectionData n) (m0 : ℝ) :
    qbcOldT (qbcOfSelection d m0) = selectionT₀ d := by
  unfold qbcOldT selectionT₀
  rw [qbc_A0_sel]
  rfl

theorem qbc_cDio_sel {n : ℕ} (d : SelectionData n) (m0 : ℝ)
    (hb : 0 < d.β) :
    (qbcOfSelection d m0).cDio = selectionCDio d := by
  unfold QuantitativeData.cDio selectionCDio selectionChat QuantitativeData.diameter
  simp only [qbcOfSelection]
  have h : d.β ^ (-1 - (d.μ : ℝ)⁻¹) = d.β⁻¹ * d.β ^ (-(1 / (d.μ : ℝ))) := by
    rw [sub_eq_add_neg, Real.rpow_add hb, Real.rpow_neg_one, one_div]
  rw [h]
  simp only [div_eq_mul_inv]
  ring

theorem qbc_gamma_sel {n : ℕ} (d : SelectionData n) (m0 : ℝ)
    (hb : 0 < d.β) :
    (qbcOfSelection d m0).gamma = selectionGamma d := by
  unfold QuantitativeData.gamma selectionGamma
  rw [qbc_cDio_sel d m0 hb]
  have : (n : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt n)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg n)]
  simp only [qbcOfSelection]
  rw [this]
  simp only [one_div]

theorem qbc_oldt_sel {n : ℕ} (d : SelectionData n) (m0 : ℝ)
    (hb : 0 < d.β) :
    qbcOldt (qbcOfSelection d m0) = selectiont₀ d := by
  unfold qbcOldt selectiont₀
  rw [qbc_oldT_sel, qbc_gamma_sel d m0 hb]
  rfl

theorem qbc_oldX_sel {n : ℕ} (d : SelectionData n) (m0 : ℝ)
    (hb : 0 < d.β) :
    qbcOldX (qbcOfSelection d m0) = selectionXi d := by
  unfold qbcOldX selectionXi
  rw [qbc_oldT_sel, qbc_oldt_sel d m0 hb]
  rfl

theorem qbc_thetaMax_sel {n : ℕ} (d : SelectionData n) :
    (qbcOfSelection d (selectionM₀ d)).thetaMax = selectionThetaMax d := rfl

/-- `stepP:p11a:qb-comp`, `bpP:p11a:budget`: the local old threshold at the upstream data
correspondence is the upstream admissibility threshold of `adm_params`. -/
theorem qbc_oldThreshold_eq_selectionAdmissible {n : ℕ} (d : SelectionData n) :
    p11c_oldThreshold (qbcOfSelection d (selectionM₀ d)) = selectionAdmissible d := by
  have hb := d.beta_pos
  rw [qbc_old_eq, qbc_oldX_sel d _ hb, qbc_oldt_sel d _ hb, qbc_oldT_sel,
    qbc_gamma_sel d _ hb, qbc_thetaMax_sel, qbc_varpi_sel, qbc_cutoffConstant_eq]
  unfold selectionAdmissible selectionLambdaMax qbcLam selectionCQ
  have h10 : (2 : ℝ) ^ (-10 : ℤ) = (2 : ℝ)⁻¹ ^ 10 := by
    rw [zpow_neg, inv_pow]; norm_num
  simp only [qbcOfSelection, h10, min_assoc]

/-- `stepP:p11a:qb-comp`, `bpP:p11a:budget` at the consumer boundary: the data-only threshold
is positive and below the upstream admissibility threshold `selectionAdmissible` (the threshold
of `adm_params`), for quantitative data corresponding to the selection data with an upper bound
`m0` of the actual derivative supremum `selectionM₀`. -/
theorem qbc_comp_selectionAdmissible {n : ℕ} (d : SelectionData n) (m0 : ℝ)
    (hd : (qbcOfSelection d m0).NumericalValid) (h0 : 0 < selectionM₀ d)
    (hM : selectionM₀ d ≤ m0) :
    0 < thresholds (qbcOfSelection d m0) ∧
      thresholds (qbcOfSelection d m0) ≤ selectionAdmissible d := by
  have h := qb_comp (qbcOfSelection d m0) hd (selectionM₀ d) h0 hM
  rw [← qbc_oldThreshold_eq_selectionAdmissible]
  exact h

end KAM.Planetary
