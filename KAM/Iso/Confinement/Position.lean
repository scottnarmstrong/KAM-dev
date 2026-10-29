/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Confinement.Setting

/-!
# Position of the torus graphs in the chart

Blueprint `bpI:p5:mu`. For a torus
graph `Y` with data `GraphData p H E Cε Y I mσ` in a chart patch `p` with constants
`PatchConst p r Lm LΦ κ`, the slope function `μ = m ∘ Y` satisfies:

* `KAM.Iso.Confinement.slope_close`: `|m (Y φ) - mσ| ≤ Lm * Cε`, the Lipschitz comparison on the
  ball `closedBall I Cε ⊆ cthickening r 𝒦` (mean value theorem on a convex set);
* `KAM.Iso.Confinement.slope_window_plus`, `KAM.Iso.Confinement.slope_window_minus`: under
  `Smallness`, the ordering `δm/4 < μ₊ < δm` and `-δm < μ₋ < -δm/4`;
* `KAM.Iso.Confinement.slope_continuous`: `μ` is continuous (`Y φ ∈ 𝒩 ⊆ W`, `m` continuous on `W`).
-/

public section

open Set Metric

namespace KAM.Iso.Confinement

open KAM KAM.ODE

/-! ## F. Position of the graphs in the chart (`bpI:p5:mu`) -/

section Position

variable {hR : (Fin 2 → ℝ) → ℝ} {B : Set (Fin 2 → ℝ)} {η₁ : ℝ}

/-- The ball `closedBall I Cε` around the base point lies in the thickening `𝒩 = cthickening r 𝒦`
as soon as `Cε ≤ r`. -/
private lemma closedBall_subset_cthickening (p : EnergyPatch hR B η₁) {r Cε : ℝ} {I : Fin 2 → ℝ}
    (hI : I ∈ p.K) (hCr : Cε ≤ r) : closedBall I Cε ⊆ cthickening r p.K := fun x hx =>
  mem_cthickening_of_dist_le x I r p.K hI ((mem_closedBall.1 hx).trans hCr)

/-- `bpI:p5:mu`, Lipschitz comparison: `|m(Y φ) - m_σ| ≤ L_m C_K ε`. -/
theorem slope_close (p : EnergyPatch hR B η₁) {r Lm LΦ κ : ℝ} (pc : PatchConst p r Lm LΦ κ)
    {H : P2 → ℝ} {E Cε : ℝ} {Y : (Fin 2 → ℝ) → (Fin 2 → ℝ)} {I : Fin 2 → ℝ} {mσ : ℝ}
    (G : GraphData p H E Cε Y I mσ) (hCr : Cε ≤ r) (φ : Fin 2 → ℝ) :
    |p.m (Y φ) - mσ| ≤ Lm * Cε := by
  have hCε : 0 ≤ Cε := (norm_nonneg _).trans (G.near φ)
  have hsub := closedBall_subset_cthickening p G.base_mem hCr
  have hdiff : ∀ x ∈ closedBall I Cε, DifferentiableAt ℝ p.m x := fun x hx =>
    (p.m_contDiffOn.differentiableOn one_ne_zero).differentiableAt
      (p.isOpen_W.mem_nhds (pc.thick_subset (hsub hx)))
  have hbound : ∀ x ∈ closedBall I Cε, ‖fderiv ℝ p.m x‖ ≤ Lm := fun x hx =>
    pc.Lm_bound x (hsub hx)
  have hY : Y φ ∈ closedBall I Cε := by
    rw [mem_closedBall, dist_eq_norm]
    exact G.near φ
  have hmv := (convex_closedBall I Cε).norm_image_sub_le_of_norm_fderiv_le hdiff hbound
    (mem_closedBall_self hCε) hY
  rw [Real.norm_eq_abs] at hmv
  calc |p.m (Y φ) - mσ| = |p.m (Y φ) - p.m I| := by rw [G.base_slope]
    _ ≤ Lm * ‖Y φ - I‖ := hmv
    _ ≤ Lm * Cε := mul_le_mul_of_nonneg_left (G.near φ) (zero_le_one.trans pc.Lm_ge)

/-- `bpI:p5:mu`, ordering, `+` torus: `δm/4 < m(Y₊ φ) < δm`. -/
theorem slope_window_plus (p : EnergyPatch hR B η₁) {r Lm LΦ κ F₁ C_K ε ρinf : ℝ}
    (pc : PatchConst p r Lm LΦ κ) (hsm : Smallness p r Lm LΦ κ F₁ C_K ρinf ε)
    {H : P2 → ℝ} {E : ℝ} {Y : (Fin 2 → ℝ) → (Fin 2 → ℝ)} {I : Fin 2 → ℝ}
    (G : GraphData p H E (C_K * ε) Y I p.mPlus) (φ : Fin 2 → ℝ) :
    p.δm / 4 < p.m (Y φ) ∧ p.m (Y φ) < p.δm := by
  have hc := slope_close p pc G hsm.lt_r.le φ
  have hk : Lm * (C_K * ε) < κ := by rw [← mul_assoc]; exact hsm.lt_kappa
  have habs := abs_lt.1 (lt_of_le_of_lt hc hk)
  have h1 := pc.κ_le_quarter
  have h2 := pc.κ_le_plus
  have h3 := p.mPlus_mem.1
  constructor <;> linarith [habs.1, habs.2]

/-- `bpI:p5:mu`, ordering, `-` torus: `-δm < m(Y₋ φ) < -δm/4`. -/
theorem slope_window_minus (p : EnergyPatch hR B η₁) {r Lm LΦ κ F₁ C_K ε ρinf : ℝ}
    (pc : PatchConst p r Lm LΦ κ) (hsm : Smallness p r Lm LΦ κ F₁ C_K ρinf ε)
    {H : P2 → ℝ} {E : ℝ} {Y : (Fin 2 → ℝ) → (Fin 2 → ℝ)} {I : Fin 2 → ℝ}
    (G : GraphData p H E (C_K * ε) Y I p.mMinus) (φ : Fin 2 → ℝ) :
    -p.δm < p.m (Y φ) ∧ p.m (Y φ) < -(p.δm / 4) := by
  have hc := slope_close p pc G hsm.lt_r.le φ
  have hk : Lm * (C_K * ε) < κ := by rw [← mul_assoc]; exact hsm.lt_kappa
  have habs := abs_lt.1 (lt_of_le_of_lt hc hk)
  have h1 := pc.κ_le_quarter
  have h2 := pc.κ_le_minus
  have h3 := p.mMinus_mem.2
  constructor <;> linarith [habs.1, habs.2]

/-- `bpI:p5:mu`, continuity: `μ = m ∘ Y` is continuous (`Y φ ∈ 𝒩 ⊆ W`, `m` continuous on `W`). -/
theorem slope_continuous (p : EnergyPatch hR B η₁) {r Lm LΦ κ : ℝ} (pc : PatchConst p r Lm LΦ κ)
    {H : P2 → ℝ} {E Cε : ℝ} {Y : (Fin 2 → ℝ) → (Fin 2 → ℝ)} {I : Fin 2 → ℝ} {mσ : ℝ}
    (G : GraphData p H E Cε Y I mσ) (hCr : Cε ≤ r) :
    Continuous (fun φ => p.m (Y φ)) := by
  have hsub := closedBall_subset_cthickening p G.base_mem hCr
  exact p.m_contDiffOn.continuousOn.comp_continuous G.continuous fun φ =>
    pc.thick_subset (hsub (by rw [mem_closedBall, dist_eq_norm]; exact G.near φ))

end Position

end KAM.Iso.Confinement
