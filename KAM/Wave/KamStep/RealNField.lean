/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.RealStep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The unbounded field `X_N` and the Riesz representation of `DN` (blueprint-W `bpW:w5:new-ham` (iii))

Off-frontier, source-faithful infrastructure (W5-REAL, item 3); the dependency graph is still being
built.

`X_N(w') = (ω/2π, 0, Ω v', -Ω u')` is a bounded affine map `𝒫 → 𝒫^{p-1}` (`bpW:w4:lie` (i)). In the
representative model a point of `𝒫^q` stores `ω_{a,q}(j+2)` times its true normal coordinates; the
`(p-1)`-representative of `Ω_j v'_j` is `Ω_j ω_{a,p-1}(j+2)/ω_{a,p}(j+2) · v̂'_j = Ω_j v̂'_j/(j+2)`,
a bounded diagonal operator since `|Ω_j| ≤ K₀ (j+2)`.

* `stepXN`: the field `X_N` with values in the `(p-1)`-representatives.
* `stepDN_eq_symp_XN` (**Riesz representation**): for `w' ∈ 𝒫` and `W ∈ 𝒫^{p_+}`,
  `DN(w')(ι W) = ϖ_{p-1,p_+}(X_N(w'), W)`, with the pairing `ϖ` of `bpW:w5:setting` extended to
  `𝒫^{p-1} × 𝒫^{p_+}` (`(p-1) + p_+ ≥ 0`).
* `stepSymp_embed_eq`: `ϖ` does not depend on the representatives:
  `ϖ_{p,p}(ι_{p_+→p} X, ι_{p_+→p} W) = ϖ_{p-1,p_+}(ι_{p_+→p-1} X, W)`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb γ K0 : ℝ} {Ω : ℕ+ → ℝ}

theorem homWt_pred_div (a p : ℝ) (j : ℕ+) :
    homWt a (p - 1) j / homWt a p j = ((j : ℝ) + 2)⁻¹ := by
  unfold homWt
  rw [ellWeight_div_ellWeight, show p - 1 - p = (-1 : ℝ) by ring, Real.rpow_neg_one]
  push_cast
  ring

/-- The coefficients `Ω_j ω_{a,p-1}(j+2)/ω_{a,p}(j+2) = Ω_j/(j+2)` of `X_N`. -/
def stepXNcoef (a p : ℝ) (Ω : ℕ+ → ℝ) (j : ℕ+) : ℂ :=
  ((Ω j * (homWt a (p - 1) j / homWt a p j) : ℝ) : ℂ)

theorem norm_stepXNcoef_le (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) (j : ℕ+) :
    ‖stepXNcoef a p Ω j‖ ≤ K0 := by
  have hj : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  unfold stepXNcoef
  rw [Complex.norm_real, Real.norm_eq_abs, homWt_pred_div, abs_mul, abs_inv, abs_of_pos hj,
    ← div_eq_mul_inv, div_le_iff₀ hj]
  exact hΩ j

/-- The diagonal operator `v̂ ↦ (Ω_j v̂_j/(j+2))_j` (`p`-representatives to `(p-1)`-ones). -/
def stepXNdiag (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) : HomOp :=
  weightedDiagCLM (stepXNcoef a p Ω) (norm_stepXNcoef_le hΩ)

/-- **The field `X_N(w') = (ω/2π, 0, Ω v', -Ω u')`** of the normal form
`N = ⟨ω, y⟩ + Σ_j Ω_j z_j \bar z_j`, as a map from `𝒫` (`p`-representatives) to `𝒫^{p-1}`
(`(p-1)`-representatives) (`bpW:w5:new-ham` (iii), `bpW:w4:lie` (i)). -/
def stepXN (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) (ω : Fin 2 → ℝ)
    (w : KamPhase) : KamPhase :=
  (fun i => (2 * Real.pi : ℂ)⁻¹ * (ω i : ℂ), 0, stepXNdiag (a := a) (p := p) hΩ w.2.2.2,
    -stepXNdiag (a := a) (p := p) hΩ w.2.2.1)

/-- `N_Ω(x, ι U) = ⟨X_N-coefficient · x, U⟩` in the `(p-1, p_+)` pairing (termwise identity of
true pairings). -/
theorem homNOmega_embed_eq_stepPair (ha : 0 ≤ a) (hpb : p ≤ pb) (hqq : 0 ≤ (p - 1) + pb)
    (hG : HomGuard a p γ) (hK0 : 0 ≤ K0) (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2))
    (x U : HomL2) :
    homNOmegaCLM hG hK0 hΩ x (homEmbed_gen a p pb hpb U) =
      stepPairCLM (q := p - 1) (q' := pb) ha hqq (stepXNdiag (a := a) (p := p) hΩ x) U := by
  rw [homNOmegaCLM_apply]
  show _ = homPairL2 (weightedDiagCLM (stepWinv a (p - 1) pb) (norm_stepWinv_le ha hqq)
    (weightedDiagCLM (stepXNcoef a p Ω) (norm_stepXNcoef_le hΩ) x)) U
  rw [homPairL2_apply]
  unfold homPairF
  refine tsum_congr fun j => ?_
  have h1 : (homWt a (p - 1) j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a (p - 1) j).ne'
  have h2 : (homWt a p j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a p j).ne'
  have h3 : (homWt a pb j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a pb j).ne'
  simp only [homEmbed_gen, weightedDiagCLM_apply, homEmbedCoef_gen, homNcoef, stepWinv,
    stepXNcoef]
  push_cast
  field_simp

/-- The `z`-bookkeeping: `N_Ω(z, \bar Z) + N_Ω(Z, \bar z) = N_Ω(u, U) + N_Ω(v, V)`. -/
theorem homNOmega_zbook (B : HomL2 →L[ℂ] HomL2 →L[ℂ] ℂ) (hB : ∀ x y, B x y = B y x)
    (u v U V : HomL2) :
    B (homSqrt2⁻¹ • (u + Complex.I • v)) (homSqrt2⁻¹ • (U - Complex.I • V)) +
        B (homSqrt2⁻¹ • (U + Complex.I • V)) (homSqrt2⁻¹ • (u - Complex.I • v)) =
      B u U + B v V := by
  simp only [map_add, map_sub, map_smul, add_apply, smul_apply, smul_eq_mul]
  rw [hB U u, hB V v, hB U v, hB V u]
  have hs := homSqrt2_inv_sq
  linear_combination (2 * (B u U - Complex.I ^ 2 * B v V)) * hs - B v V * Complex.I_sq

/-- **Riesz representation of `DN` by the unbounded field `X_N`** (blueprint `bpW:w5:new-ham` (iii),
step `n-conj`): for every `w' ∈ 𝒫` and `W ∈ 𝒫^{p_+}` (`p_+`-representatives, `ι W ∈ 𝒫`),
`DN(w')(ι W) = ϖ_{p-1,p_+}(X_N(w'), W)`. -/
theorem stepDN_eq_symp_XN (ha : 0 ≤ a) (hpb : p ≤ pb) (hqq : 0 ≤ (p - 1) + pb)
    (hG : HomGuard a p γ) (hK0 : 0 ≤ K0) (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2))
    (ω : Fin 2 → ℝ) (w W : KamPhase) :
    (homDN hG hK0 hΩ ω (stepToHom w)).comp stepToHom (kamHomEmbed a p pb hpb W) =
      stepSymp (q := p - 1) (q' := pb) ha hqq (stepXN (a := a) (p := p) hΩ ω w) W := by
  obtain ⟨θ, y, u, v⟩ := w
  obtain ⟨Θ, Y, U, V⟩ := W
  rw [ContinuousLinearMap.comp_apply, homDN_apply]
  simp only [stepToHom_apply, kamHomEmbed_apply, homPrZ, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.coe_snd', stepZ_apply, stepZb_apply]
  rw [homNOmega_zbook _ (homNOmega_comm hG hK0 hΩ),
    homNOmega_embed_eq_stepPair ha hpb hqq hG hK0 hΩ,
    homNOmega_embed_eq_stepPair ha hpb hqq hG hK0 hΩ]
  unfold stepSymp stepXN
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero, map_neg,
    neg_apply]
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 2 * Real.pi := by positivity
    exact_mod_cast this.ne'
  rw [Finset.mul_sum]
  have e : ∀ i, (2 * Real.pi : ℂ) * ((2 * Real.pi : ℂ)⁻¹ * (ω i : ℂ) * Y i) = (ω i : ℂ) * Y i :=
    fun i => by field_simp
  simp only [e]
  ring

/-- `homEmbed_gen` from a weight to itself is the identity. -/
theorem homEmbed_gen_self (a q : ℝ) (x : HomL2) : homEmbed_gen a q q le_rfl x = x := by
  ext j
  simp only [homEmbed_gen, weightedDiagCLM_apply, homEmbedCoef_gen]
  rw [div_self (homWt_pos a q j).ne']
  simp

/-- The pairing of embedded representatives is the true pairing `Σ x_j y_j/(ω_{qx} ω_{qy})`. -/
theorem stepPair_embed_eq_true {q q' qx qy : ℝ} (ha : 0 ≤ a) (hqq : 0 ≤ q + q') (hx : q ≤ qx)
    (hy : q' ≤ qy) (x y : HomL2) :
    stepPairCLM (q := q) (q' := q') ha hqq (homEmbed_gen a q qx hx x) (homEmbed_gen a q' qy hy y) =
      ∑' j : ℕ+, ((homWt a qx j * homWt a qy j)⁻¹ : ℝ) * x j * y j := by
  show homPairL2 (weightedDiagCLM (stepWinv a q q') (norm_stepWinv_le ha hqq)
    (homEmbed_gen a q qx hx x)) (homEmbed_gen a q' qy hy y) = _
  rw [homPairL2_apply]
  unfold homPairF
  refine tsum_congr fun j => ?_
  have h1 : (homWt a q j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a q j).ne'
  have h2 : (homWt a q' j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a q' j).ne'
  have h3 : (homWt a qx j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a qx j).ne'
  have h4 : (homWt a qy j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a qy j).ne'
  simp only [homEmbed_gen, weightedDiagCLM_apply, homEmbedCoef_gen, stepWinv]
  push_cast
  field_simp

/-- **`ϖ` does not depend on the representatives**:
`ϖ_{p,p}(ι_{p_+→p} X, ι_{p_+→p} W) = ϖ_{p-1,p_+}(ι_{p_+→p-1} X, W)`. -/
theorem stepSymp_embed_eq (ha : 0 ≤ a) (hpb : p ≤ pb) (hpp : 0 ≤ p + p)
    (hqq : 0 ≤ (p - 1) + pb) (hpm : p - 1 ≤ pb) (X W : KamPhase) :
    stepSymp (q := p) (q' := p) ha hpp (kamHomEmbed a p pb hpb X) (kamHomEmbed a p pb hpb W) =
      stepSymp (q := p - 1) (q' := pb) ha hqq (kamHomEmbed a (p - 1) pb hpm X) W := by
  unfold stepSymp
  simp only [kamHomEmbed_apply]
  conv_rhs => rw [← homEmbed_gen_self a pb W.2.2.2, ← homEmbed_gen_self a pb W.2.2.1]
  rw [stepPair_embed_eq_true, stepPair_embed_eq_true, stepPair_embed_eq_true,
    stepPair_embed_eq_true]

end KAM.Wave
