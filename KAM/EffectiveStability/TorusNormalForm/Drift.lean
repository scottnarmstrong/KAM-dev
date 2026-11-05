/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusNormalForm.Remainder

/-!
# The drift bound for the remainder (track B, B5-NF, item 3)

If `|D³(hR ∘ Ψ) y a b d| ≤ C₃ ‖a‖ ‖b‖ ‖d‖` on `cyl c` (the operator-norm bound on the third
Fréchet derivative, in evaluated form) and `cylClosed b ⊆ cyl c`, then for `w ∈ cylClosed b`
and every angle direction `i`:
`|D R w (e_i, 0)| ≤ C₃ ‖w.2‖² / 2`, where `‖w.2‖ = max_j |w.2 j|`. The constant is exactly
`C₃ / 2` (no `n`-dependent factor, since all norms on `ℝⁿ` are the sup norm).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set Matrix

variable {n : ℕ} {u v : (Fin n → ℝ) → (Fin n → ℝ)} {κ : ℝ}
  {hR : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {E0 : ℝ} {ω' : Fin n → ℝ} {c : Fin n → ℝ}

/-- **Drift bound** (item 3): `|∂_{φ_i} R (φ, J)| ≤ C₃ ‖J‖² / 2` on `cylClosed b`. -/
theorem torusNF_drift (h : TorusChartData u v κ) (ht : TorusNFTorus u v hR E0 ω')
    (hG : ContDiffOn ℝ 3 (hR ∘ torusChartMap u v) (cyl c)) (hc : ∀ j, 0 < c j) {C₃ : ℝ}
    (hD3 : ∀ y ∈ cyl c, ∀ a b d : (Fin n → ℝ) × (Fin n → ℝ),
      |fderiv ℝ (fderiv ℝ (fderiv ℝ (hR ∘ torusChartMap u v))) y a b d| ≤
        C₃ * ‖a‖ * ‖b‖ * ‖d‖)
    {b : Fin n → ℝ} (hbc : ∀ j, b j < c j) {w : (Fin n → ℝ) × (Fin n → ℝ)}
    (hw : w ∈ cylClosed b) (i : Fin n) :
    |fderiv ℝ (torusNFRem hR u v E0 ω') w (Pi.single i 1, 0)| ≤ C₃ * ‖w.2‖ ^ 2 / 2 := by
  obtain ⟨φ, J⟩ := w
  have hwc : (φ, J) ∈ cyl c := fun j => lt_of_le_of_lt (hw j) (hbc j)
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, ((φ, (0 : Fin n → ℝ)) + t • ((0 : Fin n → ℝ), J)) ∈ cyl c := by
    intro t ht j
    have : ((φ, (0 : Fin n → ℝ)) + t • ((0 : Fin n → ℝ), J)) = (φ, t • J) := by simp
    rw [this]
    show |(t • J) j| < c j
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht.1]
    have h1 : |J j| ≤ b j := hw j
    nlinarith [abs_nonneg (J j), ht.2, ht.1, hbc j]
  have := fderiv_taylor_bound_nfT (isOpen_cyl c) hG hseg (e := (Pi.single i 1, 0))
    (d := (0, J)) (torusNF_dG_phi h ht φ _)
    (torusNF_d2G h ht hG hc φ J _) hD3
  have hpt : ((φ, (0 : Fin n → ℝ)) + ((0 : Fin n → ℝ), J)) = (φ, J) := by simp
  have hn1 : ‖((0 : Fin n → ℝ), J)‖ = ‖J‖ := by simp [Prod.norm_def]
  have hs : ‖(Pi.single i (1 : ℝ) : Fin n → ℝ)‖ = 1 := by
    refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_) ?_
    · by_cases hj : j = i <;> simp [hj]
    · simpa using norm_le_pi_norm (Pi.single i (1 : ℝ) : Fin n → ℝ) i
  have hn2 : ‖((Pi.single i (1 : ℝ) : Fin n → ℝ), (0 : Fin n → ℝ))‖ = 1 := by
    simp [Prod.norm_def, hs]
  rw [hpt, hn1, hn2, mul_one] at this
  rw [fderiv_torusNFRem hG hwc, FunLike.coe_sub, Pi.sub_apply, torusNFLin_apply]
  simpa using this

end KAM.EffectiveStability

end
