/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.FT
public import KAM.EffectiveStability.TorusDomain
public import KAM.EffectiveStability.RealFlow
public import KAM.Canonical.Lie

/-!
# Torus one-step normalization: the finite Lie remainder (track B, B4-TSTEP)

For a Fourier–Taylor generator `χ` (complexified as `φ = ftEvalC χ`), `Ω = cstripOpen σ ρ` and the
gauge `W = scaleCLE ρ' σ'`:

* `strip_le_log_lam`: the rational strip check gives `σ ≤ log λ / (2π)`;
* `smallField_of_ftBounds`: the majorant checks on `∂_J χ` and `∂_φ χ` give `SmallField W Ω X_φ ε`;
* `torusRem`: the Lie remainder `H (X^1 z) - ∑_{j<L} (j!)⁻¹ ad_φ^j H (z)`;
* `differentiableOn_torusRem`, `norm_torusRem_le`: `Rem` is holomorphic on the half gauge
  interior and `‖Rem‖ ≤ B / L!` there, `B = ftSupBound (ftAdPow χ L H) πub λ ρ`;
* `torusRem_realInclusion₂`: at a real point `Rem (ι x)` is the real number
  `H (Ψ x) - (Lie sum)(x)`.
-/

@[expose] public noncomputable section

open Set KAM.Canonical

namespace KAM.EffectiveStability

variable {n : ℕ}

/-- The rational strip check `x = 2 πub σ < 1`, `1/(1-x) ≤ λ` gives `σ ≤ log λ / (2π)`. -/
theorem strip_le_log_lam {σ : ℝ} {πub lam : ℚ} (hπ : Real.pi ≤ ((πub : ℚ) : ℝ)) (hσ : 0 ≤ σ)
    (hx : 2 * ((πub : ℚ) : ℝ) * σ < 1)
    (hlam : 1 / (1 - 2 * ((πub : ℚ) : ℝ) * σ) ≤ ((lam : ℚ) : ℝ)) :
    σ ≤ Real.log lam / (2 * Real.pi) := by
  have hpi := Real.pi_pos
  have h1 : 2 * Real.pi * σ ≤ 2 * ((πub : ℚ) : ℝ) * σ := by nlinarith
  have h0 : 0 ≤ 2 * ((πub : ℚ) : ℝ) * σ := by nlinarith
  have h2 := Real.exp_bound_div_one_sub_of_interval h0 hx
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le (by
    have : 0 < 1 - 2 * ((πub : ℚ) : ℝ) * σ := by linarith
    positivity) hlam
  have h3 : Real.exp (2 * Real.pi * σ) ≤ lam :=
    ((Real.exp_le_exp.2 h1).trans h2).trans hlam
  have h4 : 2 * Real.pi * σ ≤ Real.log lam := (Real.le_log_iff_exp_le hlam0).2 h3
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- The Lie remainder `H (X^1 z) - ∑_{j<L} (j!)⁻¹ ad_φ^j H (z)`, as a function of `z ∈ ℂⁿ×ℂⁿ`. -/
def torusRem (χ H : FTPoly) (σ ρ : ℝ) (L : ℕ) (z : (Fin n → ℂ) × (Fin n → ℂ)) : ℂ :=
  ftEvalC H (flow (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) =>
      ftEvalC χ w)) (cstripOpen σ ρ) 1 z) - ftEvalC (ftLieSum χ H L) z

theorem ftEvalC_realInclusion₂ (P : FTPoly) (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    ftEvalC P (KAM.realInclusion₂ n x) = ((ftEvalR P x : ℝ) : ℂ) := by
  have := ftEvalC_ofReal P x
  simpa [KAM.realInclusion] using this

/-- Real points have vanishing imaginary part of any rational Fourier–Taylor polynomial. -/
theorem ftEvalC_realInclusion₂_im (P : FTPoly) (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    (ftEvalC P (KAM.realInclusion₂ n x)).im = 0 := by
  rw [ftEvalC_realInclusion₂]
  exact Complex.ofReal_im _

/-- Majorant bound for a Fourier–Taylor polynomial at a point of the strip × polydisc. -/
theorem norm_ftEvalC_le_of_strip {P : FTPoly} (hP : FTFits n P) {πub lam : ℚ} {σ ρ : ℝ}
    (hπ : Real.pi ≤ ((πub : ℚ) : ℝ)) (hlam : 0 < lam) (hσ : σ ≤ Real.log lam / (2 * Real.pi))
    (ρl : List ℚ) (hρl : ∀ i : Fin n, ((ρl.getD i 0 : ℚ) : ℝ) = ρ)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ cstripOpen σ ρ) :
    ‖ftEvalC P z‖ ≤ ((ftSupBound P πub lam ρl : ℚ) : ℝ) :=
  norm_ftEvalC_le_supBound P hP ρl hπ hlam z (fun i => (hz i).1.le.trans hσ)
    (fun i => by rw [hρl]; exact (hz i).2.le)

/-- The majorant checks give the small-field hypothesis. -/
theorem smallField_of_ftBounds {χ : FTPoly} (hχ : FTFits n χ) {πub lam : ℚ} {σ ρ σ' ρ' ε : ℝ}
    (hσ' : 0 < σ') (hρ' : 0 < ρ') (hπ : Real.pi ≤ ((πub : ℚ) : ℝ)) (hlam : 0 < lam)
    (hσ : σ ≤ Real.log lam / (2 * Real.pi))
    (ρl : List ℚ) (hρl : ∀ i : Fin n, ((ρl.getD i 0 : ℚ) : ℝ) = ρ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hJ : ∀ i : Fin n, ((ftSupBound (ftDJ i χ) πub lam ρl : ℚ) : ℝ) ≤ ε * σ')
    (hφ : ∀ i : Fin n, ((ftSupBound (ftDφ i χ) πub lam ρl : ℚ) : ℝ) ≤ ε * ρ') :
    SmallField (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ)
      (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w)) ε := by
  refine smallField_of_strip_bounds hρ' hσ' (ftEvalC_differentiable χ).differentiableOn hε0 hε
    ?_ ?_
  · intro z hz i
    rw [ftEvalC_fderiv_dJ]
    exact (norm_ftEvalC_le_of_strip (ftFits_dJ i hχ) hπ hlam hσ ρl hρl hz).trans (hJ i)
  · intro z hz i
    rw [ftEvalC_fderiv_dφ]
    exact (norm_ftEvalC_le_of_strip (ftFits_dφ i hχ) hπ hlam hσ ρl hρl hz).trans (hφ i)

section Remainder

variable {χ H : FTPoly} {σ ρ σ' ρ' ε : ℝ} {hσ' : 0 < σ'} {hρ' : 0 < ρ'}

theorem differentiableOn_torusRem
    (hS : SmallField (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ)
      (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w)) ε)
    (L : ℕ) :
    DifferentiableOn ℂ (torusRem (n := n) χ H σ ρ L)
      (gaugeInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (1 / 2)) := by
  have h1 := (flow_b hS).2.1 1 ⟨by norm_num, le_rfl⟩
  have h2 : DifferentiableOn ℂ (fun z => ftEvalC H
      (flow (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w))
        (cstripOpen σ ρ) 1 z))
      (gaugeInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (1 / 2)) :=
    (ftEvalC_differentiable H).differentiableOn.comp h1 (fun _ _ => mem_univ _)
  exact h2.sub (ftEvalC_differentiable _).differentiableOn

/-- The Lie–Taylor remainder bound on the half gauge interior. -/
theorem norm_torusRem_le (hχ : FTFits n χ) (hH : FTFits n H)
    (hS : SmallField (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ)
      (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w)) ε)
    {πub lam : ℚ} (hπ : Real.pi ≤ ((πub : ℚ) : ℝ)) (hlam : 0 < lam)
    (hσ : σ ≤ Real.log lam / (2 * Real.pi))
    (ρl : List ℚ) (hρl : ∀ i : Fin n, ((ρl.getD i 0 : ℚ) : ℝ) = ρ) {L : ℕ} (hL : 1 ≤ L)
    {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ gaugeInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (1 / 2)) :
    ‖torusRem χ H σ ρ L z‖ ≤
      ((ftSupBound (ftAdPow χ L H) πub lam ρl : ℚ) : ℝ) / (L.factorial : ℝ) := by
  obtain ⟨h1, h2⟩ := taylor_lie (ftEvalC_differentiable χ).differentiableOn hS
    (isOpen_cstripOpen σ ρ) subset_rfl (ftEvalC_differentiable H).differentiableOn hz
    (fun t ht => (flow_b hS).2.2.1 t ht z hz) hL
  have hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖adPow (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w) L
      (fun w => ftEvalC H w)
      (flow (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w))
        (cstripOpen σ ρ) t z)‖ ≤ ((ftSupBound (ftAdPow χ L H) πub lam ρl : ℚ) : ℝ) := by
    intro t ht
    have hmem := (flow_b hS).2.2.1 t ⟨by linarith [ht.1], ht.2⟩ z hz
    rw [← congrFun (ftEvalC_adPow_complex χ H hχ hH L) _]
    exact norm_ftEvalC_le_of_strip (ftFits_adPow hχ hH L) hπ hlam hσ ρl hρl hmem
  have h3 := h2 _ hB
  have h4 : torusRem χ H σ ρ L z = ∫ t in (0 : ℝ)..1, ((((1 - t) ^ (L - 1) /
      ((L - 1).factorial : ℝ) : ℝ) : ℂ)) * adPow (fun w : (Fin n → ℂ) × (Fin n → ℂ) =>
        ftEvalC χ w) L (fun w => ftEvalC H w) (flow (KAM.hamiltonianVectorFieldℂ
          (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w)) (cstripOpen σ ρ) t z) := by
    rw [torusRem, ftEvalC_lieSum_complex χ H hχ hH L z]
    show _ - _ = _
    rw [sub_eq_iff_eq_add, add_comm]
    exact h1
  rw [h4]
  exact h3

/-- At a real point the remainder is the real number `H (Ψ x) - (Lie sum)(x)`. -/
theorem torusRem_realInclusion₂
    (hS : SmallField (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ)
      (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w)) ε)
    (L : ℕ) {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : x ∈ realInterior (scaleCLE ρ' σ' hρ' hσ') (cstripOpen σ ρ) (1 / 2)) :
    torusRem χ H σ ρ L (KAM.realInclusion₂ n x) =
      (((ftEvalR H (realFlow (fun w : (Fin n → ℂ) × (Fin n → ℂ) => ftEvalC χ w)
        (cstripOpen σ ρ) 1 x) - ftEvalR (ftLieSum χ H L) x : ℝ)) : ℂ) := by
  rw [torusRem, ← realInclusion₂_realFlow (isOpen_cstripOpen σ ρ)
    (ftEvalC_differentiable χ).differentiableOn hS
    (fun y _ => ftEvalC_realInclusion₂_im χ y) hx ⟨by norm_num, le_rfl⟩,
    ftEvalC_realInclusion₂, ftEvalC_realInclusion₂]
  push_cast
  rfl

end Remainder

end KAM.EffectiveStability
