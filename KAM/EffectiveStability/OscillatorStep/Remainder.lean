/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Poly.Lie
public import KAM.EffectiveStability.PolyDomain
public import KAM.EffectiveStability.RealFlow
public import KAM.Canonical.Lie

/-!
# One-step normalization: the finite Lie remainder (track B, B2-STEP)

For a polynomial generator `χ` (complexified as `φ = χ.cartEval`), `Ω = cpolyOpen ρ` and the
gauge `W = gaugeScalar δ hδ`:

* `smallField_of_supBound`: the majorant checks `cartSupBound (cartDq i χ) ρl ρl ≤ ε δ` (and the
  `p`-version) give `SmallField W Ω X_φ ε`;
* `stepRem`: the Lie remainder `Rem z = H(X^1 z) - ∑_{j<L} (j!)⁻¹ ad_φ^j H (z)`;
* `differentiableOn_stepRem`, `norm_stepRem_le`: `Rem` is holomorphic on the half gauge interior
  and `‖Rem‖ ≤ B / L!` there, `B = cartSupBound (cartAdPow χ L H) ρl ρl`;
* `stepRem_realInclusion₂`: at a real point `Rem (ι x)` is the real number
  `H (Ψ x) - (cartLieSum χ H L)(x)`, with `Ψ = realFlow φ Ω 1`.
-/

@[expose] public noncomputable section

open Set KAM.Canonical

namespace KAM.EffectiveStability

open CartPoly

variable {n : ℕ} {K : Type} [CertCoeff K] [Algebra K ℝ] [Algebra K ℂ] [IsScalarTower K ℝ ℂ]
  [CertNormLe K ℝ] [CertNormLe K ℂ]

omit [Algebra K ℝ] [IsScalarTower K ℝ ℂ] [CertNormLe K ℝ] [CertNormLe K ℂ] in
/-- The Lie remainder `H (X^1 z) - ∑_{j<L} (j!)⁻¹ ad_φ^j H (z)`, as a function of `z ∈ ℂⁿ×ℂⁿ`. -/
def stepRem (χ H : CartPolyK K) (ρ : ℝ) (L : ℕ) (z : (Fin n → ℂ) × (Fin n → ℂ)) : ℂ :=
  cartEval H (flow (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) =>
      cartEval χ w)) (cpolyOpen ρ) 1 z) - cartEval (cartLieSum χ H L) z

omit [Algebra K ℝ] [IsScalarTower K ℝ ℂ] [CertNormLe K ℝ] [CertNormLe K ℂ] in
theorem differentiableOn_cartEval (P : CartPolyK K) (U : Set ((Fin n → ℂ) × (Fin n → ℂ))) :
    DifferentiableOn ℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval P w) U :=
  ((contDiff_eval (𝕜 := ℂ) P 1).differentiable one_ne_zero).differentiableOn

omit [CertNormLe K ℝ] [CertNormLe K ℂ] in
theorem cartEval_realInclusion₂ (P : CartPolyK K) (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    cartEval P (KAM.realInclusion₂ n x) = ((cartEval P x : ℝ) : ℂ) := by
  have := cartEval_ofReal P x
  simpa [KAM.realInclusion] using this

omit [CertNormLe K ℝ] [CertNormLe K ℂ] in
/-- The real points have vanishing imaginary part of any rational polynomial. -/
theorem cartEval_realInclusion₂_im (P : CartPolyK K) (x : (Fin n → ℝ) × (Fin n → ℝ)) :
    (cartEval P (KAM.realInclusion₂ n x)).im = 0 := by
  rw [cartEval_realInclusion₂]
  exact Complex.ofReal_im _

omit [Algebra K ℝ] [IsScalarTower K ℝ ℂ] [CertNormLe K ℝ] in
/-- The majorant checks give the small-field hypothesis. -/
theorem smallField_of_supBound {χ : CartPolyK K} (hχ : CartFits n χ) {ρ δ ε : ℝ} (hδ : 0 < δ)
    (ρl : List ℚ) (hρl : ∀ i : Fin n, ((ρl.getD i 0 : ℚ) : ℝ) = ρ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hq : ∀ i : Fin n, ((cartSupBound (cartDq i χ) ρl ρl : ℚ) : ℝ) ≤ ε * δ)
    (hp : ∀ i : Fin n, ((cartSupBound (cartDp i χ) ρl ρl : ℚ) : ℝ) ≤ ε * δ) :
    SmallField (gaugeScalar δ hδ) (cpolyOpen ρ)
      (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w)) ε := by
  refine smallField_of_coord_bounds hδ (differentiableOn_cartEval χ _) hε0 hε ?_ ?_
  · intro z hz i
    rw [fderiv_eval_q]
    refine (norm_eval_le_supBound _ (cartFits_dq i hχ) ρl ρl z (fun k => ?_) (fun k => ?_)).trans
      (hq i)
    · rw [hρl]; exact (hz k).1.le
    · rw [hρl]; exact (hz k).2.le
  · intro z hz i
    rw [fderiv_eval_p]
    refine (norm_eval_le_supBound _ (cartFits_dp i hχ) ρl ρl z (fun k => ?_) (fun k => ?_)).trans
      (hp i)
    · rw [hρl]; exact (hz k).1.le
    · rw [hρl]; exact (hz k).2.le

section Remainder

variable {χ H : CartPolyK K} {ρ δ ε : ℝ} {hδ : 0 < δ}

omit [Algebra K ℝ] [IsScalarTower K ℝ ℂ] [CertNormLe K ℝ] [CertNormLe K ℂ] in
theorem differentiableOn_stepRem (hS : SmallField (gaugeScalar δ hδ) (cpolyOpen ρ)
      (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w)) ε)
    (L : ℕ) :
    DifferentiableOn ℂ (stepRem (n := n) χ H ρ L)
      (gaugeInterior (gaugeScalar δ hδ) (cpolyOpen ρ) (1 / 2)) := by
  have h1 := (flow_b hS).2.1 1 ⟨by norm_num, le_rfl⟩
  have h2 : DifferentiableOn ℂ (fun z => cartEval H
      (flow (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w))
        (cpolyOpen ρ) 1 z)) (gaugeInterior (gaugeScalar δ hδ) (cpolyOpen ρ) (1 / 2)) :=
    (differentiableOn_cartEval H univ).comp h1 (fun _ _ => mem_univ _)
  exact h2.sub (differentiableOn_cartEval _ _)

omit [Algebra K ℝ] [IsScalarTower K ℝ ℂ] [CertNormLe K ℝ] in
/-- The Lie–Taylor remainder bound on the half gauge interior. -/
theorem norm_stepRem_le (hχ : CartFits n χ) (hH : CartFits n H)
    (hS : SmallField (gaugeScalar δ hδ) (cpolyOpen ρ)
      (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w)) ε)
    (ρl : List ℚ) (hρl : ∀ i : Fin n, ((ρl.getD i 0 : ℚ) : ℝ) = ρ) {L : ℕ} (hL : 1 ≤ L)
    {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ gaugeInterior (gaugeScalar δ hδ) (cpolyOpen ρ) (1 / 2)) :
    ‖stepRem χ H ρ L z‖ ≤
      ((cartSupBound (cartAdPow χ L H) ρl ρl : ℚ) : ℝ) / (L.factorial : ℝ) := by
  obtain ⟨h1, h2⟩ := taylor_lie (differentiableOn_cartEval χ _) hS (isOpen_cpolyOpen ρ)
    subset_rfl (differentiableOn_cartEval H _) hz
    (fun t ht => flow_mem_cpolyOpen hS hz ht) hL
  have hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖adPow (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w) L
      (fun w => cartEval H w)
      (flow (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w))
        (cpolyOpen ρ) t z)‖ ≤ ((cartSupBound (cartAdPow χ L H) ρl ρl : ℚ) : ℝ) := by
    intro t ht
    have hmem := flow_mem_cpolyOpen hS hz (t := t) ⟨by linarith [ht.1], ht.2⟩
    rw [← congrFun (cartEval_adPow_complex χ H hχ hH L) _]
    refine norm_eval_le_supBound _ (cartFits_adPow hχ hH L) ρl ρl _ (fun k => ?_) (fun k => ?_)
    · rw [hρl]; exact (hmem k).1.le
    · rw [hρl]; exact (hmem k).2.le
  have h3 := h2 _ hB
  have h4 : stepRem χ H ρ L z = ∫ t in (0 : ℝ)..1, ((((1 - t) ^ (L - 1) /
      ((L - 1).factorial : ℝ) : ℝ) : ℂ)) * adPow (fun w : (Fin n → ℂ) × (Fin n → ℂ) =>
        cartEval χ w) L (fun w => cartEval H w) (flow (KAM.hamiltonianVectorFieldℂ
          (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w)) (cpolyOpen ρ) t z) := by
    rw [stepRem, cartEval_lieSum_complex χ H hχ hH L z]
    show _ - _ = _
    rw [sub_eq_iff_eq_add, add_comm]
    exact h1
  rw [h4]
  exact h3

omit [CertNormLe K ℝ] [CertNormLe K ℂ] in
/-- At a real point the remainder is the real number `H (Ψ x) - (Lie sum)(x)`. -/
theorem stepRem_realInclusion₂ (hS : SmallField (gaugeScalar δ hδ) (cpolyOpen ρ)
      (KAM.hamiltonianVectorFieldℂ (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w)) ε)
    (L : ℕ) {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hx : x ∈ realInterior (gaugeScalar δ hδ) (cpolyOpen ρ) (1 / 2)) :
    stepRem χ H ρ L (KAM.realInclusion₂ n x) =
      (((cartEval H (realFlow (fun w : (Fin n → ℂ) × (Fin n → ℂ) => cartEval χ w)
        (cpolyOpen ρ) 1 x) - cartEval (cartLieSum χ H L) x : ℝ)) : ℂ) := by
  rw [stepRem, ← realInclusion₂_realFlow (isOpen_cpolyOpen ρ) (differentiableOn_cartEval χ _) hS
    (fun y _ => cartEval_realInclusion₂_im χ y) hx ⟨by norm_num, le_rfl⟩,
    cartEval_realInclusion₂, cartEval_realInclusion₂]
  push_cast
  rfl

end Remainder

end KAM.EffectiveStability
