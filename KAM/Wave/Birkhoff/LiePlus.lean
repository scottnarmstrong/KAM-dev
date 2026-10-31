/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LiePlusNum

/-!
# The `𝔚⁺`-estimates of the flow, abstract form (blueprint-W `bpW:w3:flow` (iii))

Package W3-FLOW, blueprint label `bpW:w3:flow`.

Two complete spaces `E` (`𝔚`) and `F` (`𝔚⁺`), `ι : F → E` with `‖ι‖ ≤ 1`, and a continuous
trilinear `S : E³ → F` with `‖S v‖ ≤ C ∏‖v_i‖`; `T = ι ∘ S` (`lieT`). The `F`-valued sequences
`liePsi` (`ι ψ_k = φ_k`) and `lieXi` (`ι ∘ Ξ_k = Dφ_k`) carry the same bounds as `φ_k`, `Dφ_k`.
`exists_lieGamma_sub`: `Γ_t(w) - w = ι ψ` with `‖ψ‖_F ≤ 3|t|C‖w‖³`;
`exists_lieGammaD_sub`: `DΓ_t(w) - I = ι ∘ Ξ` with `‖Ξ‖_{E→F} ≤ 10|t|C‖w‖²`.
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  (ι : F →L[ℂ] E) (S : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) F)

/-- `T = ι ∘ S`. -/
def lieT : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) E := ι.compContinuousMultilinearMap S

theorem lieT_apply (v : Fin 3 → E) : lieT ι S v = ι (S v) := rfl

/-- `ψ_k` with `ι ψ_{k+1} = φ_{k+1}`: the `F`-valued Cauchy recursion. -/
def liePsi (w : E) : ℕ → F
  | 0 => 0
  | k + 1 => ((1 : ℂ) / ((k : ℂ) + 1)) • ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k,
      S ![lieSeq (lieT ι S) w (x 0), lieSeq (lieT ι S) w (x 1), lieSeq (lieT ι S) w (x 2)]

theorem map_liePsi (w : E) (k : ℕ) : ι (liePsi ι S w (k + 1)) = lieSeq (lieT ι S) w (k + 1) := by
  rw [lieSeq_succ]
  simp [liePsi, map_smul, map_sum, lieT_apply]

variable {C : ℝ} (hC : 0 ≤ C) (hι : ‖ι‖ ≤ 1) (hS : ∀ v : Fin 3 → E, ‖S v‖ ≤ C * ∏ i, ‖v i‖)

include hι hS in
theorem lieT_bound (v : Fin 3 → E) : ‖lieT ι S v‖ ≤ C * ∏ i, ‖v i‖ := by
  rw [lieT_apply]
  refine (ι.le_opNorm _).trans ?_
  calc ‖ι‖ * ‖S v‖ ≤ 1 * ‖S v‖ := mul_le_mul_of_nonneg_right hι (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hS v

include hC hι hS in
theorem norm_liePsi_le (w : E) (k : ℕ) :
    ‖liePsi ι S w (k + 1)‖ ≤ birkLieM (k + 1) * C ^ (k + 1) * ‖w‖ ^ (2 * k + 3) := by
  refine lie_step_A k C ‖w‖ _ (fun x hx => ?_)
  have hx' := Finset.Nat.mem_antidiagonalTuple.1 hx
  simp only [Fin.sum_univ_three] at hx'
  refine (hS _).trans ?_
  have u0 := norm_lieSeq_le (lieT ι S) hC (lieT_bound ι S hι hS) w (x 0)
  have u1 := norm_lieSeq_le (lieT ι S) hC (lieT_bound ι S hι hS) w (x 1)
  have u2 := norm_lieSeq_le (lieT ι S) hC (lieT_bound ι S hι hS) w (x 2)
  have m0 := birkLieM_nonneg (x 0)
  have m1 := birkLieM_nonneg (x 1)
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  have hb : ‖lieSeq (lieT ι S) w (x 0)‖ * ‖lieSeq (lieT ι S) w (x 1)‖ *
      ‖lieSeq (lieT ι S) w (x 2)‖ ≤ (birkLieM (x 0) * C ^ x 0 * ‖w‖ ^ (2 * x 0 + 1)) *
        (birkLieM (x 1) * C ^ x 1 * ‖w‖ ^ (2 * x 1 + 1)) *
        (birkLieM (x 2) * C ^ x 2 * ‖w‖ ^ (2 * x 2 + 1)) :=
    mul_le_mul (mul_le_mul u0 u1 (norm_nonneg _) (by positivity)) u2 (norm_nonneg _)
      (by positivity)
  refine (mul_le_mul_of_nonneg_left hb hC).trans (le_of_eq ?_)
  have : C ^ (k + 1) = C * (C ^ x 0 * C ^ x 1 * C ^ x 2) := by
    rw [← pow_add, ← pow_add, pow_succ']; congr 2; omega
  have h2 : ‖w‖ ^ (2 * k + 3) = ‖w‖ ^ (2 * x 0 + 1) * ‖w‖ ^ (2 * x 1 + 1) *
      ‖w‖ ^ (2 * x 2 + 1) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [this, h2]; ring

include hC hι hS in
theorem exists_lieGamma_sub (t : ℝ) (w : E) (hq : 2 * |t| * C * ‖w‖ ^ 2 ≤ 1 / 10) :
    ∃ ψ : F, ι ψ = lieGamma (lieT ι S) t w - w ∧ ‖ψ‖ ≤ 3 * |t| * C * ‖w‖ ^ 3 := by
  have hT := lieT_bound ι S hι hS
  have hz : ∀ k : ℕ, ‖(t ^ (k + 1)) • liePsi ι S w (k + 1)‖ ≤
      (2 * |t| * C * ‖w‖ ^ 2) ^ (k + 1) * ‖w‖ := fun k => by
    rw [norm_smul, Real.norm_eq_abs, abs_pow]
    refine (mul_le_mul_of_nonneg_left (norm_liePsi_le ι S hC hι hS w k)
      (by positivity)).trans ?_
    have := lie_geom_bound (C := C) t ‖w‖ hC (norm_nonneg w) (k + 1)
    rwa [show 2 * (k + 1) + 1 = 2 * k + 3 by ring] at this
  obtain ⟨hs, hb⟩ := lie_tail_one (z := fun k => (t ^ k) • liePsi ι S w k) t ‖w‖ hC
    (norm_nonneg w) hq hz
  refine ⟨∑' k, (t ^ (k + 1)) • liePsi ι S w (k + 1), ?_, hb⟩
  rw [ι.map_tsum hs]
  have hE := summable_lieTerm (lieT ι S) hC hT t w hq
  have hsplit : lieGamma (lieT ι S) t w - w =
      ∑' k, (t ^ (k + 1)) • lieSeq (lieT ι S) w (k + 1) := by
    unfold lieGamma
    rw [hE.tsum_eq_zero_add]
    simp only [pow_zero, one_smul, lieSeq_zero, add_sub_cancel_left]
  rw [hsplit]
  refine tsum_congr fun k => ?_
  rw [← Complex.coe_smul, map_smul, Complex.coe_smul, map_liePsi]

omit [CompleteSpace E] [CompleteSpace F] hι in
include hC hS in
/-- The partial maps of `S`: `‖S(…,v,…)‖ ≤ C ∏_{j ≠ i} ‖m j‖ ‖v‖`. -/
theorem lieF_opNorm_toCLM_le (m : Fin 3 → E) :
    ‖S.toContinuousLinearMap m 0‖ ≤ C * (‖m 1‖ * ‖m 2‖) ∧
    ‖S.toContinuousLinearMap m 1‖ ≤ C * (‖m 0‖ * ‖m 2‖) ∧
    ‖S.toContinuousLinearMap m 2‖ ≤ C * (‖m 0‖ * ‖m 1‖) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have := hS (Function.update m 0 v)
    simp only [ContinuousMultilinearMap.toContinuousLinearMap_apply, Fin.prod_univ_three,
      Function.update] at this ⊢
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have := hS (Function.update m 1 v)
    simp only [ContinuousMultilinearMap.toContinuousLinearMap_apply, Fin.prod_univ_three,
      Function.update] at this ⊢
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have := hS (Function.update m 2 v)
    simp only [ContinuousMultilinearMap.toContinuousLinearMap_apply, Fin.prod_univ_three,
      Function.update] at this ⊢
    simpa [mul_comm, mul_left_comm, mul_assoc] using this

/-- The `F`-valued operators `Ξ_{k+1}` with `ι ∘ Ξ_{k+1} = Dφ_{k+1}`. -/
def lieXi (w : E) : ℕ → (E →L[ℂ] F)
  | 0 => 0
  | k + 1 => ((1 : ℂ) / ((k : ℂ) + 1)) • ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k, ∑ i : Fin 3,
      (S.toContinuousLinearMap (fun j => lieSeq (lieT ι S) w (x j)) i).comp
        (lieDer (lieT ι S) w (x i))

theorem comp_lieXi (w : E) (k : ℕ) :
    ι.comp (lieXi ι S w (k + 1)) = lieDer (lieT ι S) w (k + 1) := by
  rw [lieDer_succ]
  ext v
  simp [lieXi, map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousMultilinearMap.toContinuousLinearMap_apply, lieT_apply]

include hC hι hS in
theorem norm_lieXi_le (w : E) (k : ℕ) :
    ‖lieXi ι S w (k + 1)‖ ≤
      (2 * ((k + 1 : ℕ) : ℝ) + 1) * birkLieM (k + 1) * C ^ (k + 1) * ‖w‖ ^ (2 * (k + 1)) := by
  have hT := lieT_bound ι S hι hS
  refine lie_step_B k C ‖w‖ _ (fun x hx => ?_)
  have hx' := Finset.Nat.mem_antidiagonalTuple.1 hx
  simp only [Fin.sum_univ_three] at hx'
  have u0 := norm_lieSeq_le (lieT ι S) hC hT w (x 0)
  have u1 := norm_lieSeq_le (lieT ι S) hC hT w (x 1)
  have u2 := norm_lieSeq_le (lieT ι S) hC hT w (x 2)
  have d0 := norm_lieDer_le (lieT ι S) hC hT w (x 0)
  have d1 := norm_lieDer_le (lieT ι S) hC hT w (x 1)
  have d2 := norm_lieDer_le (lieT ι S) hC hT w (x 2)
  have ops := lieF_opNorm_toCLM_le S hC hS (fun j => lieSeq (lieT ι S) w (x j))
  simp only [Fin.sum_univ_three]
  refine (norm_add₃_le).trans ?_
  have b0 : ‖(S.toContinuousLinearMap (fun j => lieSeq (lieT ι S) w (x j)) 0).comp
      (lieDer (lieT ι S) w (x 0))‖ ≤ C * (‖lieSeq (lieT ι S) w (x 1)‖ *
        ‖lieSeq (lieT ι S) w (x 2)‖) * ‖lieDer (lieT ι S) w (x 0)‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right ops.1 (norm_nonneg _))
  have b1 : ‖(S.toContinuousLinearMap (fun j => lieSeq (lieT ι S) w (x j)) 1).comp
      (lieDer (lieT ι S) w (x 1))‖ ≤ C * (‖lieSeq (lieT ι S) w (x 0)‖ *
        ‖lieSeq (lieT ι S) w (x 2)‖) * ‖lieDer (lieT ι S) w (x 1)‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right ops.2.1 (norm_nonneg _))
  have b2 : ‖(S.toContinuousLinearMap (fun j => lieSeq (lieT ι S) w (x j)) 2).comp
      (lieDer (lieT ι S) w (x 2))‖ ≤ C * (‖lieSeq (lieT ι S) w (x 0)‖ *
        ‖lieSeq (lieT ι S) w (x 1)‖) * ‖lieDer (lieT ι S) w (x 2)‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right ops.2.2 (norm_nonneg _))
  refine (add_le_add (add_le_add b0 b1) b2).trans ?_
  exact lie_perx_D k x hx' C ‖w‖ _ _ _ _ _ _ hC (norm_nonneg w) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) u0 u1 u2
    d0 d1 d2

include hC hι hS in
theorem exists_lieGammaD_sub (t : ℝ) (w : E) (hq : 2 * |t| * C * ‖w‖ ^ 2 ≤ 1 / 10) :
    ∃ Ξ : E →L[ℂ] F, ι.comp Ξ = lieGammaD (lieT ι S) t w - ContinuousLinearMap.id ℂ E ∧
      ‖Ξ‖ ≤ 10 * |t| * C * ‖w‖ ^ 2 := by
  have hT := lieT_bound ι S hι hS
  have hz : ∀ k : ℕ, ‖(t ^ (k + 1)) • lieXi ι S w (k + 1)‖ ≤
      (2 * ((k + 1 : ℕ) : ℝ) + 1) * (2 * |t| * C * ‖w‖ ^ 2) ^ (k + 1) := fun k => by
    rw [norm_smul, Real.norm_eq_abs, abs_pow]
    refine (mul_le_mul_of_nonneg_left (norm_lieXi_le ι S hC hι hS w k)
      (by positivity)).trans ?_
    have := lie_geom_bound_D (C := C) t ‖w‖ hC (norm_nonneg w) (k + 1)
    push_cast at this ⊢
    exact this
  obtain ⟨hs, hb⟩ := lie_tail_two (z := fun k => (t ^ k) • lieXi ι S w k) t ‖w‖ hC
    (norm_nonneg w) hq hz
  refine ⟨∑' k, (t ^ (k + 1)) • lieXi ι S w (k + 1), ?_, hb⟩
  have hcomp : ∀ k, ι.comp ((t ^ (k + 1)) • lieXi ι S w (k + 1)) =
      (t ^ (k + 1)) • lieDer (lieT ι S) w (k + 1) := fun k => by
    rw [← Complex.coe_smul, ContinuousLinearMap.comp_smul, Complex.coe_smul (t ^ (k + 1)),
      comp_lieXi]
  have hmap : ι.comp (∑' k, (t ^ (k + 1)) • lieXi ι S w (k + 1)) =
      ∑' k, ι.comp ((t ^ (k + 1)) • lieXi ι S w (k + 1)) :=
    ((ContinuousLinearMap.compL ℂ E F E ι).map_tsum hs)
  rw [hmap]
  simp only [hcomp]
  have hs' := summable_lieDTerm (lieT ι S) hC hT t w hq
  unfold lieGammaD
  rw [hs'.tsum_eq_zero_add]
  simp only [pow_zero, one_smul, lieDer_zero, add_sub_cancel_left]

end KAM.Wave

end
