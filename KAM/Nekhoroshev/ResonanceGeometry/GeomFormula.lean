/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.ResonanceGeometry.Projection

/-!
# The projection formula (`bpN:p8:sqrt`, `bpN:p8:geom-formula`)

The numerical inequality `√(A²-1) - 1 ≥ A - √2` and the explicit formula for the change of
projection when one vector `k ∉ V` is added to a subspace `V`.
-/

@[expose] public noncomputable section
open Set Matrix Module Classical

namespace KAM.Nekhoroshev
variable {n : ℕ}

theorem sqrt (A : ℝ) (hA : Real.sqrt 2 ≤ A) :
    1 ≤ A ^ 2 - 1 ∧ A - Real.sqrt 2 ≤ Real.sqrt (A ^ 2 - 1) - 1 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h1 : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hA2 : 2 ≤ A ^ 2 := by nlinarith
  refine ⟨by linarith, ?_⟩
  have : A - (Real.sqrt 2 - 1) ≤ Real.sqrt (A ^ 2 - 1) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [mul_nonneg (sub_nonneg.2 hA) (sub_nonneg.2 h1)]
  linarith

theorem euclid_smul' (c : ℝ) (x : Fin n → ℝ) : euclid (c • x) = |c| * euclid x := by
  refine (sq_eq_sq₀ (euclid_nonneg' _) (mul_nonneg (abs_nonneg _) (euclid_nonneg' _))).1 ?_
  rw [mul_pow, sq_abs, euclid_sq_eq_dot, euclid_sq_eq_dot, smul_dotProduct, smul_eq_mul,
    dotProduct_smul, smul_eq_mul]
  ring

theorem geom_formula (V : Submodule ℝ (Fin n → ℝ)) (k w : Fin n → ℝ) (hk : k ∉ V) :
    let V' := V ⊔ Submodule.span ℝ {k}
    compProj V k ≠ 0 ∧
    proj V' w - proj V w = ((compProj V k ⬝ᵥ w) / euclid (compProj V k) ^ 2) • compProj V k ∧
    k ⬝ᵥ w = proj V k ⬝ᵥ proj V w + compProj V k ⬝ᵥ w ∧
    |compProj V k ⬝ᵥ w| = euclid (compProj V k) * euclid (proj V' w - proj V w) ∧
    euclid (proj V' w) ^ 2 = euclid (proj V w) ^ 2 + euclid (proj V' w - proj V w) ^ 2 := by
  intro V'
  obtain ⟨hP, hPV, hPid, hperp, -⟩ := projection V
  set q := compProj V k with hqdef
  have hqk : q = k - proj V k := rfl
  have hq0 : q ≠ 0 := by
    intro h
    exact hk (by
      have : k = proj V k := by rw [hqk] at h; exact sub_eq_zero.1 h
      rw [this]; exact hPV k)
  have hqq : 0 < q ⬝ᵥ q := lt_of_le_of_ne (by rw [← euclid_sq_eq_dot]; positivity)
    (fun h => hq0 (dotProduct_self_eq_zero.1 h.symm))
  have hqsq : euclid q ^ 2 = q ⬝ᵥ q := euclid_sq_eq_dot q
  have hkV' : k ∈ V' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self k)
  have hVV' : V ≤ V' := le_sup_left
  have hqV' : q ∈ V' := V'.sub_mem hkV' (hVV' (hPV k))
  have hqperp : ∀ y ∈ V, q ⬝ᵥ y = 0 := fun y hy => hperp k y hy
  have hPperp : ∀ y ∈ V, y ⬝ᵥ q = 0 := fun y hy => by rw [dotProduct_comm]; exact hqperp y hy
  set c := (q ⬝ᵥ w) / euclid q ^ 2 with hc
  have hcq : c * (q ⬝ᵥ q) = q ⬝ᵥ w := by
    rw [hc, hqsq]; field_simp
  have hv : proj V' w = proj V w + c • q := by
    symm
    refine proj_eq_of_perp V' w _ (V'.add_mem (hVV' (hPV w)) (V'.smul_mem _ hqV')) fun u hu => ?_
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hu
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have hy0 : (w - (proj V w + c • q)) ⬝ᵥ y = 0 := by
      rw [sub_dotProduct, add_dotProduct, smul_dotProduct, hqperp y hy]
      have := hperp w y hy
      simp only [compProj] at this
      rw [sub_dotProduct] at this
      simp [this]
    have hk0 : (w - (proj V w + c • q)) ⬝ᵥ k = 0 := by
      have hk' : k = proj V k + q := by rw [hqk]; abel
      rw [hk', dotProduct_add]
      have e1 : (w - (proj V w + c • q)) ⬝ᵥ proj V k = 0 := by
        rw [sub_dotProduct, add_dotProduct, smul_dotProduct, hqperp _ (hPV k)]
        have := hperp w _ (hPV k)
        simp only [compProj] at this
        rw [sub_dotProduct] at this
        simp [this]
      have e2 : (w - (proj V w + c • q)) ⬝ᵥ q = 0 := by
        rw [sub_dotProduct, add_dotProduct, smul_dotProduct, hPperp _ (hPV w), dotProduct_comm w q]
        simp only [smul_eq_mul, zero_add]
        rw [hcq]; ring
      rw [e1, e2, add_zero]
    rw [dotProduct_add, dotProduct_smul, hy0, hk0]
    simp
  have hd : proj V' w - proj V w = c • q := by rw [hv]; abel
  have hnorm : euclid (c • q) = |q ⬝ᵥ w| / euclid q := by
    rw [euclid_smul', hc, abs_div, abs_of_nonneg (sq_nonneg (euclid q))]
    have : 0 < euclid q := by
      rcases (euclid_nonneg' q).lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h] at hqsq; nlinarith
    field_simp
  refine ⟨hq0, hd, ?_, ?_, ?_⟩
  · have hk' : k = proj V k + q := by rw [hqk]; abel
    have hw' : proj V k ⬝ᵥ w = proj V k ⬝ᵥ proj V w := by
      have := hperp w _ (hPV k)
      simp only [compProj] at this
      rw [sub_dotProduct] at this
      linarith [dotProduct_comm (proj V k) w, dotProduct_comm (proj V k) (proj V w)]
    conv_lhs => rw [hk']
    rw [add_dotProduct, hw']
  · rw [hd, hnorm]
    have : 0 < euclid q := by
      rcases (euclid_nonneg' q).lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h] at hqsq; nlinarith
    field_simp
  · have h0 : proj V w ⬝ᵥ (c • q) = 0 := by rw [dotProduct_smul, hPperp _ (hPV w)]; simp
    have : euclid (proj V' w) ^ 2 = euclid (proj V w + c • q) ^ 2 := by rw [hv]
    rw [this, hd, euclid_sq_eq_dot, euclid_sq_eq_dot, euclid_sq_eq_dot, add_dotProduct,
      dotProduct_add, dotProduct_add, h0, dotProduct_comm (c • q) (proj V w), h0]
    ring

end KAM.Nekhoroshev
