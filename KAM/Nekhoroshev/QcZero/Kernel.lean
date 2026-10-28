/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The bordered kernel map of the isoenergetic derivative

Blueprint `bpN:p2:qc-kernel` and steps `qk-eqs`, `qk-pair`, `qk-scalar`, `qk-bij`: the linear map
`(v, u) ↦ (freq · v, u • freq + lam • A v)` has trivial kernel, hence is bijective, whenever
`freq ≠ 0`, `lam ≠ 0` and the quadratic form of `A` is nonvanishing on `freq^⊥ \ {0}`.
Neither symmetry nor positivity of `A` is used.
-/

@[expose] public noncomputable section

namespace KAM.Nekhoroshev

variable {n : ℕ}

/-- The linear map `(v,u) ↦ (freq·v, u freq + lam A v)`. -/
def bordered_map (freq : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) :
    ((Fin n → ℝ) × ℝ) →L[ℝ] (ℝ × (Fin n → ℝ)) :=
  ((∑ i, (ContinuousLinearMap.proj i).smulRight (freq i)).comp
    (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ)).prod
    ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ).smulRight freq +
      lam • (ContinuousLinearMap.pi fun i =>
        ∑ j, (ContinuousLinearMap.proj j).smulRight (A i j)).comp
          (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ))

theorem bordered_map_apply (freq : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (lam : ℝ) (v : Fin n → ℝ) (u : ℝ) :
    bordered_map freq A lam (v, u) =
      (∑ i, freq i * v i, u • freq + lam • (fun i => ∑ j, A i j * v j)) := by
  refine Prod.ext ?_ ?_
  · simp [bordered_map, mul_comm]
  · ext i
    simp [bordered_map, mul_comm]

theorem qk_eqs (freq : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (lam : ℝ) (v : Fin n → ℝ) (u : ℝ)
    (hz : bordered_map freq A lam (v, u) = 0) :
    (∑ i, freq i * v i) = 0 ∧
      u • freq + lam • (fun i => ∑ j, A i j * v j) = 0 := by
  rw [bordered_map_apply] at hz
  exact Prod.mk_eq_zero.mp hz

theorem qk_pair (freq : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    {lam : ℝ} (hlam : lam ≠ 0)
    (hA : ∀ v : Fin n → ℝ, (∑ i, freq i * v i) = 0 → v ≠ 0 →
      (∑ i, ∑ j, v i * A i j * v j) ≠ 0)
    (v : Fin n → ℝ) (u : ℝ) (hz : bordered_map freq A lam (v, u) = 0) :
    v = 0 := by
  by_contra hv
  obtain ⟨h1, h2⟩ := qk_eqs freq A lam v u hz
  apply hA v h1 hv
  have h3 : ∑ i, v i * (u * freq i + lam * ∑ j, A i j * v j) = 0 := by
    refine (Finset.sum_eq_zero fun i _ => ?_)
    have := congrFun h2 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [this, mul_zero]
  have h4 : ∑ i, v i * (u * freq i + lam * ∑ j, A i j * v j) =
      u * (∑ i, freq i * v i) + lam * ∑ i, ∑ j, v i * A i j * v j := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      ring
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
  rw [h4, h1, mul_zero, zero_add] at h3
  exact (mul_eq_zero.mp h3).resolve_left hlam

theorem qk_scalar (freq : Fin n → ℝ) (hfreq : freq ≠ 0)
    (A : Matrix (Fin n) (Fin n) ℝ) {lam : ℝ} (hlam : lam ≠ 0)
    (hA : ∀ v : Fin n → ℝ, (∑ i, freq i * v i) = 0 → v ≠ 0 →
      (∑ i, ∑ j, v i * A i j * v j) ≠ 0)
    (v : Fin n → ℝ) (u : ℝ) (hz : bordered_map freq A lam (v, u) = 0) :
    u = 0 := by
  have hv := qk_pair freq A hlam hA v u hz
  obtain ⟨-, h2⟩ := qk_eqs freq A lam v u hz
  subst hv
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hfreq
  have := congrFun h2 i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero] at this
  exact (mul_eq_zero.mp this).resolve_right hi

theorem qc_kernel (freq : Fin n → ℝ) (hfreq : freq ≠ 0)
    (A : Matrix (Fin n) (Fin n) ℝ) {lam : ℝ} (hlam : lam ≠ 0)
    (hA : ∀ v : Fin n → ℝ, (∑ i, freq i * v i) = 0 → v ≠ 0 →
      (∑ i, ∑ j, v i * A i j * v j) ≠ 0) :
    LinearMap.ker (bordered_map freq A lam).toLinearMap = ⊥ ∧
      Function.Bijective (bordered_map freq A lam) := by
  have hker : LinearMap.ker (bordered_map freq A lam).toLinearMap = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    rintro ⟨v, u⟩ hz
    have hz' : bordered_map freq A lam (v, u) = 0 := hz
    exact Prod.ext (qk_pair freq A hlam hA v u hz') (qk_scalar freq hfreq A hlam hA v u hz')
  refine ⟨hker, ?_⟩
  have hinj : Function.Injective (bordered_map freq A lam).toLinearMap :=
    LinearMap.ker_eq_bot.mp hker
  have hrank : Module.finrank ℝ ((Fin n → ℝ) × ℝ) = Module.finrank ℝ (ℝ × (Fin n → ℝ)) := by
    simp [Module.finrank_prod, add_comm]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj⟩

end KAM.Nekhoroshev
