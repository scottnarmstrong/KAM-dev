/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.QcZero.Derivative

/-!
# Quasi-convexity consequences: `n0`, the `qb` receipts and `qc_bij`

Blueprint `bpN:p2:n0`, `bpN:p2:qc-bij` and steps `qb-unpack`, `qb-deriv`, `qb-pos`, `qb-concl`.
`qc_bij` is supplied by the existing exact result `isoenergetic_bijective_of_qc`.
-/

@[expose] public noncomputable section

namespace KAM.Nekhoroshev

variable {n : ℕ}

theorem n0 {U : Set (Fin 0 → ℝ)} {h : (Fin 0 → ℂ) → ℂ} {m : ℝ}
    (hqc : IsStrictlyQuasiConvex U h m) : U = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun I hI => ?_
  exact (hqc.2.2.2 I hI).1 (Subsingleton.elim _ _)

section QuasiConvex
variable {U : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ} {m : ℝ}
variable (hqc : IsStrictlyQuasiConvex U h m) {I : Fin n → ℝ} (hI : I ∈ U)
include hqc hI

theorem qb_unpack : 0 < m ∧ IsOpen U ∧ ContDiffOn ℝ 2 (realPart h) U ∧
    KAM.frequencyMap h I ≠ 0 ∧ (1 ≤ n) ∧
    ∀ v : Fin n → ℝ, (∑ i, KAM.frequencyMap h I i * v i) = 0 →
      m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (realPart h)) I v v := by
  obtain ⟨hm, hU, hC, hpt⟩ := hqc
  obtain ⟨hν, hQ⟩ := hpt I hI
  refine ⟨hm, hU, hC, hν, ?_, hQ⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact absurd (Subsingleton.elim _ _) hν
  · exact hn

theorem qb_deriv (lam : ℝ) :
    fderiv ℝ (fun p : (Fin n → ℝ) × ℝ =>
      (realPart h p.1, p.2 • KAM.frequencyMap h p.1)) (I, lam) =
      bordered_map (KAM.frequencyMap h I) (real_hessian_matrix h I) lam := by
  obtain ⟨-, hU, hh, -⟩ := qb_unpack hqc hI
  exact (qc_deriv hU hh hI lam).fderiv

theorem qb_pos (v : Fin n → ℝ)
    (hv : (∑ i, KAM.frequencyMap h I i * v i) = 0) (hv0 : v ≠ 0) :
    0 < ∑ i, ∑ j, v i * real_hessian_matrix h I i j * v j := by
  obtain ⟨hm, hU, hh, -, -, hb⟩ := qb_unpack hqc hI
  rw [(qd_sym hU hh hI).2.2 v]
  exact lt_of_lt_of_le (mul_pos hm (pow_pos (norm_pos_iff.mpr hv0) 2)) (hb v hv)

/-- Existing implementation `isoenergetic_bijective_of_qc` proves this exact conclusion. -/
theorem qc_bij {lam : ℝ} (hlam : 0 < lam) :
    Function.Bijective (fderiv ℝ (fun p : (Fin n → ℝ) × ℝ =>
      (realPart h p.1, p.2 • KAM.frequencyMap h p.1)) (I, lam)) :=
  isoenergetic_bijective_of_qc hqc hI hlam
end QuasiConvex

end KAM.Nekhoroshev

end
