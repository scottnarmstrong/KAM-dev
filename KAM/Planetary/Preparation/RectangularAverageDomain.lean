/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.RectangularBracket
public import KAM.Weighted.Domains

/-!
# Rectangular averaging: the base polydisc (P11A-P4)

The rectangle `p11Box c r₁ r₂` is the `m`-neighbourhood, `m = min r₁ r₂`, of the closed polydisc
`p11AvgBase c r₁ r₂` of radii `r_j - m` about `c`; the isotropic averaging iteration is applied to
this base set with the single radius `m = r_*` (`stepP:p11:aa-same`, replacement (R3)). Inclusions
`V_m D ⊆ p11Box c r₁ r₂` and `p11Box c (r₁/2) (r₂/2) ⊆ V_{m/2} D` are proved here.
-/

@[expose] public noncomputable section
open Set
namespace KAM.Planetary

/-- Blockwise radius vector: `r₁` on the first `a` coordinates, `r₂` on the last `b`. -/
def p11BoxRad (a b : ℕ) (r1 r2 : ℝ) : Fin (a + b) → ℝ :=
  Fin.append (fun _ : Fin a => r1) (fun _ : Fin b => r2)

theorem p11Box_eq {a b : ℕ} (c : P11CVec (a + b)) (r1 r2 : ℝ) :
    p11Box c r1 r2 = {I | ∀ j, ‖I j - c j‖ < p11BoxRad a b r1 r2 j} := by
  ext I
  simp only [p11Box, mem_ofPred_eq, Fin.forall_fin_add, p11BoxRad, Fin.append_left, Fin.append_right]

theorem min_le_p11Rad {a b : ℕ} {r1 r2 : ℝ} (j : Fin (a + b)) : min r1 r2 ≤ p11BoxRad a b r1 r2 j := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [p11BoxRad]
  · simp [p11BoxRad]

/-- The closed polydisc of radii `r_j - min r₁ r₂` about `c`. -/
def p11AvgBase {a b : ℕ} (c : P11CVec (a + b)) (r1 r2 : ℝ) : Set (P11CVec (a + b)) :=
  {J | ∀ j, ‖J j - c j‖ ≤ p11BoxRad a b r1 r2 j - min r1 r2}

theorem polyNbhd_avgBase_subset {a b : ℕ} (c : P11CVec (a + b)) (r1 r2 : ℝ) :
    KAM.Weighted.polyNbhd (p11AvgBase c r1 r2) (min r1 r2) ⊆ p11Box c r1 r2 := by
  rintro I ⟨J, hJ, hIJ⟩
  rw [p11Box_eq]
  intro j
  have h1 : ‖I j - J j‖ < min r1 r2 := (norm_le_pi_norm (I - J) j).trans_lt hIJ
  have h2 := hJ j
  calc ‖I j - c j‖ = ‖(I j - J j) + (J j - c j)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖I j - J j‖ + ‖J j - c j‖ := norm_add_le _ _
    _ < p11BoxRad a b r1 r2 j := by linarith

/-- Clamping a complex number into the closed disc of radius `t`. -/
theorem exists_clamp (u : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ∃ v : ℂ, ‖v‖ ≤ t ∧ ‖u - v‖ ≤ max (‖u‖ - t) 0 := by
  by_cases hu : ‖u‖ ≤ t
  · exact ⟨u, hu, by simp⟩
  · have hu := not_le.1 hu
    have hu0 : 0 < ‖u‖ := ht.trans_lt hu
    refine ⟨((t / ‖u‖ : ℝ) : ℂ) * u, ?_, ?_⟩
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact le_of_eq (by field_simp)
    · have : u - ((t / ‖u‖ : ℝ) : ℂ) * u = ((1 - t / ‖u‖ : ℝ) : ℂ) * u := by push_cast; ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by rw [sub_nonneg, div_le_one hu0]; exact hu.le)]
      refine le_trans (le_of_eq ?_) (le_max_left _ _)
      field_simp

theorem box_half_subset {a b : ℕ} (c : P11CVec (a + b)) {r1 r2 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2) :
    p11Box c (r1 / 2) (r2 / 2) ⊆
      KAM.Weighted.polyNbhd (p11AvgBase c r1 r2) (min r1 r2 / 2) := by
  intro I hI
  rw [p11Box_eq] at hI
  have hrad : ∀ j, p11BoxRad a b (r1 / 2) (r2 / 2) j = p11BoxRad a b r1 r2 j / 2 := fun j => by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [p11BoxRad]
  have key : ∀ j, ∃ v : ℂ, ‖v‖ ≤ p11BoxRad a b r1 r2 j - min r1 r2 ∧
      ‖(I j - c j) - v‖ < min r1 r2 / 2 := fun j => by
    obtain ⟨v, hv1, hv2⟩ := exists_clamp (I j - c j) (sub_nonneg.2 (min_le_p11Rad j))
    refine ⟨v, hv1, hv2.trans_lt ?_⟩
    have h1 := hI j
    rw [hrad] at h1
    have h2 := min_le_p11Rad (a := a) (b := b) (r1 := r1) (r2 := r2) j
    refine max_lt ?_ (by positivity)
    linarith
  choose v hv1 hv2 using key
  refine ⟨fun j => c j + v j, fun j => ?_, ?_⟩
  · simpa using hv1 j
  · have hm : 0 < min r1 r2 / 2 := by have := lt_min hr1 hr2; positivity
    refine (pi_norm_lt_iff hm).2 fun j => ?_
    have := hv2 j
    show ‖I j - (c j + v j)‖ < _
    rwa [show I j - (c j + v j) = (I j - c j) - v j by ring]

end KAM.Planetary

end
