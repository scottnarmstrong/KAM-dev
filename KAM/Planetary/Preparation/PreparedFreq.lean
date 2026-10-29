/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PreparedResc
public import KAM.Planetary.Preparation.PreparedData

/-!
# The prepared frequency (P11A-P8b2, `stepP:p11:pr-b`)

For the prepared datum `Q` with `Q.N = (h₀ + g₂) ∘ (rescaling) / ε` on `actionNbhd box 1`:

* `p11_freq_partial_eq`: `∂^α ω̂_c = ε^{|α|} ∂^{α + e_c} (h₀ + g₂)` at the rescaled point;
* `p11_freq_partial`: the partials of `ω̂ = ∇ N` of order `j ≤ μ̄ + 1` on `actionNbhd box (3/4)`;
* `p11_pr_b`: `|ω̂| ≤ 2L + 1` and `‖D ω̂‖ ≤ 2L + 1` there (conjuncts 9, 10 of `P11PreparedSpec`).
-/

@[expose] public noncomputable section
open Set Metric
open scoped BigOperators
namespace KAM.Planetary

section Freq

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

theorem p11_freq_isOpen_actionNbhd {N : ℕ} (B : Set (Fin N → ℝ)) (r : ℝ) :
    IsOpen (KAM.actionNbhd B r) := by
  have : KAM.actionNbhd B r = ⋃ J ∈ B, ball (fun i => (J i : ℂ)) r := by
    ext I
    simp [KAM.actionNbhd, dist_eq_norm]
  rw [this]
  exact isOpen_biUnion fun J _ => isOpen_ball

/-- The action part of `p11Rescale C.J0 ε (0, I)`: `I ↦ b + ε • I`. -/
theorem p11_freq_res_eq (J0 : P11Vec n) (eps : ℝ) (I : P11CVec (n + n)) :
    (p11Rescale J0 eps (0, I)).2 =
      (Fin.append (KAM.realInclusion n J0) (fun _ => (2 * Real.pi * eps : ℂ)) : P11CVec (n + n)) +
        (eps : ℂ) • I := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> (simp [p11Rescale]; try ring)

/-- The rescaled action nbhd `actionNbhd box 1` lies in the slow box `Vh` (for `5ε ≤ s₂`). -/
theorem p11_freq_U1_sub {nu eps : ℝ} (heps : 0 < eps) (h5 : 5 * eps ≤ p11s2 C nu eps) :
    KAM.actionNbhd (p11PreparedBox n) 1 ⊆
      {I : P11CVec (n + n) | (p11Rescale C.J0 eps (0, I)).2 ∈
        p11Box (p11DevCenter C eps) (p11s2 C nu eps / 2) (Real.pi * eps / 2)} := by
  have hπ := Real.pi_gt_three
  rintro I ⟨x, hx, hI⟩
  have hxn : ∀ i, ‖x i‖ ≤ 1 / 2 := fun i => by
    have := hx i (Set.mem_univ i)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [this.1, this.2]
  have hIc : ∀ i, ‖I i‖ < 3 / 2 := fun i => by
    have h1 := norm_le_pi_norm (I - fun i => (x i : ℂ)) i
    have h2 : ‖I i‖ ≤ ‖I i - (x i : ℂ)‖ + ‖(x i : ℂ)‖ := by
      have := norm_add_le (I i - (x i : ℂ)) (x i : ℂ)
      simpa using this
    have h3 : ‖(x i : ℂ)‖ = ‖x i‖ := by simp
    simp only [Pi.sub_apply] at h1
    have := hxn i
    linarith
  show (p11Rescale C.J0 eps (0, I)).2 ∈
    p11Box (p11DevCenter C eps) (p11s2 C nu eps / 2) (Real.pi * eps / 2)
  rw [p11_freq_res_eq]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · simp only [Pi.add_apply, Fin.append_left, Pi.smul_apply, smul_eq_mul, p11DevCenter,
      add_sub_cancel_left, norm_mul]
    have : ‖(eps : ℂ)‖ = eps := by simp [abs_of_pos heps]
    rw [this]
    have := hIc (Fin.castAdd n i)
    nlinarith
  · simp only [Pi.add_apply, Fin.append_right, Pi.smul_apply, smul_eq_mul, p11DevCenter,
      add_sub_cancel_left, norm_mul]
    have : ‖(eps : ℂ)‖ = eps := by simp [abs_of_pos heps]
    rw [this]
    have := hIc (Fin.natAdd n i)
    nlinarith

theorem p11_freq_H_diff {Fast : P11FastData n} {nu eps c : ℝ} {A : P11SlowData n}
    (hs2 : 0 ≤ p11s2 C nu eps) (heps : 0 ≤ eps) (hA : P11SlowSpecOf C Fast nu eps c A) :
    DifferentiableOn ℂ (p11DevH A)
      (p11Box (p11DevCenter C eps) (p11s2 C nu eps / 2) (Real.pi * eps / 2)) := by
  obtain ⟨-, -, -, -, -, -, hh0d, hdg, -⟩ := id hA
  have hsub := p11_dev_Vh_sub (C := C) (nu := nu) hs2 heps
  refine differentiableOn_pi.2 fun _ => ?_
  exact (hh0d.mono hsub).add hdg

/-- `∂^α ω̂_c = ε^{|α|} ∂^{α + e_c} (h₀ + g₂)` at the rescaled point. -/
theorem p11_freq_partial_eq {Fast : P11FastData n} {nu eps c : ℝ} {A : P11SlowData n}
    {Q : P11PreparedData n} (heps : 0 < eps) (h5 : 5 * eps ≤ p11s2 C nu eps)
    (hs2 : 0 ≤ p11s2 C nu eps) (hA : P11SlowSpecOf C Fast nu eps c A)
    (hN : ∀ I ∈ KAM.actionNbhd (p11PreparedBox n) 1, Q.N I =
      (A.h0 (p11Rescale C.J0 eps (0, I)).2 + A.g2 (p11Rescale C.J0 eps (0, I)).2) / (eps : ℂ))
    {I : P11CVec (n + n)} (hI : I ∈ KAM.actionNbhd (p11PreparedBox n) 1)
    (α : Fin (n + n) → ℕ) (c' : Fin (n + n)) :
    p11PartialVec α (p11PreparedFreq Q) I c' =
      (eps : ℂ) ^ (∑ i, α i) * p11PartialVec (α + Pi.single c' 1) (p11DevH A)
        (p11Rescale C.J0 eps (0, I)).2 0 := by
  set U1 := KAM.actionNbhd (p11PreparedBox n) 1 with hU1
  have hU1o : IsOpen U1 := p11_freq_isOpen_actionNbhd _ _
  set Vh := p11Box (p11DevCenter C eps) (p11s2 C nu eps / 2) (Real.pi * eps / 2) with hVh
  have hVho : IsOpen Vh := p11_dev_box_isOpen _ _ _
  set b : P11CVec (n + n) := Fin.append (KAM.realInclusion n C.J0)
    (fun _ => (2 * Real.pi * eps : ℂ)) with hb
  have hres : ∀ I, (p11Rescale C.J0 eps (0, I)).2 = b + (eps : ℂ) • I := p11_freq_res_eq C.J0 eps
  have hsub := p11_freq_U1_sub (C := C) (nu := nu) heps h5
  have hHd := p11_freq_H_diff (C := C) hs2 heps.le hA
  have hmap : ∀ I ∈ U1, b + (eps : ℂ) • I ∈ Vh := fun I hI => by
    have := hsub hI
    simpa [hres] using this
  have hcont : Continuous fun I : P11CVec (n + n) => b + (eps : ℂ) • I := by fun_prop
  have hHaff : DifferentiableOn ℂ (fun I : P11CVec (n + n) => p11DevH A (b + (eps : ℂ) • I)) U1 :=
    hHd.comp (by fun_prop) hmap
  -- `Nv`
  set Nv : P11CVec (n + n) → P11CVec 1 := fun I _ => Q.N I with hNv
  have hNvEq : EqOn Nv (fun I => ((eps : ℂ)⁻¹) • p11DevH A (b + (eps : ℂ) • I)) U1 := by
    intro I hI
    funext x
    simp only [hNv, p11DevH, Pi.smul_apply, smul_eq_mul]
    rw [hN I hI, hres I]
    have : (eps : ℂ) ≠ 0 := by exact_mod_cast heps.ne'
    field_simp
  have hNvd : DifferentiableOn ℂ Nv U1 :=
    (hHaff.const_smul ((eps : ℂ)⁻¹)).congr hNvEq
  have hQd : ∀ I ∈ U1, DifferentiableAt ℂ Q.N I := fun I hI =>
    (differentiableOn_pi.1 hNvd 0).differentiableAt (hU1o.mem_nhds hI)
  set T : Fin (n + n) → P11CVec (n + n) →L[ℂ] P11CVec 1 := fun c =>
    ContinuousLinearMap.pi fun _ => ContinuousLinearMap.proj c with hT
  have hTW : ∀ c, EqOn (fun I => T c (p11PreparedFreq Q I)) (p11Step c Nv) U1 := by
    intro c I hI
    show _ = p11Step c (fun I (_ : Fin 1) => Q.N I) I
    rw [p11_dev_step_const c (hQd I hI)]
    rfl
  have hStd : ∀ c, DifferentiableOn ℂ (p11Step c Nv) U1 := fun c =>
    p11Step_differentiableOn hU1o hNvd c
  have hWd : DifferentiableOn ℂ (p11PreparedFreq Q) U1 := by
    refine differentiableOn_pi.2 fun c => ?_
    refine (differentiableOn_pi.1 (hStd c) 0).congr fun I hI => ?_
    have := congrFun (hTW c hI) 0
    simpa [hT] using this
  -- chain of identities
  have h1 := p11_partial_clm hU1o hWd (T c') α hI
  have h2 : p11PartialVec α (fun I => T c' (p11PreparedFreq Q I)) I =
      p11PartialVec α (p11Step c' Nv) I := p11_partial_congr hU1o (hTW c') α hI
  have h3 := p11_partial_step hU1o hNvd α c' hI
  have h4 : p11PartialVec (α + Pi.single c' 1) Nv I =
      p11PartialVec (α + Pi.single c' 1) (fun I => ((eps : ℂ)⁻¹) • p11DevH A (b + (eps : ℂ) • I))
        I := p11_partial_congr hU1o hNvEq _ hI
  have h5' := p11_partial_clm hU1o hHaff ((eps : ℂ)⁻¹ • ContinuousLinearMap.id ℂ (P11CVec 1))
    (α + Pi.single c' 1) hI
  have h6 := p11_partial_affine hVho hHd b (eps : ℂ) (α + Pi.single c' 1) (hmap I hI)
  have hsum : ∑ i, (α + Pi.single c' 1 : Fin (n + n) → ℕ) i = ∑ i, α i + 1 := by
    simp [Finset.sum_add_distrib]
  rw [hsum] at h6
  have hc0 : (eps : ℂ) ≠ 0 := by exact_mod_cast heps.ne'
  have key : (p11PartialVec α (p11PreparedFreq Q) I c') =
      (p11PartialVec α (fun I => T c' (p11PreparedFreq Q I)) I) 0 := by
    rw [h1]; rfl
  have h7 : p11PartialVec (α + Pi.single c' 1) (fun I => ((eps : ℂ)⁻¹) •
      p11DevH A (b + (eps : ℂ) • I)) I =
      (eps : ℂ)⁻¹ • p11PartialVec (α + Pi.single c' 1)
        (fun I => p11DevH A (b + (eps : ℂ) • I)) I := h5'
  rw [key, h2, h3, h4, h7, h6, hres I]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [pow_succ]
  field_simp

end Freq

end KAM.Planetary

end
