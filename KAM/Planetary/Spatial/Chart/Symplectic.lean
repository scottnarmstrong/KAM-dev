/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Poincare.Symplectic
public import KAM.Planetary.Spatial.Chart.Elements
public import KAM.Planetary.Spatial.Chart.Analytic
public import KAM.Planetary.Spatial.Chart.RotAlgebra
public import KAM.Planetary.Spatial.Chart.LineDeriv

/-!
# The regular spatial Poincare chart is symplectic

Source: `LP:MAIN L17 (562–571)`, track LP, non-frozen. Item 5.

`spatialPoincare ν w = (R Φ_q, R Φ_p)` with `Φ` the embedded planar chart, so
`DΨ h = (R Dq_h + (dR_h) Φ_q, R Dp_h + (dR_h) Φ_p)` and `dR_h = R [ω_h]ₓ`
(`rot3_deriv_eq`). With `U_h = R (Dq_h + ω_h × Φ_q)` etc. the pullback of `dp ∧ dq` is

`Ω_planar + ω_k · d(Φ_q × Φ_p)_h − ω_h · d(Φ_q × Φ_p)_k − (ω_h × ω_k) · (Φ_q × Φ_p)`,

and `Φ_q × Φ_p = G e₃`, so everything reduces to the planar form (`poincare_symplectic`) and
`rot3_form_identity`, which gives `du ∧ dv`. In the repository convention (`symplecticForm` on
`Phase 3`, coordinates `((λ, ξ, v), (I, η, u))`) the result is
`symplecticForm (DΨ h) (DΨ k) = symplecticForm h k`, i.e. `dI ∧ dλ + dη ∧ dξ + du ∧ dv`.

-/

@[expose] public noncomputable section

open Matrix Filter Topology

namespace KAM.Planetary.Spatial

open KAM KAM.Kepler KAM.Planetary

/-- The bilinear algebra of the pullback: no hypotheses beyond `Rᵀ R = 1` and `dR = R [ω]ₓ`. -/
theorem symplectic_form_alg {R Mh Mk : Matrix (Fin 3) (Fin 3) ℝ} {ωh ωk : Fin 3 → ℝ}
    (hR : Rᵀ * R = 1) (hMh : Mh = R * skewMatrix ωh) (hMk : Mk = R * skewMatrix ωk)
    (Q P Qh Ph Qk Pk : Fin 3 → ℝ) :
    ((Mh *ᵥ P + R *ᵥ Ph) ⬝ᵥ (Mk *ᵥ Q + R *ᵥ Qk)) -
        ((Mh *ᵥ Q + R *ᵥ Qh) ⬝ᵥ (Mk *ᵥ P + R *ᵥ Pk)) =
      (Ph ⬝ᵥ Qk - Qh ⬝ᵥ Pk) + ωk ⬝ᵥ (Qh ⨯₃ P + Q ⨯₃ Ph) - ωh ⬝ᵥ (Qk ⨯₃ P + Q ⨯₃ Pk) -
        (ωh ⨯₃ ωk) ⬝ᵥ (Q ⨯₃ P) := by
  have hM : ∀ (M : Matrix (Fin 3) (Fin 3) ℝ) (ω : Fin 3 → ℝ), M = R * skewMatrix ω →
      ∀ x y : Fin 3 → ℝ, M *ᵥ x + R *ᵥ y = R *ᵥ (y + ω ⨯₃ x) := by
    intro M ω hMω x y
    rw [hMω, ← Matrix.mulVec_mulVec, skewMatrix_mulVec, ← Matrix.mulVec_add, add_comm]
  rw [hM Mh ωh hMh P Ph, hM Mk ωk hMk Q Qk, hM Mh ωh hMh Q Qh, hM Mk ωk hMk P Pk,
    dotProduct_mulVec_mulVec_of_orth hR, dotProduct_mulVec_mulVec_of_orth hR]
  simp [dotProduct, cross_apply, Fin.sum_univ_three]
  ring

section Planar

variable {ν : ℝ} {w : Phase 3}

/-- The planar derivative `D(poincare ν 1)(spatialPlanar w)(spatialPlanar h)`. -/
def planarDeriv (ν : ℝ) (w h : Phase 3) : Phase 2 :=
  fderiv ℝ (poincare ν 1) (spatialPlanar w) (spatialPlanar h)

lemma spatialPlanar_line (w h : Phase 3) (τ : ℝ) :
    spatialPlanar (w + τ • h) = spatialPlanar w + τ • spatialPlanar h := by
  rw [← spatialPlanarCLM_apply, ← spatialPlanarCLM_apply, ← spatialPlanarCLM_apply, map_add,
    map_smul]

theorem hasDerivAt_planar_line (hν : 0 < ν) (hw : w ∈ spatialPoincareDom) (h : Phase 3) :
    HasDerivAt (fun τ : ℝ => poincare ν 1 (spatialPlanar (w + τ • h))) (planarDeriv ν w h) 0 := by
  have hd : DifferentiableAt ℝ (poincare ν 1) (spatialPlanar w) :=
    (analyticOnNhd_poincare hν one_pos _ (spatialPlanar_mem hw)).differentiableAt
  have := hasDerivAt_fderiv_spatialLine hd (spatialPlanar h)
  show HasDerivAt _ (fderiv ℝ (poincare ν 1) (spatialPlanar w) (spatialPlanar h)) 0
  simpa only [spatialPlanar_line] using this

theorem hasDerivAt_planar_fst (hν : 0 < ν) (hw : w ∈ spatialPoincareDom) (h : Phase 3)
    (j : Fin 2) :
    HasDerivAt (fun τ : ℝ => (poincare ν 1 (spatialPlanar (w + τ • h))).1 j)
      ((planarDeriv ν w h).1 j) 0 :=
  (ContinuousLinearMap.hasFDerivAt ((ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin 2 => ℝ) j).comp
    (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)))).comp_hasDerivAt (0 : ℝ)
      (hasDerivAt_planar_line hν hw h)

theorem hasDerivAt_planar_snd (hν : 0 < ν) (hw : w ∈ spatialPoincareDom) (h : Phase 3)
    (j : Fin 2) :
    HasDerivAt (fun τ : ℝ => (poincare ν 1 (spatialPlanar (w + τ • h))).2 j)
      ((planarDeriv ν w h).2 j) 0 :=
  (ContinuousLinearMap.hasFDerivAt ((ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin 2 => ℝ) j).comp
    (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)))).comp_hasDerivAt (0 : ℝ)
      (hasDerivAt_planar_line hν hw h)

lemma eventually_line_mem (hw : w ∈ spatialPoincareDom) (h : Phase 3) :
    ∀ᶠ τ : ℝ in 𝓝 0, w + τ • h ∈ spatialPoincareDom := by
  have hc : Continuous fun τ : ℝ => w + τ • h := by fun_prop
  exact (hc.continuousAt (x := (0 : ℝ))).eventually
    (isOpen_spatialPoincareDom.mem_nhds (by simpa using hw))

/-- The derivative of the planar angular momentum `Q × P = G`. -/
theorem planarDeriv_cross (hν : 0 < ν) (hw : w ∈ spatialPoincareDom) (h : Phase 3) :
    (planarDeriv ν w h).1 0 * (poincare ν 1 (spatialPlanar w)).2 1 +
        (poincare ν 1 (spatialPlanar w)).1 0 * (planarDeriv ν w h).2 1 -
      ((planarDeriv ν w h).1 1 * (poincare ν 1 (spatialPlanar w)).2 0 +
        (poincare ν 1 (spatialPlanar w)).1 1 * (planarDeriv ν w h).2 0) = spatialDG w h := by
  have f1 := ((hasDerivAt_planar_fst hν hw h 0).mul (hasDerivAt_planar_snd hν hw h 1)).sub
    ((hasDerivAt_planar_fst hν hw h 1).mul (hasDerivAt_planar_snd hν hw h 0))
  have f2 := f1.congr_of_eventuallyEq (f₁ := fun τ : ℝ => spatialAngMom (w + τ • h))
    ((eventually_line_mem hw h).mono fun τ hτ => (spatialPlanar_cross hν hτ).symm)
  have := f2.unique (hasDerivAt_line_angMom w h)
  simpa using this

end Planar

section Chart

variable {ν : ℝ} {w : Phase 3}

/-- The derivative of the rotated embedded planar vector along a line. -/
theorem hasDerivAt_rot_embed (w h : Phase 3) (M : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3)
    (hR : ∀ j, HasDerivAt (fun τ : ℝ => spatialRot (w + τ • h) i j) (M i j) 0)
    {G : ℝ → Fin 2 → ℝ} {G' : Fin 2 → ℝ} (hG : ∀ j : Fin 2, HasDerivAt (fun τ => G τ j) (G' j) 0) :
    HasDerivAt (fun τ : ℝ => (spatialRot (w + τ • h) *ᵥ planarEmbed (G τ)) i)
      ((M *ᵥ planarEmbed (G 0)) i + (spatialRot w *ᵥ planarEmbed G') i) 0 := by
  have e : (fun τ : ℝ => (spatialRot (w + τ • h) *ᵥ planarEmbed (G τ)) i) =
      fun τ => spatialRot (w + τ • h) i 0 * G τ 0 + spatialRot (w + τ • h) i 1 * G τ 1 := by
    funext τ
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, planarEmbed]
  rw [e]
  refine (((hR 0).mul (hG 0)).add ((hR 1).mul (hG 1))).congr_deriv ?_
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, planarEmbed]
  ring

/-- `dR` for the direction `h`. -/
def spatialRotDeriv (w h : Phase 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  rot3Deriv (spatialA w) (spatialB w) (spatialC w) (spatialDA w h) (spatialDB w h)
    (spatialDC w h)

/-- The rotation vector `ω` for the direction `h`. -/
def spatialOmega (w h : Phase 3) : Fin 3 → ℝ :=
  rot3Omega (spatialA w) (spatialB w) (spatialC w) (spatialDA w h) (spatialDB w h)
    (spatialDC w h)

theorem spatialRotDeriv_eq (hw : w ∈ spatialPoincareDom) (h : Phase 3) :
    spatialRotDeriv w h = spatialRot w * skewMatrix (spatialOmega w h) := by
  rw [spatialRotDeriv, spatialOmega, spatialRot_eq_rot3]
  exact rot3_deriv_eq (spatialC_sq hw) (spatial_rel_d hw h)

theorem spatialPoincare_fderiv_fst (hν : 0 < ν) (hw : w ∈ spatialPoincareDom) (h : Phase 3) :
    (fderiv ℝ (spatialPoincare ν) w h).1 =
      spatialRotDeriv w h *ᵥ planarEmbed (poincare ν 1 (spatialPlanar w)).1 +
        spatialRot w *ᵥ planarEmbed (planarDeriv ν w h).1 := by
  have hd : DifferentiableAt ℝ (spatialPoincare ν) w :=
    (analyticOnNhd_spatialPoincare hν w hw).differentiableAt
  have hline := hasDerivAt_fderiv_spatialLine hd h
  ext i
  have hc := (ContinuousLinearMap.hasFDerivAt ((ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin 3 => ℝ) i).comp
    (ContinuousLinearMap.fst ℝ (Fin 3 → ℝ) (Fin 3 → ℝ)))).comp_hasDerivAt (0 : ℝ) hline
  have h2 := hasDerivAt_rot_embed w h (spatialRotDeriv w h) i
    (spatialRot_line_hasDerivAt hw h i)
    (G := fun τ => (poincare ν 1 (spatialPlanar (w + τ • h))).1)
    (hasDerivAt_planar_fst hν hw h)
  have := hc.unique h2
  simpa using this

theorem spatialPoincare_fderiv_snd (hν : 0 < ν) (hw : w ∈ spatialPoincareDom) (h : Phase 3) :
    (fderiv ℝ (spatialPoincare ν) w h).2 =
      spatialRotDeriv w h *ᵥ planarEmbed (poincare ν 1 (spatialPlanar w)).2 +
        spatialRot w *ᵥ planarEmbed (planarDeriv ν w h).2 := by
  have hd : DifferentiableAt ℝ (spatialPoincare ν) w :=
    (analyticOnNhd_spatialPoincare hν w hw).differentiableAt
  have hline := hasDerivAt_fderiv_spatialLine hd h
  ext i
  have hc := (ContinuousLinearMap.hasFDerivAt ((ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin 3 => ℝ) i).comp
    (ContinuousLinearMap.snd ℝ (Fin 3 → ℝ) (Fin 3 → ℝ)))).comp_hasDerivAt (0 : ℝ) hline
  have h2 := hasDerivAt_rot_embed w h (spatialRotDeriv w h) i
    (spatialRot_line_hasDerivAt hw h i)
    (G := fun τ => (poincare ν 1 (spatialPlanar (w + τ • h))).2)
    (hasDerivAt_planar_snd hν hw h)
  have := hc.unique h2
  simpa using this

end Chart

section Main

variable {ν : ℝ} {w : Phase 3}

lemma dotProduct_e₃ (x : Fin 3 → ℝ) : x ⬝ᵥ e₃ = x 2 := by
  simp [e₃, dotProduct, Fin.sum_univ_three]

/-- Item 5, pointwise: `Ω(DΨ h, DΨ k) = Ω(h, k)`. -/
theorem spatialPoincare_symplectic_at (hν : 0 < ν) (hw : w ∈ spatialPoincareDom)
    (h k : Phase 3) :
    symplecticForm (fderiv ℝ (spatialPoincare ν) w h) (fderiv ℝ (spatialPoincare ν) w k) =
      symplecticForm h k := by
  have hR := spatialRot_transpose_mul hw
  have hform : ∀ a b : Phase 3, symplecticForm a b = (a.2 ⬝ᵥ b.1) - (a.1 ⬝ᵥ b.2) := by
    intro a b; simp [symplecticForm, dotProduct, Finset.sum_sub_distrib]
  rw [hform (fderiv ℝ (spatialPoincare ν) w h) (fderiv ℝ (spatialPoincare ν) w k),
    spatialPoincare_fderiv_fst hν hw h, spatialPoincare_fderiv_snd hν hw h,
    spatialPoincare_fderiv_fst hν hw k, spatialPoincare_fderiv_snd hν hw k,
    symplectic_form_alg hR (spatialRotDeriv_eq hw h) (spatialRotDeriv_eq hw k)]
  have hQP : planarEmbed (poincare ν 1 (spatialPlanar w)).1 ⨯₃
      planarEmbed (poincare ν 1 (spatialPlanar w)).2 = spatialAngMom w • e₃ := by
    rw [planarEmbed_cross, spatialPlanar_cross hν hw]
  have hcr : ∀ d : Phase 3, planarEmbed (planarDeriv ν w d).1 ⨯₃
      planarEmbed (poincare ν 1 (spatialPlanar w)).2 +
      planarEmbed (poincare ν 1 (spatialPlanar w)).1 ⨯₃ planarEmbed (planarDeriv ν w d).2 =
      spatialDG w d • e₃ := by
    intro d
    rw [planarEmbed_cross, planarEmbed_cross, ← add_smul]
    have := planarDeriv_cross hν hw d
    congr 1
    linarith
  rw [hcr h, hcr k, hQP, dotProduct_smul, dotProduct_smul, dotProduct_smul, dotProduct_e₃,
    dotProduct_e₃, dotProduct_e₃, planarEmbed_dot, planarEmbed_dot]
  have hsym := poincare_symplectic hν one_pos (spatialPlanar w) (spatialPlanar_mem hw)
    (spatialPlanar h) (spatialPlanar k)
  have e : planeDot (planarDeriv ν w h).2 (planarDeriv ν w k).1 -
      planeDot (planarDeriv ν w h).1 (planarDeriv ν w k).2 =
      symplecticForm (planarDeriv ν w h) (planarDeriv ν w k) := by
    simp [planeDot, symplecticForm, Fin.sum_univ_two]
  rw [e]
  have hs' : symplecticForm (planarDeriv ν w h) (planarDeriv ν w k) =
      (h.2 0 * k.1 0 - h.1 0 * k.2 0) + (h.2 1 * k.1 1 - h.1 1 * k.2 1) := by
    show symplecticForm (fderiv ℝ (poincare ν 1) (spatialPlanar w) (spatialPlanar h))
      (fderiv ℝ (poincare ν 1) (spatialPlanar w) (spatialPlanar k)) = _
    rw [hsym]
    simp [symplecticForm, Fin.sum_univ_two, spatialPlanar]
    ring
  have hF3 := rot3_form_identity (s := spatialS w) (ds := spatialDS w h) (ds' := spatialDS w k)
    (spatialC_sq hw) (spatial_rel_d hw h) (spatial_rel_d hw k)
  have hu_h := spatial_rel_u hw h
  have hu_k := spatial_rel_u hw k
  have hv_h := spatial_rel_v hw h
  have hv_k := spatial_rel_v hw k
  have hG_h := spatial_rel_G hw h
  have hG_k := spatial_rel_G hw k
  have hS := spatialS_sq hw
  rw [hs', hG_h, hG_k, ← hS]
  simp only [smul_eq_mul, cross_apply, spatialOmega, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp only [symplecticForm, Fin.sum_univ_three]
  rw [hu_h, hv_k, hv_h, hu_k]
  linear_combination hF3

end Main

end KAM.Planetary.Spatial
