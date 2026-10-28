/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.HoloStrip
public import KAM.Planetary.Preparation.HoloLift
public import KAM.Planetary.SecularSpectrum.Diagonalize
public import KAM.Planetary.SecularForm.AnalyticReal

/-!
# `F` on real points is the real fixed perturbation of the real lift (P11A-P2e, `hc-mean`)

For a rotation family `ρ` extending a real frame `R` (`ρ (ι y) = (R y)ℂ` near `Λ`),
`p11hsInput_real` identifies the complexified chart input at a real point with the real inverse
lift `liftInv R` composed with the period conversion `T₁`; `p11hsF_real_eq` then identifies
`F = p11hsF D ρ` there with `perturbation D false (liftInv R (assemble Λ (2π θ) y x))`, the
integrand of the matched average `avg` of `SecularSpectrum.diagonalize`.
-/

@[expose] public noncomputable section
open Set Filter Metric Real
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler SecularForm

section Real

variable {n : ℕ}

open scoped Matrix.Norms.Elementwise in
/-- `hc-mean`, real identification of the input: the complexified lift at a real point is the
real inverse lift after the period conversion `T₁` (`p11ChartInput_eq_liftInv` without `Re`). -/
theorem p11hsInput_real {ρ : P11CVec n → Matrix (Fin n) (Fin n) ℂ}
    {R : P11Vec n → Matrix (Fin n) (Fin n) ℝ} (z : Phase (n + n))
    (hρ : DifferentiableAt ℂ ρ (KAM.realInclusion n (fun i => fast z.2 i / (2 * π))))
    (hev : ∀ᶠ y in 𝓝 (fun i => fast z.2 i / (2 * π)),
      ρ (KAM.realInclusion n y) = (R y).map (fun r : ℝ => (r : ℂ)))
    (hR : DifferentiableAt ℝ R (fun i => fast z.2 i / (2 * π))) :
    p11hsInput ρ (KAM.realInclusion₂ (n + n) z) = KAM.realInclusion₂ (n + n)
      (SecularSpectrum.liftInv R
        (assemble (fun i => fast z.2 i / (2 * π)) (fun l => 2 * π * fast z.1 l)
          (slow z.2) (slow z.1))) := by
  set L : P11Vec n := fun i => fast z.2 i / (2 * π) with hL
  have hρL : ρ (KAM.realInclusion n L) = (R L).map (fun r : ℝ => (r : ℂ)) := hev.self_of_nhds
  have hder : ∀ l : Fin n, fderiv ℂ ρ (KAM.realInclusion n L) (Pi.single l 1) =
      (fderiv ℝ R L (Pi.single l 1)).map (fun r : ℝ => (r : ℂ)) := fun l => by
    have h1 := p11_fderiv_rho_real hρ hev hR (Pi.single l 1)
    have h2 : KAM.realInclusion n (Pi.single l (1 : ℝ)) = Pi.single l (1 : ℂ) := by
      ext k; simp [Pi.single_apply]; split_ifs <;> simp
    rwa [h2] at h1
  have hLc : (fun i : Fin n => ((z.2 (Fin.castAdd n i) : ℝ) : ℂ) / (2 * π)) =
      KAM.realInclusion n L := by
    funext i; simp [hL, fast, KAM.realInclusion_apply]
  have hTM : ∀ A B : Matrix (Fin n) (Fin n) ℝ,
      (A.map (fun r : ℝ => (r : ℂ))).transpose * B.map (fun r : ℝ => (r : ℂ)) =
        (A.transpose * B).map (fun r : ℝ => (r : ℂ)) := fun A B => by
    ext i j; simp [Matrix.mul_apply]
  have hmv : ∀ v : P11Vec n, ∀ i,
      ((R L).map (fun r : ℝ => (r : ℂ))).mulVec (KAM.realInclusion n v) i =
        (((R L).mulVec v i : ℝ) : ℂ) := fun v i => by
    simp [Matrix.mulVec, dotProduct]
  have hθ : ∀ l : Fin n, (∑ i, ∑ j, KAM.realInclusion n (slow z.2) i *
      (((R L).map (fun r : ℝ => (r : ℂ))).transpose *
        (fderiv ℝ R L (Pi.single l 1)).map (fun r : ℝ => (r : ℂ))) i j *
      KAM.realInclusion n (slow z.1) j) =
      ((∑ i, slow z.2 i * ((R L).transpose * fderiv ℝ R L (Pi.single l 1)).mulVec (slow z.1) i :
        ℝ) : ℂ) := fun l => by
    rw [hTM]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, KAM.realInclusion_apply]
    push_cast
    simp [Finset.mul_sum, mul_assoc]
  rw [SecularSpectrum.rotDiag_liftInv_assemble]
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · induction k using Fin.addCases with
    | left l =>
      simp only [p11hsInput, assemble, KAM.realInclusion₂_apply, Fin.append_left, Pi.add_apply,
        KAM.realInclusion_apply]
      rw [hLc, hρL, hder]
      have := hθ l
      simp only [slow, KAM.realInclusion_apply] at this
      rw [this]
      simp only [slow, fast]
      push_cast
      rfl
    | right l =>
      simp only [p11hsInput, assemble, KAM.realInclusion₂_apply, Fin.append_right,
        KAM.realInclusion_apply]
      rw [hLc, hρL]
      exact hmv (slow z.1) l
  · induction k using Fin.addCases with
    | left l =>
      simp only [p11hsInput, assemble, KAM.realInclusion₂_apply, Fin.append_left,
        KAM.realInclusion_apply]
      simp [hL, fast]
    | right l =>
      simp only [p11hsInput, assemble, KAM.realInclusion₂_apply, Fin.append_right,
        KAM.realInclusion_apply]
      rw [hLc, hρL]
      exact hmv (slow z.2) l

end Real

end KAM.Planetary

end
