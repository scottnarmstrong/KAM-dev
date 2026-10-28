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

theorem assemble_fast_slow {m : ℕ} (w : Phase (m + m)) :
    assemble (fast w.2) (fast w.1) (slow w.2) (slow w.1) = w :=
  Prod.ext (Fin.append_castAdd_natAdd (f := w.1)) (Fin.append_castAdd_natAdd (f := w.2))

open scoped Matrix.Norms.Elementwise in
/-- `hc-mean`: `F = p11hsF D ρ` at a real working point is the real fixed perturbation of the
real inverse lift, the integrand of the matched average of `SecularSpectrum.diagonalize`. -/
theorem p11hsF_real_eq {D : Data n} {a : Vec n} {ρ : P11CVec n → Matrix (Fin n) (Fin n) ℂ}
    {J0 : P11Vec n} {rC σ rz B B' r' σ' : ℝ} (hn : 0 < n) (ha : a ∈ axes n)
    (h : P11HsHyp D a ρ J0 rC σ rz B B' r' σ')
    {R : P11Vec n → Matrix (Fin n) (Fin n) ℝ} {z : Phase (n + n)}
    (hz : KAM.realInclusion₂ (n + n) z ∈ p11WorkingDom n J0 (2 * σ) (2 * rC) rz)
    (hρ : DifferentiableAt ℂ ρ (KAM.realInclusion n (fun i => fast z.2 i / (2 * π))))
    (hev : ∀ᶠ y in 𝓝 (fun i => fast z.2 i / (2 * π)),
      ρ (KAM.realInclusion n y) = (R y).map (fun r : ℝ => (r : ℂ)))
    (hR : DifferentiableAt ℝ R (fun i => fast z.2 i / (2 * π))) :
    p11hsF D ρ (KAM.realInclusion₂ (n + n) z) =
      ((perturbation D false (SecularSpectrum.liftInv R
        (assemble (fun i => fast z.2 i / (2 * π)) (fun l => 2 * π * fast z.1 l)
          (slow z.2) (slow z.1))) : ℝ) : ℂ) := by
  have hg := (p11hsInput_mem_good hn h hz).2.1
  have hin := p11hsInput_real (R := R) z hρ hev hR
  set w := SecularSpectrum.liftInv R
    (assemble (fun i => fast z.2 i / (2 * π)) (fun l => 2 * π * fast z.1 l)
      (slow z.2) (slow z.1)) with hw
  unfold p11hsF
  rw [hin] at hg ⊢
  have hx : (fun i => w.1 (Fin.natAdd n i), fun i => w.2 (Fin.castAdd n i),
      fun i => w.2 (Fin.natAdd n i)) ∈ realDisc D a r' := hg
  have h1 := perturbationC_inclusion D ha h.r'_lt false hx (fun l => w.1 (Fin.castAdd n l))
  have h2 : p11hsFHat D (KAM.realInclusion₂ (n + n) w) =
      perturbationC D false (fun l => w.1 (Fin.castAdd n l))
        (inclusion (fun i => w.1 (Fin.natAdd n i), fun i => w.2 (Fin.castAdd n i),
          fun i => w.2 (Fin.natAdd n i))) := by
    unfold p11hsFHat perturbationC
    simp only [Bool.false_eq_true, ite_false, add_zero]
    rfl
  rw [h2, h1]
  exact congrArg (fun v => ((perturbation D false v : ℝ) : ℂ)) (assemble_fast_slow w)

end Real

end KAM.Planetary

end
