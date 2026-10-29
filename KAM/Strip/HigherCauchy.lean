/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.Regularity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Second- and third-order Cauchy bounds

Iterating the first-order estimate on nested polydiscs yields bounds `4 A / δ²`
and `32 A / δ³` for the full second and third Fréchet derivatives. Holomorphy
alone supplies all regularity via `differentiableOn_fderiv_of_isOpen`.
These estimates complete the open-domain interface `bp:p1:cauchy-open`.
-/

public noncomputable section

open Metric Set

namespace KAM

variable {n : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The first derivative is uniformly bounded on the concentric half-radius ball. -/
theorem norm_fderiv_le_on_half_closedBall {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) {z : E} {δ A : ℝ}
    (hδ : 0 < δ) (hz : closedBall z δ ⊆ U)
    (hA : ∀ w ∈ closedBall z δ, ‖f w‖ ≤ A)
    {w : E} (hw : w ∈ closedBall z (δ / 2)) :
    ‖fderiv ℂ f w‖ ≤ A / (δ / 2) := by
  have hsub : closedBall w (δ / 2) ⊆ closedBall z δ :=
    closedBall_subset_closedBall' (by linarith [mem_closedBall.mp hw])
  exact norm_fderiv_le_of_closedBall_bound hU hf (by positivity) (hsub.trans hz)
    (fun u hu => hA u (hsub hu))

variable [FiniteDimensional ℂ E] [CompleteSpace F] [SecondCountableTopology F]

/-- Second Fréchet derivative bound from holomorphy and a bound on a closed polydisc. -/
theorem norm_iteratedFDeriv_two_le_of_closedBall {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) {z : E} {δ A : ℝ}
    (hδ : 0 < δ) (hz : closedBall z δ ⊆ U)
    (hA : ∀ w ∈ closedBall z δ, ‖f w‖ ≤ A) :
    ‖iteratedFDeriv ℂ 2 f z‖ ≤ 4 * A / δ ^ 2 := by
  have hd := norm_fderiv_le_of_closedBall_bound hU
    (differentiableOn_fderiv_of_isOpen hU hf) (by positivity : 0 < δ / 2)
    ((closedBall_subset_closedBall (by linarith : δ / 2 ≤ δ)).trans hz)
    (fun w hw => norm_fderiv_le_on_half_closedBall hU hf hδ hz hA hw)
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv] at hd
  convert hd using 1
  field_simp
  ring

/-- Third Fréchet derivative bound, with an explicit nonoptimal universal constant. -/
theorem norm_iteratedFDeriv_three_le_of_closedBall {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) {z : E} {δ A : ℝ}
    (hδ : 0 < δ) (hz : closedBall z δ ⊆ U)
    (hA : ∀ w ∈ closedBall z δ, ‖f w‖ ≤ A) :
    ‖iteratedFDeriv ℂ 3 f z‖ ≤ 32 * A / δ ^ 3 := by
  have hd := norm_iteratedFDeriv_two_le_of_closedBall hU
    (differentiableOn_fderiv_of_isOpen hU hf) (by positivity : 0 < δ / 2)
    ((closedBall_subset_closedBall (by linarith : δ / 2 ≤ δ)).trans hz)
    (fun w hw => norm_fderiv_le_on_half_closedBall hU hf hδ hz hA hw)
  rw [norm_iteratedFDeriv_fderiv] at hd
  convert hd using 1
  field_simp
  ring

/-- Second-order strip estimate for the full multilinear derivative. -/
theorem norm_iteratedFDeriv_two_le_of_mem_complexStrip {ρ δ A : ℝ}
    {f : (Fin n → ℂ) → F} (hf : DifferentiableOn ℂ f (complexStrip n ρ))
    (hA : ∀ w ∈ complexStrip n ρ, ‖f w‖ ≤ A) (hδ : 0 < δ)
    {z : Fin n → ℂ} (hz : z ∈ complexStrip n (ρ - δ)) :
    ‖iteratedFDeriv ℂ 2 f z‖ ≤ 4 * A / δ ^ 2 :=
  norm_iteratedFDeriv_two_le_of_closedBall (isOpen_complexStrip n ρ) hf hδ
    (closedBall_subset_complexStrip hz) (fun w hw => hA w (closedBall_subset_complexStrip hz hw))

/-- Third-order strip estimate for the full multilinear derivative. -/
theorem norm_iteratedFDeriv_three_le_of_mem_complexStrip {ρ δ A : ℝ}
    {f : (Fin n → ℂ) → F} (hf : DifferentiableOn ℂ f (complexStrip n ρ))
    (hA : ∀ w ∈ complexStrip n ρ, ‖f w‖ ≤ A) (hδ : 0 < δ)
    {z : Fin n → ℂ} (hz : z ∈ complexStrip n (ρ - δ)) :
    ‖iteratedFDeriv ℂ 3 f z‖ ≤ 32 * A / δ ^ 3 :=
  norm_iteratedFDeriv_three_le_of_closedBall (isOpen_complexStrip n ρ) hf hδ
    (closedBall_subset_complexStrip hz) (fun w hw => hA w (closedBall_subset_complexStrip hz hw))

end KAM

end
