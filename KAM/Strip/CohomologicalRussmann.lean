/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.CohomologicalNodes
public import KAM.Strip.CohomologicalRussmannBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The cohomological estimate with Rüssmann's exponent `τ`

`KAM.cohomological_russmann` and `KAM.cohomological_operator_russmann` are `KAM.cohomological`
and `KAM.cohomological_operator` (`KAM.Strip.CohomologicalNodes`) with the bound
`cohConst n τ / (γ δ^{τ+n}) A` replaced by `cohConstR n τ / (γ δ^τ) A`
(`KAM.cohConstR`, `KAM.Strip.CohomologicalRussmannLattice`). The scalar bound is
`KAM.norm_cohSolution_russmann_le`; this file transfers it to `ℂ^p`-valued and matrix-valued data
and to the a-priori form exactly as `KAM.Strip.CohomologicalParseval` does for the exponent
`τ + n/2`. No restriction `δ ≤ 1` is needed.
-/

public noncomputable section

open Set Filter MeasureTheory
open scoped Topology Matrix.Norms.Operator

namespace KAM

variable {n : ℕ}

section Vector

variable {ι : Type*} [Fintype ι] {ω : Fin n → ℝ} {γ τ ρ δ A : ℝ} {g : (Fin n → ℂ) → ι → ℂ}
  (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδρ : δ < ρ)
  (hg : DifferentiableOn ℂ g (complexStrip n ρ))
  (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z)
  (hA : ∀ z ∈ complexStrip n ρ, ‖g z‖ ≤ A)
  (h0 : torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0)
include hω hγ hτ hδ hδρ hg hp hA h0

/-- The Rüssmann estimate for vector-valued data, in the sup norm. -/
theorem norm_cohSolutionPi_russmann_le {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (ρ - δ)) :
    ‖cohSolutionPi ω g θ‖ ≤ cohConstR n τ / (γ * δ ^ τ) * A := by
  have hρ : 0 < ρ := hδ.trans hδρ
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA _ (ofReal_mem_complexStrip hρ 0))
  have hc := cohConstR_nonneg n τ
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun l => ?_
  obtain ⟨hgl, hpl, h0l⟩ := component_holomorphic_periodic hρ hg hp h0 l
  exact norm_cohSolution_russmann_le (g := fun z => g z l) hω hγ hτ hδ hδρ hgl hpl
    (fun z hz => (norm_le_pi_norm (g z) l).trans (hA z hz)) h0l hθ

end Vector

section Apriori

variable {ω : Fin n → ℝ} {γ τ ρ δ : ℝ}
  (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδρ : δ < ρ)

include hω hγ hτ hδ hδρ

/-- A-priori Rüssmann bound, scalar-valued (see `KAM.cohomological_apriori`). -/
theorem cohomological_apriori_russmann {u : (Fin n → ℂ) → ℂ} {H : ℝ}
    (hu : DifferentiableOn ℂ u (complexStrip n ρ))
    (hup : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → u (z + Pi.single i 1) = u z)
    (hu0 : torusAverage (fun x : Fin n → ℝ => u fun j => (x j : ℂ)) = 0)
    (hH : ∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ u θ (fun l => (ω l : ℂ))‖ ≤ H) :
    ∀ θ ∈ complexStrip n (ρ - δ),
      ‖u θ‖ ≤ cohConstR n τ / (γ * δ ^ τ) * H := by
  have hρ : 0 < ρ := hδ.trans hδρ
  have hmono : complexStrip n (ρ - δ) ⊆ complexStrip n ρ := fun z hz j => by
    have := hz j
    linarith
  set g : (Fin n → ℂ) → ℂ := fun θ => fderiv ℂ u θ (fun l => (ω l : ℂ)) with hg_def
  have hg : DifferentiableOn ℂ g (complexStrip n ρ) :=
    (differentiableOn_fderiv_of_isOpen_pi (isOpen_complexStrip n ρ) hu).clm_apply
      (differentiableOn_const _)
  have hgp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z := fun i z hz => by
    simp only [hg_def, fderiv_add_single_of_periodic hup i hz]
  have hg0 : torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0 :=
    torusAverage_complex_direction_eq_zero hρ hu hup _
  intro θ hθ
  rw [eq_cohSolution hω hγ hτ hδ hδρ hg hgp hH hg0 (hu.mono hmono)
    (fun i z hz => hup i z (hmono hz)) hu0 (fun θ _ => rfl) hθ]
  exact norm_cohSolution_russmann_le hω hγ hτ hδ hδρ hg hgp hH hg0 hθ

/-- A-priori Rüssmann bound, vector-valued, in the max norm. -/
theorem cohomological_apriori_pi_russmann {p : ℕ} {u : (Fin n → ℂ) → Fin p → ℂ} {H : ℝ}
    (hu : DifferentiableOn ℂ u (complexStrip n ρ))
    (hup : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → u (z + Pi.single i 1) = u z)
    (hu0 : torusAverage (fun x : Fin n → ℝ => u fun j => (x j : ℂ)) = 0)
    (hH : ∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ u θ (fun l => (ω l : ℂ))‖ ≤ H) :
    ∀ θ ∈ complexStrip n (ρ - δ),
      ‖u θ‖ ≤ cohConstR n τ / (γ * δ ^ τ) * H := by
  intro θ hθ
  have hρ : 0 < ρ := hδ.trans hδρ
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH _ (ofReal_mem_complexStrip hρ 0))
  have hc := cohConstR_nonneg n τ
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun l => ?_
  obtain ⟨hul, hupl, hu0l⟩ := component_holomorphic_periodic hρ hu hup hu0 l
  refine cohomological_apriori_russmann hω hγ hτ hδ hδρ (u := fun z => u z l) hul hupl hu0l ?_ θ hθ
  intro θ' hθ'
  rw [← fderiv_apply_of_differentiableAt
    (hu.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hθ'))]
  exact (norm_le_pi_norm _ l).trans (hH θ' hθ')

/-- A-priori Rüssmann bound in the operator norm (see `KAM.cohomological_apriori_operator`). -/
theorem cohomological_apriori_operator_russmann {p q : ℕ}
    {u : (Fin n → ℂ) → Matrix (Fin p) (Fin q) ℂ} {H : ℝ}
    (hu : DifferentiableOn ℂ u (complexStrip n ρ))
    (hup : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → u (z + Pi.single i 1) = u z)
    (hu0 : torusAverage (fun x : Fin n → ℝ => u fun j => (x j : ℂ)) = 0)
    (hH : ∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ u θ (fun l => (ω l : ℂ))‖ ≤ H) :
    ∀ θ ∈ complexStrip n (ρ - δ),
      ‖u θ‖ ≤ cohConstR n τ / (γ * δ ^ τ) * H := by
  intro θ hθ
  have hρ : 0 < ρ := hδ.trans hδρ
  obtain ⟨v, hv, hMv⟩ := (isGreatest_norm_mulVec (u θ)).1
  have hv1 : ‖v‖ ≤ 1 := by simpa using hv
  have hMv' : ‖(u θ).mulVec v‖ = ‖u θ‖ := hMv
  rw [← hMv']
  obtain ⟨hw, hwavg, hwd⟩ := mulVec_transfer hρ hu v ω
  refine cohomological_apriori_pi_russmann hω hγ hτ hδ hδρ (u := fun θ => (u θ).mulVec v) hw
    (fun i z hz => by simp only [hup i z hz]) ?_ ?_ θ hθ
  · rw [hwavg, hu0, Matrix.zero_mulVec]
  · intro θ' hθ'
    rw [hwd θ' hθ']
    exact (Matrix.linfty_opNorm_mulVec _ v).trans
      ((mul_le_of_le_one_right (norm_nonneg _) hv1).trans (hH θ' hθ'))

end Apriori

section MatrixData

variable {p q : ℕ} {ω : Fin n → ℝ} {γ τ ρ δ A : ℝ} {g : (Fin n → ℂ) → Matrix (Fin p) (Fin q) ℂ}
  (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδρ : δ < ρ)
  (hg : DifferentiableOn ℂ g (complexStrip n ρ))
  (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z)
  (hA : ∀ z ∈ complexStrip n ρ, ‖g z‖ ≤ A)
  (h0 : torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0)
include hω hγ hτ hδ hδρ hg hp hA h0

/-- The Rüssmann estimate in the operator norm for matrix-valued data. -/
theorem norm_cohSolutionMat_russmann_le {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (ρ - δ)) :
    ‖cohSolutionMat ω g θ‖ ≤ cohConstR n τ / (γ * δ ^ τ) * A := by
  have hρ : 0 < ρ := hδ.trans hδρ
  have hr : 0 < ρ - δ := sub_pos.mpr hδρ
  obtain ⟨v, hv, hMv⟩ := (isGreatest_norm_mulVec (cohSolutionMat ω g θ)).1
  have hv1 : ‖v‖ ≤ 1 := by simpa using hv
  have hMv' : ‖(cohSolutionMat ω g θ).mulVec v‖ = ‖cohSolutionMat ω g θ‖ := hMv
  rw [← hMv']
  obtain ⟨hG, hGavg, -⟩ := mulVec_transfer hρ hg v ω
  have hGp : ∀ (k : Fin n) z, z ∈ complexStrip n ρ →
      (g (z + Pi.single k 1)).mulVec v = (g z).mulVec v := fun k z hz => by rw [hp k z hz]
  have hGA : ∀ z ∈ complexStrip n ρ, ‖(g z).mulVec v‖ ≤ A := fun z hz =>
    (Matrix.linfty_opNorm_mulVec _ v).trans
      ((mul_le_of_le_one_right (norm_nonneg _) hv1).trans (hA z hz))
  have hG0 : torusAverage (fun x : Fin n → ℝ => (g fun j => (x j : ℂ)).mulVec v) = 0 := by
    rw [hGavg, h0, Matrix.zero_mulVec]
  have hU := differentiableOn_cohSolutionMat hω hγ hτ hδ hδρ hg hp hA h0
  obtain ⟨hw, hwavg, hwd⟩ := mulVec_transfer hr hU v ω
  have hsol : (cohSolutionMat ω g θ).mulVec v =
      cohSolutionPi ω (fun θ => (g θ).mulVec v) θ :=
    eq_cohSolutionPi hω hγ hτ hδ hδρ hG hGp hGA hG0
      (v := fun θ => (cohSolutionMat ω g θ).mulVec v) hw
      (fun k z _ => by rw [cohSolutionMat_add_single])
      (by rw [hwavg, torusAverage_cohSolutionMat hω hγ hτ hδ hδρ hg hp hA h0,
        Matrix.zero_mulVec])
      (fun θ' hθ' => by
        rw [hwd θ' hθ', fderiv_cohSolutionMat hω hγ hτ hδ hδρ hg hp hA h0 hθ']) hθ
  rw [hsol]
  exact norm_cohSolutionPi_russmann_le hω hγ hτ hδ hδρ hG hGp hGA hG0 hθ

end MatrixData

variable {ω : Fin n → ℝ} {γ τ ρ δ : ℝ}

/-- `KAM.cohomological` with the Rüssmann constant: the bound clause is
`cohConstR n τ / (γ δ^τ) A`, valid for every `0 < δ < ρ`. -/
theorem cohomological_russmann (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    (hδρ : δ < ρ) :
    (∀ (g : (Fin n → ℂ) → ℂ) (A : ℝ), DifferentiableOn ℂ g (complexStrip n ρ) →
      (∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z) →
      (∀ θ ∈ complexStrip n ρ, ‖g θ‖ ≤ A) →
      torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0 →
      DifferentiableOn ℂ (cohSolution ω g) (complexStrip n (ρ - δ)) ∧
      (∀ (i : Fin n) z, z ∈ complexStrip n (ρ - δ) →
        cohSolution ω g (z + Pi.single i 1) = cohSolution ω g z) ∧
      torusAverage (fun x : Fin n → ℝ => cohSolution ω g fun j => (x j : ℂ)) = 0 ∧
      (∀ θ ∈ complexStrip n (ρ - δ),
        fderiv ℂ (cohSolution ω g) θ (fun l => (ω l : ℂ)) = g θ) ∧
      (∀ θ ∈ complexStrip n (ρ - δ),
        ‖cohSolution ω g θ‖ ≤ cohConstR n τ / (γ * δ ^ τ) * A) ∧
      ((∀ x : Fin n → ℝ, (g fun j => (x j : ℂ)).im = 0) →
        ∀ x : Fin n → ℝ, (cohSolution ω g fun j => (x j : ℂ)).im = 0) ∧
      ∀ u : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ u (complexStrip n (ρ - δ)) →
        (∀ (i : Fin n) z, z ∈ complexStrip n (ρ - δ) → u (z + Pi.single i 1) = u z) →
        torusAverage (fun x : Fin n → ℝ => u fun j => (x j : ℂ)) = 0 →
        (∀ θ ∈ complexStrip n (ρ - δ), fderiv ℂ u θ (fun l => (ω l : ℂ)) = g θ) →
        ∀ θ ∈ complexStrip n (ρ - δ), u θ = cohSolution ω g θ) ∧
    (∀ {p : ℕ} (g : (Fin n → ℂ) → Fin p → ℂ) (A : ℝ), DifferentiableOn ℂ g (complexStrip n ρ) →
      (∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z) →
      (∀ θ ∈ complexStrip n ρ, ‖g θ‖ ≤ A) →
      torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0 →
      DifferentiableOn ℂ (cohSolutionPi ω g) (complexStrip n (ρ - δ)) ∧
      (∀ (i : Fin n) z, z ∈ complexStrip n (ρ - δ) →
        cohSolutionPi ω g (z + Pi.single i 1) = cohSolutionPi ω g z) ∧
      torusAverage (fun x : Fin n → ℝ => cohSolutionPi ω g fun j => (x j : ℂ)) = 0 ∧
      (∀ θ ∈ complexStrip n (ρ - δ),
        fderiv ℂ (cohSolutionPi ω g) θ (fun l => (ω l : ℂ)) = g θ) ∧
      (∀ θ ∈ complexStrip n (ρ - δ),
        ‖cohSolutionPi ω g θ‖ ≤ cohConstR n τ / (γ * δ ^ τ) * A) ∧
      ((∀ (x : Fin n → ℝ) (i : Fin p), (g (fun j => (x j : ℂ)) i).im = 0) →
        ∀ (x : Fin n → ℝ) (i : Fin p), (cohSolutionPi ω g (fun j => (x j : ℂ)) i).im = 0) ∧
      ∀ u : (Fin n → ℂ) → Fin p → ℂ, DifferentiableOn ℂ u (complexStrip n (ρ - δ)) →
        (∀ (i : Fin n) z, z ∈ complexStrip n (ρ - δ) → u (z + Pi.single i 1) = u z) →
        torusAverage (fun x : Fin n → ℝ => u fun j => (x j : ℂ)) = 0 →
        (∀ θ ∈ complexStrip n (ρ - δ), fderiv ℂ u θ (fun l => (ω l : ℂ)) = g θ) →
        ∀ θ ∈ complexStrip n (ρ - δ), u θ = cohSolutionPi ω g θ) :=
  ⟨fun _ _ hg hp hA h0 =>
    ⟨differentiableOn_cohSolution hω hγ hτ hδ hδρ hg hp hA h0,
      fun i z _ => cohSolution_add_single ω _ z i,
      torusAverage_cohSolution hω hγ hτ hδ hδρ hg hp hA h0,
      fun _ hθ => fderiv_cohSolution hω hγ hτ hδ hδρ hg hp hA h0 hθ,
      fun _ hθ => norm_cohSolution_russmann_le hω hγ hτ hδ hδρ hg hp hA h0 hθ,
      fun hreal x => cohSolution_im_eq_zero ω hreal x,
      fun _ hu hup hu0 hud _ hθ =>
        eq_cohSolution hω hγ hτ hδ hδρ hg hp hA h0 hu hup hu0 hud hθ⟩,
    fun _ _ hg hp hA h0 =>
    ⟨differentiableOn_cohSolutionPi hω hγ hτ hδ hδρ hg hp hA h0,
      fun i z _ => cohSolutionPi_add_single ω _ z i,
      torusAverage_cohSolutionPi hω hγ hτ hδ hδρ hg hp hA h0,
      fun _ hθ => fderiv_cohSolutionPi hω hγ hτ hδ hδρ hg hp hA h0 hθ,
      fun _ hθ => norm_cohSolutionPi_russmann_le hω hγ hτ hδ hδρ hg hp hA h0 hθ,
      fun hreal x l => cohSolutionPi_im_eq_zero ω hreal x l,
      fun _ hu hup hu0 hud _ hθ =>
        eq_cohSolutionPi hω hγ hτ hδ hδρ hg hp hA h0 hu hup hu0 hud hθ⟩⟩

/-- `KAM.cohomological_operator` with the Rüssmann constant: both bound clauses (the solution and
the a-priori bound) are `cohConstR n τ / (γ δ^τ)` times `A`, resp. `H`. -/
theorem cohomological_operator_russmann (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (hδ : 0 < δ) (hδρ : δ < ρ) :
    (∀ {p q : ℕ} (g : (Fin n → ℂ) → Matrix (Fin p) (Fin q) ℂ) (A : ℝ),
      DifferentiableOn ℂ g (complexStrip n ρ) →
      (∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z) →
      (∀ θ ∈ complexStrip n ρ, ‖g θ‖ ≤ A) →
      torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0 →
      DifferentiableOn ℂ (cohSolutionMat ω g) (complexStrip n (ρ - δ)) ∧
      (∀ (k : Fin n) z, z ∈ complexStrip n (ρ - δ) →
        cohSolutionMat ω g (z + Pi.single k 1) = cohSolutionMat ω g z) ∧
      torusAverage (fun x : Fin n → ℝ => cohSolutionMat ω g fun j => (x j : ℂ)) = 0 ∧
      (∀ θ ∈ complexStrip n (ρ - δ),
        fderiv ℂ (cohSolutionMat ω g) θ (fun l => (ω l : ℂ)) = g θ) ∧
      (∀ θ ∈ complexStrip n (ρ - δ),
        ‖cohSolutionMat ω g θ‖ ≤ cohConstR n τ / (γ * δ ^ τ) * A) ∧
      ((∀ (x : Fin n → ℝ) (i : Fin p) (j : Fin q), (g (fun l => (x l : ℂ)) i j).im = 0) →
        ∀ (x : Fin n → ℝ) (i : Fin p) (j : Fin q),
          (cohSolutionMat ω g (fun l => (x l : ℂ)) i j).im = 0) ∧
      ∀ u : (Fin n → ℂ) → Matrix (Fin p) (Fin q) ℂ,
        DifferentiableOn ℂ u (complexStrip n (ρ - δ)) →
        (∀ (k : Fin n) z, z ∈ complexStrip n (ρ - δ) → u (z + Pi.single k 1) = u z) →
        torusAverage (fun x : Fin n → ℝ => u fun j => (x j : ℂ)) = 0 →
        (∀ θ ∈ complexStrip n (ρ - δ), fderiv ℂ u θ (fun l => (ω l : ℂ)) = g θ) →
        ∀ θ ∈ complexStrip n (ρ - δ), u θ = cohSolutionMat ω g θ) ∧
    (∀ {p q : ℕ} (u : (Fin n → ℂ) → Matrix (Fin p) (Fin q) ℂ) (H : ℝ),
      DifferentiableOn ℂ u (complexStrip n ρ) →
      (∀ (i : Fin n) z, z ∈ complexStrip n ρ → u (z + Pi.single i 1) = u z) →
      torusAverage (fun x : Fin n → ℝ => u fun j => (x j : ℂ)) = 0 →
      (∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ u θ (fun l => (ω l : ℂ))‖ ≤ H) →
      ∀ θ ∈ complexStrip n (ρ - δ), ‖u θ‖ ≤ cohConstR n τ / (γ * δ ^ τ) * H) :=
  ⟨fun _ _ hg hp hA h0 =>
    ⟨differentiableOn_cohSolutionMat hω hγ hτ hδ hδρ hg hp hA h0,
      fun k z _ => cohSolutionMat_add_single ω _ z k,
      torusAverage_cohSolutionMat hω hγ hτ hδ hδρ hg hp hA h0,
      fun _ hθ => fderiv_cohSolutionMat hω hγ hτ hδ hδρ hg hp hA h0 hθ,
      fun _ hθ => norm_cohSolutionMat_russmann_le hω hγ hτ hδ hδρ hg hp hA h0 hθ,
      fun hreal x i j => cohSolutionMat_im_eq_zero ω hreal x i j,
      fun _ hu hup hu0 hud _ hθ =>
        eq_cohSolutionMat hω hγ hτ hδ hδρ hg hp hA h0 hu hup hu0 hud hθ⟩,
    fun _ _ hu hup hu0 hH =>
      cohomological_apriori_operator_russmann hω hγ hτ hδ hδρ hu hup hu0 hH⟩

end KAM

end
