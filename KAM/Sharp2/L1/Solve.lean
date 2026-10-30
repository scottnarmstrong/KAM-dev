/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.L1.Norms
public import KAM.Apost.Tools
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The ℓ¹ solves (package B10b)

Blueprint `bp:p2s2l1:solve` of `blueprint/parts/p2s2-l1hybrid.tex`, for the vector solution operator
`KAM.Apost.cohR` (componentwise `KAM.cohSolution`).

* `l1_cohR` (a): `‖𝓡g‖_{1,r-δ} ≤ Γ_∞(ω, δ) ‖g‖_{1,r}` and the sup bound on `T_{r-δ}`: the vector
    clauses of the
  SHARP-L9 estimate (`KAM.summableWeighted_cohSolutionPi_l1`, `KAM.norm_cohSolutionPi_l1_le`).
      These are
  coefficient estimates; the holomorphy, periodicity and zero average of `g` in the signature are
      not used.
* `l1_cohR_real` (b): the full bite at real points, `|𝓡g(x)| ≤ Γ_∞(ω, r) ‖g‖_{1,r}` for `x ∈ ℝⁿ`.
    The coefficient
  estimate at the target radius `0` (`KAM.summableWeighted_solve_sup`, which needs no `δ < r`) and
      the bound of an
  absolutely convergent Fourier series at real points (`norm_fourierSum_real_le`).
* `smallDivisorSup_smul_le` (c): `Γ_∞(sω, δ) ≤ Γ_∞(ω, δ)` for `s ≥ 1` (each term scales by `1/s`;
    no Diophantine
  premise: if the terms are unbounded both suprema are `0`).
* `differentiableOn_cohR_l1`, `isPeriodicOn_cohR`: the solution of ℓ¹ data is holomorphic on
    `T_{r-δ}` (it is the
  Fourier series of its summable coefficients) and `1`-periodic.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.Sharp2.L1

open KAM KAM.Torus KAM.Apost

variable {n : ℕ}

/-! ### Solutions of ℓ¹ data -/

/-- Blueprint `bp:p2s2l1:solve`(a): the vector clauses of `KAM.cohomological_l1` for `cohR`. -/
theorem l1_cohR {τ γ δ r A : ℝ} {ω : Fin n → ℝ} (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (hδ : 0 < δ) (hδr : δ < r) {p : ℕ} {g : (Fin n → ℂ) → Fin p → ℂ}
    (_hg : DifferentiableOn ℂ g (complexStrip n r)) (_hgp : IsPeriodicOn g r) (_hg0 : avg g = 0)
    (hA : L1Vec r g A) :
    L1Vec (r - δ) (cohR ω g) (smallDivisorSup ω δ * A) ∧
      ∀ θ ∈ complexStrip n (r - δ), ‖cohR ω g θ‖ ≤ smallDivisorSup ω δ * A :=
  ⟨⟨mul_nonneg (smallDivisorSup_nonneg ω δ) hA.1, fun l =>
      summableWeighted_cohSolutionPi_l1 hω hγ hτ hδ hδr hA.2 l⟩,
    fun _ hθ => norm_cohSolutionPi_l1_le hω hγ hτ hδ hδr hA.1 hA.2 hθ⟩

/-- An absolutely convergent Fourier series is bounded at real points by the sum of its
    coefficients. -/
theorem norm_fourierSum_real_le {b : (Fin n → ℤ) → ℂ} (hb : Fourier.SummableWeighted 0 b)
    (x : Fin n → ℝ) : ‖fourierSum b (fun j => (x j : ℂ))‖ ≤ Fourier.weightedNorm 0 b := by
  unfold fourierSum
  refine tsum_of_norm_bounded hb.hasSum fun k => ?_
  rw [norm_mul, norm_character_real]
  simp

/-- Blueprint `bp:p2s2l1:solve`(b): the full bite, at real points. -/
theorem l1_cohR_real {τ γ r A : ℝ} {ω : Fin n → ℝ} (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0
    ≤ τ)
    (hr : 0 < r) {p : ℕ} {g : (Fin n → ℂ) → Fin p → ℂ} (_hg : DifferentiableOn ℂ g (complexStrip n
        r))
    (_hgp : IsPeriodicOn g r) (_hg0 : avg g = 0) (hA : L1Vec r g A) :
    ∀ x : Fin n → ℝ, ‖cohR ω g (fun i => (x i : ℂ))‖ ≤ smallDivisorSup ω r * A := by
  intro x
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (smallDivisorSup_nonneg ω r) hA.1)).mpr fun l => ?_
  obtain ⟨h1, h2⟩ := summableWeighted_solve_sup hω.condition hγ hτ hr (hA.2 l).1
  rw [sub_self] at h1 h2
  show ‖cohSolution ω (fun z => g z l) (fun i => (x i : ℂ))‖ ≤ _
  rw [cohSolution_eq_fourierSum]
  exact (norm_fourierSum_real_le h1 x).trans
    (h2.trans (mul_le_mul_of_nonneg_left (hA.2 l).2 (smallDivisorSup_nonneg ω r)))

/-- The solution of ℓ¹ data is holomorphic on `T_{r-δ}`. -/
theorem differentiableOn_cohR_l1 {τ γ δ r A : ℝ} {ω : Fin n → ℝ} (hω : IsDiophantine γ τ ω)
    (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδr : δ < r) {p : ℕ} {g : (Fin n → ℂ) → Fin p → ℂ}
    (hA : L1Vec r g A) : DifferentiableOn ℂ (cohR ω g) (complexStrip n (r - δ)) :=
  differentiableOn_pi.mpr fun l => by
    have h := (torusCoeff_cohSolution_l1 (g := fun z => g z l) hω hγ hτ hδ hδr (hA.2 l).1).1
    show DifferentiableOn ℂ (cohSolution ω (fun z => g z l)) _
    rw [cohSolution_eq_fourierSum]
    exact differentiableOn_fourierSum h

/-- The solution operator produces `1`-periodic maps. -/
theorem isPeriodicOn_cohR {p : ℕ} (ω : Fin n → ℝ) (g : (Fin n → ℂ) → Fin p → ℂ) (r : ℝ) :
    IsPeriodicOn (cohR ω g) r := fun i z _ =>
  funext fun l => cohSolution_add_single ω (fun z => g z l) z i

/-! ### The ray -/

/-- Each term of `Γ_∞` scales by `1/s` along the ray. -/
theorem smallDivisorSupTerm_smul {ω : Fin n → ℝ} {s δ : ℝ} (hs : 0 < s) (k : Fin n → ℤ) :
    smallDivisorSupTerm (s • ω) δ k = smallDivisorSupTerm ω δ k / s := by
  unfold smallDivisorSupTerm
  split_ifs with hk
  · simp
  · have hdot : Diophantine.frequencyDot (s • ω) k = s * Diophantine.frequencyDot ω k := by
      simp only [Diophantine.frequencyDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hdot, abs_mul, abs_of_pos hs]
    ring

/-- Blueprint `bp:p2s2l1:solve`(c): a certificate for `ω*` serves the ray `{s ω* : s ≥ 1}`. -/
theorem smallDivisorSup_smul_le {ω : Fin n → ℝ} {s δ : ℝ} (hs : 1 ≤ s) :
    smallDivisorSup (s • ω) δ ≤ smallDivisorSup ω δ := by
  have hs0 : 0 < s := by linarith
  have hterm : ∀ k, smallDivisorSupTerm (s • ω) δ k ≤ smallDivisorSupTerm ω δ k := fun k => by
    rw [smallDivisorSupTerm_smul hs0]
    exact div_le_self (smallDivisorSupTerm_nonneg ω δ k) hs
  unfold smallDivisorSup
  by_cases hb : BddAbove (Set.range (smallDivisorSupTerm ω δ))
  · exact ciSup_le fun k => (hterm k).trans (le_ciSup hb k)
  · have hb' : ¬ BddAbove (Set.range (smallDivisorSupTerm (s • ω) δ)) := by
      rintro ⟨B, hB⟩
      refine hb ⟨s * B, ?_⟩
      rintro _ ⟨k, rfl⟩
      have hk := hB ⟨k, rfl⟩
      rw [smallDivisorSupTerm_smul hs0, div_le_iff₀ hs0] at hk
      linarith
    rw [Real.iSup_of_not_bddAbove hb, Real.iSup_of_not_bddAbove hb']

end KAM.Sharp2.L1

end
