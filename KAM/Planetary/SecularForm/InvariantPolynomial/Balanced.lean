/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.InvariantPolynomial.Coordinates

/-!
# Invariant polynomials: the balanced part

If a real polynomial `P` in the coordinates `(x, y)` of `n` planar vectors is invariant under all
orthogonal maps, then its complexification `toZW P` in the coordinates `(z, w)` agrees, at every
real point, with its *balanced part* (the monomials in which the `z`-degree equals the `w`-degree).
-/

@[expose] public noncomputable section
open MvPolynomial
namespace KAM.Planetary
namespace SecularForm
namespace Weyl

variable {n : ℕ}

/-- The `z`-degree of a monomial in the coordinates `(z, w)`. -/
def degT (μ : Fin n × Bool →₀ ℕ) : ℕ := ∑ k, μ (k, true)

/-- The `w`-degree of a monomial in the coordinates `(z, w)`. -/
def degF (μ : Fin n × Bool →₀ ℕ) : ℕ := ∑ k, μ (k, false)

/-- The sum of the monomials with equal `z`- and `w`-degree. -/
def balancedPart (Q : MvPolynomial (Fin n × Bool) ℂ) : MvPolynomial (Fin n × Bool) ℂ :=
  ∑ μ ∈ Q.support with degT μ = degF μ, monomial μ (Q.coeff μ)

theorem degT_add_degF (μ : Fin n × Bool →₀ ℕ) : degT μ + degF μ = μ.sum fun _ e => e := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type]
  simp [degT, degF, Fintype.sum_bool, Finset.sum_add_distrib, add_comm]

/-- The point `(t z, t⁻¹ w)`. -/
def zwScale (t : ℂ) (ζ : Fin n × Bool → ℂ) : Fin n × Bool → ℂ :=
  fun kb => if kb.2 then t * ζ kb else t⁻¹ * ζ kb

theorem prod_zwScale (t : ℂ) (ζ : Fin n × Bool → ℂ) (μ : Fin n × Bool →₀ ℕ) :
    ∏ i, zwScale t ζ i ^ μ i = (∏ i, ζ i ^ μ i) * t ^ degT μ * (t⁻¹) ^ degF μ := by
  have h1 : ∀ i : Fin n × Bool, zwScale t ζ i ^ μ i =
      (if i.2 then t ^ μ i else (t⁻¹) ^ μ i) * ζ i ^ μ i := by
    intro i
    obtain ⟨k, b⟩ := i
    cases b <;> simp [zwScale, mul_pow]
  simp only [h1, Finset.prod_mul_distrib, Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
  simp only [degT, degF]
  ring

theorem zw_rot_eq (t : ℂ) (ht : ‖t‖ = 1) (u : Fin n → Fin 2 → ℝ) :
    zw (fun k => (rotMat t).mulVec (u k)) = zwScale t (zw u) := by
  funext kb
  rw [zw_rot]
  have : starRingEnd ℂ t = t⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, ht]; simp
  simp [zwScale, this]

theorem eval_zwScale (Q : MvPolynomial (Fin n × Bool) ℂ) (t : ℂ) (ζ : Fin n × Bool → ℂ) :
    MvPolynomial.eval (zwScale t ζ) Q =
      ∑ μ ∈ Q.support, (Q.coeff μ * ∏ i, ζ i ^ μ i) * t ^ degT μ * (t⁻¹) ^ degF μ := by
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [prod_zwScale]; ring

theorem eval_zwScale_one (Q : MvPolynomial (Fin n × Bool) ℂ) (ζ : Fin n × Bool → ℂ) :
    MvPolynomial.eval ζ Q = ∑ μ ∈ Q.support, (Q.coeff μ * ∏ i, ζ i ^ μ i) := by
  rw [MvPolynomial.eval_eq']

theorem eval_balancedPart (Q : MvPolynomial (Fin n × Bool) ℂ) (ζ : Fin n × Bool → ℂ) :
    MvPolynomial.eval ζ (balancedPart Q) =
      ∑ μ ∈ Q.support with degT μ = degF μ, (Q.coeff μ * ∏ i, ζ i ^ μ i) := by
  simp only [balancedPart, map_sum, MvPolynomial.eval_monomial]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

/-- The invariance of `P` forces `toZW P` to agree with its balanced part at real points. -/
theorem eval_balancedPart_toZW (P : MvPolynomial (Fin n × Fin 2) ℝ)
    (hInv : ∀ R : Matrix (Fin 2) (Fin 2) ℝ, R.transpose * R = 1 →
      ∀ u : Fin n → Fin 2 → ℝ,
      MvPolynomial.eval (fun ic => (R.mulVec (u ic.1)) ic.2) P =
        MvPolynomial.eval (fun ic => u ic.1 ic.2) P)
    (u : Fin n → Fin 2 → ℝ) :
    MvPolynomial.eval (zw u) (balancedPart (toZW P)) = MvPolynomial.eval (zw u) (toZW P) := by
  classical
  set Q := toZW P with hQ
  have hrot : ∀ t : ℂ, ‖t‖ = 1 →
      MvPolynomial.eval (zwScale t (zw u)) Q = MvPolynomial.eval (zw u) Q := by
    intro t ht
    rw [← zw_rot_eq t ht, hQ, eval_toZW, eval_toZW]
    exact congrArg _ (hInv _ (rotMat_orth ht) u)
  have hbound : ∀ μ ∈ Q.support, degT μ ≤ Q.totalDegree ∧ degF μ ≤ Q.totalDegree := by
    intro μ hμ
    have := MvPolynomial.le_totalDegree hμ
    have h2 := degT_add_degF μ
    omega
  have key := sum_unbalanced_eq_zero Q.support (fun μ => Q.coeff μ * ∏ i, zw u i ^ μ i)
    degT degF Q.totalDegree (fun μ hμ => (hbound μ hμ).1) (fun μ hμ => (hbound μ hμ).2)
    (by
      intro t ht
      rw [← eval_zwScale_one, ← hrot t ht, eval_zwScale])
  rw [eval_balancedPart, eval_zwScale_one, ← Finset.sum_filter_add_sum_filter_not Q.support
    (fun μ => degT μ = degF μ)]
  rw [show (∑ μ ∈ Q.support with ¬degT μ = degF μ, Q.coeff μ * ∏ i, zw u i ^ μ i) = 0 from key]
  simp

end Weyl
end SecularForm
end KAM.Planetary
