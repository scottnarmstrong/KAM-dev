/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.HamExpr
public import KAM.Frozen.Defs.InvarianceError

/-!
# The lunar client in the rotated frame (track SO, package SO-ROT; owner ruling O5)

The linear symplectic unimodular change of variables `Q₀ = q - φ`, `Q₁ = φ`, `P₀ = p`,
`P₁ = p + J`, and the Hamiltonian `H' = soHC ∘ soRotMap = P₀²/2 - P₀ + P₁ + V(Q₀ + Q₁, Q₁)`.

* `soRotMap`, `soRotMapInv`: the map and its inverse; `soRotMap_symplectic`.
* `soRotHC`, `hamiltonianVectorFieldℂ_soRotHC`: the vector field of `H'`.
* `soRotHamExpr`, `soRotHamExpr_eval`, `soRotHamExpr_clock`: `H'` in the expression language.
* `soRotHamExprScaled` and `invarianceError_const_mul`: the time-scaled client.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

open KAM KAM.Certificate

/-- The linear symplectic unimodular change of variables from the rotated coordinates
`((Q₀, Q₁), (P₀, P₁))` to the original `((q, φ), (p, J)) = ((Q₀ + Q₁, Q₁), (P₀, P₁ - P₀))`. -/
def soRotMap (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  (![z.1 0 + z.1 1, z.1 1], ![z.2 0, z.2 1 - z.2 0])

/-- Its inverse `((q, φ), (p, J)) ↦ ((q - φ, φ), (p, p + J))`. -/
def soRotMapInv (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  (![z.1 0 - z.1 1, z.1 1], ![z.2 0, z.2 0 + z.2 1])

theorem soRotMapInv_soRotMap (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : soRotMapInv (soRotMap z) = z := by
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp [soRotMapInv, soRotMap]

theorem soRotMap_soRotMapInv (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : soRotMap (soRotMapInv z) = z := by
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp [soRotMapInv, soRotMap]

/-- Symplectic: the angle block `A = [[1, 1], [0, 1]]` and the action block
`B = [[1, 0], [-1, 1]]` satisfy `Aᵀ B = I`, so `Σ_i (u_Q v_P - u_P v_Q)_i` is preserved. -/
theorem soRotMap_symplectic (u v : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    ∑ i, ((soRotMap u).1 i * (soRotMap v).2 i - (soRotMap u).2 i * (soRotMap v).1 i) =
      ∑ i, (u.1 i * v.2 i - u.2 i * v.1 i) := by
  simp only [Fin.sum_univ_two, soRotMap]
  simp
  ring

/-- `H' = soHC ∘ soRotMap = P₀²/2 - P₀ + P₁ + V(Q₀ + Q₁, Q₁)`. -/
def soRotHC (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : ℂ := soHC (soRotMap z)

theorem soRotMap_add_smul (z v : (Fin 2 → ℂ) × (Fin 2 → ℂ)) (t : ℂ) :
    soRotMap (z + t • v) = soRotMap z + t • soRotMap v := by
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp [soRotMap] <;> ring

theorem soRotMap_differentiable : Differentiable ℂ soRotMap := by
  refine Differentiable.prodMk ?_ ?_ <;> refine differentiable_pi.2 fun i => ?_ <;>
    fin_cases i <;> simp <;> fun_prop

theorem soRotHC_differentiable : Differentiable ℂ soRotHC :=
  soHC_differentiable.comp soRotMap_differentiable

theorem fderiv_soRotHC_apply (z v : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    fderiv ℂ soRotHC z v = fderiv ℂ soHC (soRotMap z) (soRotMap v) := by
  rw [fderiv_apply_eq_deriv_line (soRotHC_differentiable z)]
  have h : (fun t : ℂ => soRotHC (z + t • v)) =
      fun t : ℂ => soHC (soRotMap z + t • soRotMap v) := by
    funext t; simp only [soRotHC, soRotMap_add_smul]
  rw [h, ← fderiv_apply_eq_deriv_line (soHC_differentiable _)]

/-- `X_{H ∘ L} = L⁻¹ X_H ∘ L` for the symplectic `L` (rows `(q - φ, φ, p, p + J)` of `X_H`). -/
theorem hamiltonianVectorFieldℂ_soRotHC (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    hamiltonianVectorFieldℂ soRotHC z =
      soRotMapInv (hamiltonianVectorFieldℂ soHC (soRotMap z)) := by
  unfold hamiltonianVectorFieldℂ
  simp only [fderiv_soRotHC_apply, fderiv_soHC_apply]
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;>
    simp [soRotMapInv, soRotMap] <;> ring

/-- `H'` in the expression language: `P₁ + (P₀²/2 - P₀) + Σ_m (-ε A_m) cos(2π(2Q₀ + (2 - m)Q₁))`
(mode `(2, 2 - m)`, `m = 1, …, 7`; the `m = 2` mode is independent of `Q₁`). Division-free. -/
def soRotHamExpr : HamExpr 2 :=
  .add (.action 1) (.add (.add (.mul (.const (1 / 2)) (.pow (.action 0) 2))
      (.mul (.const (-1)) (.action 0)))
    ((List.range 7).foldr (fun m acc =>
      .add (.mul (.const (-soEpsQ * soAQ (m + 1))) (.cosMode [2, 1 - (m : ℤ)])) acc)
      (.const 0)))

theorem soRotHamExpr_foldr (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) (l : List ℕ) :
    (l.foldr (fun (m : ℕ) (acc : HamExpr 2) =>
      .add (.mul (.const (-soEpsQ * soAQ (m + 1))) (.cosMode [2, 1 - (m : ℤ)])) acc)
      (.const 0)).eval z =
    (l.foldr (fun (m : ℕ) (acc : HamExpr 2) =>
      .add (.mul (.const (-soEpsQ * soAQ (m + 1))) (.cosMode [2, -((m : ℤ) + 1)])) acc)
      (.const 0)).eval (soRotMap z) := by
  induction l with
  | nil => simp [HamExpr.eval]
  | cons m l ih =>
    simp only [List.foldr_cons, HamExpr.eval, ih]
    congr 2
    simp [modePhase, certKeyFun, Fin.sum_univ_two, soRotMap]
    congr 1
    ring

/-- **Evaluation identity**: `soRotHamExpr` denotes the landed `soHC` composed with `soRotMap`. -/
theorem soRotHamExpr_eval (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : soRotHamExpr.eval z = soRotHC z := by
  rw [soRotHC, ← soHamExpr_eval]
  simp only [soRotHamExpr, soHamExpr, HamExpr.eval, soRotHamExpr_foldr z, soRotMap]
  simp
  ring

/-- The clock direction `P₁` (`inr 1`): `∂_{P₁} H' ≡ 1`. -/
theorem soRotHamExpr_clock (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    fderiv ℂ soRotHamExpr.eval z (phaseBasis (.inr 1)) = 1 := by
  have h : soRotHamExpr.eval = soRotHC := funext soRotHamExpr_eval
  rw [h, fderiv_soRotHC_apply, fderiv_soHC_apply, phaseBasis_inr]
  simp [soRotMap]

/-- The time-scaled client Hamiltonian `c · H'` (package R1: `c = 7/4`, CONSTANTS-STUDY P4). -/
def soRotHamExprScaled (c : ℚ) : HamExpr 2 := .mul (.const c) soRotHamExpr

theorem soRotHamExprScaled_eval (c : ℚ) (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    (soRotHamExprScaled c).eval z = (c : ℂ) * soRotHC z := by
  simp [soRotHamExprScaled, HamExpr.eval, soRotHamExpr_eval]

theorem soRotHamExprScaled_clock (c : ℚ) (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    fderiv ℂ (soRotHamExprScaled c).eval z (phaseBasis (.inr 1)) = c := by
  have h : (soRotHamExprScaled c).eval = fun z => (c : ℂ) * soRotHC z :=
    funext (soRotHamExprScaled_eval c)
  rw [h, fderiv_const_mul (soRotHC_differentiable z), smul_apply,
    fderiv_soRotHC_apply, fderiv_soHC_apply, phaseBasis_inr]
  simp [soRotMap]

/-- Time scaling: `invarianceError (c H) K ω = c · invarianceError H K (c⁻¹ ω)` (`c ≠ 0`; both
sides use `fderiv`, so no differentiability premise is needed). -/
theorem invarianceError_const_mul {n : ℕ} {c : ℝ} (hc : c ≠ 0)
    (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (θ : Fin n → ℂ) :
    invarianceError (fun z => (c : ℂ) * H z) K ω θ = (c : ℂ) • invarianceError H K (c⁻¹ • ω) θ := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc
  have hf : ∀ x, fderiv ℂ (fun z => (c : ℂ) * H z) x = (c : ℂ) • fderiv ℂ H x := fun x => by
    have : Invertible (c : ℂ) := invertibleOfNonzero hc'
    exact fderiv_const_smul_of_invertible (𝕜 := ℂ) (f := H) (x := x) (c : ℂ)
  have hω : (fun i => (((c⁻¹ • ω) i : ℝ) : ℂ)) = (c : ℂ)⁻¹ • fun i => (ω i : ℂ) := by
    funext i; simp
  unfold invarianceError hamiltonianVectorFieldℂ
  simp only [hf, hω, map_smul, smul_apply, smul_inv_smul₀ hc', smul_sub, Prod.smul_mk]
  refine Prod.ext ?_ ?_ <;> ext i <;> simp

end KAM.SpinOrbit

end
