/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import KAM.Frozen.Defs.HamiltonianVectorFieldC
public import KAM.Strip.Bridges
public import KAM.Strip.RealRestriction

/-!
# Canonical setting: Poisson bracket, iterated brackets, scaled norm, symplectic form

Blueprint-N Part 5, node `bpN:p5:setting`. Phase space is `ℂⁿ × ℂⁿ` (angles first).

* `KAM.Canonical.poissonBracket`, `KAM.Canonical.adPow`: the bracket `{u, v}` and the iterated
  bracket `ad_φ^j u`, defined from Fréchet derivatives (hence total);
* `KAM.Canonical.scaledNorm`, `KAM.Canonical.scaleCLE`, `KAM.Canonical.norm_scaleCLE`: the norm
  `ν_{ρ,σ}` as a plain function, and its gauge `diag(σ⁻¹, ρ⁻¹)`;
* `KAM.Canonical.symplFormC`: the complexified symplectic form;
* `KAM.Canonical.poissonBracket_eq_fderiv_field`: `{u, v} = Du · X_v` for the frozen field
  `KAM.hamiltonianVectorFieldℂ`; antisymmetry; holomorphy of brackets and of `adPow`;
  vanishing for functions of `I` alone;
* `KAM.Canonical.RealOn`: reality on real points.
-/

@[expose] public noncomputable section

namespace KAM.Canonical

variable {n : ℕ}

/-- `bpN:p5:setting`: the Poisson bracket `{u, v} = ∑ᵢ (∂_{θᵢ}u ∂_{Iᵢ}v - ∂_{Iᵢ}u ∂_{θᵢ}v)` of
functions on `ℂⁿ × ℂⁿ` (angles first); `Fréchet` derivatives, so total. -/
def poissonBracket (u v : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (z : (Fin n → ℂ) × (Fin n → ℂ)) : ℂ :=
  ∑ i, (fderiv ℂ u z (Pi.single i 1, 0) * fderiv ℂ v z (0, Pi.single i 1) -
    fderiv ℂ u z (0, Pi.single i 1) * fderiv ℂ v z (Pi.single i 1, 0))

/-- `bpN:p5:setting`: `ad_φ⁰ u = u`, `ad_φ^{j+1} u = {ad_φ^j u, φ}`. -/
def adPow (φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) :
    ℕ → ((Fin n → ℂ) × (Fin n → ℂ) → ℂ) → ((Fin n → ℂ) × (Fin n → ℂ) → ℂ)
  | 0, u => u
  | j + 1, u => poissonBracket (adPow φ j u) φ

/-- `bpN:p5:setting`: the scaled norm `ν_{ρ,σ}(a, b) = max(|a|/σ, |b|/ρ)`; `σ` weights angles,
`ρ` actions. It is a plain function, not an instance. -/
def scaledNorm (ρ σ : ℝ) (z : (Fin n → ℂ) × (Fin n → ℂ)) : ℝ := max (‖z.1‖ / σ) (‖z.2‖ / ρ)

/-- The gauge `W = diag(σ⁻¹, ρ⁻¹)` of `scaledNorm`: `‖scaleCLE ρ σ _ _ z‖ = scaledNorm ρ σ z`. -/
def scaleCLE (ρ σ : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ) :
    ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ)) :=
  (ContinuousLinearEquiv.smulLeft (Units.mk0 ((σ : ℂ)⁻¹) (by simpa using hσ.ne'))).prodCongr
    (ContinuousLinearEquiv.smulLeft (Units.mk0 ((ρ : ℂ)⁻¹) (by simpa using hρ.ne')))

theorem norm_scaleCLE {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    ‖scaleCLE ρ σ hρ hσ z‖ = scaledNorm ρ σ z := by
  simp [scaleCLE, scaledNorm, Prod.norm_def, norm_smul, abs_of_pos hρ, abs_of_pos hσ,
    div_eq_inv_mul]

/-- The complexified frozen form `Σ (v_I w_θ - v_θ w_I)` (`KAM.symplecticForm` on `ℂⁿ × ℂⁿ`);
`symplFormC v w = ∑ i, (v.1 i, v.2 i) ⬝ Ω₀ w` for the frozen `KAM.omegaZero`. -/
def symplFormC (v w : (Fin n → ℂ) × (Fin n → ℂ)) : ℂ := ∑ i, (v.2 i * w.1 i - v.1 i * w.2 i)

/-- A `ℂ`-linear functional on `ℂⁿ × ℂⁿ` is determined by its values on the basis vectors
`(eᵢ, 0)` and `(0, eᵢ)`. -/
private theorem clm_apply_prod (L : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] ℂ) (a b : Fin n → ℂ) :
    L (a, b) = ∑ i, a i * L (Pi.single i 1, 0) + ∑ i, b i * L (0, Pi.single i 1) := by
  have h1 : ((a, b) : (Fin n → ℂ) × (Fin n → ℂ)) =
      ∑ i, a i • ((Pi.single i 1 : Fin n → ℂ), (0 : Fin n → ℂ)) +
        ∑ i, b i • ((0 : Fin n → ℂ), (Pi.single i 1 : Fin n → ℂ)) := by
    ext j <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h1]
  rw [map_add, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- `bpN:p5:setting`: `{u, v} = Du · X_v` for the frozen field
`X_v = KAM.hamiltonianVectorFieldℂ v`. -/
theorem poissonBracket_eq_fderiv_field (u v : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    poissonBracket u v z = fderiv ℂ u z (KAM.hamiltonianVectorFieldℂ v z) := by
  rw [KAM.hamiltonianVectorFieldℂ, clm_apply_prod, poissonBracket, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem poissonBracket_antisymm (u v : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (z : (Fin n → ℂ) × (Fin n → ℂ)) : poissonBracket u v z = - poissonBracket v u z := by
  rw [poissonBracket, poissonBracket, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Bracket of holomorphic functions is holomorphic (on the common open domain). -/
theorem differentiableOn_poissonBracket {U : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hU : IsOpen U)
    {u v : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hu : DifferentiableOn ℂ u U)
    (hv : DifferentiableOn ℂ v U) : DifferentiableOn ℂ (poissonBracket u v) U := by
  have hu' := (KAM.holomorphic_regularity_of_finiteDimensional hU hu).1
  have hv' := (KAM.holomorphic_regularity_of_finiteDimensional hU hv).1
  refine DifferentiableOn.fun_sum fun i _ => ?_
  have hmul : ∀ a b : (Fin n → ℂ) × (Fin n → ℂ), DifferentiableOn ℂ
      (fun z => fderiv ℂ u z a * fderiv ℂ v z b) U := fun a b =>
    (hu'.clm_apply (differentiableOn_const a)).mul (hv'.clm_apply (differentiableOn_const b))
  exact (hmul _ _).sub (hmul _ _)

theorem differentiableOn_adPow {U : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hU : IsOpen U)
    {φ u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hφ : DifferentiableOn ℂ φ U)
    (hu : DifferentiableOn ℂ u U) (j : ℕ) : DifferentiableOn ℂ (adPow φ j u) U := by
  induction j with
  | zero => exact hu
  | succ j ih => exact differentiableOn_poissonBracket hU ih hφ

/-- The derivative of a function of `I` alone vanishes in the angle directions. -/
private theorem fderiv_fst_eq_zero_of_snd {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hu : ∀ θ θ' I, u (θ, I) = u (θ', I)) (z : (Fin n → ℂ) × (Fin n → ℂ)) (a : Fin n → ℂ) :
    fderiv ℂ u z (a, 0) = 0 := by
  by_cases hd : DifferentiableAt ℂ u z
  · set v : (Fin n → ℂ) × (Fin n → ℂ) := (a, 0) with hv
    have hline : HasDerivAt (fun t : ℂ => z + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
    have hcomp : HasDerivAt (fun t : ℂ => u (z + t • v)) (fderiv ℂ u z v) 0 := by
      have hd' : HasFDerivAt u (fderiv ℂ u z) (z + (0 : ℂ) • v) := by
        simpa using hd.hasFDerivAt
      exact hd'.comp_hasDerivAt (0 : ℂ) hline
    have hconst : HasDerivAt (fun t : ℂ => u (z + t • v)) 0 0 := by
      have : (fun t : ℂ => u (z + t • v)) = fun _ => u z := by
        funext t
        obtain ⟨θ, I⟩ := z
        simpa [hv] using hu _ _ _
      rw [this]
      exact hasDerivAt_const _ _
    exact hcomp.unique hconst
  · rw [fderiv_zero_of_not_differentiableAt hd]
    rfl

/-- `{u, v} = 0` if `u, v` depend only on `I`. -/
theorem poissonBracket_eq_zero_of_snd {u v : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hu : ∀ θ θ' I, u (θ, I) = u (θ', I)) (hv : ∀ θ θ' I, v (θ, I) = v (θ', I))
    (z : (Fin n → ℂ) × (Fin n → ℂ)) : poissonBracket u v z = 0 := by
  simp [poissonBracket, fderiv_fst_eq_zero_of_snd hu, fderiv_fst_eq_zero_of_snd hv]

/-- "Real on real points" on a set `U ⊆ ℂⁿ × ℂⁿ`. -/
def RealOn (U : Set ((Fin n → ℂ) × (Fin n → ℂ))) (u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : Prop :=
  ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ U → (u (KAM.realInclusion₂ n x)).im = 0

end KAM.Canonical

end
