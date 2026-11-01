/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Product.Chart
public import KAM.Planetary.Spatial.Product.Deficit
public import KAM.Planetary.Spatial.Model

/-!
# The n-body spatial product chart: the exact Hamiltonian split

Package LP-SP-PROD, `LP:MAIN L17 (533–578)` with MAIN (1), track LP, non-frozen.

* `fSpatial ν z = |Σ_i p_i|²/2 − Σ_{i<j} ν_i ν_j/|q_i − q_j|`: the literal perturbation of MAIN (1)
  (recoil plus pair potentials);
* `spatialHamiltonian_split`: `H_μ = Σ_i ν_i E_i + μ · fSpatial` identically;
* `spatialHamiltonian_spatialPoincareProd`: on the product domain
  `H_μ(Ψ w) = −Σ_i ν_i³/(2 I_i²) + μ · fSpatial (Ψ w)`;
* `analyticOnNhd_fSpatial_spatialPoincareProd`: `fSpatial ∘ Ψ` is analytic on the part of the domain
  whose image is collision free.

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Planetary.Spatial

open KAM KAM.Planetary

variable {n : ℕ}

/-- The literal perturbation of MAIN (1): `|Σ_i p_i|²/2 − Σ_{i<j} ν_i ν_j/|q_i − q_j|`. -/
def fSpatial (ν : Fin n → ℝ) (z : Phase (n * 3)) : ℝ :=
  spaceSq (∑ i, bodyVector3 z.2 i) / 2 -
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      ν i * ν j / spaceLength (bodyVector3 z.1 i - bodyVector3 z.1 j)

/-- The Kepler part of the chart Hamiltonian, `h(I) = −Σ_i ν_i³/(2 I_i²)`. -/
def spatialHProd (ν : Fin n → ℝ) (w : Phase (n + (n + n))) : ℝ :=
  -∑ i, ν i ^ 3 / (2 * spatialActions w i ^ 2)

/-- The exact split of `H_μ` into the Kepler part and `μ f`. -/
theorem spatialHamiltonian_split (ν : Fin n → ℝ) (μ : ℝ) (z : Phase (n * 3)) :
    spatialHamiltonian ν μ z = (∑ i, spatialKeplerEnergy ν z i) + μ * fSpatial ν z := rfl

/-- Item 4: `H_μ ∘ Ψ = −Σ ν_i³/(2 I_i²) + μ · fSpatial ∘ Ψ` on the product domain. -/
theorem spatialHamiltonian_spatialPoincareProd {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (μ : ℝ)
    {w : Phase (n + (n + n))} (hw : w ∈ spatialPoincareProdDom n) :
    spatialHamiltonian ν μ (spatialPoincareProd ν w) =
      spatialHProd ν w + μ * fSpatial ν (spatialPoincareProd ν w) := by
  rw [spatialHamiltonian_split]
  congr 1
  unfold spatialHProd
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [spatialKeplerEnergy_spatialPoincareProd hν hw i, spatialBlock_snd_zero, neg_div]

/-- `fSpatial` is analytic at every collision-free point. -/
theorem analyticOnNhd_fSpatial (ν : Fin n → ℝ) :
    AnalyticOnNhd ℝ (fSpatial ν) (spatialCollisionFreeDomain n) := by
  intro z hz
  have hw : ∀ i j, i ≠ j → (posCLM3 i - posCLM3 j) z ≠ 0 := fun i j hij =>
    spaceLength_pos_iff.mp (hz.2 i j hij)
  show AnalyticAt ℝ (fun z : Phase (n * 3) =>
    spaceSq (∑ i, bodyVector3 z.2 i) / 2 -
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ν i * ν j / spaceLength (bodyVector3 z.1 i - bodyVector3 z.1 j)) z
  have hP : AnalyticAt ℝ (fun z : Phase (n * 3) =>
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ν i * ν j / spaceLength (bodyVector3 z.1 i - bodyVector3 z.1 j)) z := by
    refine Finset.analyticAt_fun_sum _ fun i _ => Finset.analyticAt_fun_sum _ fun j hj => ?_
    have hij : i ≠ j := (Finset.mem_filter.mp hj).2.ne
    have hi : AnalyticAt ℝ
        (fun x : Phase (n * 3) => (spaceLength ((posCLM3 i - posCLM3 j) x))⁻¹) z :=
      analyticAt_inv_spaceLength_comp _ (hw i j hij)
    simp only [div_eq_mul_inv]
    exact analyticAt_const.mul hi
  have hS : AnalyticAt ℝ (fun z : Phase (n * 3) => spaceSq (∑ i, bodyVector3 z.2 i)) z := by
    have := analyticAt_spaceSq_comp (∑ i, momCLM3 i : Phase (n * 3) →L[ℝ] (Fin 3 → ℝ)) z
    simpa [momCLM3_apply] using this
  have hS' : AnalyticAt ℝ (fun z : Phase (n * 3) => spaceSq (∑ i, bodyVector3 z.2 i) / 2) z := by
    simp only [div_eq_mul_inv]
    exact hS.mul analyticAt_const
  exact hS'.sub hP

/-- Item 4: `fSpatial ∘ Ψ` is analytic on the collision-free part of the domain. -/
theorem analyticOnNhd_fSpatial_spatialPoincareProd {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) :
    AnalyticOnNhd ℝ (fun w => fSpatial ν (spatialPoincareProd ν w))
      (spatialPoincareProdDom n ∩ spatialPoincareProd ν ⁻¹' spatialCollisionFreeDomain n) :=
  (analyticOnNhd_fSpatial ν).comp
    ((analyticOnNhd_spatialPoincareProd hν).mono inter_subset_left) fun _ hw => hw.2

/-- The collision-free part of the domain is open. -/
theorem isOpen_spatialPoincareProd_preimage {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) :
    IsOpen (spatialPoincareProdDom n ∩ spatialPoincareProd ν ⁻¹' spatialCollisionFreeDomain n) :=
  (analyticOnNhd_spatialPoincareProd hν).continuousOn.isOpen_inter_preimage
    (isOpen_spatialPoincareProdDom n) (isOpen_spatialCollisionFreeDomain n)

/-- The full Hamiltonian in the chart is analytic on the collision-free part of the domain. -/
theorem analyticOnNhd_spatialHamiltonian_spatialPoincareProd {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    (μ : ℝ) :
    AnalyticOnNhd ℝ (fun w => spatialHamiltonian ν μ (spatialPoincareProd ν w))
      (spatialPoincareProdDom n ∩ spatialPoincareProd ν ⁻¹' spatialCollisionFreeDomain n) :=
  (analyticOnNhd_spatialHamiltonian ν μ).comp
    ((analyticOnNhd_spatialPoincareProd hν).mono inter_subset_left) fun _ hw => hw.2

end KAM.Planetary.Spatial

end
