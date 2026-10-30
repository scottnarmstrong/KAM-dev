/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Linear.Defs
public import KAM.Apost.Exactness
public import KAM.Strip.CohomologicalNodes
public import KAM.Strip.CohomologicalOperator
public import KAM.Strip.Bridges
public import KAM.Head.Lagrangian

/-!
# Part 1 (isoenergetic linear step): approximate energy identities and energy conservation

Blueprint nodes `bpI:p1:energy-approx` (parts (a)-(e); part (f) is `energy_defect` in
`KAM/Iso/Linear/EnergyDefect.lean`) and `bpI:p1:energy-conservation`.

* `KAM.Iso.Linear.energy_approx`: (a) `H ∘ K` is holomorphic, `1`-periodic, real on reals, with
  `D(H ∘ K) = DH(K) DK`, and its average is the frozen `energyAverage`, which is real; (b)
  `∂_ω (H ∘ K) = -DH(K) E`; (c) `ηᴺ = (D(H ∘ K))ᵀ - Ω_K ω`; (d) the three vanishing averages;
  (e) the size of the energy fluctuation and of `D(H ∘ K)`.
* `KAM.Iso.Linear.energy_conservation`: an invariant torus has constant energy `Ē_H(K)`; this is
  the uniqueness clause of Part 1's cohomological equation (`KAM.cohomological`) applied to
  `u = H ∘ K - Ē_H(K)` and `g = 0`.

The auxiliary lemmas live in `KAM.Iso.Linear.Energy`. All conventions of `KAM.Apost` apply.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology

namespace KAM.Iso.Linear

open KAM KAM.Torus KAM.Apost

namespace Energy

variable {n : ℕ}

/-- A `ℂ`-linear form on `ℂⁿ` is the sum of its values on the basis vectors. -/
theorem apply_pi_decomp (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (v : Fin n → ℂ) :
    ℓ v = ∑ j, v j * ℓ (Pi.single j 1) := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- `DH(z) X_H(z) = 0` (HL19 Lemma 4.2 proof: `Ω₀` is antisymmetric). -/
theorem fderiv_apply_ham_self (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (z : (Fin n → ℂ) × (Fin n → ℂ)) : fderiv ℂ H z (hamiltonianVectorFieldℂ H z) = 0 := by
  rw [KAM.Head.clm_prod_apply_eq_sum]
  simp only [hamiltonianVectorFieldℂ, neg_mul, Finset.sum_neg_distrib]
  rw [add_neg_eq_zero]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The chain rule for `H ∘ K` at a point of the strip. -/
theorem fderiv_comp_apply {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}
    (hH : DifferentiableAt ℂ H (K θ)) (hK : DifferentiableAt ℂ K θ) (v : Fin n → ℂ) :
    fderiv ℂ (fun y => H (K y)) θ v = fderiv ℂ H (K θ) (fderiv ℂ K θ v) := by
  have h : fderiv ℂ (fun y => H (K y)) θ = (fderiv ℂ H (K θ)).comp (fderiv ℂ K θ) :=
    (hH.hasFDerivAt.comp θ hK.hasFDerivAt).fderiv
  rw [h]
  rfl

/-- `∂_ω (H ∘ K) = -DH(K) E` (HL19 (4.3)), pointwise at a point where `H` and `K` are
differentiable. -/
theorem fderiv_comp_omega {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}
    (hH : DifferentiableAt ℂ H (K θ)) (hK : DifferentiableAt ℂ K θ) (ω : Fin n → ℝ) :
    fderiv ℂ (fun y => H (K y)) θ (fun l => (ω l : ℂ)) =
      -fderiv ℂ H (K θ) (invarianceError H K ω θ) := by
  rw [fderiv_comp_apply hH hK, invarianceError, map_sub, fderiv_apply_ham_self]
  ring

/-- Strips are monotone in the width. -/
theorem strip_subset {r r' : ℝ} (h : r' ≤ r) : complexStrip n r' ⊆ complexStrip n r :=
  fun _ hθ i => (hθ i).trans_le h

/-- Every point of the strip `T_r` lies in `T_{r-δ}` for some `δ ∈ (0, r)`. -/
theorem exists_strip_margin (i₀ : Fin n) {θ : Fin n → ℂ} {r : ℝ} (hr : 0 < r)
    (hθ : θ ∈ complexStrip n r) : ∃ δ, 0 < δ ∧ δ < r ∧ θ ∈ complexStrip n (r - δ) := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => |(θ i).im|)
    ⟨i₀, Finset.mem_univ _⟩
  refine ⟨(r - |(θ j).im|) / 2, ?_, ?_, fun i => ?_⟩
  · linarith [hθ j]
  · linarith [abs_nonneg (θ j).im]
  · have := hj i (Finset.mem_univ _)
    linarith [hθ j]

/-- The average of `f - c` is the average of `f` minus `c` (for continuous `f`). -/
theorem torusAverage_sub_const {f : (Fin n → ℝ) → ℂ} (hf : Continuous f) (c : ℂ) :
    torusAverage (fun x => f x - c) = torusAverage f - c := by
  unfold torusAverage
  have hfin : volume (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1) ≠ ⊤ := by
    rw [volume_unitCube]
    exact ENNReal.one_ne_top
  rw [integral_sub (integrableOn_unitCube_of_continuous hf) (integrableOn_const hfin),
    setIntegral_const, measureReal_def, volume_unitCube]
  simp

end Energy

section Torus

variable {n : ℕ} {τ M σK σB σT γ : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ}

/-- The centred energy `u = H ∘ K - Ē_H(K)` is holomorphic and `1`-periodic on `T_r`, with zero
average (HL19 Lemma 4.2). -/
theorem Energy.centered (hS : Setting n τ M σK σB σT D H ω γ) {r : ℝ} (hr : 0 < r)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKp : IsPrimaryOnStrip K r) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D) :
    DifferentiableOn ℂ (fun θ => H (K θ) - KAM.Iso.energyAverage H K) (complexStrip n r) ∧
      (∀ (i : Fin n) z, z ∈ complexStrip n r →
        (fun θ => H (K θ) - KAM.Iso.energyAverage H K) (z + Pi.single i 1) =
          (fun θ => H (K θ) - KAM.Iso.energyAverage H K) z) ∧
      torusAverage (fun x : Fin n → ℝ =>
        (fun θ => H (K θ) - KAM.Iso.energyAverage H K) fun j => (x j : ℂ)) = 0 := by
  have hHK : DifferentiableOn ℂ (fun θ => H (K θ)) (complexStrip n r) := hS.holo.comp hK hKD
  have hper : IsPeriodicOn (fun θ => H (K θ)) r := periodic_h_comp_K hS.toStanding hKD hKp
  refine ⟨hHK.sub_const _, fun i z hz => ?_, ?_⟩
  · simp only [hper i z hz]
  · have hcont : Continuous (fun x : Fin n → ℝ => H (K fun j => (x j : ℂ))) :=
      Exactness.continuous_real_of_differentiableOn hr hHK
    show torusAverage (fun x : Fin n → ℝ => H (K fun j => (x j : ℂ)) -
      KAM.Iso.energyAverage H K) = 0
    rw [Energy.torusAverage_sub_const hcont]
    exact sub_eq_zero.2 rfl

/-- `bpI:p1:energy-approx` (a)–(e); `Γ_δ = c_R γ⁻¹ δ^{-κ}`. -/
theorem energy_approx (hS : Setting n τ M σK σB σT D H ω γ) {r : ℝ} (hr : 0 < r)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKp : IsPrimaryOnStrip K r) (hKr : IsRealOnReals K) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D) :
    (DifferentiableOn ℂ (fun θ => H (K θ)) (complexStrip n r) ∧
      IsPeriodicOn (fun θ => H (K θ)) r ∧ (∀ x : Fin n → ℝ, (H (K fun i => (x i : ℂ))).im = 0) ∧
      (∀ θ ∈ complexStrip n r,
        fderiv ℂ (fun y => H (K y)) θ = (fderiv ℂ H (K θ)).comp (fderiv ℂ K θ)) ∧
      avg (fun θ => H (K θ)) = KAM.Iso.energyAverage H K ∧
      (KAM.Iso.energyAverage H K).im = 0) ∧
    (∀ θ ∈ complexStrip n r, fderiv ℂ (fun y => H (K y)) θ (fun l => (ω l : ℂ)) =
      -fderiv ℂ H (K θ) (invarianceError H K ω θ)) ∧
    (∀ θ ∈ complexStrip n r, ∀ j, etaN H K ω θ j =
      fderiv ℂ (fun y => H (K y)) θ (Pi.single j 1) - ∑ l, lagrangeMat K θ j l * (ω l : ℂ)) ∧
    ((∀ j, avg (fun θ => fderiv ℂ (fun y => H (K y)) θ (Pi.single j 1)) = 0) ∧
      avg (lagrangeMat K) = 0 ∧ avg (etaN H K ω) = 0) ∧
    ∀ ε δ : ℝ, (∀ θ ∈ complexStrip n r, ‖invarianceError H K ω θ‖ ≤ ε) → 0 < δ → δ < r →
      (∀ θ ∈ complexStrip n (r - δ), ‖H (K θ) - KAM.Iso.energyAverage H K‖ ≤
        M * (cR n τ * γ⁻¹ * δ ^ (-kappa n τ)) * ε) ∧
      ∀ δ' : ℝ, 0 < δ' → δ' < r - δ → ∀ θ ∈ complexStrip n (r - δ - δ'),
        ‖fderiv ℂ (fun y => H (K y)) θ‖ ≤ n * M * (cR n τ * γ⁻¹ * δ ^ (-kappa n τ)) * ε / δ' := by
  have hHK : DifferentiableOn ℂ (fun θ => H (K θ)) (complexStrip n r) := hS.holo.comp hK hKD
  have hper : IsPeriodicOn (fun θ => H (K θ)) r := periodic_h_comp_K hS.toStanding hKD hKp
  have hHd : ∀ θ ∈ complexStrip n r, DifferentiableAt ℂ H (K θ) := fun θ hθ =>
    hS.holo.differentiableAt (hS.isOpen.mem_nhds (hKD θ hθ))
  have hKd : ∀ θ ∈ complexStrip n r, DifferentiableAt ℂ K θ := fun θ hθ =>
    hK.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθ)
  have hchain : ∀ θ ∈ complexStrip n r,
      fderiv ℂ (fun y => H (K y)) θ = (fderiv ℂ H (K θ)).comp (fderiv ℂ K θ) := fun θ hθ =>
    ((hHd θ hθ).hasFDerivAt.comp θ (hKd θ hθ).hasFDerivAt).fderiv
  have hreal : ∀ x : Fin n → ℝ, (H (K fun i => (x i : ℂ))).im = 0 := fun x => by
    obtain ⟨z, hz⟩ := hKr x
    have hmem := hKD _ (ofReal_mem_complexStrip hr x)
    rw [hz] at hmem ⊢
    exact hS.real z.1 z.2 hmem
  have hderω : ∀ θ ∈ complexStrip n r, fderiv ℂ (fun y => H (K y)) θ (fun l => (ω l : ℂ)) =
      -fderiv ℂ H (K θ) (invarianceError H K ω θ) := fun θ hθ =>
    Energy.fderiv_comp_omega (hHd θ hθ) (hKd θ hθ) ω
  have havg0 : ∀ j, avg (fun θ => fderiv ℂ (fun y => H (K y)) θ (Pi.single j 1)) = 0 := fun j =>
    Tools.torusAverage_fderiv_apply_eq_zero hr hHK hper (Pi.single j 1)
  refine ⟨⟨hHK, hper, hreal, hchain, rfl, ?_⟩, hderω,
    fun θ hθ j => Exactness.etaN_apply hS.toStanding hK hKD hθ j,
    ⟨havg0, Exactness.avg_lagrangeMat hr hK hKp, Exactness.avg_etaN hS.toStanding hr hK hKp hKD⟩,
    ?_⟩
  · exact Tools.im_integral_eq_zero hreal
  · intro ε δ hE hδ hδr
    have hε : 0 ≤ ε := (norm_nonneg _).trans (hE _ (ofReal_mem_complexStrip hr 0))
    obtain ⟨hu, hup, hu0⟩ := Energy.centered hS hr hK hKp hKD
    have hdu : ∀ θ ∈ complexStrip n r,
        ‖fderiv ℂ (fun θ => H (K θ) - KAM.Iso.energyAverage H K) θ (fun l => (ω l : ℂ))‖ ≤
          M * ε := by
      intro θ hθ
      simp only [fderiv_sub_const]
      rw [hderω θ hθ, norm_neg]
      calc ‖fderiv ℂ H (K θ) (invarianceError H K ω θ)‖
          ≤ ‖fderiv ℂ H (K θ)‖ * ‖invarianceError H K ω θ‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ M * ε := mul_le_mul (hS.dH_le _ (hKD θ hθ)) (hE θ hθ) (norm_nonneg _) hS.M_pos.le
    have hap := KAM.cohomological_apriori hS.dio hS.gamma_pos
      (cohomological_tau_nonneg hS.toStanding) hδ hδr hu hup hu0 hdu
    have hfirst : ∀ θ ∈ complexStrip n (r - δ), ‖H (K θ) - KAM.Iso.energyAverage H K‖ ≤
        M * (cR n τ * γ⁻¹ * δ ^ (-kappa n τ)) * ε := by
      intro θ hθ
      refine (hap θ hθ).trans ?_
      calc _ ≤ cR n τ * γ⁻¹ * δ ^ (-kappa n τ) * (M * ε) :=
            Tools.cohConst_div_le_cR hS.gamma_pos hδ (mul_nonneg hS.M_pos.le hε)
        _ = _ := by ring
    refine ⟨hfirst, fun δ' hδ' hδ'r θ hθ => ?_⟩
    have hsub : DifferentiableOn ℂ (fun θ => H (K θ) - KAM.Iso.energyAverage H K)
        (complexStrip n (r - δ)) := hu.mono (Energy.strip_subset (by linarith))
    have hc := (KAM.cauchy_strip hsub hfirst hδ').2 θ hθ
    simp only [fderiv_sub_const] at hc
    refine hc.trans (le_of_eq ?_)
    rw [div_eq_mul_inv]
    ring

/-- `bpI:p1:energy-conservation`: an invariant torus has constant energy `Ē_H(K)`. -/
theorem energy_conservation (hS : Setting n τ M σK σB σT D H ω γ) {r : ℝ} (hr : 0 < r)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKp : IsPrimaryOnStrip K r) (hKr : IsRealOnReals K) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hE : ∀ θ ∈ complexStrip n r, invarianceError H K ω θ = 0) :
    (∀ θ ∈ complexStrip n r, H (K θ) = KAM.Iso.energyAverage H K) ∧
    (∀ E₀ : ℂ, KAM.Iso.energyAverage H K = E₀ → ∀ θ ∈ complexStrip n r, H (K θ) = E₀) ∧
    ∀ E₀ : ℂ, ∀ θ ∈ complexStrip n r, ‖H (K θ) - E₀‖ = ‖KAM.Iso.energyAverage H K - E₀‖ := by
  -- `hKr` is part of the source setting; the proof does not need it.
  have _ := hKr
  have key : ∀ θ ∈ complexStrip n r, H (K θ) = KAM.Iso.energyAverage H K := by
    intro θ hθ
    obtain ⟨δ, hδ, hδr, hθδ⟩ :=
      Energy.exists_strip_margin ⟨0, by have := hS.two_le; omega⟩ hr hθ
    obtain ⟨hscalar, -⟩ := KAM.cohomological hS.dio hS.gamma_pos
      (cohomological_tau_nonneg hS.toStanding) hδ hδr
    obtain ⟨-, -, -, -, -, -, huniq⟩ := hscalar (fun _ => 0) 0 (differentiableOn_const _)
      (fun _ _ _ => rfl) (fun _ _ => by simp) (by simp [torusAverage])
    obtain ⟨hu, hup, hu0⟩ := Energy.centered hS hr hK hKp hKD
    have hsub : complexStrip n (r - δ) ⊆ complexStrip n r := Energy.strip_subset (by linarith)
    have h1 := huniq (fun θ => H (K θ) - KAM.Iso.energyAverage H K) (hu.mono hsub)
      (fun i z hz => hup i z (hsub hz)) hu0 (fun θ' hθ' => by
        simp only [fderiv_sub_const]
        rw [Energy.fderiv_comp_omega
          (hS.holo.differentiableAt (hS.isOpen.mem_nhds (hKD θ' (hsub hθ'))))
          (hK.differentiableAt ((isOpen_complexStrip n r).mem_nhds (hsub hθ'))) ω,
          hE θ' (hsub hθ'), map_zero, neg_zero]) θ hθδ
    have h2 := huniq (fun _ => 0) (differentiableOn_const _) (fun _ _ _ => rfl)
      (by simp [torusAverage]) (fun θ' _ => by simp) θ hθδ
    exact sub_eq_zero.1 (h1.trans h2.symm)
  exact ⟨key, fun E₀ hE₀ θ hθ => (key θ hθ).trans hE₀, fun E₀ θ hθ => by rw [key θ hθ]⟩

end Torus

end KAM.Iso.Linear

end
