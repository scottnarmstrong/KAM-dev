/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.OrbitComplex
public import KAM.Iso.RestrictedHam
public import KAM.Iso.PeriodOne

/-!
# Literal exports of the restricted-Hamiltonian and transfer steps (package GAP-I7b)

Append-only exports stating the literal conclusions of graph nodes of Blueprint-I Part 7 from the
landed declarations.

* `he_smooth` (`stepI:p7:he-smooth`): the squared radii are polynomial and positive on `W_μ`, the
  radii and their inverses are real analytic there, the remaining terms are polynomial, and
  `H^R3_μ` is `C^∞` on `W_μ`.
* `orbitMapC_k_holomorphic` (the `k = √(1 - e²)` clause of `bpI:p7:orbit-maps-e`): the principal
  square root is holomorphic on the domain of `Q_el`, squares to `1 - e²`, is real at real points,
  and `Q_el` with `k` replaced by it is holomorphic.
* `tr_cf` (`stepI:p7:tr-cf`) and `tr_chain` (`stepI:p7:tr-chain`): the collision-freedom and the
  chain-rule steps of `bpI:p7:transfer`, under the hypotheses of `transfer`.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Iso

open KAM KAM.Kepler KAM.Planetary

section Part7TransferSteps

/-- `stepI:p7:he-smooth`: `r_j² = θ(q - a_j)` is a polynomial positive on `W_μ`; `r_j` and `1/r_j`
are real analytic on `W_μ`; the remaining terms of `H^R3_μ` are polynomial; `H^R3_μ` is `C^∞` on
`W_μ`. -/
theorem he_smooth (μ : ℝ) :
    (∀ a ∈ ({primary₁ μ, primary₂ μ} : Set (Fin 2 → ℝ)),
      (∀ z : Phase 2, radiusSq (z.1 - a) = (z.1 0 - a 0) ^ 2 + (z.1 1 - a 1) ^ 2) ∧
      AnalyticOnNhd ℝ (fun z : Phase 2 => radiusSq (z.1 - a)) univ ∧
      (∀ z ∈ {z : Phase 2 | CollisionFree μ z}, 0 < radiusSq (z.1 - a)) ∧
      AnalyticOnNhd ℝ (fun z : Phase 2 => radius (z.1 - a)) {z : Phase 2 | CollisionFree μ z} ∧
      AnalyticOnNhd ℝ (fun z : Phase 2 => (radius (z.1 - a))⁻¹)
        {z : Phase 2 | CollisionFree μ z}) ∧
    AnalyticOnNhd ℝ
      (fun z : Phase 2 => radiusSq z.2 / 2 + z.1 1 * z.2 0 - z.1 0 * z.2 1) univ ∧
    ContDiffOn ℝ ∞ (restrictedHamTotal μ) {z : Phase 2 | CollisionFree μ z} := by
  have a0 : ∀ k : Fin 2, AnalyticOnNhd ℝ (fun z : Phase 2 => z.1 k) univ := fun k z _ =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).analyticAt _
      |>.comp analyticAt_fst
  have a1 : ∀ k : Fin 2, AnalyticOnNhd ℝ (fun z : Phase 2 => z.2 k) univ := fun k z _ =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).analyticAt _
      |>.comp analyticAt_snd
  have hsq : ∀ v : Fin 2 → ℝ, radiusSq v = v 0 ^ 2 + v 1 ^ 2 := fun v => by
    simp [radiusSq, Fin.sum_univ_two]
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · have hpos : ∀ z : Phase 2, CollisionFree μ z → 0 < radius (z.1 - a) := by
      intro z hz
      rcases ha with rfl | rfl
      · exact hz.1
      · exact hz.2
    have hpoly : ∀ z : Phase 2, radiusSq (z.1 - a) = (z.1 0 - a 0) ^ 2 + (z.1 1 - a 1) ^ 2 :=
      fun z => by simp [hsq]
    have hrad : ∀ z : Phase 2, CollisionFree μ z →
        AnalyticAt ℝ (fun z : Phase 2 => radius (z.1 - a)) z := by
      intro z hz
      have hv : z.1 - a ≠ 0 := planeLength_pos_iff.mp (hpos z hz)
      exact AnalyticAt.comp (g := planeLength) (f := fun z : Phase 2 => z.1 - a)
        (analyticAt_planeLength hv) (analyticAt_fst.sub analyticAt_const)
    refine ⟨hpoly, ?_, ?_, fun z hz => hrad z hz, fun z hz => ?_⟩
    · intro z hz
      simp only [hpoly]
      exact (((a0 0 z hz).sub analyticAt_const).pow 2).add
        (((a0 1 z hz).sub analyticAt_const).pow 2)
    · intro z hz
      exact Real.sqrt_pos.mp (hpos z hz)
    · exact (hrad z hz).inv (hpos z hz).ne'
  · intro z hz
    simp only [hsq]
    exact ((((a1 0 z hz).pow 2).add ((a1 1 z hz).pow 2)).div_const).add
      ((a0 1 z hz).mul (a1 0 z hz)) |>.sub ((a0 0 z hz).mul (a1 1 z hz))
  · exact (analyticOnNhd_restrictedHamTotal μ).contDiffOn

/-- The `k = √(1 - e²)` clause of `bpI:p7:orbit-maps-e`: on `{(ℓ, g, L, e, k) : (ℓ, e) ∈ 𝒫(e₁),
L ≠ 0}` one has `Re (1 - e²) > 0`, so the principal square root `k = (1 - e²)^{1/2}` is
holomorphic, `k² = 1 - e²`, `k` is the real square root at real `e` with `e² < 1`, and `Q_el` with
its fifth coordinate replaced by `k` is holomorphic. -/
theorem orbitMapC_k_holomorphic {e₁ : ℝ} (h0 : 0 < e₁) (h1 : e₁ < 1) :
    (∀ x ∈ orbitDomC e₁, 0 < (1 - x 3 ^ 2).re) ∧
    DifferentiableOn ℂ (fun x : Fin 5 → ℂ => (1 - x 3 ^ 2) ^ (2⁻¹ : ℂ)) (orbitDomC e₁) ∧
    (∀ x ∈ orbitDomC e₁, ((1 - x 3 ^ 2) ^ (2⁻¹ : ℂ)) ^ 2 = 1 - x 3 ^ 2) ∧
    (∀ e : ℝ, e ^ 2 < 1 → (1 - (e : ℂ) ^ 2) ^ (2⁻¹ : ℂ) = ((√(1 - e ^ 2) : ℝ) : ℂ)) ∧
    DifferentiableOn ℂ
      (fun x : Fin 5 → ℂ => orbitMapC e₁ (Function.update x 4 ((1 - x 3 ^ 2) ^ (2⁻¹ : ℂ))))
      (orbitDomC e₁) := by
  have hre : ∀ x ∈ orbitDomC e₁, 0 < (1 - x 3 ^ 2).re := by
    intro x hx
    have hb := (KAM.Kepler.tube_bounds h0 hx.1).1
    have hlt : ‖x 3‖ < 1 := lt_of_le_of_lt hb (by unfold keplerE2; linarith)
    have h2 : (x 3 ^ 2).re ≤ ‖x 3 ^ 2‖ := Complex.re_le_norm _
    rw [norm_pow] at h2
    have h3 : ‖x 3‖ ^ 2 < 1 := by nlinarith [norm_nonneg (x 3)]
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hslit : ∀ x ∈ orbitDomC e₁, 1 - x 3 ^ 2 ∈ Complex.slitPlane := fun x hx =>
    Complex.mem_slitPlane_iff.2 (Or.inl (hre x hx))
  have hk : DifferentiableOn ℂ (fun x : Fin 5 → ℂ => (1 - x 3 ^ 2) ^ (2⁻¹ : ℂ)) (orbitDomC e₁) := by
    intro x hx
    have hd : DifferentiableAt ℂ (fun x : Fin 5 → ℂ => 1 - x 3 ^ 2) x :=
      (differentiableAt_const _).sub ((differentiable_apply 3 x).pow 2)
    exact (hd.cpow (differentiableAt_const _) (hslit x hx)).differentiableWithinAt
  have hsqrt : ∀ x ∈ orbitDomC e₁, ((1 - x 3 ^ 2) ^ (2⁻¹ : ℂ)) ^ 2 = 1 - x 3 ^ 2 := by
    intro x _
    have := Complex.cpow_nat_inv_pow (1 - x 3 ^ 2) (n := 2) (by norm_num)
    simpa using this
  refine ⟨hre, hk, hsqrt, ?_, ?_⟩
  · intro e he
    have h : (0 : ℝ) ≤ 1 - e ^ 2 := by linarith
    have := Complex.ofReal_cpow h (2⁻¹ : ℝ)
    rw [Real.sqrt_eq_rpow]
    push_cast at this ⊢
    exact this.symm
  · have hu : DifferentiableOn ℂ
        (fun x : Fin 5 → ℂ => Function.update x 4 ((1 - x 3 ^ 2) ^ (2⁻¹ : ℂ))) (orbitDomC e₁) := by
      rw [differentiableOn_pi]
      intro i
      by_cases hi : i = 4
      · subst hi
        simpa using hk
      · simp only [Function.update_of_ne hi]
        exact (differentiable_apply i).differentiableOn
    refine (orbitMapC_differentiableOn h0 h1).comp hu fun x hx => ?_
    refine ⟨?_, ?_⟩
    · simpa [Function.update_of_ne (show (0 : Fin 5) ≠ 4 by decide),
        Function.update_of_ne (show (3 : Fin 5) ≠ 4 by decide)] using hx.1
    · simpa [Function.update_of_ne (show (2 : Fin 5) ≠ 4 by decide)] using hx.2

open PeriodOneAux in
/-- `stepI:p7:tr-cf`: for `t ∈ J`, `(L, G) = (𝖲 z̃(t))₂ ∈ 𝒦`, `𝖲 z̃(t)` is real and lies in the
Delaunay domain and in `𝒰(δ₂)`, and `z(t) = 𝖰 (𝖲 z̃(t))` is collision free, i.e. lies in `W_μ`. -/
theorem tr_cf {K : Set (Fin 2 → ℝ)} (hK : SafeAction K) (hρ : kRhoMax K < 1)
    {B : Set (Fin 2 → ℝ)} (hB : ∀ I ∈ B, (fun i => I i / (2 * π)) ∈ K) {μ : ℝ}
    (hμ : |μ| < exactMu2 K) {J : Set ℝ} {zt : ℝ → Phase 2}
    (hz : IsHamiltonianSolutionOn
      (realHamiltonian (keplerRotH ((2 * π) ^ 2) (1 / (2 * π))) (tildeF K μ)) B J zt) :
    ∀ t ∈ J, (fun i => (zt t).2 i / (2 * π)) ∈ K ∧ periodOneMap (zt t) ∈ deDom ∧
      phaseToC (periodOneMap (zt t)) ∈ UDelta K (exactDelta K) ∧
      CollisionFree μ (delaunay (periodOneMap (zt t))) := by
  intro t ht
  have hδ := exactDelta_pos hK hρ
  have hs : 0 < exactDelta K / (2 * π) := by positivity
  have hr : 0 < 2 * π * exactDelta K := by positivity
  obtain ⟨hBt, -, -⟩ := hz t ht
  have hmem := phaseToC_mem hs hr hBt
  obtain ⟨hdom, -, hcf, -⟩ := periodOne_real hK hρ hB hμ hmem
  refine ⟨hB _ hBt, hdom, ?_, hcf⟩
  rw [← periodOneMapC_phaseToC]
  exact periodOneMapC_mem_UDelta hδ hB hmem

open PeriodOneAux in
/-- `stepI:p7:tr-chain`: for `t ∈ J`, `z̃'(t) = X_{realHamiltonian h̃ f̃_μ}(z̃(t)) = X_{H ∘ 𝖰 ∘ 𝖲}(z̃(t))`;
`(𝖰 ∘ 𝖲 ∘ z̃)'(t) = D𝖰(𝖲 z̃(t)) (𝖲 z̃'(t)) = X_{H^R3_μ}(z(t)) = V_μ(z(t))`; and the formulas for
`rad(q)` and the energy. -/
theorem tr_chain {K : Set (Fin 2 → ℝ)} (hK : SafeAction K) (hρ : kRhoMax K < 1)
    {B : Set (Fin 2 → ℝ)} (hB : ∀ I ∈ B, (fun i => I i / (2 * π)) ∈ K) {μ : ℝ}
    (hμ : |μ| < exactMu2 K) {J : Set ℝ} {zt : ℝ → Phase 2}
    (hz : IsHamiltonianSolutionOn
      (realHamiltonian (keplerRotH ((2 * π) ^ 2) (1 / (2 * π))) (tildeF K μ)) B J zt) :
    ∀ t ∈ J,
      HasDerivAt zt (hamiltonianVectorField
        (realHamiltonian (keplerRotH ((2 * π) ^ 2) (1 / (2 * π))) (tildeF K μ)) (zt t)) t ∧
      hamiltonianVectorField
          (realHamiltonian (keplerRotH ((2 * π) ^ 2) (1 / (2 * π))) (tildeF K μ)) (zt t) =
        hamiltonianVectorField ((restrictedHamTotal μ ∘ delaunay) ∘ periodOneMap) (zt t) ∧
      HasDerivAt (fun s => delaunay (periodOneMap (zt s)))
        (fderiv ℝ delaunay (periodOneMap (zt t)) (periodOneMap (hamiltonianVectorField
          (realHamiltonian (keplerRotH ((2 * π) ^ 2) (1 / (2 * π))) (tildeF K μ)) (zt t)))) t ∧
      (fderiv ℝ delaunay (periodOneMap (zt t)) (periodOneMap (hamiltonianVectorField
          (realHamiltonian (keplerRotH ((2 * π) ^ 2) (1 / (2 * π))) (tildeF K μ)) (zt t))) =
        hamiltonianVectorField (restrictedHamTotal μ) (delaunay (periodOneMap (zt t))) ∧
      ∃ hcf : CollisionFree μ (delaunay (periodOneMap (zt t))),
        hamiltonianVectorField (restrictedHamTotal μ) (delaunay (periodOneMap (zt t))) =
          restrictedVectorField μ ⟨delaunay (periodOneMap (zt t)), hcf⟩) ∧
      (let w := periodOneMap (zt t)
       let z := delaunay w
       planeLength z.1 =
          w.2 0 ^ 2 * (1 - eccOf (w.2 0) (w.2 1) *
            Real.cos (eccAnom (w.1 0) (eccOf (w.2 0) (w.2 1)))) ∧
        elemL z = w.2 0 ∧ planeCross z.1 z.2 = w.2 1 ∧ elemA z = w.2 0 ^ 2 ∧
        elemEcc z = eccOf (w.2 0) (w.2 1) ∧
        ∃ hcf : CollisionFree μ z, restrictedHamiltonian μ ⟨z, hcf⟩ =
          realHamiltonian (keplerRotH ((2 * π) ^ 2) (1 / (2 * π))) (tildeF K μ) (zt t)) := by
  intro t ht
  have hδ := exactDelta_pos hK hρ
  have hs : 0 < exactDelta K / (2 * π) := by positivity
  have hr : 0 < 2 * π * exactDelta K := by positivity
  have hOopen : IsOpen {z : Phase 2 | phaseToC z ∈
      complexStrip 2 (exactDelta K / (2 * π)) ×ˢ actionNbhd B (2 * π * exactDelta K)} :=
    ((isOpen_complexStrip 2 _).prod (isOpen_actionNbhd B _)).preimage continuous_phaseToC
  obtain ⟨hBt, -, hder⟩ := hz t ht
  have hmem := phaseToC_mem hs hr hBt
  obtain ⟨hdom, -, hcf, -⟩ := periodOne_real hK hρ hB hμ hmem
  have hev : realHamiltonian (keplerRotH ((2 * π) ^ 2) (1 / (2 * π))) (tildeF K μ)
      =ᶠ[nhds (zt t)] fun z => restrictedHamTotal μ (delaunay (periodOneMap z)) := by
    filter_upwards [hOopen.mem_nhds hmem] with z hzO
    obtain ⟨-, -, -, heq⟩ := periodOne_real hK hρ hB hμ hzO
    exact heq.symm
  have hRd : DifferentiableAt ℝ (restrictedHamTotal μ) (delaunay (periodOneMap (zt t))) :=
    ((analyticOnNhd_restrictedHamTotal μ) _ hcf).differentiableAt
  have hQd : DifferentiableAt ℝ delaunay (periodOneMap (zt t)) :=
    (analyticOnNhd_delaunay _ hdom).differentiableAt
  have hfield : hamiltonianVectorField
        (realHamiltonian (keplerRotH ((2 * π) ^ 2) (1 / (2 * π))) (tildeF K μ)) (zt t) =
      hamiltonianVectorField ((restrictedHamTotal μ ∘ delaunay) ∘ periodOneMap) (zt t) :=
    hamiltonianVectorField_congr hev.fderiv_eq
  have hder' : HasDerivAt zt
      (hamiltonianVectorField ((restrictedHamTotal μ ∘ delaunay) ∘ periodOneMap) (zt t)) t := by
    rw [← hfield]; exact hder
  have hS := (periodOneMap_hasDerivAt_iff (hRd.comp _ hQd)).1 hder'
  have hSv : periodOneMap (hamiltonianVectorField
        (realHamiltonian (keplerRotH ((2 * π) ^ 2) (1 / (2 * π))) (tildeF K μ)) (zt t)) =
      hamiltonianVectorField (restrictedHamTotal μ ∘ delaunay) (periodOneMap (zt t)) := by
    rw [hfield]
    exact periodOneMap_hamiltonianVectorField (hRd.comp _ hQd)
  have hQ := hQd.hasFDerivAt.comp_hasDerivAt t hS
  have hX : fderiv ℝ delaunay (periodOneMap (zt t)) (periodOneMap (hamiltonianVectorField
        (realHamiltonian (keplerRotH ((2 * π) ^ 2) (1 / (2 * π))) (tildeF K μ)) (zt t))) =
      hamiltonianVectorField (restrictedHamTotal μ) (delaunay (periodOneMap (zt t))) := by
    rw [hSv]
    exact delaunay_hamiltonianVectorField hdom hRd
  refine ⟨hder, hfield, ?_, hX, ⟨hcf, restrictedVectorField_eq_hamiltonian hcf |>.symm⟩, ?_⟩
  · rw [hSv]; exact hQ
  · intro w z
    obtain ⟨hG, hGL⟩ := hdom
    have hL : 0 < w.2 0 := hG.trans hGL
    obtain ⟨he0, he1⟩ := ComplexDomainAux.eccOf_pos_lt_one hG hGL
    have hel := delaunay_elements ⟨hG, hGL⟩
    obtain ⟨-, -, hcf', heq⟩ := periodOne_real hK hρ hB hμ hmem
    exact ⟨orbitMapR_radius hL he0.le he1, hel.1, hel.2.1, hel.2.2.1, hel.2.2.2, hcf', heq⟩

end Part7TransferSteps

end KAM.Iso

end
