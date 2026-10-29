/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Linear.FullRange

/-!
# Part 1 step exports: the energy identities (graph gap GAP-I1b)

Literal exports of the proof-step nodes of `bpI:p1:energy-approx` (`ea-*`) and
`bpI:p1:energy-conservation` (`ec-*`) under the source setting `SettingSrc` (`τ ≥ 0`), built from
the landed `energy_approx_src`, `energy_defect_src`, `energy_conservation_src` and the landed
helper lemmas of `KAM.Iso.Linear.Energy`.

* `step_ea_chain`, `step_ea_gradient`, `step_ea_avg`, `step_ea_size`, `step_ea_defect`;
* `step_ec_derivative`, `step_ec_unique`, `step_ec_pointwise`.
-/

public section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory

namespace KAM.Iso.Linear

open KAM KAM.Torus KAM.Apost

variable {n : ℕ} {τ M γ : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {r : ℝ}

/-- `bpI:p1:energy-approx`, step `ea-chain` (a): `H ∘ K` is holomorphic, `1`-periodic on `T_r`,
real on reals, `D(H ∘ K) = DH(K) DK`; `⟨H ∘ K⟩ = Ē_H(K)` is real and `H ∘ K` is integrable on
`[0,1]ⁿ`. -/
theorem step_ea_chain (hS : SettingSrc n τ M D H ω γ) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKp : IsPrimaryOnStrip K r)
    (hKr : IsRealOnReals K) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D) :
    (DifferentiableOn ℂ (fun θ => H (K θ)) (complexStrip n r) ∧
      IsPeriodicOn (fun θ => H (K θ)) r ∧ (∀ x : Fin n → ℝ, (H (K fun i => (x i : ℂ))).im = 0) ∧
      (∀ θ ∈ complexStrip n r,
        fderiv ℂ (fun y => H (K y)) θ = (fderiv ℂ H (K θ)).comp (fderiv ℂ K θ)) ∧
      avg (fun θ => H (K θ)) = KAM.Iso.energyAverage H K ∧
      (KAM.Iso.energyAverage H K).im = 0) ∧
    IntegrableOn (fun x : Fin n → ℝ => H (K fun i => (x i : ℂ)))
      (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
  obtain ⟨h, -⟩ := energy_approx_src hS hr hK hKp hKr hKD
  exact ⟨h, integrableOn_unitCube_of_continuous
    (Exactness.continuous_real_of_differentiableOn hr h.1)⟩

/-- `bpI:p1:energy-approx`, step `ea-gradient` (c): `Lᵀ Ω₀ E = (D(H ∘ K))ᵀ - Ω_K ω` on `T_r`,
and `η^N = Lᵀ Ω₀ E`. -/
theorem step_ea_gradient (hS : SettingSrc n τ M D H ω γ) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKp : IsPrimaryOnStrip K r)
    (hKr : IsRealOnReals K) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D) :
    ∀ θ ∈ complexStrip n r,
      (tangentMat K θ)ᵀ *ᵥ (omegaZeroMatrix n *ᵥ sumVec n (invarianceError H K ω θ)) =
        (fun j => fderiv ℂ (fun y => H (K y)) θ (Pi.single j 1)) -
          lagrangeMat K θ *ᵥ (fun l => (ω l : ℂ)) ∧
      etaN H K ω θ =
        (tangentMat K θ)ᵀ *ᵥ (omegaZeroMatrix n *ᵥ sumVec n (invarianceError H K ω θ)) := by
  intro θ hθ
  obtain ⟨-, -, he, -⟩ := energy_approx_src hS hr hK hKp hKr hKD
  have hη : etaN H K ω θ =
      (tangentMat K θ)ᵀ *ᵥ (omegaZeroMatrix n *ᵥ sumVec n (invarianceError H K ω θ)) := by
    simp only [etaN, Matrix.mulVec_mulVec]
  refine ⟨?_, hη⟩
  rw [← hη]
  ext j
  rw [he θ hθ j, Pi.sub_apply, Matrix.mulVec, dotProduct]

/-- `bpI:p1:energy-approx`, step `ea-avg` (d): `⟨D(H ∘ K)⟩ = 0`, `⟨Ω_K⟩ = 0`, `⟨η^N⟩ = 0`. -/
theorem step_ea_avg (hS : SettingSrc n τ M D H ω γ) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKp : IsPrimaryOnStrip K r)
    (hKr : IsRealOnReals K) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D) :
    (∀ j, avg (fun θ => fderiv ℂ (fun y => H (K y)) θ (Pi.single j 1)) = 0) ∧
      avg (lagrangeMat K) = 0 ∧ avg (etaN H K ω) = 0 :=
  (energy_approx_src hS hr hK hKp hKr hKD).2.2.2.1

/-- `bpI:p1:energy-approx`, step `ea-size` (e): if `|E| ≤ ε` on `T_r` and `0 < δ < r` then
`|E^en| ≤ M Γ_δ ε` on `T_{r-δ}`, and for `0 < δ' < r - δ`,
`|D(H ∘ K)| ≤ n M Γ_δ ε / δ'` on `T_{r-δ-δ'}`, with `Γ_δ = c_R γ⁻¹ δ^{-κ}`. -/
theorem step_ea_size (hS : SettingSrc n τ M D H ω γ) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKp : IsPrimaryOnStrip K r)
    (hKr : IsRealOnReals K) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D) :
    ∀ ε δ : ℝ, (∀ θ ∈ complexStrip n r, ‖invarianceError H K ω θ‖ ≤ ε) → 0 < δ → δ < r →
      (∀ θ ∈ complexStrip n (r - δ), ‖H (K θ) - KAM.Iso.energyAverage H K‖ ≤
        M * (cR n τ * γ⁻¹ * δ ^ (-kappa n τ)) * ε) ∧
      ∀ δ' : ℝ, 0 < δ' → δ' < r - δ → ∀ θ ∈ complexStrip n (r - δ - δ'),
        ‖fderiv ℂ (fun y => H (K y)) θ‖ ≤ n * M * (cR n τ * γ⁻¹ * δ ^ (-kappa n τ)) * ε / δ' :=
  (energy_approx_src hS hr hK hKp hKr hKD).2.2.2.2

/-- `bpI:p1:energy-approx`, step `ea-defect` (f): for `ξ = (ξᴸ, ξᴺ)` holomorphic on `T_{r'}`,
`ΔK = Pξ`: `DH(K) ΔK = Y ξᴺ + D(H ∘ K) ξᴸ = Y ξᴺ + (ηᴺ)ᵀ ξᴸ - ωᵀ Ω_K ξᴸ`; the average splits
linearly; if `⟨Y ξᴺ⟩ = η^ω` then `⟨DH(K) ΔK⟩ = η^ω + E^ω_lin`, `E^ω_lin = ⟨D(H ∘ K) ξᴸ⟩`; and
`|E^ω_lin| ≤ n (sup|ηᴺ| + |ω| sup|Ω_K|) sup|ξᴸ|` over the cube. -/
theorem step_ea_defect (hS : SettingSrc n τ M D H ω γ) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKp : IsPrimaryOnStrip K r)
    (hKr : IsRealOnReals K) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) {r' : ℝ} (hr' : 0 < r')
    (hr'r : r' ≤ r) {ξL ξN : (Fin n → ℂ) → Fin n → ℂ}
    (hξL : DifferentiableOn ℂ ξL (complexStrip n r'))
    (hξN : DifferentiableOn ℂ ξN (complexStrip n r')) :
    (∀ θ ∈ complexStrip n r',
      fderiv ℂ H (K θ) ((sumVec n).symm (frameMat K θ *ᵥ Sum.elim (ξL θ) (ξN θ))) =
        energyRow H K θ ⬝ᵥ ξN θ + fderiv ℂ (fun y => H (K y)) θ (ξL θ) ∧
      fderiv ℂ (fun y => H (K y)) θ (ξL θ) =
        etaN H K ω θ ⬝ᵥ ξL θ - (fun l => (ω l : ℂ)) ⬝ᵥ (lagrangeMat K θ *ᵥ ξL θ)) ∧
    avg (fun θ => fderiv ℂ H (K θ) ((sumVec n).symm (frameMat K θ *ᵥ Sum.elim (ξL θ) (ξN θ)))) =
      avg (fun θ => energyRow H K θ ⬝ᵥ ξN θ) + avg (fun θ => fderiv ℂ (fun y => H (K y)) θ (ξL θ)) ∧
    (∀ ηω : ℂ, avg (fun θ => energyRow H K θ ⬝ᵥ ξN θ) = ηω →
      avg (fun θ => fderiv ℂ H (K θ) ((sumVec n).symm (frameMat K θ *ᵥ Sum.elim (ξL θ) (ξN θ)))) =
        ηω + avg (fun θ => fderiv ℂ (fun y => H (K y)) θ (ξL θ))) ∧
    (∀ X : ℝ, ∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
      ‖ξL (fun i => (x i : ℂ))‖ ≤ X →
      ‖fderiv ℂ (fun y => H (K y)) (fun i => (x i : ℂ)) (ξL fun i => (x i : ℂ))‖ ≤
        ‖fderiv ℂ (fun y => H (K y)) (fun i => (x i : ℂ))‖ * X) ∧
    ∀ Aη AΩ X : ℝ,
      (∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖etaN H K ω (fun i => (x i : ℂ))‖ ≤ Aη) →
      (∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖lagrangeMat K (fun i => (x i : ℂ))‖ ≤ AΩ) →
      (∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖ξL (fun i => (x i : ℂ))‖ ≤ X) →
      ‖avg (fun θ => fderiv ℂ (fun y => H (K y)) θ (ξL θ))‖ ≤ n * (Aη + ‖ω‖ * AΩ) * X := by
  obtain ⟨hpt, hsplit, hbd⟩ := energy_defect_src hS hr hK hKp hKr hKD hG hr' hr'r hξL hξN
  refine ⟨fun θ hθ => ⟨(hpt θ hθ).1, (hpt θ hθ).2.1⟩, hsplit, fun ηω h => ?_,
    fun X x _ hX => ContinuousLinearMap.le_opNorm _ _ |>.trans
      (mul_le_mul_of_nonneg_left hX (norm_nonneg _)), ?_⟩
  · rw [hsplit, h]
  · intro Aη AΩ X hη hΩ hX
    refine hbd (n * (Aη + ‖ω‖ * AΩ)) X (fun x hx => ?_) hX
    refine (hpt _ (ofReal_mem_complexStrip hr' x)).2.2.trans ?_
    exact mul_le_mul_of_nonneg_left (add_le_add (hη x hx)
      (mul_le_mul_of_nonneg_left (hΩ x hx) (norm_nonneg _))) (Nat.cast_nonneg n)

/-- `bpI:p1:energy-conservation`, step `ec-derivative`: if `E = 0` on `T_r`, then
`u = H ∘ K - ⟨H ∘ K⟩` is holomorphic, `1`-periodic on `T_r` with `⟨u⟩ = 0` and `Du ω = 0`. -/
theorem step_ec_derivative (hS : SettingSrc n τ M D H ω γ) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKp : IsPrimaryOnStrip K r)
    (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hE : ∀ θ ∈ complexStrip n r, invarianceError H K ω θ = 0) :
    DifferentiableOn ℂ (fun θ => H (K θ) - KAM.Iso.energyAverage H K) (complexStrip n r) ∧
    IsPeriodicOn (fun θ => H (K θ) - KAM.Iso.energyAverage H K) r ∧
    avg (fun θ => H (K θ) - KAM.Iso.energyAverage H K) = 0 ∧
    ∀ θ ∈ complexStrip n r,
      fderiv ℂ (fun θ => H (K θ) - KAM.Iso.energyAverage H K) θ (fun l => (ω l : ℂ)) = 0 := by
  have hS' := hS.setting one_pos one_pos one_pos
  obtain ⟨hu, hup, hu0⟩ := Energy.centered hS' hr hK hKp hKD
  refine ⟨hu, fun i z hz => hup i z hz, hu0, fun θ hθ => ?_⟩
  simp only [fderiv_sub_const]
  rw [Energy.fderiv_comp_omega
    (hS.holo.differentiableAt (hS.isOpen.mem_nhds (hKD θ hθ)))
    (hK.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθ)) ω, hE θ hθ, map_zero, neg_zero]

/-- `bpI:p1:energy-conservation`, step `ec-unique`: if `E = 0` on `T_r`, then
`u = H ∘ K - ⟨H ∘ K⟩` vanishes on `T_{r-δ}` for every `0 < δ < r`, hence on `T_r`. -/
theorem step_ec_unique (hS : SettingSrc n τ M D H ω γ) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKp : IsPrimaryOnStrip K r)
    (hKr : IsRealOnReals K) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hE : ∀ θ ∈ complexStrip n r, invarianceError H K ω θ = 0) :
    (∀ δ : ℝ, 0 < δ → δ < r → ∀ θ ∈ complexStrip n (r - δ),
      H (K θ) - KAM.Iso.energyAverage H K = 0) ∧
    ∀ θ ∈ complexStrip n r, H (K θ) - KAM.Iso.energyAverage H K = 0 := by
  have h := (energy_conservation_src hS hr hK hKp hKr hKD hE).1
  exact ⟨fun δ _ hδr θ hθ => sub_eq_zero.2 (h θ (Energy.strip_subset (by linarith) hθ)),
    fun θ hθ => sub_eq_zero.2 (h θ hθ)⟩

/-- `bpI:p1:energy-conservation`, step `ec-pointwise`: if `E = 0` on `T_r` then `H ∘ K ≡ Ē_H(K)`;
if `Ē_H(K) = E₀` then `H(K(θ)) = E₀` everywhere; for arbitrary `E₀`,
`sup_{T_r} |H ∘ K - E₀| = |Ē_H(K) - E₀|`. -/
theorem step_ec_pointwise (hS : SettingSrc n τ M D H ω γ) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKp : IsPrimaryOnStrip K r)
    (hKr : IsRealOnReals K) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hE : ∀ θ ∈ complexStrip n r, invarianceError H K ω θ = 0) :
    (∀ θ ∈ complexStrip n r, H (K θ) = KAM.Iso.energyAverage H K) ∧
    (∀ E₀ : ℂ, KAM.Iso.energyAverage H K = E₀ → ∀ θ ∈ complexStrip n r, H (K θ) = E₀) ∧
    ∀ E₀ : ℂ, sSup ((fun θ => ‖H (K θ) - E₀‖) '' complexStrip n r) =
      ‖KAM.Iso.energyAverage H K - E₀‖ := by
  obtain ⟨h1, h2, h3⟩ := energy_conservation_src hS hr hK hKp hKr hKD hE
  refine ⟨h1, h2, fun E₀ => ?_⟩
  have hne : (complexStrip n r).Nonempty := ⟨0, fun i => by simpa using hr⟩
  have : (fun θ => ‖H (K θ) - E₀‖) '' complexStrip n r =
      {‖KAM.Iso.energyAverage H K - E₀‖} := by
    refine (Set.eq_singleton_iff_unique_mem).2 ⟨?_, ?_⟩
    · obtain ⟨θ, hθ⟩ := hne
      exact ⟨θ, hθ, h3 E₀ θ hθ⟩
    · rintro _ ⟨θ, hθ, rfl⟩
      exact h3 E₀ θ hθ
  rw [this, csSup_singleton]

end KAM.Iso.Linear
