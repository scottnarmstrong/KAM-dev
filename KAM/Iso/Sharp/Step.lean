/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp.NewtonError
public import KAM.Iso.Sharp.Twist
public import KAM.Iso.Apost.Torsion
import Mathlib.Tactic.Linarith

/-!
# The sharp isoenergetic step

Blueprint `bpI:p2s:step` (`KAM.Iso.Sharp.iso_step_spec`): one isoenergetic quasi-Newton step
`(K, s) ↦ (K̄, s̄)` on `T_{r-2δ}` with general small-divisor data `(κ, c_R)`, under the split
smallness `ĉ_step ε/(γ⁴δ^{2a}) ≤ 1` and `2d ≤ β`, where `d = C_ΔK ε/(γ²δ^a)` and `a = 2κ`:

* (a) `K̄` is holomorphic on `T_{r-2δ}`, primary and real;
* (b) `|K̄ - K| ≤ d`, the ball margin `β - d`, and `|s̄ - s| |ω*| ≤ C_Δω ε/(γ²δ^a)`;
* (c) the new invariance and energy errors are `≤ C_E ε²/(γ⁴δ^{2a}) ≤ ε`;
* (d), (e) the frame and bordered-twist increments on `T_{r-3δ}` at the rates `ϱ_D, ϱ_B, ϱ_𝖳`.

The proof follows the blueprint:

* `stepI:p2s:st-small`: `KAM.Iso.Sharp.iso_step_small`;
* `stepI:p2s:st-all`: `KAM.Iso.Sharp.iso_correction_bounds`, `iso_newton_error_bounds` (with the
  qualitative clauses of `KAM.Iso.Apost.correction` and the helpers of
  `KAM.Iso.Apost.TorsionAux` for (a)); the ball and the frame from `KAM.Sharp.perturbation_poly`
  at `ω̃ = s̄ ω*`; the bordered twist from `KAM.Iso.Sharp.iso_twist` with `ω̄ - ω = Δω`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Iso.Sharp

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost KAM.Sharp

variable {n : ℕ} {κ cR M σK σB σT γb : ℝ}
variable {τ σω ν : ℝ} {ωstar : Fin n → ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {γ : ℝ}

/-- Blueprint `bpI:p2s:step`. -/
theorem iso_step_spec (hC : CohData n τ κ cR) (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ)
    (hγb : γ ≤ γb) {E₀ r β ε δ s : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : IsoAdmissible σK σB σT D H ωstar E₀ r β ε s K) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h3δ : 3 * δ < r)
    (hsmall : iCStep n κ cR M σK σB σT γb * ε / (γ ^ 4 * δ ^ (2 * (2 * κ))) ≤ 1)
    (hβ : 2 * (iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ≤ β) :
    (DifferentiableOn ℂ (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) (complexStrip n (r - 2 * δ)) ∧
      IsPrimaryOnStrip (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) (r - 2 * δ) ∧
      IsRealOnReals (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))) ∧
    ((∀ θ ∈ complexStrip n (r - 2 * δ), ‖isoNewtonMap H K ωstar E₀ s (r - 2 * δ) θ - K θ‖ ≤
        iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ∧
      (∀ θ ∈ complexStrip n (r - 2 * δ), Metric.ball (isoNewtonMap H K ωstar E₀ s (r - 2 * δ) θ)
        (β - iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ⊆ D) ∧
      |isoNewS H K ωstar E₀ s - s| * ‖ωstar‖ ≤
        iCDw n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ∧
    ((∀ θ ∈ complexStrip n (r - 2 * δ),
        ‖invarianceError H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))
          (isoNewS H K ωstar E₀ s • ωstar) θ‖ ≤
          iCE n cR M σK σB σT γb * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ)))) ∧
      ‖KAM.Iso.energyAverage H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) - (E₀ : ℂ)‖ ≤
        iCE n cR M σK σB σT γb * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ))) ∧
      iCE n cR M σK σB σT γb * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ))) ≤ ε) ∧
    (∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖fderiv ℂ (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) θ - fderiv ℂ K θ‖ ≤
        iRateD n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) ∧
      IsUnit (gramMatrix (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) θ).det ∧
      ‖(gramMatrix (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤
        iRateB n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1))) ∧
    IsUnit (KAM.Iso.extendedTorsionAverage H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))
        (isoNewS H K ωstar E₀ s • ωstar)).det ∧
    ‖(KAM.Iso.extendedTorsionAverage H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))
        (isoNewS H K ωstar E₀ s • ωstar))⁻¹ -
      (KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹‖ ≤
      iRateT n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) := by
  have hSt := (hS.setting hK.s_gt.le).toStanding
  have hKN := hK.toAdmissibleNoTwist
  have hγ := hS.gamma_pos
  have hr := hK.r_pos
  have hβ0 := hK.β_pos
  have hε0 := hK.ε_nonneg
  have h2δ : 2 * δ < r := by linarith
  have hr2 : 0 < r - 2 * δ := by linarith
  have hsub : complexStrip n (r - 2 * δ) ⊆ complexStrip n r :=
    Triangular.strip_mono (by linarith)
  -- step `st-small`
  obtain ⟨hεδ, hTS, hsym, hs1, hs2, hs3, hE⟩ := iso_step_small hC.one_le_kappa hC.cR_pos hS.M_pos
    hS.σK_pos hS.σB_pos hS.σT_pos hγ hγb hδ hδ1 hε0 hsmall
  have hdβ : iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) < β := by linarith
  -- step `st-all`: correction and errors
  obtain ⟨⟨-, -, -, hcd, hcp, hcr, -⟩, -⟩ := KAM.Iso.Apost.correction hS hK hδ hδ1 h2δ
  obtain ⟨-, hbd, hωeq, hωle⟩ := iso_correction_bounds hC hS hγb hK hδ hδ1 h2δ hεδ hTS
  obtain ⟨-, hnewt, hen⟩ := iso_newton_error_bounds hC hS hγb hK hδ hδ1 h2δ hεδ hTS hdβ hsym
  have hdiff : DifferentiableOn ℂ (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))
      (complexStrip n (r - 2 * δ)) :=
    TorsionAux.isoNewtonMap_differentiableOn (hK.holo.mono hsub) hcd
  have hdist : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖isoNewtonMap H K ωstar E₀ s (r - 2 * δ) θ - K θ‖ ≤
      iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) := fun θ hθ => by
    rw [TorsionAux.isoNewtonMap_of_mem hθ, add_sub_cancel_left]
    exact (hbd θ hθ).2.1
  -- the ball and the frame (`bp:p2s:perturbation` at `ω̃ = s̄ ω*`) and the twist
  obtain ⟨hball, hfr, -, -, -⟩ :=
    perturbation_poly hC hSt hKN hδ hδ1 h3δ hεδ hdiff hdist hdβ hnewt hE hs1 hs2
  obtain ⟨hTu, -, hTd⟩ :=
    iso_twist hC hS hγb hK hδ hδ1 h3δ hεδ hdiff hdist hdβ hnewt hE hωle hs1 hs2 hs3
  refine ⟨⟨hdiff, TorsionAux.isoNewtonMap_isPrimaryOnStrip (by linarith) hK.primary hcp,
      TorsionAux.isoNewtonMap_isRealOnReals hr2 hK.real hcr⟩,
    ⟨hdist, hball, hωeq.symm.trans_le hωle⟩, ⟨hnewt, hen, hE⟩, fun θ hθ => ?_, hTu, hTd⟩
  obtain ⟨h1, -, h3, -, h5⟩ := hfr θ hθ
  exact ⟨h1.trans_eq (StepSharp.div_delta_eq hγ hδ), h3,
    h5.trans_eq (StepSharp.div_delta_eq hγ hδ)⟩

end KAM.Iso.Sharp

end
