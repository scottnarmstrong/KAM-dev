/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp.Correction
public import KAM.Iso.Apost.NewtonError
import KAM.Strip.Taylor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The new errors of the isoenergetic step, with general small-divisor data

Blueprint `bpI:p2s:newton-error` (`KAM.Iso.Sharp.iso_newton_error_bounds`): `K̄ = K + ΔK` maps
`T_{r-2δ}` into `D`, and the invariance error of `K̄` at `ω̄ = s̄ ω*` and its energy error are at
most `C_E ε²/(γ⁴δ^{2a})`.

The proof follows the blueprint:

* `stepI:p2s:ne-id`: the identities `Ē = P S⁻¹ E_lin + Δ²X + ξ^ω ∂_ω ΔK` and
  `Ē^ω = ⟨D(H ∘ K) ξᴸ⟩ + ⟨Δ²H⟩` are those of `KAM.Iso.Apost.newton_error`; the copies
  `IsoNewtonErrorSharp.sumVec_error_eq_of` and `energyAverage_sub_eq_of` take the pointwise
  hypotheses `det S ≠ 0` and `|ΔK| < β` in place of the old constants (design §2.2);
* `stepI:p2s:ne-e`: `|E_lin| ≤ C_lin ε²/(γ²δ^{a+1})` (`KAM.Sharp.geometry_sep`,
  `KAM.Iso.Sharp.iso_correction_bounds`), Taylor's `M/2` (`norm_isoQuadX_half`) and the absorption
  `KAM.Sharp.absorb` (`iso_total_le`);
* `stepI:p2s:ne-en`: `|D(H ∘ K)| ≤ n(|ηᴺ| + |ω| |Ω_K|)` (`KAM.Iso.Linear.energy_defect`),
  `|ξᴸ| ≤ c_R C_g ε/(γ²δ^a)` (`IsoCorrectionSharp.correction_core`), Taylor's `M/2`
  (`norm_isoQuadH_half`) and the absorption (`energy_total_le`, using `κ ≥ 1`).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology

namespace KAM.Iso.Sharp

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost KAM.Sharp

variable {n : ℕ} {κ cR M σK σB σT γb : ℝ}

namespace IsoNewtonErrorSharp

/-! ### Arithmetic -/

section Arith

variable {γ δ ε : ℝ}

theorem e21a (hδ : 0 < δ) :
    ε / δ * (ε / (γ ^ 2 * δ ^ (2 * κ))) = ε ^ 2 / (γ ^ 2 * δ ^ (2 * κ + 1)) := by
  rw [div_mul_div_comm, Real.rpow_add_one hδ.ne']
  congr 1 <;> ring

theorem e21b (hδ : 0 < δ) :
    ε / (γ * δ ^ (κ + 1)) * (ε / (γ * δ ^ κ)) = ε ^ 2 / (γ ^ 2 * δ ^ (2 * κ + 1)) := by
  rw [div_mul_div_comm, Real.rpow_add_one hδ.ne' κ, Real.rpow_add_one hδ.ne' (2 * κ), two_mul,
    Real.rpow_add hδ]
  congr 1 <;> ring

theorem e3 (hδ : 0 < δ) :
    ε / (γ * δ ^ κ) * (ε / (γ ^ 2 * δ ^ (2 * κ))) = ε ^ 2 / (γ ^ 3 * δ ^ (3 * κ)) := by
  rw [div_mul_div_comm, show 3 * κ = κ + 2 * κ by ring, Real.rpow_add hδ]
  congr 1 <;> ring

theorem e31 (hδ : 0 < δ) :
    ε / (γ * δ ^ (κ + 1)) * (ε / (γ ^ 2 * δ ^ (2 * κ))) = ε ^ 2 / (γ ^ 3 * δ ^ (3 * κ + 1)) := by
  rw [div_mul_div_comm, Real.rpow_add_one hδ.ne' κ, Real.rpow_add_one hδ.ne' (3 * κ),
    show 3 * κ = κ + 2 * κ by ring, Real.rpow_add hδ]
  congr 1 <;> ring

theorem e4 (hδ : 0 < δ) :
    (ε / (γ ^ 2 * δ ^ (2 * κ))) ^ 2 = ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ))) := by
  rw [div_pow, show 2 * (2 * κ) = 2 * κ + 2 * κ by ring, Real.rpow_add hδ]
  congr 1
  ring

/-- Step `stepI:p2s:ne-e`, constants: the three terms of `E_lin` give `C_lin ε²/(γ²δ^{2κ+1})`. -/
theorem iso_lin_eq (hδ : 0 < δ) :
    cRed n σK σB * ε / δ * (iCXi n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) +
        cSym n cR σK σB * ε / (γ * δ ^ (κ + 1)) *
          (iCDXi n cR M σK σB σT γb * ε / (γ * δ ^ κ)) +
        cOm n cR σK * ε / (γ * δ ^ (κ + 1)) * thetaS n M σK σB *
          (iCS n cR M σK σB σT γb * ε / (γ * δ ^ κ)) =
      iCLin n cR M σK σB σT γb * ε ^ 2 / (γ ^ 2 * δ ^ (2 * κ + 1)) := by
  calc _ = cRed n σK σB * iCXi n cR M σK σB σT γb * (ε / δ * (ε / (γ ^ 2 * δ ^ (2 * κ)))) +
        cSym n cR σK σB * iCDXi n cR M σK σB σT γb *
          (ε / (γ * δ ^ (κ + 1)) * (ε / (γ * δ ^ κ))) +
        cOm n cR σK * thetaS n M σK σB * iCS n cR M σK σB σT γb *
          (ε / (γ * δ ^ (κ + 1)) * (ε / (γ * δ ^ κ))) := by ring
    _ = _ := by
      rw [e21a hδ, e21b hδ]
      unfold iCLin
      ring

/-- Step `stepI:p2s:ne-e`, constants: with `|P| ≤ σ_K(1 + σ_B)`, `|S⁻¹| ≤ 2`, the bound of `E_lin`,
`|ΔK| ≤ C_ΔK ε/(γ²δ^{2κ})`, `|ξ^ω| ≤ C_S ε/(γδ^κ)` and `|∂_ω ΔK| ≤ C_∂K ε/(γ²δ^{2κ})`, the total
is at most `C_E ε²/(γ⁴δ^{4κ})`. -/
theorem iso_total_le (hκ : 1 ≤ κ) (hγ : 0 < γ) (hγb : γ ≤ γb) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 ≤ ε) (hσK : 0 ≤ σK) (hσB : 0 ≤ σB) (hc : 0 ≤ iCLin n cR M σK σB σT γb)
    (hcS : 0 ≤ iCS n cR M σK σB σT γb) (hcd : 0 ≤ iCdK n cR M σK σB σT γb) :
    σK * (1 + σB) * (2 * (iCLin n cR M σK σB σT γb * ε ^ 2 / (γ ^ 2 * δ ^ (2 * κ + 1)))) +
        M / 2 * (iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ^ 2 +
        iCS n cR M σK σB σT γb * ε / (γ * δ ^ κ) *
          (iCdK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ≤
      iCE n cR M σK σB σT γb * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ))) := by
  obtain ⟨-, -, -, ⟨d1, d2, -⟩⟩ := absorb (γb := γb) hκ hγ hγb hδ hδ1 hε
  have hγb0 : 0 ≤ γb := hγ.le.trans hγb
  set X := ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ))) with hX
  have hX0 : 0 ≤ X := div_nonneg (sq_nonneg ε) (by positivity)
  have h1 : σK * (1 + σB) * (2 * (iCLin n cR M σK σB σT γb * ε ^ 2 /
      (γ ^ 2 * δ ^ (2 * κ + 1)))) ≤
      2 * σK * (1 + σB) * γb ^ 2 * iCLin n cR M σK σB σT γb * X :=
    calc _ = 2 * σK * (1 + σB) * iCLin n cR M σK σB σT γb *
          (ε ^ 2 / (γ ^ 2 * δ ^ (2 * κ + 1))) := by ring
      _ ≤ 2 * σK * (1 + σB) * iCLin n cR M σK σB σT γb * (γb ^ 2 * X) :=
          mul_le_mul_of_nonneg_left d1 (by positivity)
      _ = _ := by ring
  have h2 : M / 2 * (iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ^ 2 =
      M / 2 * iCDK n cR M σK σB σT γb ^ 2 * X := by
    rw [mul_div_assoc, mul_pow, e4 hδ]
    ring
  have h3 : iCS n cR M σK σB σT γb * ε / (γ * δ ^ κ) *
      (iCdK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ≤
      γb * iCS n cR M σK σB σT γb * iCdK n cR M σK σB σT γb * X :=
    calc _ = iCS n cR M σK σB σT γb * iCdK n cR M σK σB σT γb *
          (ε / (γ * δ ^ κ) * (ε / (γ ^ 2 * δ ^ (2 * κ)))) := by ring
      _ = iCS n cR M σK σB σT γb * iCdK n cR M σK σB σT γb *
          (ε ^ 2 / (γ ^ 3 * δ ^ (3 * κ))) := by rw [e3 hδ]
      _ ≤ iCS n cR M σK σB σT γb * iCdK n cR M σK σB σT γb * (γb * X) :=
          mul_le_mul_of_nonneg_left d2 (by positivity)
      _ = _ := by ring
  rw [h2]
  calc _ ≤ 2 * σK * (1 + σB) * γb ^ 2 * iCLin n cR M σK σB σT γb * X +
        M / 2 * iCDK n cR M σK σB σT γb ^ 2 * X +
        γb * iCS n cR M σK σB σT γb * iCdK n cR M σK σB σT γb * X :=
        add_le_add (add_le_add h1 le_rfl) h3
    _ = iCE1 n cR M σK σB σT γb * X := by unfold iCE1; ring
    _ ≤ iCE n cR M σK σB σT γb * X := mul_le_mul_of_nonneg_right (le_max_left _ _) hX0
    _ = _ := by rw [hX, mul_div_assoc]

/-- Step `stepI:p2s:ne-en`, constants: `|D(H ∘ K)| |ξᴸ| + (M/2)|ΔK|² ≤ C_E ε²/(γ⁴δ^{4κ})`. -/
theorem energy_total_le (hκ : 1 ≤ κ) (hγ : 0 < γ) (hγb : γ ≤ γb) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 ≤ ε) (hσK : 0 ≤ σK) (hcR : 0 ≤ cR) (hcG : 0 ≤ iCG n cR M σK σB σT γb)
    (hΘ : 0 ≤ thetaS n M σK σB) (hcO : 0 ≤ cOm n cR σK) :
    n * (2 * n * σK * ε + thetaS n M σK σB * (cOm n cR σK * ε / (γ * δ ^ (κ + 1)))) *
        (cR * iCG n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) +
        M / 2 * (iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ^ 2 ≤
      iCE n cR M σK σB σT γb * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ))) := by
  obtain ⟨-, -, -, ⟨-, -, d3⟩⟩ := absorb (γb := γb) hκ hγ hγb hδ hδ1 hε
  obtain ⟨-, -, ⟨-, -, -, c4⟩, -⟩ := absorb (γb := γb) hκ hγ hγb hδ hδ1 (sq_nonneg ε)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hγb0 : 0 ≤ γb := hγ.le.trans hγb
  set X := ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ))) with hX
  have hX0 : 0 ≤ X := div_nonneg (sq_nonneg ε) (by positivity)
  have hsplit : n * (2 * n * σK * ε + thetaS n M σK σB * (cOm n cR σK * ε / (γ * δ ^ (κ + 1)))) *
      (cR * iCG n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) =
      2 * n ^ 2 * σK * cR * iCG n cR M σK σB σT γb * (ε ^ 2 / (γ ^ 2 * δ ^ (2 * κ))) +
        n * thetaS n M σK σB * cOm n cR σK * cR * iCG n cR M σK σB σT γb *
          (ε ^ 2 / (γ ^ 3 * δ ^ (3 * κ + 1))) := by
    rw [← e31 hδ]
    have e : ε * (ε / (γ ^ 2 * δ ^ (2 * κ))) = ε ^ 2 / (γ ^ 2 * δ ^ (2 * κ)) := by ring
    rw [← e]
    ring
  have h2 : M / 2 * (iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ^ 2 =
      M / 2 * iCDK n cR M σK σB σT γb ^ 2 * X := by
    rw [mul_div_assoc, mul_pow, e4 hδ]
    ring
  rw [hsplit, h2]
  calc _ ≤ 2 * n ^ 2 * σK * cR * iCG n cR M σK σB σT γb * (γb ^ 2 * X) +
        n * thetaS n M σK σB * cOm n cR σK * cR * iCG n cR M σK σB σT γb * (γb * X) +
        M / 2 * iCDK n cR M σK σB σT γb ^ 2 * X :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left c4 (by positivity))
          (mul_le_mul_of_nonneg_left d3 (by positivity))) le_rfl
    _ = iCE2 n cR M σK σB σT γb * X := by unfold iCE2; ring
    _ ≤ iCE n cR M σK σB σT γb * X := mul_le_mul_of_nonneg_right (le_max_right _ _) hX0
    _ = _ := by rw [hX, mul_div_assoc]

end Arith

/-! ### Taylor with `M/2` -/

section Taylor

variable {τ σω ν γ : ℝ} {ωstar : Fin n → ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
  {ω : Fin n → ℝ} {E₀ β d : ℝ} {θ : Fin n → ℂ}

/-- `|Δ²X| ≤ (M/2) d²` if `|ΔK(θ)| ≤ d < β` and `B_β(K(θ)) ⊆ D` (`bp:p1:taylor`). -/
theorem norm_isoQuadX_half {ω₀ : Fin n → ℝ} (hS : Standing n τ M σK σB σT D H ω₀ γ)
    (hball : Metric.ball (K θ) β ⊆ D) (hcorr : ‖isoCorrection H K ω E₀ θ‖ ≤ d) (hd : d < β) :
    ‖isoQuadX H K ω E₀ θ‖ ≤ M / 2 * d ^ 2 := by
  have hw : ‖isoCorrection H K ω E₀ θ‖ < β := lt_of_le_of_lt hcorr hd
  have hβ : 0 < β := lt_of_le_of_lt (norm_nonneg _) hw
  have hzw : K θ + isoCorrection H K ω E₀ θ ∈ Metric.ball (K θ) β := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hseg : segment ℝ (K θ) (K θ + isoCorrection H K ω E₀ θ) ⊆ D :=
    ((convex_ball (K θ) β).segment_subset (Metric.mem_ball_self hβ) hzw).trans hball
  have h1 := taylor_iteratedFDeriv hS.isOpen (differentiableOn_ham hS) (A := M)
    (fun x hx => (hS.bounds x hx).2.2) hseg
  calc ‖isoQuadX H K ω E₀ θ‖ ≤ M / 2 * ‖isoCorrection H K ω E₀ θ‖ ^ 2 := h1
    _ ≤ M / 2 * d ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hcorr 2)
          (by linarith [hS.M_pos])

/-- `|Δ²H| ≤ (M/2) d²` if `|ΔK(θ)| ≤ d < β` and `B_β(K(θ)) ⊆ D` (`|D²H| ≤ M`). -/
theorem norm_isoQuadH_half (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ)
    (hball : Metric.ball (K θ) β ⊆ D) (hcorr : ‖isoCorrection H K ω E₀ θ‖ ≤ d) (hd : d < β) :
    ‖isoQuadH H K ω E₀ θ‖ ≤ M / 2 * d ^ 2 := by
  have hw : ‖isoCorrection H K ω E₀ θ‖ < β := lt_of_le_of_lt hcorr hd
  have hβ : 0 < β := lt_of_le_of_lt (norm_nonneg _) hw
  have hzw : K θ + isoCorrection H K ω E₀ θ ∈ Metric.ball (K θ) β := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hseg : segment ℝ (K θ) (K θ + isoCorrection H K ω E₀ θ) ⊆ D :=
    ((convex_ball (K θ) β).segment_subset (Metric.mem_ball_self hβ) hzw).trans hball
  have h1 := taylor_iteratedFDeriv hS.isOpen hS.holo (A := M)
    (fun x hx => (hS.bounds x hx).2.2.2.2) hseg
  calc ‖isoQuadH H K ω E₀ θ‖ ≤ M / 2 * ‖isoCorrection H K ω E₀ θ‖ ^ 2 := h1
    _ ≤ M / 2 * d ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hcorr 2)
          (by linarith [hS.M_pos])

end Taylor

/-! ### The identities with pointwise hypotheses (generic copies, design §2.2) -/

section Identity

variable {τ σω ν γ : ℝ} {ωstar : Fin n → ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {E₀ r β ε δ s : ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

/-- Steps `ne-expand`, `ne-reduce` of `bpI:p2:newton-error` (as
`KAM.Iso.Apost.NewtonErrorAux.sumVec_error_eq`), with the invertibility of `S` as hypothesis:
`Ē = P S⁻¹ E_lin + Δ²X + ξ^ω ∂_ω ΔK` on `T_{r-2δ}`. -/
theorem sumVec_error_eq_of (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ)
    (hK : IsoAdmissible σK σB σT D H ωstar E₀ r β ε s K) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h2δ : 2 * δ < r) (hSu : ∀ θ ∈ complexStrip n (r - 2 * δ), IsUnit (sMat K θ).det) :
    ∀ θ ∈ complexStrip n (r - 2 * δ),
      sumVec n (invarianceError H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))
          (isoNewS H K ωstar E₀ s • ωstar) θ) =
        frameMat K θ *ᵥ ((sMat K θ)⁻¹ *ᵥ isoLinError H K (s • ωstar)
          (isoXi H K (s • ωstar) E₀) (isoXiOmega H K (s • ωstar) E₀) θ) +
        sumVec n (isoQuadX H K (s • ωstar) E₀ θ) +
        isoXiOmega H K (s • ωstar) E₀ • sumVec n
          (fderiv ℂ (isoCorrection H K (s • ωstar) E₀) θ (fun l => ((s • ωstar) l : ℂ))) := by
  have hSet := hS.setting hK.s_gt.le
  have hKN := hK.toAdmissibleNoTwist
  have hr := hK.r_pos
  have hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ D := fun θ hθ =>
    hK.ball_sub θ hθ (Metric.mem_ball_self hK.β_pos)
  have hGu : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  obtain ⟨⟨hξd, -, -, -, -, -, hre⟩, -⟩ := KAM.Iso.Apost.correction hS hK hδ hδ1 h2δ
  obtain ⟨hbord, -, -, -, -⟩ :=
    NewtonErrorAux.border_facts hSet hKN hK.twist hK.energy_le hδ hδ1 h2δ
  have hPd := Identities.differentiableOn_frameMat hK.holo hGu
  have hred := reduced hSet hr hK.holo hK𝔅 hGu (r' := r - 2 * δ) (by linarith) (by linarith) hξd
    (isoXiOmega H K (s • ωstar) E₀)
  intro θ hθ
  have hθr : θ ∈ complexStrip n r := Triangular.strip_mono (by linarith) hθ
  have hopen_r := (isOpen_complexStrip n r).mem_nhds hθr
  have hopen_w := (isOpen_complexStrip n (r - 2 * δ)).mem_nhds hθ
  rw [NewtonErrorAux.sumVec_invarianceError_isoNewtonMap hθ (hK.holo.differentiableAt hopen_r)
    (hPd.differentiableAt hopen_r) (hξd.differentiableAt hopen_w) hre,
    NewtonErrorAux.isoResidual_eq_frame (hred.2.2.1 θ hθ (hbord θ hθ)) (hSu θ hθ)]

/-- Step `ne-energy` of `bpI:p2:newton-error` (as
`KAM.Iso.Apost.NewtonErrorAux.energyAverage_sub_eq`), with `|ΔK| < β` on `T_{r-2δ}` as hypothesis:
`Ē^ω = ⟨D(H ∘ K) ξᴸ⟩ + ⟨Δ²H⟩`. -/
theorem energyAverage_sub_eq_of (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ)
    (hK : IsoAdmissible σK σB σT D H ωstar E₀ r β ε s K) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h2δ : 2 * δ < r)
    (hβ : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖isoCorrection H K (s • ωstar) E₀ θ‖ < β) :
    KAM.Iso.energyAverage H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) - (E₀ : ℂ) =
      avg (fun θ => fderiv ℂ (fun y => H (K y)) θ
        (bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0 θ)) +
      avg (isoQuadH H K (s • ωstar) E₀) := by
  have hSet := hS.setting hK.s_gt.le
  have hSt := hSet.toStanding
  have hKN := hK.toAdmissibleNoTwist
  have hr := hK.r_pos
  have hr' : 0 < r - 2 * δ := by linarith
  have hsub : complexStrip n (r - 2 * δ) ⊆ complexStrip n r :=
    Triangular.strip_mono (by linarith)
  have hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ D := fun θ hθ =>
    hK.ball_sub θ hθ (Metric.mem_ball_self hK.β_pos)
  have hGu : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  obtain ⟨⟨-, -, -, hΔd, -, -, -⟩, -⟩ := KAM.Iso.Apost.correction hS hK hδ hδ1 h2δ
  obtain ⟨-, hY, -, hXLd, hXNd⟩ :=
    NewtonErrorAux.border_facts hSet hKN hK.twist hK.energy_le hδ hδ1 h2δ
  have hsplit : avg (fun θ => fderiv ℂ H (K θ) (isoCorrection H K (s • ωstar) E₀ θ)) =
      avg (fun θ => energyRow H K θ ⬝ᵥ bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ) +
      avg (fun θ => fderiv ℂ (fun y => H (K y)) θ
        (bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0 θ)) :=
    (energy_defect hSet hr hK.holo hK.primary hK.real hK𝔅 hGu (r' := r - 2 * δ) hr'
      (by linarith) hXLd hXNd).2.1
  have hKw : DifferentiableOn ℂ K (complexStrip n (r - 2 * δ)) := hK.holo.mono hsub
  have hHK : DifferentiableOn ℂ (fun θ => H (K θ)) (complexStrip n r) :=
    hS.holo.comp hK.holo hK𝔅
  have hDH : DifferentiableOn ℂ
      (fun θ => fderiv ℂ H (K θ) (isoCorrection H K (s • ωstar) E₀ θ))
      (complexStrip n (r - 2 * δ)) :=
    ((differentiableOn_fderiv_h hSt).comp hKw (fun θ hθ => hK𝔅 θ (hsub hθ))).clm_apply hΔd
  have hKΔ : ∀ θ ∈ complexStrip n (r - 2 * δ),
      K θ + isoCorrection H K (s • ωstar) E₀ θ ∈ D := fun θ hθ =>
    hK.ball_sub θ (hsub hθ) (by simpa [Metric.mem_ball, dist_eq_norm] using hβ θ hθ)
  have hHKΔ : DifferentiableOn ℂ
      (fun θ => H (K θ + isoCorrection H K (s • ωstar) E₀ θ)) (complexStrip n (r - 2 * δ)) :=
    hS.holo.comp (hKw.add hΔd) hKΔ
  have c1 : Continuous fun x : Fin n → ℝ => H (K fun i => (x i : ℂ)) :=
    Exactness.continuous_real_of_differentiableOn hr hHK
  have c2 : Continuous fun x : Fin n → ℝ =>
      fderiv ℂ H (K fun i => (x i : ℂ)) (isoCorrection H K (s • ωstar) E₀ fun i => (x i : ℂ)) :=
    Exactness.continuous_real_of_differentiableOn hr' hDH
  have c3 : Continuous fun x : Fin n → ℝ => isoQuadH H K (s • ωstar) E₀ fun i => (x i : ℂ) :=
    Exactness.continuous_real_of_differentiableOn hr' ((hHKΔ.sub (hHK.mono hsub)).sub hDH)
  have hpt : ∀ θ, H (K θ + isoCorrection H K (s • ωstar) E₀ θ) =
      (H (K θ) + fderiv ℂ H (K θ) (isoCorrection H K (s • ωstar) E₀ θ)) +
        isoQuadH H K (s • ωstar) E₀ θ := fun θ => by
    unfold isoQuadH
    ring
  have h1 : KAM.Iso.energyAverage H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) =
      avg (fun θ => H (K θ + isoCorrection H K (s • ωstar) E₀ θ)) :=
    avg_congr (f := fun θ => H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ) θ)) hr' fun θ hθ => by
      rw [NewtonErrorAux.isoNewtonMap_of_mem hθ]
  have h2 : avg (fun θ => H (K θ + isoCorrection H K (s • ωstar) E₀ θ)) =
      avg (fun θ => H (K θ)) +
        avg (fun θ => fderiv ℂ H (K θ) (isoCorrection H K (s • ωstar) E₀ θ)) +
        avg (isoQuadH H K (s • ωstar) E₀) := by
    rw [funext hpt, avg_add_of_continuous
        (f := fun θ => H (K θ) + fderiv ℂ H (K θ) (isoCorrection H K (s • ωstar) E₀ θ))
        (g := isoQuadH H K (s • ωstar) E₀) (c1.add c2) c3,
      avg_add_of_continuous (f := fun θ => H (K θ))
        (g := fun θ => fderiv ℂ H (K θ) (isoCorrection H K (s • ωstar) E₀ θ)) c1 c2]
  have h3 : avg (fun θ => H (K θ)) = KAM.Iso.energyAverage H K := rfl
  rw [h1, h2, hsplit, hY, h3]
  ring

end Identity

end IsoNewtonErrorSharp

variable {τ σω ν : ℝ} {ωstar : Fin n → ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {γ : ℝ}

/-- Blueprint `bpI:p2s:newton-error` (identities as in `KAM.Iso.Apost.newton_error`, from its
constant-free helpers). -/
theorem iso_newton_error_bounds (hC : CohData n τ κ cR)
    (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ) (hγb : γ ≤ γb) {E₀ r β ε δ s : ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : IsoAdmissible σK σB σT D H ωstar E₀ r β ε s K) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h2δ : 2 * δ < r) (hεδ : ε ≤ δ)
    (hTS : cT1 n σK σB * ε / δ + cT2 n κ cR M σK σB * ε / (γ * δ ^ (κ + 1)) ≤ 1)
    (hβ : iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) < β)
    (hsym : cSym n cR σK σB * ε / (γ * δ ^ (κ + 1)) ≤ 1 / 2) :
    (∀ θ ∈ complexStrip n (r - 2 * δ), isoNewtonMap H K ωstar E₀ s (r - 2 * δ) θ ∈ D) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖invarianceError H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))
          (isoNewS H K ωstar E₀ s • ωstar) θ‖ ≤
        iCE n cR M σK σB σT γb * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ)))) ∧
    ‖KAM.Iso.energyAverage H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) - (E₀ : ℂ)‖ ≤
      iCE n cR M σK σB σT γb * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ))) := by
  have hSet := hS.setting hK.s_gt.le
  have hSt := hSet.toStanding
  have hKN := hK.toAdmissibleNoTwist
  have hr := hK.r_pos
  have hr' : 0 < r - 2 * δ := by linarith
  have hε0 := hK.ε_nonneg
  have hγ := hS.gamma_pos
  have hγb0 : 0 < γb := hγ.trans_le hγb
  have hcR := hC.cR_pos
  have hσK := hS.σK_pos
  have hσB := hS.σB_pos
  have hσT := hS.σT_pos
  have hM := hS.M_pos
  have hn : 0 < n := by have := hS.two_le; omega
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨-, hΘ0, hCS0, -, hCG0, -, -, -⟩ :=
    IsoCorrectionSharp.iso_nonneg (n := n) hcR hM hσK hσB hσT hγb0
  have hsub2 : complexStrip n (r - 2 * δ) ⊆ complexStrip n r :=
    Triangular.strip_mono (by linarith)
  have hsub1 : complexStrip n (r - 2 * δ) ⊆ complexStrip n (r - δ) :=
    Triangular.strip_mono (by linarith)
  have hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ D := fun θ hθ =>
    hK.ball_sub θ hθ (Metric.mem_ball_self hK.β_pos)
  have hGu : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  obtain ⟨-, hω1, -⟩ := frequency hSt hr hK.ε_le_one hK𝔅 hK.deriv_le hK.gram hK.error_le
  have hω : ‖s • ωstar‖ ≤ thetaS n M σK σB := by
    refine hω1.trans ?_
    unfold thetaS
    exact mul_le_mul_of_nonneg_left (by linarith [hK.ε_le_one]) (by positivity)
  obtain ⟨⟨⟨-, hXω, -⟩, hcb, -, -⟩, hXL⟩ :=
    IsoCorrectionSharp.correction_core hC hS hγb hK hδ hδ1 h2δ hεδ hTS
  obtain ⟨hgeo1, hgeo2⟩ := geometry_sep hC hSt hKN hδ hδ1 h2δ
  have hSb : ∀ θ ∈ complexStrip n (r - 2 * δ), IsUnit (sMat K θ).det ∧ ‖(sMat K θ)⁻¹‖ ≤ 2 :=
    fun θ hθ => NewtonError.sMat_spec hn ((hgeo2 θ hθ).2.trans hsym)
  have hcorr : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖isoCorrection H K (s • ωstar) E₀ θ‖ < β :=
    fun θ hθ => lt_of_le_of_lt (hcb θ hθ).2.1 hβ
  have hcO : 0 ≤ cOm n cR σK := by unfold cOm; positivity
  refine ⟨fun θ hθ => ?_, fun θ hθ => ?_, ?_⟩
  · -- `K̄(T_{r-2δ}) ⊂ D`
    rw [NewtonErrorAux.isoNewtonMap_of_mem hθ]
    exact hK.ball_sub θ (hsub2 hθ) (by simpa [Metric.mem_ball, dist_eq_norm] using hcorr θ hθ)
  · -- step `ne-e`
    have hid := IsoNewtonErrorSharp.sumVec_error_eq_of hS hK hδ hδ1 h2δ
      (fun θ hθ => (hSb θ hθ).1) θ hθ
    obtain ⟨hxi, hΔ, hdξ, hdΔ⟩ := hcb θ hθ
    have hred := (hgeo1 θ (hsub1 hθ)).2.2.2
    obtain ⟨hΩ, hsymθ⟩ := hgeo2 θ hθ
    have hlin : ‖isoLinError H K (s • ωstar) (isoXi H K (s • ωstar) E₀)
        (isoXiOmega H K (s • ωstar) E₀) θ‖ ≤
        iCLin n cR M σK σB σT γb * ε ^ 2 / (γ ^ 2 * δ ^ (2 * κ + 1)) := by
      refine (norm_isoLinError_le H K (s • ωstar) _ _ θ).trans (le_of_le_of_eq ?_
        (IsoNewtonErrorSharp.iso_lin_eq hδ))
      refine add_le_add (add_le_add ?_ ?_) ?_
      · exact mul_le_mul hred hxi (norm_nonneg _) ((norm_nonneg _).trans hred)
      · exact mul_le_mul hsymθ hdξ (norm_nonneg _) ((norm_nonneg _).trans hsymθ)
      · exact mul_le_mul (mul_le_mul hΩ hω (norm_nonneg _) ((norm_nonneg _).trans hΩ)) hXω
          (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans hΩ) hΘ0)
    have hq : ‖sumVec n (isoQuadX H K (s • ωstar) E₀ θ)‖ ≤
        M / 2 * (iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ^ 2 := by
      rw [norm_sumVec]
      exact IsoNewtonErrorSharp.norm_isoQuadX_half hSt (hK.ball_sub θ (hsub2 hθ)) hΔ hβ
    have hω' : ‖isoXiOmega H K (s • ωstar) E₀ • sumVec n
        (fderiv ℂ (isoCorrection H K (s • ωstar) E₀) θ (fun l => ((s • ωstar) l : ℂ)))‖ ≤
        iCS n cR M σK σB σT γb * ε / (γ * δ ^ κ) *
          (iCdK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) := by
      rw [norm_smul, norm_sumVec]
      exact mul_le_mul hXω hdΔ (norm_nonneg _) ((norm_nonneg _).trans hXω)
    have hPn : ‖frameMat K θ‖ ≤ σK * (1 + σB) :=
      (frame_bounds hSt (hK𝔅 θ (hsub2 hθ)) (hK.deriv_le θ (hsub2 hθ)) (hGu θ (hsub2 hθ))
        (hK.gram θ (hsub2 hθ)).2 (s • ωstar)).2.2.2.2.2.2.1
    have hcL : 0 ≤ iCLin n cR M σK σB σT γb := by
      have : 0 ≤ cRed n σK σB := by unfold cRed; positivity
      have : 0 ≤ cSym n cR σK σB := by unfold cSym; positivity
      have : 0 ≤ iCXi n cR M σK σB σT γb := by unfold iCXi; positivity
      have : 0 ≤ iCDXi n cR M σK σB σT γb := by unfold iCDXi; positivity
      unfold iCLin
      positivity
    have hcd : 0 ≤ iCdK n cR M σK σB σT γb := by
      have : 0 ≤ iCP n M σK σB := by unfold iCP; positivity
      have : 0 ≤ iCXi n cR M σK σB σT γb := by unfold iCXi; positivity
      have : 0 ≤ iCDXi n cR M σK σB σT γb := by unfold iCDXi; positivity
      unfold iCdK
      positivity
    rw [← norm_sumVec, hid]
    calc _ ≤ ‖frameMat K θ *ᵥ ((sMat K θ)⁻¹ *ᵥ isoLinError H K (s • ωstar)
            (isoXi H K (s • ωstar) E₀) (isoXiOmega H K (s • ωstar) E₀) θ)‖ +
          ‖sumVec n (isoQuadX H K (s • ωstar) E₀ θ)‖ +
          ‖isoXiOmega H K (s • ωstar) E₀ • sumVec n
            (fderiv ℂ (isoCorrection H K (s • ωstar) E₀) θ (fun l => ((s • ωstar) l : ℂ)))‖ :=
          norm_add₃_le
      _ ≤ σK * (1 + σB) *
            (2 * (iCLin n cR M σK σB σT γb * ε ^ 2 / (γ ^ 2 * δ ^ (2 * κ + 1)))) +
          M / 2 * (iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ^ 2 +
          iCS n cR M σK σB σT γb * ε / (γ * δ ^ κ) *
            (iCdK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) :=
          add_le_add (add_le_add (NewtonError.norm_mulVec_mulVec_le hPn (hSb θ hθ).2 hlin) hq)
            hω'
      _ ≤ _ := IsoNewtonErrorSharp.iso_total_le hC.one_le_kappa hγ hγb hδ hδ1 hε0 hσK.le
          hσB.le hcL hCS0 hcd
  · -- step `ne-en`
    obtain ⟨-, -, -, hXLd, hXNd⟩ :=
      NewtonErrorAux.border_facts hSet hKN hK.twist hK.energy_le hδ hδ1 h2δ
    have hed := energy_defect hSet hr hK.holo hK.primary hK.real hK𝔅 hGu (r' := r - 2 * δ) hr'
      (by linarith) hXLd hXNd
    have hA : ‖avg (fun θ => fderiv ℂ (fun y => H (K y)) θ
        (bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0 θ))‖ ≤
        n * (2 * n * σK * ε + thetaS n M σK σB * (cOm n cR σK * ε / (γ * δ ^ (κ + 1)))) *
          (cR * iCG n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) := by
      refine hed.2.2 _ _ (fun x _ => ?_) (fun x _ => hXL _ (ofReal_mem_complexStrip hr' x))
      have hθ := ofReal_mem_complexStrip hr' x (n := n)
      have hηN : ‖etaN H K (s • ωstar) (fun i => (x i : ℂ))‖ ≤ 2 * n * σK * ε :=
        ((frame_bounds hSt (hK𝔅 _ (hsub2 hθ)) (hK.deriv_le _ (hsub2 hθ)) (hGu _ (hsub2 hθ))
          (hK.gram _ (hsub2 hθ)).2 (s • ωstar)).2.2.2.2.2.2.2.2.2.2.1 ε
            (hK.error_le _ (hsub2 hθ))).2.2
      refine (hed.1 _ hθ).2.2.trans ?_
      exact mul_le_mul_of_nonneg_left (add_le_add hηN
        (mul_le_mul hω (hgeo2 _ hθ).1 (norm_nonneg _) hΘ0)) hn0
    have hQ : ‖avg (isoQuadH H K (s • ωstar) E₀)‖ ≤
        M / 2 * (iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ^ 2 :=
      norm_torusAverage_le_of_strip_bound hr' fun θ hθ =>
        IsoNewtonErrorSharp.norm_isoQuadH_half hS (hK.ball_sub θ (hsub2 hθ)) (hcb θ hθ).2.1 hβ
    rw [IsoNewtonErrorSharp.energyAverage_sub_eq_of hS hK hδ hδ1 h2δ hcorr]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add hA hQ
      _ ≤ _ := IsoNewtonErrorSharp.energy_total_le hC.one_le_kappa hγ hγb hδ hδ1 hε0 hσK.le
          hcR.le hCG0 hΘ0 hcO

end KAM.Iso.Sharp

end
