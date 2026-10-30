/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp.Constants
public import KAM.Iso.Apost.Standing
public import KAM.Iso.Apost.TorsionDiff
public import KAM.Iso.Linear.LastRow
public import KAM.Sharp.Step
import KAM.Iso.Sharp.ConstantsArith
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The new averaged bordered torsion

Blueprint `bpI:p2s:twist` (`KAM.Iso.Sharp.iso_twist`): for an `IsoAdmissible` torus `K` at
`ω = s ω*` and a torus `K̃` holomorphic on `T_{r-2δ}`, `d`-close to `K`, with invariance error
`≤ ε̃ ≤ ε` at an arbitrary `ω̃ = s̃ ω*` close to `ω`, the averaged bordered torsion `⟨𝖳̃⟩` of
`(K̃, ω̃)` is invertible, within `C_{Δ𝖳} U` of `⟨𝖳⟩`, and its inverse within `ϱ_𝖳 U`
(`U = ε/(γ²δ^{a+1})`).

The proof follows the blueprint; nothing is assumed of the new pair beyond the hypotheses (the new
frequency is not Diophantine, `K̃` is not primary or real, `s̃ > 1` is not used):

* `stepI:p2s:tw-t`: `KAM.Sharp.perturbation_poly` at `ω̃` gives the frame of `K̃` on `T_{r-3δ}` and
  `|T_{ω̃}(K̃) - T_ω(K)| ≤ twistD ≤ C_ΔT U` at real points (`IsoTwistSharp.twistD_le_iCDT`);
* `stepI:p2s:tw-y`: `Y = ωᵀ - (ηᴸ)ᵀ` for both pairs (`KAM.Iso.Linear.LastRowAux.energyRow_eq_sub_etaL`,
  whose only premise is `det G ≠ 0`), so `∑ |Ỹ - Y| ≤ n|ω̃ - ω| + n|η̃ᴸ| + n|ηᴸ|`
  (`IsoTwistSharp.sum_norm_energyRow_sub_le_eta`);
* `stepI:p2s:tw-avg`: the bordered matrix of the differences at each real point
  (`KAM.Iso.Apost.TorsionDiff.norm_extendedTorsion_sub_le`) and the average
  (`TorsionDiff.norm_extendedTorsionAverage_sub_le`; continuity of both bordered torsions from
  `KAM.Iso.Linear.extended_regular`, which accepts the arbitrary new frequency);
* `stepI:p2s:tw-inv`: `KAM.Sharp.neumann_ratio` with `q = ϑ`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology

namespace KAM.Iso.Sharp

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost KAM.Sharp

variable {n : ℕ} {κ cR M σK σB σT γb : ℝ}

namespace IsoTwistSharp

/-- Step `stepI:p2s:tw-t`: `twistD` at `d = C_ΔK ε/(γ²δ^{2κ})` is at most `C_ΔT ε/(γ²δ^{2κ+1})`
(absorption of `ε/δ` and `ε/(γδ^{κ+1})`, as `KAM.Sharp.StepSharp.twistD_le_cDT`). -/
theorem twistD_le_iCDT {γ δ ε : ℝ} (hκ : 1 ≤ κ) (hcR : 0 < cR) (hM : 0 < M) (hσK : 0 < σK)
    (hσB : 0 < σB) (hγ : 0 < γ) (hγb : γ ≤ γb) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) :
    twistD n κ cR M σK σB γ ε δ (iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ≤
      iCDT n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) := by
  obtain ⟨-, ⟨-, a2b, a2c, -⟩, -, -⟩ := absorb hκ hγ hγb hδ hδ1 hε
  have c1 : 0 ≤ (1 + vthh ^ 3) * cT1 n σK σB := by unfold cT1; rw [vthh_eq]; positivity
  have c2 : 0 ≤ (1 + vthh ^ 5) * σB ^ 3 * wT n M σK * cOm n cR σK := by
    unfold wT cOm; rw [vthh_eq]; positivity
  have t1 : (1 + vthh ^ 3) * cT1 n σK σB * ε / δ ≤
      (1 + vthh ^ 3) * cT1 n σK σB * γb ^ 2 * (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) :=
    calc (1 + vthh ^ 3) * cT1 n σK σB * ε / δ = (1 + vthh ^ 3) * cT1 n σK σB * (ε / δ) :=
          mul_div_assoc _ _ _
      _ ≤ (1 + vthh ^ 3) * cT1 n σK σB * (γb ^ 2 * (ε / (γ ^ 2 * δ ^ (2 * κ + 1)))) :=
          mul_le_mul_of_nonneg_left a2b c1
      _ = _ := by ring
  have t2 : (1 + vthh ^ 5) * σB ^ 3 * wT n M σK * cOm n cR σK * ε / (γ * δ ^ (κ + 1)) ≤
      (1 + vthh ^ 5) * σB ^ 3 * wT n M σK * cOm n cR σK * γb *
        (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) :=
    calc (1 + vthh ^ 5) * σB ^ 3 * wT n M σK * cOm n cR σK * ε / (γ * δ ^ (κ + 1)) =
          (1 + vthh ^ 5) * σB ^ 3 * wT n M σK * cOm n cR σK * (ε / (γ * δ ^ (κ + 1))) :=
          mul_div_assoc _ _ _
      _ ≤ (1 + vthh ^ 5) * σB ^ 3 * wT n M σK * cOm n cR σK *
            (γb * (ε / (γ ^ 2 * δ ^ (2 * κ + 1)))) :=
          mul_le_mul_of_nonneg_left a2c c2
      _ = _ := by ring
  have t0 : (cDab n M σK σB + cDc n M σK σB) *
      (iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) / δ =
      (cDab n M σK σB + cDc n M σK σB) * iCDK n cR M σK σB σT γb *
        (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) := by
    rw [StepSharp.div_delta_eq hγ hδ, mul_div_assoc]
  calc twistD n κ cR M σK σB γ ε δ (iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) =
        (cDab n M σK σB + cDc n M σK σB) *
          (iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) / δ +
        (1 + vthh ^ 3) * cT1 n σK σB * ε / δ +
        (1 + vthh ^ 5) * σB ^ 3 * wT n M σK * cOm n cR σK * ε / (γ * δ ^ (κ + 1)) := rfl
    _ ≤ (cDab n M σK σB + cDc n M σK σB) * iCDK n cR M σK σB σT γb *
          (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) +
        (1 + vthh ^ 3) * cT1 n σK σB * γb ^ 2 * (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) +
        (1 + vthh ^ 5) * σB ^ 3 * wT n M σK * cOm n cR σK * γb *
          (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) := by
      rw [t0]; exact add_le_add (add_le_add le_rfl t1) t2
    _ = iCDT n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) := by unfold iCDT; ring

/-- Step `stepI:p2s:tw-y`: with `Y = ωᵀ - (ηᴸ)ᵀ` for both pairs (only `det G ≠ 0` is used),
`∑_j |Ỹ_j - Y_j| ≤ n|ω̃ - ω| + n|η̃ᴸ| + n|ηᴸ|` at `θ`. -/
theorem sum_norm_energyRow_sub_le_eta {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω ω' : Fin n → ℝ} {θ : Fin n → ℂ}
    (hG : IsUnit (gramMatrix K θ).det) (hG' : IsUnit (gramMatrix K' θ).det) :
    ∑ j, ‖energyRow H K' θ j - energyRow H K θ j‖ ≤
      n * ‖ω' - ω‖ + n * ‖etaL H K' ω' θ‖ + n * ‖etaL H K ω θ‖ := by
  have hj : ∀ j, ‖energyRow H K' θ j - energyRow H K θ j‖ ≤
      ‖ω' - ω‖ + ‖etaL H K' ω' θ‖ + ‖etaL H K ω θ‖ := by
    intro j
    rw [LastRowAux.energyRow_eq_sub_etaL (H := H) (ω := ω') hG',
      LastRowAux.energyRow_eq_sub_etaL (H := H) (ω := ω) hG]
    simp only [Pi.sub_apply]
    have e : ((ω' j : ℂ) - etaL H K' ω' θ j) - ((ω j : ℂ) - etaL H K ω θ j) =
        ((ω' j : ℂ) - (ω j : ℂ)) - etaL H K' ω' θ j + etaL H K ω θ j := by ring
    have h1 : ‖(ω' j : ℂ) - (ω j : ℂ)‖ ≤ ‖ω' - ω‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real]
      exact norm_le_pi_norm (ω' - ω) j
    rw [e]
    calc _ ≤ ‖((ω' j : ℂ) - (ω j : ℂ)) - etaL H K' ω' θ j‖ + ‖etaL H K ω θ j‖ :=
          norm_add_le _ _
      _ ≤ ‖(ω' j : ℂ) - (ω j : ℂ)‖ + ‖etaL H K' ω' θ j‖ + ‖etaL H K ω θ j‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ _ := add_le_add (add_le_add h1 (norm_le_pi_norm _ j)) (norm_le_pi_norm _ j)
  calc ∑ j, ‖energyRow H K' θ j - energyRow H K θ j‖
      ≤ ∑ _j : Fin n, (‖ω' - ω‖ + ‖etaL H K' ω' θ‖ + ‖etaL H K ω θ‖) :=
        Finset.sum_le_sum fun j _ => hj j
    _ = n * ‖ω' - ω‖ + n * ‖etaL H K' ω' θ‖ + n * ‖etaL H K ω θ‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end IsoTwistSharp

variable {τ σω ν : ℝ} {ωstar : Fin n → ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {γ : ℝ}

/-- Blueprint `bpI:p2s:twist`. -/
theorem iso_twist (hC : CohData n τ κ cR) (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ)
    (hγb : γ ≤ γb) {E₀ r β ε δ s : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : IsoAdmissible σK σB σT D H ωstar E₀ r β ε s K) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h3δ : 3 * δ < r) (hεδ : ε ≤ δ) {K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {s' ε' : ℝ}
    (hK' : DifferentiableOn ℂ K' (complexStrip n (r - 2 * δ)))
    (hd : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖K' θ - K θ‖ ≤ iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)))
    (hdβ : iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) < β)
    (hE' : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖invarianceError H K' (s' • ωstar) θ‖ ≤ ε')
    (hε' : ε' ≤ ε)
    (hω : ‖s' • ωstar - s • ωstar‖ ≤ iCDw n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)))
    (hs1 : n * (iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) / δ ≤ vth * σK)
    (hs2 : σB * cGram n σK * (iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) / δ ≤ vth)
    (hs3 : σT * (iCDTb n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1))) ≤ vth) :
    IsUnit (KAM.Iso.extendedTorsionAverage H K' (s' • ωstar)).det ∧
    ‖KAM.Iso.extendedTorsionAverage H K' (s' • ωstar) -
        KAM.Iso.extendedTorsionAverage H K (s • ωstar)‖ ≤
      iCDTb n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) ∧
    ‖(KAM.Iso.extendedTorsionAverage H K' (s' • ωstar))⁻¹ -
        (KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹‖ ≤
      iRateT n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) := by
  have hSet := hS.setting hK.s_gt.le
  have hSt := hSet.toStanding
  have hKN := hK.toAdmissibleNoTwist
  have hr := hK.r_pos
  have hr3 : 0 < r - 3 * δ := by linarith
  have hε0 := hK.ε_nonneg
  have hγ := hS.gamma_pos
  have hγb0 : 0 < γb := hγ.trans_le hγb
  have hcR := hC.cR_pos
  have hσK := hS.σK_pos
  have hσB := hS.σB_pos
  have hσT := hS.σT_pos
  have hM := hS.M_pos
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsub3 : complexStrip n (r - 3 * δ) ⊆ complexStrip n r :=
    Triangular.strip_mono (by linarith)
  have hsub32 : complexStrip n (r - 3 * δ) ⊆ complexStrip n (r - 2 * δ) :=
    Triangular.strip_mono (by linarith)
  have hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ D := fun θ hθ =>
    hK.ball_sub θ hθ (Metric.mem_ball_self hK.β_pos)
  have hGu : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  -- step `tw-t`: the frame of `K̃` and the torsion block
  obtain ⟨hball, hfr, -, hTdiff, -⟩ :=
    perturbation_poly hC hSt hKN hδ hδ1 h3δ hεδ hK' hd hdβ hE' hε' hs1 hs2
  have hd0 : 0 ≤ iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) :=
    (norm_nonneg _).trans (hd _ (ofReal_mem_complexStrip (by linarith) (0 : Fin n → ℝ)))
  have hK'D : ∀ θ ∈ complexStrip n (r - 2 * δ), K' θ ∈ D := fun θ hθ =>
    hball θ hθ (Metric.mem_ball_self (by linarith))
  -- continuity of both bordered torsions on `ℝⁿ`
  have hc := (extended_regular hSt hr hK.holo hK𝔅 hGu (s • ωstar)).2.2
  have hc' := (extended_regular hSt hr3 (hK'.mono hsub32) (fun θ hθ => hK'D θ (hsub32 hθ))
    (fun θ hθ => (hfr θ hθ).2.2.1) (s' • ωstar)).2.2
  -- the constants
  obtain ⟨-, ⟨hεU, -, -, hEU⟩, -, -⟩ := absorb hC.one_le_kappa hγ hγb hδ hδ1 hε0
  set U := ε / (γ ^ 2 * δ ^ (2 * κ + 1)) with hU
  have hU0 : 0 ≤ U := div_nonneg hε0 (by positivity)
  have hCw : 0 ≤ iCDw n cR M σK σB σT γb := (iso_consts_pos (κ := κ) (μ := 1) (ν := 1)
    (by have := hS.two_le; omega) hcR hM hσK hσB hσT hγb0 one_pos one_pos).2.1.le
  have hdω : iCDw n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) ≤
      iCDw n cR M σK σB σT γb * U := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hEU hCw
  have htD := IsoTwistSharp.twistD_le_iCDT (n := n) (σT := σT) hC.one_le_kappa hcR hM hσK hσB hγ
    hγb hδ hδ1 hε0 |>.trans_eq (mul_div_assoc _ _ _)
  -- steps `tw-y`, `tw-avg`: the bordered torsions differ by `≤ C_{Δ𝖳} U` at every real point
  have hpt : ∀ x : Fin n → ℝ,
      ‖KAM.Iso.extendedTorsion H K' (s' • ωstar) (fun i => (x i : ℂ)) -
        KAM.Iso.extendedTorsion H K (s • ωstar) (fun i => (x i : ℂ))‖ ≤
      iCDTb n cR M σK σB σT γb * U := by
    intro x
    have hθ := ofReal_mem_complexStrip hr3 x (n := n)
    have hθr := hsub3 hθ
    obtain ⟨-, hL', hG', hB', -⟩ := hfr _ hθ
    have hη := LastRowAux.norm_etaL_le_of_le (hK.deriv_le _ hθr) (hK.gram _ hθr).2
      (hK.error_le _ hθr)
    have hη' := LastRowAux.norm_etaL_le_of_le hL' hB' (hE' _ (hsub32 hθ))
    have hY : ∑ j, ‖energyRow H K' (fun i => (x i : ℂ)) j -
        energyRow H K (fun i => (x i : ℂ)) j‖ ≤
        n * (iCDw n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) +
          2 * n ^ 2 * (1 + vthh ^ 2) * σK * σB * ε := by
      refine (IsoTwistSharp.sum_norm_energyRow_sub_le_eta (ω := s • ωstar) (ω' := s' • ωstar)
        (hGu _ hθr) hG').trans ?_
      have hv : 0 ≤ vthh := by rw [vthh_eq]; norm_num
      have h2 : 2 * n * (vthh * σK) * (vthh * σB) * ε' ≤ 2 * n * (vthh * σK) * (vthh * σB) * ε :=
        mul_le_mul_of_nonneg_left hε' (by positivity)
      calc _ ≤ n * (iCDw n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) +
            n * (2 * n * (vthh * σK) * (vthh * σB) * ε) + n * (2 * n * σK * σB * ε) :=
            add_le_add (add_le_add (mul_le_mul_of_nonneg_left hω hn0)
              (mul_le_mul_of_nonneg_left (hη'.trans h2) hn0)) (mul_le_mul_of_nonneg_left hη hn0)
        _ = _ := by ring
    refine (TorsionDiff.norm_extendedTorsion_sub_le _ (hTdiff x) hω hY).trans ?_
    have hm1 : twistD n κ cR M σK σB γ ε δ (iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) +
        iCDw n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) ≤
        (iCDT n cR M σK σB σT γb + iCDw n cR M σK σB σT γb) * U := by
      rw [add_mul]
      exact add_le_add htD hdω
    have hm2 : n * (iCDw n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) +
        2 * n ^ 2 * (1 + vthh ^ 2) * σK * σB * ε ≤
        (n * iCDw n cR M σK σB σT γb + 2 * (n : ℝ) ^ 2 * (1 + vthh ^ 2) * σK * σB * γb ^ 2) *
          U := by
      have hc2 : 0 ≤ 2 * (n : ℝ) ^ 2 * (1 + vthh ^ 2) * σK * σB := by
        rw [vthh_eq]; positivity
      calc _ ≤ n * (iCDw n cR M σK σB σT γb * U) +
            2 * n ^ 2 * (1 + vthh ^ 2) * σK * σB * (γb ^ 2 * U) :=
            add_le_add (mul_le_mul_of_nonneg_left hdω hn0) (mul_le_mul_of_nonneg_left hεU hc2)
        _ = _ := by ring
    calc _ ≤ max ((iCDT n cR M σK σB σT γb + iCDw n cR M σK σB σT γb) * U)
          ((n * iCDw n cR M σK σB σT γb +
            2 * (n : ℝ) ^ 2 * (1 + vthh ^ 2) * σK * σB * γb ^ 2) * U) := max_le_max hm1 hm2
      _ = iCDTb n cR M σK σB σT γb * U := by unfold iCDTb; rw [max_mul_of_nonneg _ _ hU0]
  have hdiff : ‖KAM.Iso.extendedTorsionAverage H K' (s' • ωstar) -
      KAM.Iso.extendedTorsionAverage H K (s • ωstar)‖ ≤
      iCDTb n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) := by
    rw [mul_div_assoc]
    exact TorsionDiff.norm_extendedTorsionAverage_sub_le hc hc' hpt
  -- step `tw-inv`
  have hA : IsUnit (KAM.Iso.extendedTorsionAverage H K (s • ωstar)) :=
    (Matrix.isUnit_iff_isUnit_det _).2 hK.twist.1
  have hsmall : ‖(KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹‖ *
      ‖KAM.Iso.extendedTorsionAverage H K' (s' • ωstar) -
        KAM.Iso.extendedTorsionAverage H K (s • ωstar)‖ ≤ vth :=
    (mul_le_mul hK.twist.2 hdiff (norm_nonneg _) hσT.le).trans hs3
  obtain ⟨hUn, -, hBdiff⟩ := neumann_ratio hA (q := vth) (by rw [vth_eq]; norm_num) hsmall
  rw [add_sub_cancel] at hUn hBdiff
  have h17 : (1 : ℝ) - vth = 7 / 8 := by rw [vth_eq]; norm_num
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).1 hUn, hdiff, ?_⟩
  have hTT : ‖(KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹‖ ^ 2 ≤ σT ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hK.twist.2 2
  calc _ ≤ ‖(KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹‖ ^ 2 *
        ‖KAM.Iso.extendedTorsionAverage H K' (s' • ωstar) -
          KAM.Iso.extendedTorsionAverage H K (s • ωstar)‖ / (1 - vth) := hBdiff
    _ ≤ σT ^ 2 * (iCDTb n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1))) / (1 - vth) :=
        div_le_div_of_nonneg_right (mul_le_mul hTT hdiff (norm_nonneg _) (by positivity))
          (by rw [h17]; norm_num)
    _ = iRateT n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1)) := by
        rw [h17]
        unfold iRateT
        rw [vthh_eq]
        ring

end KAM.Iso.Sharp

end
