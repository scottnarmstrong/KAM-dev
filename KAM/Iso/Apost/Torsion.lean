/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Apost.Correction
public import KAM.Iso.Apost.TorsionDiff
import KAM.Strip.Periodic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Part 2 (isoenergetic iteration): the new averaged extended torsion

Blueprint node `bpI:p2:torsion`
(`KAM.Iso.Apost.torsion_step`). For an `IsoAdmissible` torus `K` at `ω = s ω*`, the Newton map
`K̄ = isoNewtonMap … (r - 2δ)` (`K̄ = K + ΔK` on `T_{r-2δ}`) and the new frequency `ω̄ = s̄ ω*`:
`K̄` is holomorphic, primary and real on reals, its frame is controlled by the perturbation lemma
`KAM.Iso.Linear.perturbation_noA5`, and the averaged bordered torsion `⟨𝖳_H(K̄, ω̄)⟩` is defined,
invertible, and a perturbation of `⟨𝖳_H(K, ω)⟩` of size `C_{Δ𝖳} d/δ²`.

The proof follows the steps of the blueprint:

* `to-frame`: `perturbation_noA5` on `T_{r-2δ}` (loss `δ`) for `K̄ - K`, `|K̄ - K| ≤ d`;
  regularity of `𝖳_H(K̄, ω̄)` at the non-certified frequency `ω̄` is
  `KAM.Iso.Linear.extended_regular` (blueprint issue B1).
* `to-omega`, `to-row`, `to-avg`: the helper lemmas of `KAM/Iso/Apost/TorsionDiff.lean`.
* `to-inv`: the Neumann lemma `KAM.Iso.Linear.neumann_fintype` on `Fin n ⊕ Unit` matrices.

`isoNewtonMap_of_mem` and the regularity of the Newton map are in `KAM.Iso.Apost.TorsionAux`.
-/

@[expose] public section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.Iso.Apost

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear

namespace TorsionAux

variable {n : ℕ} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ωstar : Fin n → ℝ} {E₀ s w r : ℝ}

/-- On `T_w` the Newton map is `K + ΔK`. -/
theorem isoNewtonMap_of_mem {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n w) :
    isoNewtonMap H K ωstar E₀ s w θ = K θ + isoCorrection H K (s • ωstar) E₀ θ := by
  simp [isoNewtonMap, hθ]

/-- `K̄` is holomorphic on `T_w` when `K` and `ΔK` are. -/
theorem isoNewtonMap_differentiableOn (hK : DifferentiableOn ℂ K (complexStrip n w))
    (hc : DifferentiableOn ℂ (isoCorrection H K (s • ωstar) E₀) (complexStrip n w)) :
    DifferentiableOn ℂ (isoNewtonMap H K ωstar E₀ s w) (complexStrip n w) :=
  (hK.add hc).congr fun _ hθ => isoNewtonMap_of_mem hθ

/-- `K̄` is primary on `T_w`: `K` is primary on `T_r ⊇ T_w` and `ΔK` is `1`-periodic on `T_w`. -/
theorem isoNewtonMap_isPrimaryOnStrip (hwr : w ≤ r) (hK : IsPrimaryOnStrip K r)
    (hc : IsPeriodicOn (isoCorrection H K (s • ωstar) E₀) w) :
    IsPrimaryOnStrip (isoNewtonMap H K ωstar E₀ s w) w := by
  intro θ hθ k
  have hθk : θ + (fun i => (k i : ℂ)) ∈ complexStrip n w :=
    add_mem_complexStrip_of_im_eq_zero hθ fun j => by simp
  rw [isoNewtonMap_of_mem hθk, isoNewtonMap_of_mem hθ, hK θ (Triangular.strip_mono hwr hθ) k,
    periodic_int_shift hc k hθ]
  abel

/-- `K̄` is real on reals when `K` and `ΔK` are and `0 < w`. -/
theorem isoNewtonMap_isRealOnReals (hw : 0 < w) (hK : IsRealOnReals K)
    (hc : IsRealOnReals (isoCorrection H K (s • ωstar) E₀)) :
    IsRealOnReals (isoNewtonMap H K ωstar E₀ s w) := by
  intro θ
  have hθ : (fun i => (θ i : ℂ)) ∈ complexStrip n w := fun i => by simpa using hw
  obtain ⟨z, hz⟩ := hK θ
  obtain ⟨z', hz'⟩ := hc θ
  refine ⟨(z.1 + z'.1, z.2 + z'.2), ?_⟩
  rw [isoNewtonMap_of_mem hθ, hz, hz']
  ext i <;> simp

end TorsionAux

section Step

variable {n : ℕ} {τ M σK σB σT σω ν γ : ℝ} {ωstar : Fin n → ℝ}
  {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

/-- `bpI:p2:torsion` (`d = dStep`): the frame of `K̄` and the new averaged extended torsion. -/
theorem torsion_step (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ) {E₀ r β ε δ s : ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : IsoAdmissible σK σB σT D H ωstar E₀ r β ε s K) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h4δ : 4 * δ < r) (hβ : dStep n τ M σK σB σT γ ε δ < β)
    (hsmall : 2 * mSize M σK σB σT * CDTbord n M σK σB σT *
      dStep n τ M σK σB σT γ ε δ / δ ^ 2 ≤ 1) :
    (DifferentiableOn ℂ (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) (complexStrip n (r - 2 * δ)) ∧
      IsPrimaryOnStrip (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) (r - 2 * δ) ∧
      IsRealOnReals (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ), Metric.ball (isoNewtonMap H K ωstar E₀ s (r - 2 * δ) θ)
      (β - dStep n τ M σK σB σT γ ε δ) ⊆ D) ∧
    (∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖fderiv ℂ (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) θ - fderiv ℂ K θ‖ ≤
        n * dStep n τ M σK σB σT γ ε δ / δ ∧
      ‖fderiv ℂ (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) θ‖ ≤ 2 * mSize M σK σB σT ∧
      IsUnit (gramMatrix (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) θ).det ∧
      ‖(gramMatrix (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) θ)⁻¹‖ ≤ 2 * mSize M σK σB σT ∧
      ‖(gramMatrix (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤
        C_B n M σK σB σT * dStep n τ M σK σB σT γ ε δ / δ) ∧
    Continuous (fun x : Fin n → ℝ => KAM.Iso.extendedTorsion H
      (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) (isoNewS H K ωstar E₀ s • ωstar)
      (fun i => (x i : ℂ))) ∧
    ‖KAM.Iso.extendedTorsionAverage H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))
        (isoNewS H K ωstar E₀ s • ωstar) - KAM.Iso.extendedTorsionAverage H K (s • ωstar)‖ ≤
      CDTbord n M σK σB σT * dStep n τ M σK σB σT γ ε δ / δ ^ 2 ∧
    IsUnit (KAM.Iso.extendedTorsionAverage H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))
      (isoNewS H K ωstar E₀ s • ωstar)).det ∧
    ‖(KAM.Iso.extendedTorsionAverage H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))
        (isoNewS H K ωstar E₀ s • ωstar))⁻¹ - (KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹‖ ≤
      2 * mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT * dStep n τ M σK σB σT γ ε δ / δ ^ 2 := by
  have hSet := hS.setting hK.s_gt.le
  have hSt := hSet.toStanding
  have hP := hS.toParams
  have hr := hK.r_pos
  have hr2 : 0 < r - 2 * δ := by linarith
  have hr3 : 0 < r - 3 * δ := by linarith
  have hr4 : 0 < r - 4 * δ := by linarith
  have hsub2 : complexStrip n (r - 2 * δ) ⊆ complexStrip n r :=
    Triangular.strip_mono (by linarith)
  have hsub32 : complexStrip n (r - 3 * δ) ⊆ complexStrip n (r - 2 * δ) :=
    Triangular.strip_mono (by linarith)
  have hsub43 : complexStrip n (r - 4 * δ) ⊆ complexStrip n (r - 3 * δ) :=
    Triangular.strip_mono (by linarith)
  have hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ D := fun θ hθ =>
    hK.ball_sub θ hθ (Metric.mem_ball_self hK.β_pos)
  have hGu : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  obtain ⟨-, hω⟩ := hK.freq hS
  obtain ⟨⟨-, -, -, hcd, hcp, hcr, -⟩, -, -, -, hdist, hdω⟩ :=
    correction hS hK hδ hδ1 (by linarith)
  have h0 : (0 : Fin n → ℂ) ∈ complexStrip n (r - 2 * δ) := fun i => by simpa using hr2
  have hd0 : 0 ≤ dStep n τ M σK σB σT γ ε δ := (norm_nonneg _).trans (hdist 0 h0)
  -- the Newton map
  have hdiff : DifferentiableOn ℂ (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))
      (complexStrip n (r - 2 * δ)) :=
    TorsionAux.isoNewtonMap_differentiableOn (hK.holo.mono hsub2) hcd
  have hdK : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖isoNewtonMap H K ωstar E₀ s (r - 2 * δ) θ - K θ‖ ≤ dStep n τ M σK σB σT γ ε δ :=
    fun θ hθ => by
      rw [TorsionAux.isoNewtonMap_of_mem hθ, add_sub_cancel_left]
      exact hdist θ hθ
  -- `to-frame`: the perturbation lemma on `T_{r-2δ}`
  have hsmall' : 2 * mSize M σK σB σT * C_DT n M σK σB σT * dStep n τ M σK σB σT γ ε δ / δ ^ 2 ≤
      1 := by
    refine le_trans ?_ hsmall
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    refine mul_le_mul_of_nonneg_right ?_ hd0
    exact mul_le_mul_of_nonneg_left (C_DT_le_CDTbord hP)
      (mul_nonneg zero_le_two (zero_le_one.trans one_le_mSize))
  obtain ⟨hs1, -, -, -⟩ := perturbation_small hP hδ hδ1 hd0 hsmall'
  obtain ⟨hball, hDK, hB, hN, hT⟩ := perturbation_noA5 hSet hr2 hδ hδ1 (by linarith) hω
    (hK.holo.mono hsub2) (fun θ hθ => hK.ball_sub θ (hsub2 hθ))
    (fun θ hθ => hK.deriv_le θ (hsub2 hθ)) (fun θ hθ => hK.gram θ (hsub2 hθ)) hdiff hdK hβ hsmall'
  have e3 : r - 2 * δ - δ = r - 3 * δ := by ring
  have e4 : r - 2 * δ - 2 * δ = r - 4 * δ := by ring
  rw [e3] at hDK hB hN
  rw [e4] at hT
  have hK'D : ∀ θ ∈ complexStrip n (r - 2 * δ),
      isoNewtonMap H K ωstar E₀ s (r - 2 * δ) θ ∈ D := fun θ hθ =>
    (hball θ hθ).1 (Metric.mem_ball_self (sub_pos.2 hβ))
  have hdiff3 := hdiff.mono hsub32
  have hG3 : ∀ θ ∈ complexStrip n (r - 3 * δ),
      IsUnit (gramMatrix (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) θ).det :=
    fun θ hθ => (hB θ hθ).1
  -- continuity of `𝖳_H(K̄, ω̄)` on the reals (`extended_regular`, issue B1)
  obtain ⟨-, -, hcont⟩ := extended_regular hSt hr3 hdiff3 (fun θ hθ => hK'D θ (hsub32 hθ)) hG3
    (isoNewS H K ωstar E₀ s • ωstar)
  obtain ⟨-, -, hcont0⟩ := extended_regular hSt hr hK.holo hK𝔅 hGu (s • ωstar)
  -- steps `to-omega`, `to-row`, `to-avg`: the pointwise bound on `ℝⁿ`
  have hNd3 := differentiableOn_normalMat hdiff3 hG3
  have hNb3 : ∀ θ ∈ complexStrip n (r - 3 * δ),
      ‖normalMat (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) θ‖ ≤ 2 * mSize M σK σB σT ^ 2 :=
    fun θ hθ => (hN θ hθ).2.1
  have e43 : r - 3 * δ - δ = r - 4 * δ := by ring
  have hb : ∀ x : Fin n → ℝ, ‖KAM.Iso.extendedTorsion H
      (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) (isoNewS H K ωstar E₀ s • ωstar)
        (fun i => (x i : ℂ)) - KAM.Iso.extendedTorsion H K (s • ωstar) (fun i => (x i : ℂ))‖ ≤
      CDTbord n M σK σB σT * dStep n τ M σK σB σT γ ε δ / δ ^ 2 := by
    intro x
    have hx4 : (fun i => (x i : ℂ)) ∈ complexStrip n (r - 4 * δ) :=
      ofReal_mem_complexStrip hr4 x
    have hx3 := hsub43 hx4
    have hx2 := hsub32 hx3
    have hxr := hsub2 hx2
    -- the torsion block
    have hfreq := TorsionDiff.norm_torsion_sub_freq_le (H := H) (s • ωstar)
      (isoNewS H K ωstar E₀ s • ωstar) hδ hNd3 hNb3 hdω _ (by rw [e43]; exact hx4)
    have hTb := hT _ hx4
    have hTK : ‖torsion H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))
        (isoNewS H K ωstar E₀ s • ωstar) (fun i => (x i : ℂ)) -
        torsion H K (s • ωstar) (fun i => (x i : ℂ))‖ ≤
        C_DT n M σK σB σT * dStep n τ M σK σB σT γ ε δ / δ ^ 2 +
          8 * (n : ℝ) ^ 2 * mSize M σK σB σT ^ 4 * dStep n τ M σK σB σT γ ε δ / δ := by
      have hsplit := norm_add_le
        (torsion H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))
          (isoNewS H K ωstar E₀ s • ωstar) (fun i => (x i : ℂ)) -
          torsion H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) (s • ωstar) (fun i => (x i : ℂ)))
        (torsion H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) (s • ωstar) (fun i => (x i : ℂ)) -
          torsion H K (s • ωstar) (fun i => (x i : ℂ)))
      rw [sub_add_sub_cancel] at hsplit
      have e8 : 2 * (n : ℝ) * (2 * mSize M σK σB σT ^ 2) *
          (n * dStep n τ M σK σB σT γ ε δ * δ⁻¹ * (2 * mSize M σK σB σT ^ 2)) =
          8 * (n : ℝ) ^ 2 * mSize M σK σB σT ^ 4 * dStep n τ M σK σB σT γ ε δ / δ := by
        ring
      linarith
    -- the energy row
    have hY : ∑ j, ‖energyRow H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) (fun i => (x i : ℂ)) j -
        energyRow H K (fun i => (x i : ℂ)) j‖ ≤
        CY n M σK σB σT * dStep n τ M σK σB σT γ ε δ / δ := by
      have hw : ‖isoNewtonMap H K ωstar E₀ s (r - 2 * δ) (fun i => (x i : ℂ)) -
          K (fun i => (x i : ℂ))‖ < β := lt_of_le_of_lt (hdK _ hx2) hβ
      have hmvt := TorsionDiff.norm_fderiv_sub_le_mvt hS.isOpen hS.holo
        (fun z hz => (hS.bounds z hz).2.2.2.2) (hK.ball_sub _ hxr) hw
      rw [add_sub_cancel] at hmvt
      have hφ : ‖fderiv ℂ H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ) (fun i => (x i : ℂ))) -
          fderiv ℂ H (K (fun i => (x i : ℂ)))‖ ≤ M * dStep n τ M σK σB σT γ ε δ :=
        hmvt.trans (mul_le_mul_of_nonneg_left (hdK _ hx2) hS.M_pos.le)
      exact (TorsionDiff.sum_norm_energyRow_sub_le _ (hN _ hx3).2.1 (hN _ hx3).1 hφ
        (hS.bounds _ (hK𝔅 _ hxr)).1).trans (TorsionDiff.energy_row_arith hP hδ hδ1 hd0)
    refine (TorsionDiff.norm_extendedTorsion_sub_le _ hTK hdω hY).trans ?_
    exact TorsionDiff.torsion_diff_arith hP hδ hδ1 hd0
  have havg := TorsionDiff.norm_extendedTorsionAverage_sub_le hcont0 hcont hb
  -- step `to-inv`: Neumann series on `Fin n ⊕ Unit`
  have hmσ : σT ≤ mSize M σK σB σT := σT_le_mSize
  have hΔ : ‖KAM.Iso.extendedTorsionAverage H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))
      (isoNewS H K ωstar E₀ s • ωstar) - KAM.Iso.extendedTorsionAverage H K (s • ωstar)‖ ≤
      CDTbord n M σK σB σT * dStep n τ M σK σB σT γ ε δ / δ ^ 2 := havg
  have hs : σT * ‖KAM.Iso.extendedTorsionAverage H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))
      (isoNewS H K ωstar E₀ s • ωstar) - KAM.Iso.extendedTorsionAverage H K (s • ωstar)‖ ≤
      1 / 2 := by
    have hm0 : 0 ≤ mSize M σK σB σT := zero_le_one.trans one_le_mSize
    calc _ ≤ mSize M σK σB σT * (CDTbord n M σK σB σT * dStep n τ M σK σB σT γ ε δ / δ ^ 2) :=
          mul_le_mul hmσ hΔ (norm_nonneg _) hm0
      _ ≤ 1 / 2 := by
          have : 2 * mSize M σK σB σT * CDTbord n M σK σB σT *
              dStep n τ M σK σB σT γ ε δ / δ ^ 2 =
              2 * (mSize M σK σB σT * (CDTbord n M σK σB σT *
                dStep n τ M σK σB σT γ ε δ / δ ^ 2)) := by ring
          linarith
  obtain ⟨hu, -, hinv⟩ := neumann_fintype hK.twist.1 hK.twist.2 hs
  rw [add_sub_cancel] at hu hinv
  refine ⟨⟨hdiff, TorsionAux.isoNewtonMap_isPrimaryOnStrip (by linarith) hK.primary hcp,
      TorsionAux.isoNewtonMap_isRealOnReals hr2 hK.real hcr⟩,
    fun θ hθ => (hball θ hθ).1,
    fun θ hθ => ⟨hDK θ hθ, ?_, (hB θ hθ).1, (hB θ hθ).2.1, (hB θ hθ).2.2⟩,
    hcont, havg, hu, ?_⟩
  · have hθr : θ ∈ complexStrip n r := hsub2 (hsub32 hθ)
    have h1 := norm_sub_norm_le (fderiv ℂ (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) θ)
      (fderiv ℂ K θ)
    have h2 := hK.deriv_le θ hθr
    have h3 : σK ≤ mSize M σK σB σT := σK_le_mSize
    linarith [hDK θ hθ, hs1]
  · refine hinv.trans ?_
    have hσ0 : 0 ≤ σT := hP.σT_pos.le
    calc 2 * σT ^ 2 * ‖KAM.Iso.extendedTorsionAverage H
          (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) (isoNewS H K ωstar E₀ s • ωstar) -
          KAM.Iso.extendedTorsionAverage H K (s • ωstar)‖
        ≤ 2 * mSize M σK σB σT ^ 2 * (CDTbord n M σK σB σT * dStep n τ M σK σB σT γ ε δ / δ ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hσ0 hmσ 2) zero_le_two) hΔ
            (norm_nonneg _) (by positivity)
      _ = _ := by ring

end Step

end KAM.Iso.Apost
