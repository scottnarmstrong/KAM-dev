/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.ChartLift.Stopped
public import KAM.Planetary.StrongAMD.Threshold.Pair

/-!
# Star-dominated thresholds and the data of LP-LIFT

Design `docs/campaign/design/HD11964-PILOT.md` §5, generic in the number of planets.

When planet `k` has the smallest action and every adjacent pair threshold is at least `I_k`, the
strong threshold is the star threshold `B(I) = I_k`; no contact problem has to be solved. A pair
threshold is bounded below without solving the contact problem: every feasible `(u, v)` of the pair
`(i, j)` has `v ≥ v₀` once `2 a_i ≤ a_j (1 - v₀)`, and then the objective is at least
`I_j D(v₀) ≥ I_j (1 - s)` for any `s ≥ 0` with `s² ≥ 1 - v₀²`.

`pairThreshold` is the `sInf` of the objective over the feasible set; the lower bound goes through
the attained minimum `pairThreshold_isLeast` (whose proof uses `pairFeasible_nonempty`, the point
`(1, 1)`), so the convention `sInf ∅ = 0` never enters.

## Main results

* `pairThreshold_ge_of_axis`: the monotone lower bound of a pair threshold.
* `strongThreshold_eq_of_le`: `B(I) = I_k` for a star-dominated `I`.
* `strongThresholdModulus_le_of_eq`: then `Ω_B(r) ≤ r`.
* `mem_Icc_of_norm_sub_le`: the `r`-ball of a point of a box lies in the box enlarged by `r`.
* `liftData_of_star`: LP-LIFT's `LiftData` from rational-checkable inequalities, when `B = I_k` on
  `U`.
-/

@[expose] public noncomputable section

open Set KAM KAM.Planetary KAM.Planetary.StrongAMD

namespace KAM.Application.LambdaDrift

variable {n : ℕ}

/-- **Monotone lower bound of a pair threshold** (design §5, `pairThreshold_ge`). If
`2 a_i ≤ a_j (1 - v₀)` with `a_j > 0` and `0 ≤ v₀`, every feasible `(u, v)` has `v ≥ v₀`; with
`s ≥ 0`, `s² ≥ 1 - v₀²`, the pair threshold is at least `I_j (1 - s)`. -/
theorem pairThreshold_ge_of_axis {ν I : Fin n → ℝ} {i j : Fin n} (hIi : 0 ≤ I i) (hIj : 0 ≤ I j)
    (haj : 0 < actionAxis ν I j) {v₀ s : ℝ} (hv₀ : 0 ≤ v₀)
    (hax : 2 * actionAxis ν I i ≤ actionAxis ν I j * (1 - v₀)) (hs : 0 ≤ s)
    (hs2 : 1 - v₀ ^ 2 ≤ s ^ 2) :
    I j * (1 - s) ≤ pairThreshold ν I i j := by
  obtain ⟨⟨uv, ⟨hu, hv, hfeas⟩, heq⟩, -⟩ := pairThreshold_isLeast ν I i j
  rw [← heq]
  have hai : 0 ≤ actionAxis ν I i := sq_nonneg _
  have hvv : v₀ ≤ uv.2 := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : actionAxis ν I j * (1 - v₀) < actionAxis ν I j * (1 - uv.2) :=
      mul_lt_mul_of_pos_left (by linarith) haj
    have h2 : actionAxis ν I i * (1 + uv.1) ≤ 2 * actionAxis ν I i := by nlinarith [hu.2]
    linarith
  have hD : eccDeficit v₀ ≤ eccDeficit uv.2 := eccDeficit_mono hv₀ hvv hv.2
  have hsq : Real.sqrt (1 - v₀ ^ 2) ≤ s := by
    calc Real.sqrt (1 - v₀ ^ 2) ≤ Real.sqrt (s ^ 2) := Real.sqrt_le_sqrt hs2
      _ = s := Real.sqrt_sq hs
  have hD0 : 1 - s ≤ eccDeficit v₀ := by unfold eccDeficit; linarith
  have hui : 0 ≤ I i * eccDeficit uv.1 := mul_nonneg hIi (eccDeficit_nonneg hu)
  have hvj : I j * (1 - s) ≤ I j * eccDeficit uv.2 :=
    mul_le_mul_of_nonneg_left (hD0.trans hD) hIj
  show I j * (1 - s) ≤ I i * eccDeficit uv.1 + I j * eccDeficit uv.2
  linarith

/-- **Star-dominated threshold** (design §5): if `I_k ≤ I_i` for every `i` and every adjacent pair
threshold is at least `I_k`, then `B(I) = I_k`. -/
theorem strongThreshold_eq_of_le {ν I : Fin n → ℝ} (hn : 2 ≤ n) {k : Fin n}
    (hk : ∀ i, I k ≤ I i) (hpair : ∀ a : AdjIdx n, I k ≤ pairThreshold ν I a.1 a.upperIdx) :
    strongThreshold ν I = I k := by
  have : Nonempty (AdjIdx n) := ⟨⟨⟨0, by omega⟩, by show 0 + 1 < n; omega⟩⟩
  have : Nonempty (Fin n) := ⟨k⟩
  have hstar : starThreshold I = I k :=
    le_antisymm (ciInf_le (Finite.bddBelow_range _) k) (le_ciInf hk)
  have hcross : I k ≤ crossThreshold ν I := le_ciInf hpair
  unfold strongThreshold
  rw [hstar]
  exact min_eq_right hcross

/-- If `B(I) = I_k` on `U`, the threshold modulus is at most the radius: `Ω_B(r) ≤ r`. -/
theorem strongThresholdModulus_le_of_eq {ν : Fin n → ℝ} {U : Set (Fin n → ℝ)} {k : Fin n}
    (hU : ∀ I ∈ U, strongThreshold ν I = I k) {r : ℝ} (hr : 0 ≤ r) :
    strongThresholdModulus ν U r ≤ r := by
  unfold strongThresholdModulus
  refine Real.sSup_le (fun x hx => ?_) hr
  obtain ⟨I, hI, J, hJ, hIJ, rfl⟩ := hx
  rw [hU I hI, hU J hJ]
  have := norm_le_pi_norm (I - J) k
  rw [Real.norm_eq_abs, Pi.sub_apply] at this
  exact this.trans hIJ

/-- The closed `r`-ball (sup norm) of a point of the box `[a, b]` lies in `[a - r, b + r]`. -/
theorem mem_Icc_of_norm_sub_le {a b Λ : Fin n → ℝ} (hΛ : Λ ∈ Icc a b) {r : ℝ} {I : Fin n → ℝ}
    (hI : ‖I - Λ‖ ≤ r) : I ∈ Icc (fun i => a i - r) (fun i => b i + r) := by
  have h : ∀ i, |I i - Λ i| ≤ r := fun i => by
    have h1 := norm_le_pi_norm (I - Λ) i
    rw [Real.norm_eq_abs, Pi.sub_apply] at h1
    exact h1.trans hI
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h2 := abs_le.1 (h i)
    have h3 : a i ≤ Λ i := hΛ.1 i
    show a i - r ≤ I i
    linarith [h2.1]
  · have h2 := abs_le.1 (h i)
    have h4 : Λ i ≤ b i := hΛ.2 i
    show I i ≤ b i + r
    linarith [h2.2]

/-- **The data of LP-LIFT for a star-dominated system** (design §5). If `B = I_k` on the compact
`U ⊆ 𝒬`, `(n + 1) r ≤ δ / 4`, the closed `r`-action ball of the physical state `z₀` lies in `U`,
`C(z₀) ≤ Λ_k(z₀) - δ` and `L(z₀) > 0`, then `LiftData ν U z₀ δ r` holds. -/
theorem liftData_of_star {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {U : Set (Fin n → ℝ)} (hUc : IsCompact U) (hUch : U ⊆ chamber ν) {k : Fin n}
    (hU : ∀ I ∈ U, strongThreshold ν I = I k) {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r)
    (hbud : (n + 1) * r ≤ δ / 4) {z₀ : Phase (n * 2)} (hphys : IsPhysicalState ν z₀)
    (hball : ∀ I, ‖I - actionVector ν z₀‖ ≤ r → I ∈ U)
    (hC : strongAMD ν z₀ ≤ keplerAction ν z₀ k - δ) (hL : 0 < totalMomentum z₀) :
    LiftData ν U z₀ δ r where
  pos_mass := hν
  two_le := hn
  compact := hUc
  subset_chamber := hUch
  delta_pos := hδ
  r_pos := hr
  budget := by
    have h1 := strongThresholdModulus_le_of_eq hU hr.le
    have h2 : ((n : ℝ) + 1) * r = n * r + r := by ring
    linarith
  physical := hphys
  ball := hball
  amd := by
    rw [hU _ (hball _ (by simpa using hr.le))]
    exact hC
  orient := hL

end KAM.Application.LambdaDrift

end
