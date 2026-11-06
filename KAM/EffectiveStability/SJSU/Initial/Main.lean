/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Initial.Data
public import KAM.EffectiveStability.SJSU.Ham.Center
public import KAM.EffectiveStability.SJSU.Ecc.Data
public import KAM.EffectiveStability.Tube.Initial.Point
public import KAM.EffectiveStability.Tube.Check.Lip

/-!
# The SJSU initial box lies in the tube domain (T2-CONF, package N5c)

The ball hypotheses of the tube checker `KAM.EffectiveStability.Tube.tubeChart_confinement`
(`KAM/EffectiveStability/Tube/Check/TubeChart.lean`) for `V = sjsuV`, `B = sjsuB` (N5a),
`z = sjsuZStar`, `r = 10⁻⁶`, `ρ = 2·10⁻⁶`, `δ = 10⁻⁶`:

* `sjsu_hN`: `Σ_k |V′_kj| ≤ N_V`;
* `sjsu_hAb`, `sjsu_ha`, `sjsu_hab`: mode bounds `|q_j| + |p_j| ≤ A_j`, `0 < a_j ≤ q_j² + p_j²` on
  the
  ball (so every point of the ball has all rotated modes nonzero);
* `sjsu_hβ`: `|∂_{φ_b} B_l| ≤ β_l` for all `φ`;
* `sjsu_hμ`: `|u_j(z*)| ≤ μ = 10⁻⁹` (exact enclosure through rational circle points);
* `sjsu_hμρ`: `μ + chartLip … (e_j) 0 · r < ρ`, so `|u| < ρ` on the ball;
* `sjsu_hLF`: `chartLip … (Fu_j) (Fφ_j) · r ≤ δ/2` for the ceilings `sjsuFuMax`, `sjsuFphiMax` of
  the
  observable partials (to be met by the coefficient norms of the literal observables, through
  `KAM.EffectiveStability.Tube.abs_fderiv_tmEvalPair_u_le` and `…_φ_le`).

Also `sjsuV_eq_eccV` (N5a's `V′` is N6's) and `sjsuZStar_mem_modesPos`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube Matrix

/-! ### The nominal point -/

theorem sjsuZStar_fst (j : Fin 3) : sjsuZStar.1 j = (sjsuEtaQ j : ℝ) := by
  fin_cases j <;> simp [sjsuZStar, sjsuEtaQ] <;> norm_num

theorem sjsuZStar_snd (j : Fin 3) : sjsuZStar.2 j = (sjsuXiQ j : ℝ) := by
  fin_cases j <;> simp [sjsuZStar, sjsuXiQ] <;> norm_num

theorem sjsuV_apply (i j : Fin 3) : sjsuV i j = (sjsuVq i j : ℝ) := by
  simp [sjsuV, sjsuVq]

/-- N5a's rotation `V′` is N6's `sjsuEccV`. -/
theorem sjsuVq_eq_eccV : sjsuVq = sjsuEccV := by
  funext i j; revert i j; decide +kernel

theorem sjsuV_eq_eccV (i j : Fin 3) : sjsuV i j = (sjsuEccV i j : ℝ) := by
  rw [sjsuV_apply, sjsuVq_eq_eccV]

theorem rotMap_sjsuZStar_fst (j : Fin 3) : (rotMap sjsuVᵀ sjsuZStar).1 j = (sjsuQStar j : ℝ) := by
  simp only [rotMap, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply,
    sjsuV_apply, sjsuZStar_fst, sjsuQStar]
  push_cast; ring

theorem rotMap_sjsuZStar_snd (j : Fin 3) : (rotMap sjsuVᵀ sjsuZStar).2 j = (sjsuPStar j : ℝ) := by
  simp only [rotMap, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply,
    sjsuV_apply, sjsuZStar_snd, sjsuPStar]
  push_cast; ring

/-! ### Rational checks (kernel) -/

theorem sjsuNv_ok : ∀ j, |sjsuVq 0 j| + |sjsuVq 1 j| + |sjsuVq 2 j| ≤ sjsuNv := by decide +kernel

theorem sjsuA_ok : ∀ j, |sjsuQStar j| + |sjsuPStar j| + 2 * (sjsuNv * (1 / 10 ^ 6)) ≤ sjsuA j := by
  decide +kernel

theorem sjsua_ok : ∀ j, sjsua j ≤ sjsuQStar j ^ 2 + sjsuPStar j ^ 2 -
    2 * (|sjsuQStar j| + |sjsuPStar j|) * (sjsuNv * (1 / 10 ^ 6)) := by
  decide +kernel

theorem sjsua_pos : ∀ j, 0 < sjsua j := by decide +kernel

theorem sjsuBeta_ok : ∀ l, sjsuEccData.L₁ l ≤ sjsuBeta l ∧ sjsuEccData.L₂ l ≤ sjsuBeta l := by
  decide +kernel

theorem sjsuPt₁_ok : unitOK (pointZeta sjsuQStar sjsuPStar 0) (circPt sjsuPt₁.1 sjsuPt₁.2) sjsuEps =
    true := by
  decide +kernel

theorem sjsuPt₂_ok : unitOK (pointZeta sjsuQStar sjsuPStar 1) (circPt sjsuPt₂.1 sjsuPt₂.2) sjsuEps =
    true := by
  decide +kernel

theorem sjsuMu_ok : ∀ k, pointMu sjsuEccData sjsuQStar sjsuPStar sjsuPt₁.1 sjsuPt₂.1 sjsuPt₁.2
    sjsuPt₂.2 sjsuEps sjsuEps k ≤ sjsuMu := by
  decide +kernel

/-! ### The ball hypotheses of the tube checker -/

/-- `Σ_k |V′_kj| ≤ N_V`. -/
theorem sjsu_hN (j : Fin 3) : ∑ k, |sjsuV k j| ≤ (sjsuNv : ℝ) := by
  rw [Fin.sum_univ_three, sjsuV_apply, sjsuV_apply, sjsuV_apply]
  exact_mod_cast sjsuNv_ok j

/-- `|q_j| + |p_j| ≤ A_j` on the ball `|x - z*|∞ ≤ 10⁻⁶`. -/
theorem sjsu_hAb : ∀ y ∈ Metric.closedBall sjsuZStar (1 / 10 ^ 6), ∀ j,
    |(rotMap sjsuVᵀ y).1 j| + |(rotMap sjsuVᵀ y).2 j| ≤ (sjsuA j : ℝ) := by
  intro y hy j
  refine ((modeBounds_of_mem_closedBall sjsu_hN hy j).1).trans ?_
  rw [rotMap_sjsuZStar_fst, rotMap_sjsuZStar_snd]
  have h : ((|sjsuQStar j| + |sjsuPStar j| + 2 * (sjsuNv * (1 / 10 ^ 6)) : ℚ) : ℝ) ≤
      ((sjsuA j : ℚ) : ℝ) := Rat.cast_le.mpr (sjsuA_ok j)
  push_cast at h
  linarith

/-- `0 < a_j`. -/
theorem sjsu_ha (j : Fin 3) : 0 < (sjsua j : ℝ) := by exact_mod_cast sjsua_pos j

/-- `a_j ≤ q_j² + p_j²` on the ball. -/
theorem sjsu_hab : ∀ y ∈ Metric.closedBall sjsuZStar (1 / 10 ^ 6), ∀ j,
    (sjsua j : ℝ) ≤ modeSq sjsuV y j := by
  intro y hy j
  refine le_trans ?_ ((modeBounds_of_mem_closedBall sjsu_hN hy j).2)
  rw [rotMap_sjsuZStar_fst, rotMap_sjsuZStar_snd]
  have h : ((sjsua j : ℚ) : ℝ) ≤ ((sjsuQStar j ^ 2 + sjsuPStar j ^ 2 -
      2 * (|sjsuQStar j| + |sjsuPStar j|) * (sjsuNv * (1 / 10 ^ 6)) : ℚ) : ℝ) :=
    Rat.cast_le.mpr (sjsua_ok j)
  push_cast at h
  linarith

/-- Every point of the ball has all rotated modes nonzero. -/
theorem sjsu_ball_subset_modesPos :
    ∀ y ∈ Metric.closedBall sjsuZStar (1 / 10 ^ 6), y ∈ modesPos sjsuV :=
  fun y hy j => (sjsu_ha j).trans_le (sjsu_hab y hy j)

theorem sjsuZStar_mem_modesPos : sjsuZStar ∈ modesPos sjsuV :=
  sjsu_ball_subset_modesPos _ (Metric.mem_closedBall_self (by norm_num))

/-- `|∂_{φ_b} B_l| ≤ β_l` for every `φ`. -/
theorem sjsu_hβ (φ : Fin 2 → ℝ) (b : Fin 2) (l : Fin 3) :
    |fderiv ℝ sjsuB φ (Pi.single b 1) l| ≤ (sjsuBeta l : ℝ) := by
  obtain ⟨-, -, hLk⟩ := globalOK_spec sjsuEcc_globalOK
  obtain ⟨hL₁, hL₂, -⟩ := hLk l
  refine (abs_fderiv_tubeCenter_le sjsuEccModes sjsuEccIbar φ b l).trans ?_
  obtain ⟨hb₁, hb₂⟩ := sjsuBeta_ok l
  split_ifs
  · exact_mod_cast hL₁.trans hb₁
  · exact_mod_cast hL₂.trans hb₂

/-- `|u_j(z*)| ≤ μ = 10⁻⁹`. -/
theorem sjsu_hμ (j : Fin 3) : |tubeU sjsuV sjsuB sjsuZStar j| ≤ (sjsuMu : ℝ) := by
  have h := abs_tubeU_le_of_point (d := sjsuEccData) sjsuEcc_globalOK sjsuZStar_mem_modesPos
    rotMap_sjsuZStar_fst rotMap_sjsuZStar_snd sjsuPt₁_ok sjsuPt₂_ok j
  exact h.trans (by exact_mod_cast sjsuMu_ok j)

/-- `μ + chartLip … (e_j) 0 · r < ρ`: `|u| < 2·10⁻⁶` on the ball. -/
theorem sjsu_hμρ (j : Fin 3) :
    (sjsuMu : ℝ) + chartLip (sjsuNv : ℝ) (fun j => (sjsuA j : ℝ)) (fun j => (sjsua j : ℝ))
      (fun l => (sjsuBeta l : ℝ)) (Pi.single j 1) 0 * (1 / 10 ^ 6) < 2 / 10 ^ 6 := by
  fin_cases j <;>
    simp [chartLip, thetaW, Pi.single_apply, sjsuMu, sjsuNv, sjsuA, sjsua, sjsuBeta] <;> norm_num

/-- `chartLip … (Fu_j) (Fφ_j) · r ≤ δ/2` for the ceilings `sjsuFuMax`, `sjsuFphiMax`. -/
theorem sjsu_hLF (j : Fin 3) :
    chartLip (sjsuNv : ℝ) (fun j => (sjsuA j : ℝ)) (fun j => (sjsua j : ℝ))
      (fun l => (sjsuBeta l : ℝ)) (fun l => (sjsuFuMax j l : ℝ)) (fun b => (sjsuFphiMax j b : ℝ)) *
      (1 / 10 ^ 6) ≤ 1 / 10 ^ 6 / 2 := by
  fin_cases j <;>
    simp [chartLip, thetaW, Fin.sum_univ_three, Fin.sum_univ_two, sjsuNv, sjsuA, sjsua, sjsuBeta,
      sjsuFuMax, sjsuFphiMax] <;> norm_num

end KAM.EffectiveStability.SJSU

end
