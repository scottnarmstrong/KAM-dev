/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.Phase
public import KAM.Wave.Homological.LemmaOneAll
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The symplectic form (blueprint-W `bpW:w5:omega`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

On the carrier `KamPhase` (normal parts by their representatives at the weights `q`, `q'` of the
two arguments)
`ϖ_{q,q'}(W,W') = 2π(⟨Θ,Y'⟩ - ⟨Y,Θ'⟩) + ⟨U,V'⟩₀ - ⟨V,U'⟩₀`, where for representatives
`⟨c,z⟩₀ = ∑ ĉ_j ẑ_j/(ω_{a,q}(j+2) ω_{a,q'}(j+2))` (`stepPairCLM`, bounded by `‖ĉ‖‖ẑ‖` when
`a ≥ 0`, `q + q' ≥ 0`, `bpW:w4:pairing`).

* `norm_stepSymp_le`: `|ϖ(W,W')| ≤ (4π + 1) r² |W|_r |W'|_r` (the blueprint's `(4π+2)r²` is
  weaker);
* `stepSymp_antisymm`, `stepSymp_nondeg`: antisymmetry and nondegeneracy for `q = q'`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

/-- `1/(ω_{a,q}(j+2) ω_{a,q'}(j+2))` as a bounded sequence. -/
def stepWinv (a q q' : ℝ) (j : ℕ+) : ℂ := (((homWt a q j) * (homWt a q' j))⁻¹ : ℝ)

theorem norm_stepWinv_le {a q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') (j : ℕ+) :
    ‖stepWinv a q q' j‖ ≤ 1 := by
  unfold stepWinv
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h1 := one_le_homWt_mul ha hqq' j
  have h0 : 0 < homWt a q j * homWt a q' j := lt_of_lt_of_le one_pos h1
  rw [abs_of_pos (inv_pos.mpr h0)]
  exact inv_le_one_of_one_le₀ h1

/-- The pairing of a representative at `q` with a representative at `q'`. -/
def stepPairCLM {a q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') : HomL2 →L[ℂ] HomL2 →L[ℂ] ℂ :=
  homPairL2.comp (weightedDiagCLM (stepWinv a q q') (norm_stepWinv_le ha hqq'))

theorem norm_stepPairCLM_apply_le {a q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') (c z : HomL2) :
    ‖stepPairCLM ha hqq' c z‖ ≤ ‖c‖ * ‖z‖ := by
  show ‖homPairF (weightedDiagCLM (stepWinv a q q') (norm_stepWinv_le ha hqq') c) z‖ ≤ _
  refine (norm_homPairF_le _ _).trans ?_
  rw [one_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact ((weightedDiagCLM (stepWinv a q q') (norm_stepWinv_le ha hqq')).le_opNorm c).trans
    (mul_le_of_le_one_left (norm_nonneg c) (norm_diagCLM_le _ (norm_stepWinv_le ha hqq')))

theorem stepPairCLM_comm {a q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') (hq : q = q') (c z : HomL2) :
    stepPairCLM ha hqq' c z = stepPairCLM ha hqq' z c := by
  subst hq
  show homPairF _ z = homPairF _ c
  unfold homPairF
  exact tsum_congr fun j => by simp [weightedDiagCLM_apply]; ring

/-- The symplectic form `ϖ_{q,q'}` of `bpW:w5:setting`. -/
def stepSymp {a q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') (W W' : KamPhase) : ℂ :=
  2 * Real.pi * ((∑ i, W.1 i * W'.2.1 i) - ∑ i, W.2.1 i * W'.1 i)
    + stepPairCLM ha hqq' W.2.2.1 W'.2.2.2 - stepPairCLM ha hqq' W.2.2.2 W'.2.2.1

theorem norm_sum_two_le (b y : Fin 2 → ℂ) : ‖∑ i, b i * y i‖ ≤ 2 * (‖b‖ * ‖y‖) := by
  rw [Fin.sum_univ_two]
  have h0 := norm_le_pi_norm b 0
  have h1 := norm_le_pi_norm b 1
  have g0 := norm_le_pi_norm y 0
  have g1 := norm_le_pi_norm y 1
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  nlinarith [mul_le_mul h0 g0 (norm_nonneg _) (norm_nonneg _),
    mul_le_mul h1 g1 (norm_nonneg _) (norm_nonneg _)]

theorem stepSymp_arith {c r α β γ δ α' β' γ' δ' : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hα' : 0 ≤ α') (hβ' : 0 ≤ β') (hγ' : 0 ≤ γ')
    (hδ' : 0 ≤ δ') :
    c * (2 * (α * (r ^ 2 * β')) + 2 * (α' * (r ^ 2 * β))) + r ^ 2 * (γ * δ' + δ * γ') ≤
      (2 * c + 1) * r ^ 2 * ((α + β + γ + δ) * (α' + β' + γ' + δ')) := by
  have hr2 : 0 ≤ r ^ 2 := by positivity
  have hP : (α * β' + α' * β) + (γ * δ' + δ * γ') ≤ (α + β + γ + δ) * (α' + β' + γ' + δ') := by
    nlinarith [mul_nonneg hα hα', mul_nonneg hα hγ', mul_nonneg hα hδ', mul_nonneg hβ hα',
      mul_nonneg hβ hβ', mul_nonneg hβ hγ', mul_nonneg hβ hδ', mul_nonneg hγ hα', mul_nonneg hγ hβ',
      mul_nonneg hγ hγ', mul_nonneg hδ hα', mul_nonneg hδ hβ', mul_nonneg hδ hδ']
  have hS1 : 0 ≤ α * β' + α' * β := by positivity
  have hS2 : 0 ≤ γ * δ' + δ * γ' := by positivity
  have e1 : c * (2 * (α * (r ^ 2 * β')) + 2 * (α' * (r ^ 2 * β))) + r ^ 2 * (γ * δ' + δ * γ') =
      2 * c * r ^ 2 * (α * β' + α' * β) + r ^ 2 * (γ * δ' + δ * γ') := by ring
  have e2 : (2 * c + 1) * r ^ 2 * (α * β' + α' * β + (γ * δ' + δ * γ')) =
      2 * c * r ^ 2 * (α * β' + α' * β) + r ^ 2 * (γ * δ' + δ * γ') +
        (2 * c * r ^ 2 * (γ * δ' + δ * γ') + r ^ 2 * (α * β' + α' * β)) := by ring
  have e3 : 0 ≤ 2 * c * r ^ 2 * (γ * δ' + δ * γ') + r ^ 2 * (α * β' + α' * β) := by positivity
  have h4 := mul_le_mul_of_nonneg_left hP (by positivity : 0 ≤ (2 * c + 1) * r ^ 2)
  rw [e1]
  have : 2 * c * r ^ 2 * (α * β' + α' * β) + r ^ 2 * (γ * δ' + δ * γ') ≤
      (2 * c + 1) * r ^ 2 * (α * β' + α' * β + (γ * δ' + δ * γ')) := by rw [e2]; linarith
  exact this.trans h4

/-- **`bpW:w5:omega`, bound**: `|ϖ(W,W')| ≤ (4π+1) r² |W|_r |W'|_r`. -/
theorem norm_stepSymp_le {a q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') {r : ℝ} (hr : 0 < r)
    (W W' : KamPhase) :
    ‖stepSymp ha hqq' W W'‖ ≤ (4 * Real.pi + 1) * r ^ 2 * (kamNorm r W * kamNorm r W') := by
  unfold stepSymp kamNorm
  set α := ‖W.1‖; set β := ‖W.2.1‖ / r ^ 2; set γ := ‖W.2.2.1‖ / r; set δ := ‖W.2.2.2‖ / r
  set α' := ‖W'.1‖; set β' := ‖W'.2.1‖ / r ^ 2; set γ' := ‖W'.2.2.1‖ / r
  set δ' := ‖W'.2.2.2‖ / r
  have hα : 0 ≤ α := norm_nonneg _
  have hα' : 0 ≤ α' := norm_nonneg _
  have hβ : 0 ≤ β := by positivity
  have hβ' : 0 ≤ β' := by positivity
  have hγ : 0 ≤ γ := by positivity
  have hγ' : 0 ≤ γ' := by positivity
  have hδ : 0 ≤ δ := by positivity
  have hδ' : 0 ≤ δ' := by positivity
  have e1 := norm_sum_two_le W.1 W'.2.1
  have e2 := norm_sum_two_le W.2.1 W'.1
  have e3 := norm_stepPairCLM_apply_le ha hqq' W.2.2.1 W'.2.2.2
  have e4 := norm_stepPairCLM_apply_le ha hqq' W.2.2.2 W'.2.2.1
  have hY' : ‖W'.2.1‖ = r ^ 2 * β' := by simp only [β']; field_simp
  have hY : ‖W.2.1‖ = r ^ 2 * β := by simp only [β]; field_simp
  have hU : ‖W.2.2.1‖ = r * γ := by simp only [γ]; field_simp
  have hV : ‖W.2.2.2‖ = r * δ := by simp only [δ]; field_simp
  have hU' : ‖W'.2.2.1‖ = r * γ' := by simp only [γ']; field_simp
  have hV' : ‖W'.2.2.2‖ = r * δ' := by simp only [δ']; field_simp
  have hπ := Real.pi_pos
  have n1 : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by simp [abs_of_pos hπ]
  have t1 : ‖(∑ i, W.1 i * W'.2.1 i) - ∑ i, W.2.1 i * W'.1 i‖ ≤
      2 * (α * (r ^ 2 * β')) + 2 * (α' * (r ^ 2 * β)) := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [hY'] at e1; exact e1
    · have := e2; rw [hY] at this; nlinarith [this]
  have t2 : ‖(2 * Real.pi : ℂ) * ((∑ i, W.1 i * W'.2.1 i) - ∑ i, W.2.1 i * W'.1 i)‖ ≤
      2 * Real.pi * (2 * (α * (r ^ 2 * β')) + 2 * (α' * (r ^ 2 * β))) := by
    rw [norm_mul, n1]; exact mul_le_mul_of_nonneg_left t1 (by positivity)
  have t3 : ‖stepPairCLM ha hqq' W.2.2.1 W'.2.2.2 - stepPairCLM ha hqq' W.2.2.2 W'.2.2.1‖ ≤
      r ^ 2 * (γ * δ' + δ * γ') := by
    refine (norm_sub_le _ _).trans ?_
    rw [hU, hV'] at e3; rw [hV, hU'] at e4
    nlinarith [e3, e4]
  have : ‖2 * (Real.pi : ℂ) * ((∑ i, W.1 i * W'.2.1 i) - ∑ i, W.2.1 i * W'.1 i)
      + stepPairCLM ha hqq' W.2.2.1 W'.2.2.2 - stepPairCLM ha hqq' W.2.2.2 W'.2.2.1‖ ≤
      2 * Real.pi * (2 * (α * (r ^ 2 * β')) + 2 * (α' * (r ^ 2 * β))) +
        r ^ 2 * (γ * δ' + δ * γ') := by
    rw [add_sub_assoc]
    exact (norm_add_le _ _).trans (add_le_add (by simpa using t2) t3)
  refine this.trans ?_
  have := stepSymp_arith (c := 2 * Real.pi) (by positivity) hr.le hα hβ hγ hδ hα' hβ' hγ' hδ'
  refine this.trans (le_of_eq ?_)
  ring


/-- **Antisymmetry** of `ϖ` (`bpW:w5:omega`). -/
theorem stepSymp_antisymm {a q : ℝ} (ha : 0 ≤ a) (hqq : 0 ≤ q + q) (W W' : KamPhase) :
    stepSymp (q := q) (q' := q) ha hqq W W' = -stepSymp (q := q) (q' := q) ha hqq W' W := by
  unfold stepSymp
  rw [stepPairCLM_comm ha hqq rfl W'.2.2.1 W.2.2.2, stepPairCLM_comm ha hqq rfl W'.2.2.2 W.2.2.1]
  have e1 : ∑ x, W'.2.1 x * W.1 x = ∑ x, W.1 x * W'.2.1 x :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have e2 : ∑ x, W'.1 x * W.2.1 x = ∑ x, W.2.1 x * W'.1 x :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [e1, e2]
  ring

theorem stepPairCLM_basis {a q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') (c : HomL2) (j : ℕ+) :
    stepPairCLM ha hqq' c (kamBasis ℂ j) = stepWinv a q q' j * c j := by
  show homPairF (weightedDiagCLM (stepWinv a q q') (norm_stepWinv_le ha hqq') c) (kamBasis ℂ j) = _
  have := homPairL2_single_right (weightedDiagCLM (stepWinv a q q') (norm_stepWinv_le ha hqq') c) j
  exact this

theorem stepWinv_ne_zero (a q q' : ℝ) (j : ℕ+) : stepWinv a q q' j ≠ 0 := by
  unfold stepWinv
  have := homWt_pos a q j
  have := homWt_pos a q' j
  exact_mod_cast (inv_pos.mpr (by positivity)).ne'

theorem stepSymp_sub_left {a q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') (W₁ W₂ W : KamPhase) :
    stepSymp ha hqq' (W₁ - W₂) W = stepSymp ha hqq' W₁ W - stepSymp ha hqq' W₂ W := by
  unfold stepSymp
  simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib,
    map_sub, sub_apply]
  ring

/-- **Nondegeneracy** of `ϖ_{q,q'}` (`bpW:w5:omega`): a vector of `𝒫^q` pairing to zero with all of
`𝒫^{q'}` vanishes. -/
theorem stepSymp_nondeg {a q q' : ℝ} (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') {W : KamPhase}
    (h : ∀ W', stepSymp (q := q) (q' := q') ha hqq' W W' = 0) : W = 0 := by
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_) (Prod.ext ?_ ?_))
  · have := h (0, Pi.single i 1, 0, 0)
    simp [stepSymp, Pi.single_apply] at this
    simpa using this
  · have := h (Pi.single i 1, 0, 0, 0)
    simp [stepSymp, Pi.single_apply] at this
    simpa using this
  · refine lp.ext (funext fun j => ?_)
    have := h (0, 0, 0, kamBasis ℂ j)
    simp only [stepSymp, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, mul_zero,
        Finset.sum_const_zero,
      sub_self, map_zero, ContinuousLinearMap.zero_apply, sub_zero, zero_add] at this
    rw [stepPairCLM_basis] at this
    have h2 := (mul_eq_zero.mp this).resolve_left (stepWinv_ne_zero a q q' j)
    simpa using h2
  · refine lp.ext (funext fun j => ?_)
    have := h (0, 0, kamBasis ℂ j, 0)
    simp only [stepSymp, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, mul_zero,
        Finset.sum_const_zero,
      sub_self, map_zero, ContinuousLinearMap.zero_apply, zero_sub, zero_add, sub_zero] at this
    rw [stepPairCLM_basis] at this
    have h2 := (mul_eq_zero.mp (neg_eq_zero.mp this)).resolve_left (stepWinv_ne_zero a q q' j)
    simpa using h2

end KAM.Wave
