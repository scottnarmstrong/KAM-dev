/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.OrbitJet.Analytic
public import KAM.Planetary.Nondegeneracy.DiagonalTensor

/-!
# Planar quartic torsion: jets from one-dimensional expansions

For two functions analytic at `0` on `Fin 2 → ℝ` with values in `ℂ`, equality of the iterated
derivatives of order at most four at `0` follows from the one-variable estimates
`f (t • w) - g (t • w) = O(t⁵)` along every line (`jetEq_of_line_isBigO`).  The proof compares the
diagonal terms of the power series (strong induction on the order), and then polarizes using the
symmetry of the iterated derivative of an analytic function.
-/

@[expose] public noncomputable section

open Filter Asymptotics Topology
open scoped ContDiff

namespace KAM.Planetary.OrbitJet

private theorem pow_isBigO_pow {j : ℕ} (hj : j ≤ 5) :
    (fun t : ℝ => t ^ 5) =O[𝓝 0] fun t : ℝ => t ^ j := by
  refine IsBigO.of_bound 1 ?_
  have : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
    simpa using ht
  filter_upwards [this] with t ht
  simp only [norm_pow, Real.norm_eq_abs, one_mul]
  exact pow_le_pow_of_le_one (abs_nonneg t) ht.le hj

/-- If `t^j * c = O(t^(j+1))` then `c = 0`. -/
private theorem eq_zero_of_isBigO {j : ℕ} {c : ℂ}
    (h : (fun t : ℝ => (t : ℂ) ^ j * c) =O[𝓝 0] fun t : ℝ => t ^ (j + 1)) : c = 0 := by
  obtain ⟨C, hC⟩ := h.bound
  have hev : ∀ᶠ t : ℝ in 𝓝[≠] 0, ‖c‖ ≤ C * |t| := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hC, self_mem_nhdsWithin] with t ht ht0
    have ht0' : t ≠ 0 := ht0
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] at ht
    have hp : 0 < |t| ^ j := pow_pos (abs_pos.2 ht0') j
    rw [pow_succ] at ht
    have : |t| ^ j * ‖c‖ ≤ |t| ^ j * (C * |t|) := by nlinarith
    exact le_of_mul_le_mul_left this hp
  have hlim : Tendsto (fun t : ℝ => C * |t|) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => C * |t|) (𝓝 0) (𝓝 (C * |0|)) :=
      (continuous_const.mul continuous_abs).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  exact norm_eq_zero.1 (le_antisymm (ge_of_tendsto hlim hev) (norm_nonneg _))

/-- The diagonal terms of a power series that is `O(t⁵)` along every line vanish up to order `4`. -/
private theorem diag_eq_zero {h : (Fin 2 → ℝ) → ℂ} {p : FormalMultilinearSeries ℝ (Fin 2 → ℝ) ℂ}
    (hp : HasFPowerSeriesAt h p 0)
    (hl : ∀ w : Fin 2 → ℝ, (fun t : ℝ => h (t • w)) =O[𝓝 0] fun t : ℝ => t ^ 5) :
    ∀ j ≤ 4, ∀ w, p j (fun _ => w) = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj w
    have hlow : ∀ k ∈ Finset.range (j + 1), k ≠ j → ∀ y, p k (fun _ => y) = 0 :=
      fun k hk hne y => by
        have hk' := Finset.mem_range.1 hk
        exact ih k (by omega) (by omega) y
    have hps : p.partialSum (j + 1) = fun y => p j fun _ => y := by
      funext y
      refine Finset.sum_eq_single_of_mem j (Finset.mem_range.2 (Nat.lt_succ_self j)) ?_
      intro k hk hne
      exact hlow k hk hne y
    have h1 := hp.isBigO_sub_partialSum_pow (j + 1)
    rw [hps] at h1
    have h2 : Tendsto (fun t : ℝ => t • w) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun t : ℝ => t • w := by fun_prop
      simpa using hc.tendsto 0
    have h3 := h1.comp_tendsto h2
    simp only [Function.comp_def, zero_add] at h3
    have h4 : (fun t : ℝ => ‖t • w‖ ^ (j + 1)) =O[𝓝 0] fun t : ℝ => t ^ (j + 1) := by
      refine IsBigO.of_bound (‖w‖ ^ (j + 1)) (Eventually.of_forall fun t => ?_)
      simp only [norm_smul, mul_pow, Real.norm_eq_abs, norm_pow]
      rw [abs_of_nonneg (by positivity), mul_comm]
    have h5 := (h3.trans h4)
    have h6 : (fun t : ℝ => h (t • w)) =O[𝓝 0] fun t : ℝ => t ^ (j + 1) :=
      (hl w).trans (pow_isBigO_pow (by omega))
    have h8 : (fun t : ℝ => (t : ℂ) ^ j * p j (fun _ => w)) =O[𝓝 0] fun t : ℝ => t ^ (j + 1) := by
      refine (h6.sub h5).congr_left fun t => ?_
      have : p j (fun _ => t • w) = (t : ℂ) ^ j * p j (fun _ => w) := by
        have := (p j).map_smul_univ (fun _ : Fin j => (t : ℝ)) (fun _ => w)
        simpa [Finset.prod_const, Finset.card_fin, Complex.real_smul] using this
      simp only [sub_sub_cancel, this]
    exact eq_zero_of_isBigO h8

/-- Analytic functions on `Fin 2 → ℝ` whose difference is `O(t⁵)` along every line have equal
jets of order at most four at `0`. -/
theorem jetEq_of_line_isBigO {f g : (Fin 2 → ℝ) → ℂ} (hf : AnalyticAt ℝ f 0)
    (hg : AnalyticAt ℝ g 0)
    (h : ∀ w : Fin 2 → ℝ, (fun t : ℝ => f (t • w) - g (t • w)) =O[𝓝 0] fun t : ℝ => t ^ 5) :
    p11c_JetEq 4 f g := by
  intro j hj
  obtain ⟨pf, hpf⟩ := hf
  obtain ⟨pg, hpg⟩ := hg
  have hd : HasFPowerSeriesAt (f - g) (pf - pg) 0 := hpf.sub hpg
  have hdiag := diag_eq_zero hd (fun w => by simpa using h w)
  obtain ⟨rf, hrf⟩ := hpf
  obtain ⟨rg, hrg⟩ := hpg
  have hsame : ∀ w, iteratedFDeriv ℝ j f 0 (fun _ => w) = iteratedFDeriv ℝ j g 0 (fun _ => w) := by
    intro w
    rw [← hrf.factorial_smul w j, ← hrg.factorial_smul w j]
    have := hdiag j hj w
    simp only [FormalMultilinearSeries.sub_apply, sub_apply] at this
    rw [sub_eq_zero.1 this]
  have hfa : ContDiffAt ℝ ω f 0 := hrf.hasFPowerSeriesAt.analyticAt.contDiffAt
  have hga : ContDiffAt ℝ ω g 0 := hrg.hasFPowerSeriesAt.analyticAt.contDiffAt
  set T : (Fin 2 → ℝ) [×j]→L[ℝ] ℂ := iteratedFDeriv ℝ j f 0 - iteratedFDeriv ℝ j g 0 with hT
  have hsym : ∀ (σ : Equiv.Perm (Fin j)) (v : Fin j → Fin 2 → ℝ), T (v ∘ σ) = T v := by
    intro σ v
    simp only [hT, sub_apply]
    rw [hfa.iteratedFDeriv_comp_perm, hga.iteratedFDeriv_comp_perm]
  have key : ∀ L : ℂ →L[ℝ] ℝ, L.compContinuousMultilinearMap T = 0 := by
    intro L
    rw [Nondegeneracy.f_pol _ (fun σ v => by simp [hsym σ v])]
    intro v
    simp [hT, hsame v]
  have hT0 : T = 0 := by
    ext m
    refine Complex.ext ?_ ?_
    · simpa using congrArg (fun A => A m) (key Complex.reCLM)
    · simpa using congrArg (fun A => A m) (key Complex.imCLM)
  exact sub_eq_zero.1 hT0

end KAM.Planetary.OrbitJet

end
