/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# Planar quartic torsion: jets of analytic remainders (P11C, package T6)

Generic calculus used by `quartic_explicit` (`bpP:p11b:quartic-explicit`, step `qe-an`): an analytic
function whose size near `0` is `O(‖z‖^N)` has vanishing diagonal iterated derivatives of every order
below `N` (`qeJet_diag_eq_zero`), hence `qeJet_iteratedFDeriv_eq_zero`; conversely a vanishing jet of
order `N - 1` gives the bound `O(‖z‖^N)` (`qeJet_isBigO_of_jet_zero`).
-/

@[expose] public noncomputable section
open Set Filter Asymptotics Topology
namespace KAM.Planetary

private theorem qeJet_eq_zero_of_isBigO {j : ℕ} {c : ℝ}
    (h : (fun t : ℝ => t ^ j * c) =O[𝓝 0] fun t : ℝ => t ^ (j + 1)) : c = 0 := by
  obtain ⟨C, hC⟩ := h.bound
  have hev : ∀ᶠ t : ℝ in 𝓝[≠] 0, ‖c‖ ≤ C * |t| := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hC, self_mem_nhdsWithin] with t ht ht0
    have ht0' : t ≠ 0 := ht0
    simp only [norm_mul, norm_pow, Real.norm_eq_abs] at ht
    have hp : 0 < |t| ^ j := pow_pos (abs_pos.2 ht0') j
    rw [pow_succ] at ht
    have : |t| ^ j * ‖c‖ ≤ |t| ^ j * (C * |t|) := by
      rw [Real.norm_eq_abs]; linarith
    exact le_of_mul_le_mul_left this hp
  have hlim : Tendsto (fun t : ℝ => C * |t|) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => C * |t|) (𝓝 0) (𝓝 (C * |0|)) :=
      (continuous_const.mul continuous_abs).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  exact norm_eq_zero.1 (le_antisymm (ge_of_tendsto hlim hev) (norm_nonneg _))

/-- A power series of an `O(‖z‖^N)` function has no diagonal terms of order below `N`. -/
theorem qeJet_diag_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : E → ℝ} {p : FormalMultilinearSeries ℝ E ℝ} (hp : HasFPowerSeriesAt h p 0) {C : ℝ}
    {N : ℕ} (hl : ∀ᶠ z in 𝓝 (0 : E), |h z| ≤ C * ‖z‖ ^ N) :
    ∀ j < N, ∀ w, p j (fun _ => w) = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj w
    have hps : p.partialSum (j + 1) = fun y => p j fun _ => y := by
      funext y
      refine Finset.sum_eq_single_of_mem j (Finset.mem_range.2 (Nat.lt_succ_self j)) ?_
      intro k hk hne
      have hk' := Finset.mem_range.1 hk
      exact ih k (by omega) (by omega) y
    have h1 := hp.isBigO_sub_partialSum_pow (j + 1)
    rw [hps] at h1
    have hc : Continuous fun t : ℝ => t • w := by fun_prop
    have h2 : Tendsto (fun t : ℝ => t • w) (𝓝 0) (𝓝 0) := by simpa using hc.tendsto 0
    have h3 := h1.comp_tendsto h2
    simp only [Function.comp_def, zero_add] at h3
    have h4 : (fun t : ℝ => ‖t • w‖ ^ (j + 1)) =O[𝓝 0] fun t : ℝ => t ^ (j + 1) := by
      refine IsBigO.of_bound (‖w‖ ^ (j + 1)) (Eventually.of_forall fun t => ?_)
      simp only [norm_smul, mul_pow, Real.norm_eq_abs, norm_pow]
      rw [abs_of_nonneg (by positivity), mul_comm]
    have h5 := h3.trans h4
    have h6 : (fun t : ℝ => h (t • w)) =O[𝓝 0] fun t : ℝ => t ^ (j + 1) := by
      have hb : (fun t : ℝ => h (t • w)) =O[𝓝 0] fun t : ℝ => ‖t • w‖ ^ N := by
        refine IsBigO.of_bound C ?_
        filter_upwards [h2.eventually hl] with t ht
        simpa using ht
      refine hb.trans ?_
      have h7 : (fun t : ℝ => ‖t • w‖ ^ N) =O[𝓝 0] fun t : ℝ => t ^ N := by
        refine IsBigO.of_bound (‖w‖ ^ N) (Eventually.of_forall fun t => ?_)
        simp only [norm_smul, mul_pow, Real.norm_eq_abs, norm_pow]
        rw [abs_of_nonneg (by positivity), mul_comm]
      refine h7.trans (IsBigO.of_bound 1 ?_)
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
      have ht' : |t| < 1 := by simpa using ht
      simp only [norm_pow, Real.norm_eq_abs, one_mul]
      exact pow_le_pow_of_le_one (abs_nonneg t) ht'.le (by omega)
    have h8 : (fun t : ℝ => t ^ j * p j (fun _ => w)) =O[𝓝 0] fun t : ℝ => t ^ (j + 1) := by
      refine (h6.sub h5).congr_left fun t => ?_
      have : p j (fun _ => t • w) = t ^ j * p j (fun _ => w) := by
        have := (p j).map_smul_univ (fun _ : Fin j => (t : ℝ)) (fun _ => w)
        simpa [Finset.prod_const, Finset.card_fin] using this
      simp only [sub_sub_cancel, this]
    exact qeJet_eq_zero_of_isBigO h8

/-- An analytic function that is `O(‖z‖^N)` at `0` has vanishing diagonal derivatives below `N`. -/
theorem qeJet_iteratedFDeriv_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : E → ℝ} (hh : AnalyticAt ℝ h 0) {C : ℝ} {N : ℕ}
    (hl : ∀ᶠ z in 𝓝 (0 : E), |h z| ≤ C * ‖z‖ ^ N) {j : ℕ} (hj : j < N) (z : E) :
    iteratedFDeriv ℝ j h 0 (fun _ => z) = 0 := by
  obtain ⟨p, r, hp⟩ := hh
  have h2 := hp.factorial_smul z j
  rw [qeJet_diag_eq_zero hp.hasFPowerSeriesAt hl j hj z] at h2
  simpa using h2.symm

/-- Conversely, an analytic function with vanishing diagonal jet below `N` is `O(‖z‖^N)`. -/
theorem qeJet_isBigO_of_jet_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : E → ℝ} (hh : AnalyticAt ℝ h 0) {N : ℕ}
    (hj : ∀ j < N, ∀ z : E, iteratedFDeriv ℝ j h 0 (fun _ => z) = 0) :
    ∃ C : ℝ, ∀ᶠ z in 𝓝 (0 : E), |h z| ≤ C * ‖z‖ ^ N := by
  obtain ⟨p, r, hp⟩ := hh
  have hps : ∀ z, p.partialSum N z = 0 := by
    intro z
    simp only [FormalMultilinearSeries.partialSum]
    refine Finset.sum_eq_zero fun k hk => ?_
    have h2 := hp.factorial_smul z k
    rw [hj k (Finset.mem_range.1 hk) z] at h2
    exact (smul_eq_zero.1 h2).resolve_left (Nat.factorial_ne_zero k)
  have h1 := hp.hasFPowerSeriesAt.isBigO_sub_partialSum_pow N
  obtain ⟨C, hC⟩ := h1.bound
  refine ⟨C, ?_⟩
  filter_upwards [hC] with z hz
  have h0 : h (0 + z) = h z := by rw [zero_add]
  simp only [zero_add, hps, sub_zero, norm_pow, Real.norm_eq_abs] at hz
  simpa using hz

end KAM.Planetary

end
