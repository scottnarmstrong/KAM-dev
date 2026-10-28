/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.SelectionRecord
public import KAM.Planetary.WeakKAM.SelectionTests
public import KAM.Planetary.WeakKAM.Iteration
public import KAM.Planetary.WeakKAM.ContinuousSeries
public import KAM.Planetary.WeakMeasure.Bridge

/-! # P11B parameter selection (`bpP:p11a:parameter-selection`)

`parameter_selection` builds `SelectionOutput d f (adm_params d ε)` from the iteration of the
inductive lemma: one cutoff family `χ_j` (`ps-iter`), the frequency and energy series on
`K_∞ = ⋂ K_j` by `continuous_series_on_compact` (`ps-lim`, applied twice), the compact nested finite
tests `H_ν` with `meas H_∞ ≥ meas K - loss` by continuity from above (`ps-H`), and the
Diophantine conclusion on `H_∞` only, by `limit_bridge` and the one-tail estimate (`ps-dio`).
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

theorem norm_selectionRe_le (x : SelectionC n) : ‖selectionRe x‖ ≤ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i => ?_
  exact (Complex.abs_re_le_norm (x i)).trans (norm_le_pi_norm x i)

theorem selectionVarpi_le_half (n μ : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    selectionVarpi n μ τ ≤ 1 / 2 := by
  have hE : 1 ≤ selectionExponent n μ τ := by
    unfold selectionExponent
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have : (0 : ℝ) ≤ μ := Nat.cast_nonneg μ
    nlinarith
  unfold selectionVarpi
  calc (2 : ℝ) ^ (-2 * selectionExponent n μ τ) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

theorem selectionReal_mem_collar {K : Set (SelectionR n)} {t : ℝ} (ht : 0 < t) {b : SelectionR n}
    (hb : b ∈ K) : selectionReal b ∈ actionNbhd K t :=
  ⟨b, hb, by
    rw [show selectionReal b - (fun i => (b i : ℂ)) = 0 from sub_self _, norm_zero]
    exact ht⟩

theorem selectionModeLength_pos {k : Fin n → ℤ} (hk : k ≠ 0) : 0 < selectionModeLength k := by
  refine lt_of_le_of_ne (Finset.sum_nonneg fun i _ => abs_nonneg _) fun h => hk ?_
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => abs_nonneg ((k i : ℤ) : ℝ)).1 h.symm i
    (Finset.mem_univ i)
  simpa using this

section Limit
variable {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {a : SelectionSchedule n}

theorem selection_Kinf_subset {o : SelectionIteration d f a} (j : ℕ) :
    (⋂ i, o.K i) ⊆ o.K j := iInter_subset _ j

/-- `ps-lim`: the frequency and energy series converge uniformly on `K_∞`, with continuous sums
and the one-tail estimates, by `continuous_series_on_compact` applied twice. -/
theorem selection_limit_series (cx : WeakBudgetCtx d a) (o : SelectionIteration d f a) :
    ∃ ωstar : SelectionR n → SelectionR n, ∃ hstar : SelectionR n → ℝ,
      (∀ b ∈ ⋂ j, o.K j, Summable (fun j => selectionRe (o.Δω j (selectionReal b)))) ∧
      (∀ b ∈ ⋂ j, o.K j, Summable (fun j => (o.Δh j (selectionReal b)).re)) ∧
      TendstoUniformlyOn
        (fun ν b => selectionRe (selectionFrequency d o.toSelectionChain ν (selectionReal b)))
        ωstar atTop (⋂ j, o.K j) ∧
      TendstoUniformlyOn
        (fun ν b => (selectionEnergy o.toSelectionChain ν (selectionReal b)).re)
        hstar atTop (⋂ j, o.K j) ∧
      (∀ b ∈ ⋂ j, o.K j, ωstar b = frequencyMap d.h b +
        ∑' j, selectionRe (o.Δω j (selectionReal b))) ∧
      (∀ b ∈ ⋂ j, o.K j, hstar b = ∑' j, (o.Δh j (selectionReal b)).re) ∧
      ContinuousOn ωstar (⋂ j, o.K j) ∧ ContinuousOn hstar (⋂ j, o.K j) ∧
      (∀ m, ∀ b ∈ ⋂ j, o.K j, ‖ωstar b - selectionRe (selectionFrequency d o.toSelectionChain m
        (selectionReal b))‖ ≤ selectionTail a m) ∧
      (∀ m, ∀ b ∈ ⋂ j, o.K j, |hstar b -
        (selectionEnergy o.toSelectionChain m (selectionReal b)).re| ≤ 4 * selectionε a m) := by
  have hC := cx.hyp
  have hτ : 0 ≤ a.τ := hC.hτ
  have hKd : ∀ j, o.K j ⊆ d.K := fun j => by
    have := selectionChain_antitone (o.chain j).toSelectionExtensionChain (j := 0) j (by omega)
    rw [zero_add, (o.chain j).initial] at this
    exact this
  have hKV : ∀ j, ∀ b ∈ o.K j, selectionReal b ∈ actionNbhd d.K (2 * d.ϑ) := fun j b hb =>
    selectionReal_mem_collar (by linarith [d.theta_pos]) (hKd j hb)
  set Kinf : Set (SelectionR n) := ⋂ j, o.K j with hKinf
  set v : ℕ → SelectionR n → SelectionR n := fun j b => selectionRe (o.Δω j (selectionReal b))
    with hv
  set u : ℕ → SelectionR n → ℝ := fun j b => (o.Δh j (selectionReal b)).re with hu
  have hell : Summable (selectionell a) := by
    simpa using (iter_tail cx 0).1
  have hεsum : Summable (fun j => 2 * selectionε a j) := by
    have hg := (summable_geometric_of_lt_one (selectionVarpi_pos_le_one n a.μ hτ).1.le
      (by linarith [selectionVarpi_le_half n a.μ hτ])).mul_left (2 * a.ε₀)
    refine hg.congr fun j => ?_
    simp only [selectionε]
    ring
  have hvb : ∀ j, ∀ b ∈ Kinf, ‖v j b‖ ≤ selectionell a j := fun j b hb => by
    have hbj : b ∈ o.K j := selection_Kinf_subset j hb
    exact (norm_selectionRe_le _).trans ((o.chain (j + 1)).bound j (by omega) _
      (selectionReal_mem_collar (selectiont_pos hC.ht j) hbj))
  have hub : ∀ j, ∀ b ∈ Kinf, ‖u j b‖ ≤ 2 * selectionε a j := fun j b hb => by
    have hbj : b ∈ o.K j := selection_Kinf_subset j hb
    refine (Complex.abs_re_le_norm _).trans ?_
    exact o.energy_bound j _ (selectionReal_mem_collar (selectiont_pos hC.ht j) hbj)
  have hvc : ∀ j, ContinuousOn (v j) Kinf := fun j => by
    have h1 : ContinuousOn (o.Δω j) (actionNbhd (o.K j) (selectiont a j)) :=
      ((o.chain (j + 1)).holomorphic j (by omega)).continuousOn
    have h2 : ContinuousOn (fun b => o.Δω j (selectionReal b)) Kinf :=
      h1.comp continuous_selectionReal.continuousOn fun b hb =>
        selectionReal_mem_collar (selectiont_pos hC.ht j) (selection_Kinf_subset j hb)
    exact (continuous_pi fun i => Complex.continuous_re.comp (continuous_apply i)).comp_continuousOn
      h2
  have huc : ∀ j, ContinuousOn (u j) Kinf := fun j => by
    have h1 : ContinuousOn (o.Δh j) (actionNbhd (o.K j) (selectiont a j)) :=
      (o.increment_holo j).continuousOn
    have h2 : ContinuousOn (fun b => o.Δh j (selectionReal b)) Kinf :=
      h1.comp continuous_selectionReal.continuousOn fun b hb =>
        selectionReal_mem_collar (selectiont_pos hC.ht j) (selection_Kinf_subset j hb)
    exact Complex.continuous_re.comp_continuousOn h2
  obtain ⟨hTv, hCv, hSv⟩ := continuous_series_on_compact Kinf v (selectionell a) hvc hell hvb
  obtain ⟨hTu, hCu, hSu⟩ := continuous_series_on_compact Kinf u (fun j => 2 * selectionε a j)
    huc hεsum hub
  have hfreq : ∀ ν, ∀ b ∈ Kinf, selectionRe (selectionFrequency d o.toSelectionChain ν
      (selectionReal b)) = frequencyMap d.h b + ∑ j ∈ Finset.range ν, v j b := fun ν b hb => by
    funext i
    simp only [selectionFrequency, selectionRe, Pi.add_apply, Finset.sum_apply, Complex.add_re,
      Complex.re_sum, hv]
    rw [selectionFrequencyMap_apply (p11_isOpen_actionNbhd d.K (2 * d.ϑ)) d.holo
      (hKV 0 b (selection_Kinf_subset 0 hb)) i]
  have henergy : ∀ ν, ∀ b ∈ Kinf, (selectionEnergy o.toSelectionChain ν (selectionReal b)).re =
      ∑ j ∈ Finset.range ν, u j b := fun ν b _ => by
    simp [selectionEnergy, Complex.re_sum, hu]
  refine ⟨fun b => frequencyMap d.h b + ∑' j, v j b, fun b => ∑' j, u j b, hSv, hSu, ?_, ?_,
    fun _ _ => rfl, fun _ _ => rfl, ?_, hCu, ?_, ?_⟩
  · rw [Metric.tendstoUniformlyOn_iff] at hTv ⊢
    intro ε hε
    filter_upwards [hTv ε hε] with m hm b hb
    rw [hfreq m b hb, dist_add_left]
    exact hm b hb
  · refine hTu.congr (Eventually.of_forall fun m b hb => ?_)
    exact (henergy m b hb).symm
  · have hF : ContinuousOn (frequencyMap d.h) Kinf :=
      ((selectionFrequencyMap_contDiffOn (p11_isOpen_actionNbhd d.K (2 * d.ϑ)) d.holo
        d.μ).continuousOn).mono fun b hb => hKV 0 b (selection_Kinf_subset 0 hb)
    exact hF.add hCv
  · intro m b hb
    have hs1 : Summable (fun j => v j b) := hSv b hb
    rw [hfreq m b hb, add_sub_add_left_eq_sub, ← hs1.sum_add_tsum_nat_add m]
    simp only [add_sub_cancel_left]
    have hg : HasSum (fun j => selectionell a (j + m)) (selectionTail a m) :=
      ((summable_nat_add_iff m).2 hell).hasSum
    exact tsum_of_norm_bounded hg fun j => hvb (j + m) b hb
  · intro m b hb
    have hs1 : Summable (fun j => u j b) := hSu b hb
    show |∑' j, u j b - _| ≤ _
    rw [henergy m b hb, ← hs1.sum_add_tsum_nat_add m, add_sub_cancel_left]
    have hvl := selectionVarpi_pos_le_one n a.μ hτ
    have hg0 := geom_tsum_le_two hvl.1.le (selectionVarpi_le_half n a.μ hτ)
    have hε0 : 0 ≤ selectionε a m := by
      have := cx.hyp.he
      unfold selectionε
      have := hvl.1
      positivity
    have hg : HasSum (fun j => 2 * selectionε a (j + m))
        (2 * selectionε a m * ∑' i : ℕ, selectionVarpi n a.μ a.τ ^ i) := by
      refine (hg0.1.hasSum.mul_left (2 * selectionε a m)).congr_fun ?_
      intro j
      simp only [selectionε, pow_add]
      ring
    rw [← Real.norm_eq_abs]
    refine (tsum_of_norm_bounded hg fun j => hub (j + m) b hb).trans ?_
    nlinarith [hg0.2]

end Limit

end KAM.Planetary

end
