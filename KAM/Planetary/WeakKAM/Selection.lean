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

section Main

theorem selectionT_unbounded (a : SelectionSchedule n) (hT : 1 ≤ a.T₀) (L : ℝ) :
    ∃ ν, L ≤ selectionT a ν := by
  obtain ⟨ν, hν⟩ := pow_unbounded_of_one_lt L (by norm_num : (1 : ℝ) < 2)
  exact ⟨ν, hν.le.trans (by unfold selectionT; nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) ν])⟩

/-- `bpP:p11a:parameter-selection`: the parameter selection, built on the iteration of the
inductive lemma. -/
theorem parameter_selection (d : SelectionData n) (ε : ℝ) (he : 0 ≤ ε)
    (hsmall : ε ≤ selectionAdmissible d) (f : SelectionPhaseC n → ℂ)
    (hf : SelectionPerturbation d f ε) : Nonempty (SelectionOutput d f (adm_params d ε)) := by
  obtain ⟨o⟩ := inductive_lemma d ε he hsmall f hf
  obtain ⟨hA, ht1, hs, he0⟩ := selection_adm_facts d ε he hsmall
  set a := adm_params d ε with ha
  have hT : 1 ≤ a.T₀ := hA.cutoff_ge
  have cx : WeakBudgetCtx d a := weakBudgetCtx_of d a hA rfl rfl rfl rfl rfl rfl hs he0
  obtain ⟨χ, hχ⟩ := selection_all_cutoffs d a o.toSelectionChain
    (fun ν => (o.chain ν).toSelectionExtensionChain) hA.t_pos ht1 d.tau_nonneg
  obtain ⟨ωstar, hstar, hSω, hSh, hUω, hUh, hωs, hhs, hCω, hCh, hTω, hTh⟩ :=
    selection_limit_series cx o
  have htests := selection_tests_of_cutoffs d ε he hsmall o.toSelectionChain o.chain χ hχ
  have hstage := selection_stage_all d ε he hsmall o.toSelectionChain
    (fun ν => (o.chain ν).toSelectionExtensionChain) χ hχ
  set Hfin := selectionFiniteTests d a o.toSelectionChain χ with hHfin
  set Hinf : Set (SelectionR n) := {b ∈ d.K | ∀ k : Fin n → ℤ, k ≠ 0 →
    2 * a.γ / selectionModeLength k ^ a.τ ≤
      |∑ i, (k i : ℝ) * selectionExtendedFrequency d o.toSelectionChain χ
        (selectionModeStage a k) b i|} with hHinf
  have hmono : Antitone Hfin := fun ν ν' hνν' b hb =>
    ⟨hb.1, fun k hk hkT => hb.2 k hk (hkT.trans (by
      unfold selectionT
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hνν') (by linarith)))⟩
  have hHeq : Hinf = ⋂ ν, Hfin ν := by
    ext b
    simp only [mem_iInter]
    constructor
    · rintro ⟨hb, h⟩ ν
      exact ⟨hb, fun k hk _ => h k fun h0 => by simp [h0, selectionModeLength] at hk⟩
    · intro h
      refine ⟨(h 0).1, fun k hk => ?_⟩
      obtain ⟨ν, hν⟩ := selectionT_unbounded a hT (selectionModeLength k)
      exact (h ν).2 k (selectionModeLength_pos hk) hν
  have hKd : ∀ j, o.K j ⊆ d.K := fun j => by
    have := selectionChain_antitone (o.chain j).toSelectionExtensionChain (j := 0) j (by omega)
    rw [zero_add, (o.chain j).initial] at this
    exact this
  have hHsub : Hinf ⊆ ⋂ j, o.K j := by
    intro b hb
    rw [hHeq] at hb
    simp only [mem_iInter] at hb ⊢
    intro j
    cases j with
    | zero => rw [(o.chain 0).initial]; exact (hb 0).1
    | succ ν =>
      rw [(o.chain (ν + 1)).retained ν (by omega)]
      exact (htests ν).2.1 (hb ν)
  have hcompH : ∀ ν, IsCompact (Hfin ν) := fun ν => (htests ν).1
  have hcompKinf : IsCompact (⋂ j, o.K j) :=
    ((o.chain 0).compact 0 le_rfl).of_isClosed_subset
      (isClosed_iInter fun j => ((o.chain j).compact j le_rfl).isClosed) (iInter_subset _ 0)
  have hcompHinf : IsCompact Hinf := by
    rw [hHeq]
    exact (hcompH 0).of_isClosed_subset (isClosed_iInter fun ν => (hcompH ν).isClosed)
      (iInter_subset _ 0)
  have hmeas : volume d.K - ENNReal.ofReal d.loss ≤ volume Hinf := by
    rw [hHeq]
    have hlim := tendsto_measure_iInter_atTop (μ := volume) (s := Hfin)
      (fun ν => (hcompH ν).isClosed.measurableSet.nullMeasurableSet) hmono
      ⟨0, (hcompH 0).measure_lt_top.ne⟩
    exact ge_of_tendsto' hlim fun ν => (htests ν).2.2
  have hγ : 0 < a.γ := selectionGamma_pos d
  have hdio : ∀ b ∈ Hinf, IsDiophantine a.γ a.τ (ωstar b) := by
    intro b hb k hk
    have hbK : b ∈ ⋂ j, o.K j := hHsub hb
    have hL := selectionModeLength_pos hk
    set m := selectionModeStage a k with hm
    have hbm : b ∈ o.K m := mem_iInter.1 hbK m
    have hext := (hstage m).2.1 b hbm
    have htail := hTω m b hbK
    have hLT : selectionModeLength k ≤ selectionT a m :=
      (selectionModeStage_mem_shell a hT hL).2.1
    have hpow : a.γ * selectionT a m ^ (-a.τ - 1) ≤
        a.γ * selectionModeLength k ^ (-a.τ - 1) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hL hLT
        (by linarith [cx.hyp.hτ])) hγ.le
    have e : 2 * a.γ * KAM.Fourier.modeSize k ^ (-a.τ) =
        2 * a.γ / selectionModeLength k ^ a.τ := by
      rw [Real.rpow_neg (KAM.Fourier.modeSize_nonneg k), div_eq_mul_inv]
      rfl
    have hu : 2 * a.γ * KAM.Fourier.modeSize k ^ (-a.τ) ≤
        |p11dotZ k (selectionExtendedFrequency d o.toSelectionChain χ m b)| := by
      rw [e]
      exact hb.2 k hk
    have ht : ‖selectionExtendedFrequency d o.toSelectionChain χ m b - ωstar b‖ ≤
        a.γ * KAM.Fourier.modeSize k ^ (-a.τ - 1) := by
      rw [norm_sub_rev, hext]
      exact htail.trans (((iter_tail cx m).2).trans hpow)
    have hbr := limit_bridge (m := n) hγ hk hu ht
    rw [Real.rpow_neg (KAM.Fourier.modeSize_nonneg k), ← div_eq_mul_inv] at hbr
    exact hbr
  exact ⟨{ toSelectionIteration := o
           cutoffs := χ
           cutoff_spec := fun j => ⟨(hχ j).1, (hχ j).2.1, (hχ j).2.2.1, (hχ j).2.2.2.1⟩
           extended := selectionExtendedFrequency d o.toSelectionChain χ
           extended_formula := fun _ => rfl
           extended_regular := fun j => (hstage j).1
           extended_eq := fun j => (hstage j).2.1
           Kinf := ⋂ j, o.K j
           Hinf := Hinf
           Kinf_eq := rfl
           compact_K := hcompKinf
           compact_H := hcompHinf
           H_subset := hHsub
           modeStage := selectionModeStage a
           modeStage_eq := rfl
           modeStage_spec := fun k hk =>
             selectionModeStage_mem_shell a hT (selectionModeLength_pos hk)
           Hinf_eq := rfl
           finite_compact := fun ν => (htests ν).1
           finite_inclusion := fun ν b hb => by
             rw [(o.chain (ν + 1)).retained ν (by omega)]
             exact (htests ν).2.1 hb
           finite_measure := fun ν => (htests ν).2.2
           measure_H := hmeas
           ωstar := ωstar
           hstar := hstar
           frequency_summable := hSω
           energy_summable := hSh
           frequency_uniform := hUω
           energy_uniform := hUh
           ωstar_sum := hωs
           hstar_sum := hhs
           ωstar_cont := hCω
           hstar_cont := hCh
           frequency_tail := hTω
           energy_tail := hTh
           diophantine := hdio }⟩

end Main

end KAM.Planetary

end
