/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.Standing
public import KAM.Head.CoverMono
public import KAM.Head.DyadicApprox

/-!
# HEAD-Q from HEAD

Blueprint Part 4, the proof of `bp:p0:headq` (steps `step:p4:hq-trivial`, `step:p4:hq-approx`,
`step:p4:hq-head`, `step:p4:hq-transfer`, `step:p4:hq-cover`), as the conditional helper
`KAM.Head.headq_of_head`. The hypothesis `hHEAD` is the whole
frozen HEAD at the data `(n, τ, s₀, r₀, h)` for every action domain `B'`; the HEAD-Q provider
supplies it from the sealed `KAM.kam_positive_measure`. This module imports neither the frozen
theorems nor a provider.

* `KAM.Head.volume_fundamentalDomain` is `meas F_B = meas B`.
* `KAM.Head.fundamentalDomain_diff_subset` is the covering inclusion of `step:p4:hq-cover`.
* `KAM.Head.nonneg_of_bound_nonempty` is the sign of `ε` (`step:p4:head-negative`).
* `KAM.Head.headq_epsilon_bounds` is the arithmetic of the choice of `ε₀` (`step:p4:hq-head`).
* `KAM.Head.headq_of_head` is the assembly.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace KAM.Head

variable {n : ℕ} {τ s₀ r₀ : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}

/-! ### The fundamental domain -/

/-- The unit cube `[0,1)ⁿ` has volume one. -/
theorem volume_pi_Ico_zero_one :
    volume (Set.pi Set.univ fun _ : Fin n => Set.Ico (0 : ℝ) 1) = 1 := by
  rw [Real.volume_pi_Ico]
  simp

/-- Blueprint `step:p4:hq-trivial`: `meas F_B = meas B`, since `F_B = [0,1)ⁿ × B`. -/
theorem volume_fundamentalDomain (A : Set (Fin n → ℝ)) :
    volume (fundamentalDomain A) = volume A := by
  unfold fundamentalDomain
  rw [Measure.volume_eq_prod, Measure.prod_prod, volume_pi_Ico_zero_one, one_mul]

/-- The complex action neighbourhood grows with the action domain. -/
theorem actionNbhd_subset_of_subset {A A' : Set (Fin n → ℝ)} (hA : A' ⊆ A) (r : ℝ) :
    actionNbhd A' r ⊆ actionNbhd A r := by
  rintro I ⟨J, hJ, hlt⟩
  exact ⟨J, hA hJ, hlt⟩

/-- Blueprint `step:p4:hq-cover`: for `B' ⊆ B` and `κ' ≤ κ`,
`F_B \ 𝒦_B(κ) ⊆ ([0,1)ⁿ × (B \ B')) ∪ (F_{B'} \ 𝒦_{B'}(κ'))`. -/
theorem fundamentalDomain_diff_subset (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    {B' : Set (Fin n → ℝ)} (hB : B' ⊆ B) (r₀ τ : ℝ) {κ' κ : ℝ} (hκ : κ' ≤ κ) :
    fundamentalDomain B \ kamCover h f B r₀ τ κ ⊆
      fundamentalDomain (B \ B') ∪ (fundamentalDomain B' \ kamCover h f B' r₀ τ κ') := by
  rintro ⟨θ, I⟩ ⟨⟨hθ, hI⟩, hnot⟩
  by_cases hI' : I ∈ B'
  · exact Or.inr ⟨⟨hθ, hI'⟩, fun hz => hnot (kamCover_mono h f hB r₀ τ hκ hz)⟩
  · exact Or.inl ⟨hθ, hI, hI'⟩

/-! ### The sign of `ε` and the choice of `ε₀` -/

/-- Blueprint `step:p4:head-negative`: if `B` is nonempty and `‖f‖ ≤ ε` on `T_{s₀} × B_{r₀}`, then
`0 ≤ ε`. -/
theorem nonneg_of_bound_nonempty (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) (hB : B.Nonempty)
    {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hbd : ∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ‖f z‖ ≤ ε) : 0 ≤ ε := by
  obtain ⟨J, hJ⟩ := hB
  have hz : ((0 : Fin n → ℂ), fun i => (J i : ℂ)) ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀ :=
    ⟨fun i => by simpa using hs₀, J, hJ, by simpa using hr₀⟩
  exact (norm_nonneg _).trans (hbd _ hz)

/-- Blueprint `step:p4:hq-head`: the three consequences of `ε ≤ ε₀` with
`ε₀ = min (ε₀', (κ/C')², (κ meas B/(2C'))⁴)` that the proof uses. Here `V = meas B`. -/
theorem headq_epsilon_bounds {C' κ V ε ε₀' : ℝ} (hC : 0 < C') (hκ : 0 < κ) (hV : 0 < V)
    (hε : 0 ≤ ε)
    (hle : ε ≤ min ε₀' (min ((κ / C') ^ 2) ((κ * V / (2 * C')) ^ 4))) :
    ε ≤ ε₀' ∧ C' * Real.sqrt ε ≤ κ ∧ C' * ε ^ ((1 : ℝ) / 4) ≤ κ * V / 2 := by
  have h1 : ε ≤ ε₀' := hle.trans (min_le_left _ _)
  have h2 : ε ≤ (κ / C') ^ 2 := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : ε ≤ (κ * V / (2 * C')) ^ 4 := hle.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨h1, ?_, ?_⟩
  · have : Real.sqrt ε ≤ κ / C' := Real.sqrt_le_iff.2 ⟨by positivity, h2⟩
    calc C' * Real.sqrt ε ≤ C' * (κ / C') := by gcongr
      _ = κ := by field_simp
  · have hx : 0 ≤ κ * V / (2 * C') := by positivity
    have hroot : ((κ * V / (2 * C')) ^ 4) ^ ((1 : ℝ) / 4) = κ * V / (2 * C') := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
      norm_num
    have : ε ^ ((1 : ℝ) / 4) ≤ κ * V / (2 * C') :=
      hroot ▸ Real.rpow_le_rpow hε h3 (by norm_num)
    calc C' * ε ^ ((1 : ℝ) / 4) ≤ C' * (κ * V / (2 * C')) := by gcongr
      _ = κ * V / 2 := by field_simp

/-! ### The assembly -/

/-- Blueprint `bp:p0:headq`, steps `hq-trivial` … `hq-cover`, given HEAD at the data
`(n, τ, s₀, r₀, h)` for every action domain (conditional helper; the HEAD-Q provider supplies
`hHEAD := KAM.kam_positive_measure hn hτ hs₀ hr₀`). -/
theorem headq_of_head (hn : 2 ≤ n) (hτ : (n : ℝ) - 1 < τ) (hs₀ : 0 < s₀) (hr₀ : 0 < r₀)
    (hB_open : IsOpen B) (hB_bdd : Bornology.IsBounded B)
    (hh : DifferentiableOn ℂ h (actionNbhd B r₀))
    (hh_real : ∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ actionNbhd B r₀ →
      (h fun i => (I i : ℂ)).im = 0)
    (h_nondeg : ∃ L : ℝ, ∀ I ∈ closure B, ∀ J ∈ closure B,
      ‖I - J‖ ≤ L * ‖frequencyMap h I - frequencyMap h J‖)
    (hHEAD : ∀ B' : Set (Fin n → ℝ), IsOpen B' → Bornology.IsBounded B' →
      (∃ C_B : ℝ, ∀ δ : ℝ, 0 < δ →
        volume {I ∈ B' | Metric.infDist I B'ᶜ < δ} ≤ ENNReal.ofReal (C_B * δ)) →
      DifferentiableOn ℂ h (actionNbhd B' r₀) →
      (∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ actionNbhd B' r₀ →
        (h fun i => (I i : ℂ)).im = 0) →
      (∃ L : ℝ, ∀ I ∈ closure B', ∀ J ∈ closure B',
        ‖I - J‖ ≤ L * ‖frequencyMap h I - frequencyMap h J‖) →
      HeadConclusion τ s₀ r₀ B' h) :
    HeadQConclusion τ s₀ r₀ B h := by
  have _ := hτ -- the condition on `τ` is needed only inside `hHEAD`; kept for the signature
  intro κ hκ
  rcases B.eq_empty_or_nonempty with rfl | hne
  · -- `step:p4:hq-trivial`: `B = ∅`, so `F_B = ∅`
    refine ⟨1, one_pos, fun f ε _ _ _ _ _ => ?_⟩
    simp [fundamentalDomain]
  -- `step:p4:hq-trivial`: `0 < meas B < ∞`
  have hVpos : 0 < volume B := hB_open.measure_pos volume hne
  have hVlt : volume B < ⊤ := hB_bdd.measure_lt_top
  have hV0 : 0 < (volume B).toReal := ENNReal.toReal_pos hVpos.ne' hVlt.ne
  have hη : 0 < κ * (volume B).toReal / 2 := by positivity
  -- `step:p4:hq-approx`
  obtain ⟨B', hB'o, hB'sub, hB'meas, C_B', hlayer⟩ :=
    dyadic_approx (by omega : 0 < n) hB_open hB_bdd hη
  -- `step:p4:hq-head`
  have hB'bdd : Bornology.IsBounded B' := hB_bdd.subset hB'sub
  have hsub : actionNbhd B' r₀ ⊆ actionNbhd B r₀ := actionNbhd_subset_of_subset hB'sub r₀
  have hnd : ∃ L : ℝ, ∀ I ∈ closure B', ∀ J ∈ closure B',
      ‖I - J‖ ≤ L * ‖frequencyMap h I - frequencyMap h J‖ := by
    obtain ⟨L, hL⟩ := h_nondeg
    exact ⟨L, fun I hI J hJ => hL I (closure_mono hB'sub hI) J (closure_mono hB'sub hJ)⟩
  obtain ⟨C', ε₀', hC', hε₀', H⟩ := hHEAD B' hB'o hB'bdd ⟨C_B', hlayer⟩ (hh.mono hsub)
    (fun I hI => hh_real I (hsub hI)) hnd
  refine ⟨min ε₀' (min ((κ / C') ^ 2) ((κ * (volume B).toReal / (2 * C')) ^ 4)), ?_, ?_⟩
  · exact lt_min hε₀' (lt_min (by positivity) (by positivity))
  -- `step:p4:hq-transfer`
  intro f ε hf hper hreal hbd hε
  have hprod : complexStrip n s₀ ×ˢ actionNbhd B' r₀ ⊆ complexStrip n s₀ ×ˢ actionNbhd B r₀ :=
    Set.prod_mono subset_rfl hsub
  obtain ⟨hε', hsqrt, hroot⟩ := headq_epsilon_bounds hC' hκ hV0
    (nonneg_of_bound_nonempty hs₀ hr₀ hne hbd) hε
  have hHead := H f ε (hf.mono hprod) (fun z hz k => hper z (hprod hz) k)
    (fun θ I hz => hreal θ I (hprod hz)) (fun z hz => hbd z (hprod hz)) hε'
  -- `step:p4:hq-cover`
  calc volume (fundamentalDomain B \ kamCover h f B r₀ τ κ)
      ≤ volume (fundamentalDomain (B \ B') ∪
          (fundamentalDomain B' \ kamCover h f B' r₀ τ (C' * Real.sqrt ε))) :=
        measure_mono (fundamentalDomain_diff_subset f hB'sub r₀ τ hsqrt)
    _ ≤ volume (fundamentalDomain (B \ B')) +
          volume (fundamentalDomain B' \ kamCover h f B' r₀ τ (C' * Real.sqrt ε)) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (κ * (volume B).toReal / 2) +
          ENNReal.ofReal (κ * (volume B).toReal / 2) :=
        add_le_add (by rw [volume_fundamentalDomain]; exact hB'meas)
          (hHead.trans (ENNReal.ofReal_le_ofReal hroot))
    _ = ENNReal.ofReal κ * volume (fundamentalDomain B) := by
        rw [volume_fundamentalDomain, ← ENNReal.ofReal_add hη.le hη.le]
        conv_rhs => rw [← ENNReal.ofReal_toReal hVlt.ne]
        rw [← ENNReal.ofReal_mul hκ.le]
        congr 1
        ring

end KAM.Head

end
