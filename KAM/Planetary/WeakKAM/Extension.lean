/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.WeakKAM.ExtensionFrequency
public import KAM.Planetary.WeakKAM.Cutoff
public import KAM.Planetary.WeakKAM.Schedule

/-! # P11B finite extension (`finite-extension`)

For an arbitrary nested chain `K = K₀ ⊇ K₁ ⊇ … ⊇ K_ν` of nonempty compact sets carrying holomorphic,
real, bounded increments `Δω_j` on the collars `K_j + t_j`, the cutoff-weighted frequency
`ω + ∑_{j<ν} χ_j Δω_j` is `C^μ` on the real points of the action neighbourhood, agrees with
`Re ω_ν` on `K_ν`, and differs from `ω` by at most `c' ∑ ℓ_j t_j^{-μ}` in the Euclidean `C^k`
seminorm `selectionDGVector` (`k ≤ μ`). The Leibniz expansion and the Cauchy estimates are in
`ExtensionStage`; the Euclidean/max norm conversion is in `ExtensionNorm`.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ : ℝ}

theorem selectionCutoffC_nonneg (n μ k : ℕ) : 0 ≤ selectionCutoffC n μ k :=
  mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.sSup_nonneg (by
    rintro v ⟨a, -, rfl⟩
    exact Finset.prod_nonneg fun i _ => selectionBumpL1_nonneg _ _))

theorem selectionExtensionSet_bddAbove (n μ : ℕ) :
    BddAbove {v | ∃ k ≤ μ, v = (4 : ℝ) ^ k *
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        selectionCutoffC n μ j * (k - j : ℕ) ^ (k - j)} := by
  refine Set.Finite.bddAbove (((Set.finite_Iic μ).image fun k => (4 : ℝ) ^ k *
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        selectionCutoffC n μ j * (k - j : ℕ) ^ (k - j)).subset ?_)
  rintro v ⟨k, hk, rfl⟩
  exact ⟨k, hk, rfl⟩

theorem le_selectionExtensionC {k : ℕ} (hk : k ≤ μ) :
    Real.sqrt n * ((4 : ℝ) ^ k * ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
      selectionCutoffC n μ j * (k - j : ℕ) ^ (k - j)) ≤ selectionExtensionC n μ := by
  unfold selectionExtensionC
  exact mul_le_mul_of_nonneg_left (le_csSup (selectionExtensionSet_bddAbove n μ) ⟨k, hk, rfl⟩)
    (Real.sqrt_nonneg _)

/-- Euclidean-scaled Leibniz bound for one stage in terms of the extension constant. -/
theorem selectionStage_extension_bound {E : Set (SelectionR n)} (hE : IsCompact E)
    (hne : E.Nonempty) (ht : 0 < t) (ht1 : t ≤ 1) {Δ : SelectionC n → SelectionC n} {ℓ : ℝ}
    (hΔ : DifferentiableOn ℂ Δ (actionNbhd E t))
    (hreal : ∀ b : SelectionR n, selectionReal b ∈ actionNbhd E t →
      Δ (selectionReal b) = selectionReal (selectionRe (Δ (selectionReal b))))
    (hbd : ∀ b ∈ actionNbhd E t, ‖Δ b‖ ≤ ℓ) {χ : SelectionR n → ℝ}
    (hχ : ContDiff ℝ μ χ) (hsupp : tsupport χ ⊆ {y | Metric.infDist y E ≤ t / 2})
    (hχb : ∀ k ≤ μ, ∀ y, ∀ a : Fin k → SelectionR n, (∀ i, ‖a i‖ ≤ 1) →
      |iteratedFDeriv ℝ k χ y a| ≤ selectionCutoffC n μ k * (4 / t) ^ k)
    {k : ℕ} (hk : k ≤ μ) (y : SelectionR n) :
    Real.sqrt n * ‖iteratedFDeriv ℝ k (fun y => χ y • selectionIncrement Δ y) y‖ ≤
      ℓ / t ^ μ * selectionExtensionC n μ := by
  have hℓ : 0 ≤ ℓ := by
    obtain ⟨J, hJ⟩ := hne
    exact (norm_nonneg _).trans (hbd (selectionReal J) ⟨J, hJ, by
      rw [show selectionReal J - (fun i => (J i : ℂ)) = 0 from sub_self _, norm_zero]
      exact ht⟩)
  have h1 := selectionStage_norm_iteratedFDeriv_le hE hne ht hΔ hreal hbd
    (selectionCutoffC_nonneg n μ) hχ hsupp hχb hk y
  have hS := le_selectionExtensionC (n := n) hk
  have hpow : (4 / t) ^ k ≤ 4 ^ k / t ^ μ := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_of_le_one ht.le ht1 hk)
  set Sk := ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * selectionCutoffC n μ i * ((k - i : ℕ) : ℝ) ^ (k - i) with hSk
  have hSk0 : 0 ≤ Sk := Finset.sum_nonneg fun i _ => mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (selectionCutoffC_nonneg _ _ _))
    (pow_nonneg (Nat.cast_nonneg _) _)
  calc Real.sqrt n * ‖iteratedFDeriv ℝ k (fun y => χ y • selectionIncrement Δ y) y‖
      ≤ Real.sqrt n * (ℓ * (4 / t) ^ k * Sk) := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt n * (ℓ * (4 ^ k / t ^ μ) * Sk) := by gcongr
    _ = ℓ / t ^ μ * (Real.sqrt n * (4 ^ k * Sk)) := by ring
    _ ≤ ℓ / t ^ μ * selectionExtensionC n μ := by
        exact mul_le_mul_of_nonneg_left hS (div_nonneg hℓ (by positivity))

theorem selectionLength_single_zero (hn : 1 ≤ n) :
    selectionLength (Pi.single ⟨0, hn⟩ (1 : ℝ) : SelectionR n) = 1 := by
  unfold selectionLength
  simp [Pi.single_apply]

theorem selectionChain_antitone {d : SelectionData n} {a : SelectionSchedule n}
    {c : SelectionChain n} {ν : ℕ} (hc : SelectionExtensionChain d a c ν) {j : ℕ} :
    ∀ i, j + i ≤ ν → c.K (j + i) ⊆ c.K j := by
  intro i
  induction i with
  | zero => intro _; exact subset_rfl
  | succ i ih =>
    intro h
    exact (hc.nested (j + i) (by omega)).trans (ih (by omega))

theorem selectiont_pos {a : SelectionSchedule n} (ht : 0 < a.t₀) (j : ℕ) : 0 < selectiont a j :=
  mul_pos ht (Real.rpow_pos_of_pos two_pos _)

theorem selectiont_le_one {a : SelectionSchedule n} (ht : 0 < a.t₀) (ht1 : a.t₀ ≤ 1)
    (hτ : 0 ≤ a.τ) (j : ℕ) :
    selectiont a j ≤ 1 := by
  unfold selectiont
  have : (2 : ℝ) ^ (-(a.τ + 1) * j) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by nlinarith [Nat.cast_nonneg (α := ℝ) j])
  calc a.t₀ * (2 : ℝ) ^ (-(a.τ + 1) * j) ≤ a.t₀ * 1 :=
        mul_le_mul_of_nonneg_left this ht.le
    _ ≤ 1 := by linarith

theorem finite_extension (d : SelectionData n) (a : SelectionSchedule n)
    (c : SelectionChain n) (ν : ℕ) (hc : SelectionExtensionChain d a c ν)
    (hμ : a.μ = d.μ) (ht : 0 < a.t₀) (ht1 : a.t₀ ≤ 1)
    (htθ : a.t₀ ≤ d.ϑ / Real.sqrt n) (hτ : 0 ≤ a.τ) :
    ∃ χ : ℕ → SelectionR n → ℝ, ∃ w : SelectionR n → SelectionR n,
      (∀ j < ν, ContDiff ℝ d.μ (χ j) ∧
        (∀ y, 0 ≤ χ j y ∧ χ j y ≤ 1) ∧ (∀ y ∈ c.K j, χ j y = 1) ∧
        tsupport (χ j) ⊆ {y | Metric.infDist y (c.K j) ≤ selectiont a j / 2}) ∧
      w = selectionExtendedFrequency d c χ ν ∧
      ContDiffOn ℝ d.μ w {y | selectionReal y ∈ actionNbhd d.K (2 * d.ϑ)} ∧
      (∀ b ∈ c.K ν, w b = selectionRe (selectionFrequency d c ν (selectionReal b))) ∧
      (ν = 0 → w = frequencyMap d.h) ∧
      ∀ j ≤ d.μ, ∀ y ∈ selectionThick d.K d.ϑ,
        selectionDGVector j (w - frequencyMap d.h) y ≤ selectionExtensionC n d.μ *
          ∑ i ∈ Finset.range ν, selectionell a i / selectiont a i ^ d.μ := by
  -- `hμ`, `htθ` are not needed: the cutoffs are globally smooth, so supports need no room in `V`.
  have _ := And.intro hμ htθ
  have hcut : ∀ j, ∃ χ : SelectionR n → ℝ, j < ν → (ContDiff ℝ d.μ χ ∧
      (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧ (∀ y ∈ c.K j, χ y = 1) ∧
      tsupport χ ⊆ {y | Metric.infDist y (c.K j) ≤ selectiont a j / 2} ∧
      ∀ k ≤ d.μ, ∀ y, ∀ a' : Fin k → SelectionR n, (∀ i, ‖a' i‖ ≤ 1) →
        |iteratedFDeriv ℝ k χ y a'| ≤ selectionCutoffC n d.μ k * (4 / selectiont a j) ^ k) := by
    intro j
    by_cases hj : j < ν
    · obtain ⟨χ, h⟩ := smooth_cutoff (μ := d.μ) d.n_pos d.μ_pos (c.K j)
        (hc.compact j hj.le) (hc.nonempty j hj.le) (selectiont_pos ht j)
        (selectiont_le_one ht ht1 hτ j)
      exact ⟨χ, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose χ hχ using hcut
  have hφ : ∀ j < ν, ContDiff ℝ d.μ
      (fun y => χ j y • selectionIncrement (c.Δω j) y) := fun j hj =>
    selectionStage_contDiff (hc.compact j hj.le) (hc.nonempty j hj.le) (selectiont_pos ht j)
      (hc.holomorphic j hj) (hχ j hj).1 (hχ j hj).2.2.2.1
  have hsub : ∀ j < ν, c.K ν ⊆ c.K j := fun j hj => by
    have := selectionChain_antitone hc (j := j) (ν - j) (by omega)
    rwa [Nat.add_sub_cancel' hj.le] at this
  have hKd : c.K ν ⊆ d.K := by
    rcases Nat.eq_zero_or_pos ν with rfl | hν
    · exact hc.initial ▸ subset_rfl
    · exact hc.initial ▸ hsub 0 hν
  refine ⟨χ, selectionExtendedFrequency d c χ ν, fun j hj => ?_, rfl, ?_, ?_, ?_, ?_⟩
  · exact ⟨(hχ j hj).1, (hχ j hj).2.1, (hχ j hj).2.2.1, (hχ j hj).2.2.2.1⟩
  · have h1 := selectionFrequencyMap_contDiffOn (p11_isOpen_actionNbhd d.K (2 * d.ϑ)) d.holo d.μ
    have h2 : ContDiff ℝ d.μ (fun y => ∑ j ∈ Finset.range ν,
        χ j y • selectionIncrement (c.Δω j) y) :=
      ContDiff.sum fun j hj => hφ j (Finset.mem_range.1 hj)
    exact h1.add h2.contDiffOn
  · intro b hb
    have hbA : selectionReal b ∈ actionNbhd d.K (2 * d.ϑ) :=
      ⟨b, hKd hb, by
        rw [show selectionReal b - (fun i => (b i : ℂ)) = 0 from sub_self _, norm_zero]
        linarith [d.theta_pos]⟩
    funext i
    simp only [selectionExtendedFrequency, selectionFrequency, selectionRe, Pi.add_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.add_re, Complex.re_sum]
    rw [selectionFrequencyMap_apply (p11_isOpen_actionNbhd d.K (2 * d.ϑ)) d.holo hbA i]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [(hχ j (Finset.mem_range.1 hj)).2.2.1 b (hsub j (Finset.mem_range.1 hj) hb), one_mul]
  · intro h0
    subst h0
    funext y
    simp [selectionExtendedFrequency]
  · intro k hk y _
    have hkμ : (k : WithTop ℕ∞) ≤ d.μ := by exact_mod_cast hk
    have hfun : (selectionExtendedFrequency d c χ ν - frequencyMap d.h) =
        fun y => ∑ j ∈ Finset.range ν, χ j y • selectionIncrement (c.Δω j) y := by
      funext z
      simp [selectionExtendedFrequency, selectionIncrement]
    rw [hfun]
    have hterm : ∀ j ∈ Finset.range ν, Real.sqrt n *
        ‖iteratedFDeriv ℝ k (fun y => χ j y • selectionIncrement (c.Δω j) y) y‖ ≤
        selectionell a j / selectiont a j ^ d.μ * selectionExtensionC n d.μ := by
      intro j hj
      have hj' := Finset.mem_range.1 hj
      exact selectionStage_extension_bound (hc.compact j hj'.le) (hc.nonempty j hj'.le)
        (selectiont_pos ht j) (selectiont_le_one ht ht1 hτ j) (hc.holomorphic j hj')
        (fun b hb => hc.real j hj' b hb) (fun b hb => hc.bound j hj' b hb) (hχ j hj').1
        (hχ j hj').2.2.2.1 (hχ j hj').2.2.2.2 hk y
    have hne : {v | ∃ a' : SelectionR n, selectionLength a' = 1 ∧ v = selectionLength
        (iteratedFDeriv ℝ k (fun y => ∑ j ∈ Finset.range ν,
          χ j y • selectionIncrement (c.Δω j) y) y (fun _ => a'))}.Nonempty :=
      ⟨_, _, selectionLength_single_zero d.n_pos, rfl⟩
    unfold selectionDGVector
    refine csSup_le hne ?_
    rintro v ⟨a', ha', rfl⟩
    rw [iteratedFDeriv_fun_sum_apply fun j hj =>
      ((hφ j (Finset.mem_range.1 hj)).of_le hkμ).contDiffAt]
    simp only [sum_apply]
    have ha1 : ‖a'‖ ≤ 1 := norm_le_one_of_selectionLength_eq_one ha'
    have hv : ∀ j ∈ Finset.range ν,
        ‖iteratedFDeriv ℝ k (fun y => χ j y • selectionIncrement (c.Δω j) y) y
          (fun _ => a')‖ ≤
        ‖iteratedFDeriv ℝ k (fun y => χ j y • selectionIncrement (c.Δω j) y) y‖ := by
      intro j _
      refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
      have : ∏ _i : Fin k, ‖a'‖ ≤ 1 := Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
        fun _ _ => ha1
      exact mul_le_of_le_one_right (norm_nonneg _) this
    calc selectionLength (∑ j ∈ Finset.range ν,
          iteratedFDeriv ℝ k (fun y => χ j y • selectionIncrement (c.Δω j) y) y (fun _ => a'))
        ≤ Real.sqrt n * ‖∑ j ∈ Finset.range ν,
          iteratedFDeriv ℝ k (fun y => χ j y • selectionIncrement (c.Δω j) y) y (fun _ => a')‖ :=
          selectionLength_le_sqrt_mul_norm _
      _ ≤ Real.sqrt n * ∑ j ∈ Finset.range ν,
          ‖iteratedFDeriv ℝ k (fun y => χ j y • selectionIncrement (c.Δω j) y) y (fun _ => a')‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt n * ∑ j ∈ Finset.range ν,
          ‖iteratedFDeriv ℝ k (fun y => χ j y • selectionIncrement (c.Δω j) y) y‖ :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hv) (Real.sqrt_nonneg _)
      _ = ∑ j ∈ Finset.range ν, Real.sqrt n *
          ‖iteratedFDeriv ℝ k (fun y => χ j y • selectionIncrement (c.Δω j) y) y‖ :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ j ∈ Finset.range ν, selectionell a j / selectiont a j ^ d.μ *
          selectionExtensionC n d.μ := Finset.sum_le_sum hterm
      _ = selectionExtensionC n d.μ * ∑ i ∈ Finset.range ν,
          selectionell a i / selectiont a i ^ d.μ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end KAM.Planetary
