/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Quantitative.AssemblyLipschitz
public import KAM.Planetary.Quantitative.BudgetPositivity
public import KAM.Russmann.Data
public import KAM.Russmann.Domain
public import KAM.Russmann.Extension
public import KAM.Russmann.FamilyVolume
public import KAM.Russmann.Nondegeneracy
public import KAM.Russmann.StrongBudget
public import KAM.Russmann.Torus
public import KAM.Frozen.Defs.FundamentalDomain

/-!
# Track R: the strong form of Rüssmann's KAM theorem, assembled

`russmann_tori_strong` has exactly the hypotheses of R-HEAD and the conclusion of the audit's F1
form (`AUDIT-RUSSMANN-STATEMENT-1`), with the cover `russmannCover` written out as a set-builder:
for every closeness `δ > 0` and every loss `κ > 0`, small perturbations leave a set of volume at
most `κ · meas([0,1)ⁿ × B)` of `[0,1)ⁿ × B` off the invariant Lagrangian tori with
`(γ, τ)`-Diophantine frequencies that are `δ`-close to unperturbed tori.

Route (B) of `docs/tracks/R/PROOF-ROUTE.md`: as in `russmann_tori`, but the family comes from
`KAM.Planetary.weak_kam_quantitative_lip` (defect `2⁻¹⁰`-Lipschitz), the defect is extended to a
global lipeomorphism `E` with `‖E - id‖ ≤ Δ(ε)` (`exists_lipeo_extension`), and
`volume_image_cell_lower` with an open `U ⊇ K` turns `Δ(ε) → 0` into a near-full image.

`russmann_tori_of_strong` derives the fixed-fraction form `russmann_tori` (`4⁻ⁿ`) from the strong
form, through `quarter_le_of_diff_le`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Russmann

open KAM KAM.Planetary

variable {n : ℕ}

/-- Every integer angle translate of a point on the union of track P's tori over
`[0,1)ⁿ × good` lies on a torus satisfying the clauses of the draft cover. -/
theorem familyImage_translate_mem {B : Set (Fin n → ℝ)} {r₀ : ℝ} {h : (Fin n → ℂ) → ℂ}
    {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {d : QuantitativeData n} {cΔ ε : ℝ}
    (Q : QuantitativeFamily d (realHamiltonian h f) cΔ ε) (hKB : d.K ⊆ B)
    (hϑr : 2 * d.vartheta < r₀) (hγ : 0 < d.gamma) {δ : ℝ}
    (hdisp : ∀ b ∈ Q.good, ∀ θ, ‖Q.torus b θ - (θ, b)‖ ≤ δ) :
    ∀ z ∈ (fun z : (Fin n → ℝ) × (Fin n → ℝ) => Q.torus z.2 z.1) '' (unitCube n ×ˢ Q.good),
    ∀ k : Fin n → ℤ, z + angleTranslate k ∈
      {z | ∃ (K : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) (ω : Fin n → ℝ) (γ : ℝ)
        (I₀ : Fin n → ℝ),
        0 < γ ∧ IsDiophantine γ d.tau ω ∧
        IsInvariantLagrangianTorus (realHamiltonian h f) ω K ∧
        (∀ θ, ∃ J ∈ B, ‖(K θ).2 - J‖ < r₀) ∧
        I₀ ∈ B ∧ (∀ θ, ‖K θ - (θ, I₀)‖ ≤ δ) ∧ z ∈ Set.range K} := by
  rintro _ ⟨⟨θ, b⟩, ⟨-, hb⟩, rfl⟩ k
  refine ⟨Q.torus b, Q.freq b, d.gamma, b, hγ, Q.dio b hb,
    isInvariantLagrangianTorus_of_isLatticeTorus (Q.lattice b hb), fun θ' => ?_,
    hKB (Q.subset hb), hdisp b hb, ⟨θ + fun i => (k i : ℝ), (Q.lattice b hb).2.1 θ k⟩⟩
  obtain ⟨J, hJ, hlt⟩ := ((Q.lattice b hb).1.2 θ').1
  refine ⟨J, hKB hJ, ?_⟩
  have : ‖realInclusion n (Q.torus b θ').2 - realInclusion n J‖ < 2 * d.vartheta := hlt
  rw [← map_sub, norm_realInclusion] at this
  exact this.trans hϑr

/-- The actions of the union of track P's tori over `[0,1)ⁿ × good` lie in `B` when the
displacement is below the margin of `d.K` in `B`. -/
theorem familyImage_actions_mem {B : Set (Fin n → ℝ)} {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {d : QuantitativeData n} {cΔ ε : ℝ} (Q : QuantitativeFamily d H cΔ ε) {m δ : ℝ}
    (hmarg : ∀ b ∈ d.K, ∀ y : Fin n → ℝ, ‖y - b‖ < m → y ∈ B) (hδm : δ < m)
    (hdisp : ∀ b ∈ Q.good, ∀ θ, ‖Q.torus b θ - (θ, b)‖ ≤ δ) :
    ∀ z ∈ (fun z : (Fin n → ℝ) × (Fin n → ℝ) => Q.torus z.2 z.1) '' (unitCube n ×ˢ Q.good),
      z.2 ∈ B := by
  rintro _ ⟨⟨θ, b⟩, ⟨-, hb⟩, rfl⟩
  refine hmarg b (Q.subset hb) _ (lt_of_le_of_lt ?_ hδm)
  calc ‖(Q.torus b θ).2 - b‖ ≤ ‖Q.torus b θ - (θ, b)‖ := by
        simpa using norm_snd_le (Q.torus b θ - (θ, b))
    _ ≤ δ := hdisp b hb θ

/-- **Rüssmann's KAM theorem (maximal case), strong form, assembled.** The hypotheses are those of
R-HEAD; the conclusion is the audit's F1 form with the draft cover written out. -/
theorem russmann_tori_strong (hn : 1 ≤ n) {s₀ r₀ : ℝ} (hs₀ : 0 < s₀) (hr₀ : 0 < r₀)
    {B : Set (Fin n → ℝ)} (hB_open : IsOpen B) (hB_conn : IsConnected B)
    (hB_bdd : Bornology.IsBounded B)
    {h : (Fin n → ℂ) → ℂ} (hh : DifferentiableOn ℂ h (actionNbhd B r₀))
    (hh_real : ∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ actionNbhd B r₀ →
      (h fun i => (I i : ℂ)).im = 0)
    (h_russmann : ∀ c : Fin n → ℝ, c ≠ 0 → ∃ I ∈ B, ∑ i, c i * frequencyMap h I i ≠ 0) :
    ∃ τ : ℝ, (n : ℝ) - 1 < τ ∧ ∀ δ : ℝ, 0 < δ → ∀ κ : ℝ, 0 < κ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ε : ℝ),
        DifferentiableOn ℂ f (complexStrip n s₀ ×ˢ actionNbhd B r₀) →
        (∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ∀ k : Fin n → ℤ,
          f (z.1 + (fun i => (k i : ℂ)), z.2) = f z) →
        (∀ θ I : Fin n → ℝ,
          ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀ →
          (f ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0) →
        (∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ‖f z‖ ≤ ε) → ε ≤ ε₀ →
        volume (fundamentalDomain B \
            {z | ∃ (K : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) (ω : Fin n → ℝ) (γ : ℝ)
              (I₀ : Fin n → ℝ),
              0 < γ ∧ IsDiophantine γ τ ω ∧ IsInvariantLagrangianTorus (realHamiltonian h f) ω K ∧
              (∀ θ, ∃ J ∈ B, ‖(K θ).2 - J‖ < r₀) ∧
              I₀ ∈ B ∧ (∀ θ, ‖K θ - (θ, I₀)‖ ≤ δ) ∧ z ∈ Set.range K}) ≤
          ENNReal.ofReal κ * volume (fundamentalDomain B) := by
  -- Step 1: the order of non-degeneracy on `closure B` and the exponent `τ = n μ`
  obtain ⟨μ, hμ, β₀, hβ₀, hfinB⟩ :=
    russmann_finite_order_frequencyMap hr₀ hB_conn hB_bdd hh h_russmann
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hμ' : (1 : ℝ) ≤ μ := by exact_mod_cast hμ
  refine ⟨(n : ℝ) * μ, by nlinarith, fun δ hδ κ hκ => ?_⟩
  -- Step 2: the compact and open parameter sets
  set L : ℝ := (1 + (2 : ℝ) ^ (-10 : ℤ)) ^ (2 * n) with hLdef
  have hL : 0 ≤ L := by positivity
  set η : ℝ := κ / (3 + 2 * L) with hηdef
  have hη : 0 < η := by positivity
  have hκη : (3 + 2 * L) * η = κ := by rw [hηdef]; field_simp
  obtain ⟨K, hK, hKB, hKa, ⟨m, hm, hmarg⟩, ⟨U, hUo, hKU, hUB, hUK⟩, εs, hεs, hεsη, hεK⟩ :=
    exists_compact_open_budget hB_open hB_bdd hB_conn.nonempty hη
  have hfin : volume B ≠ ⊤ := hB_bdd.measure_lt_top.ne
  set V : ℝ := (volume B).toReal with hVdef
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hUa : ENNReal.ofReal ((1 - 2 * η) * V) < volume U :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by nlinarith)) (hKa.trans_le (measure_mono hKU))
  obtain ⟨Δ₀, hΔ₀, hUΔ₀⟩ := exists_inner_volume_gt hUo hUa
  -- Step 3: the data of track P
  set ϑ : ℝ := min 1 (r₀ / 4) with hϑdef
  set s : ℝ := min 1 s₀ with hsdef
  have hϑ0 : 0 < ϑ := lt_min one_pos (by positivity)
  have hϑ1 : ϑ ≤ 1 := min_le_left _ _
  have hϑr : 2 * ϑ < r₀ := by
    have : ϑ ≤ r₀ / 4 := min_le_right _ _
    linarith
  have hs0 : 0 < s := lt_min one_pos hs₀
  have hs1 : s ≤ 1 := min_le_left _ _
  have hss : s ≤ s₀ := min_le_right _ _
  obtain ⟨A, hA0, hA⟩ := exists_bound_iteratedFDeriv (isCompact_euclidThick hK ϑ)
    (euclidThick_subset_realNbhd hKB (show ϑ < r₀ by linarith)) (analyticOnNhd_frequencyMap hh)
    (μ + 1)
  obtain ⟨C, hC⟩ := exists_hessian_bound hh hK hKB hϑr
  set d := russmannData n μ ϑ s (min β₀ 1) (max (n * A) 1) (max (Real.sqrt n * A) 1) (max C 1)
    εs K with hd_def
  have hd : d.Valid := russmannData_valid hn hμ hϑ0 hϑ1 hs0 hs1 (le_max_right _ _)
    (lt_of_lt_of_le one_pos (le_max_right _ _)) (lt_min hβ₀ one_pos)
    ((min_le_right _ _).trans (le_max_right _ _)) (min_le_right _ _) hK hεs hεK
  obtain ⟨cΔ, hcΔ, hQ⟩ := weak_kam_quantitative_lip n μ ((n : ℝ) * μ) s (max C 1)
  have hγ : 0 < d.gamma := qbc_gamma_pos hd.1
  have hth : 0 < thresholds d := qbc_thresholds_pos hd.1
  have hn0 : (0 : ℝ) < n := by linarith
  set δ' : ℝ := min (min δ (m / 2)) (min Δ₀ (η / (2 * n))) with hδ'def
  have hδ' : 0 < δ' := lt_min (lt_min hδ (by positivity)) (lt_min hΔ₀ (by positivity))
  refine ⟨min (thresholds d) ((δ' * d.gamma / cΔ) ^ 2), lt_min hth (by positivity), ?_⟩
  intro f ε hf hf_per hf_real hf_bd hε
  -- Step 4: the family of tori, with its defect Lipschitz bound
  obtain ⟨b₀, hb₀⟩ := hB_conn.nonempty
  have hε0 : 0 ≤ ε := by
    refine (norm_nonneg _).trans (hf_bd (0, fun i => (b₀ i : ℂ)) ⟨fun i => ?_, b₀, hb₀, ?_⟩)
    · simpa using hs₀
    · simpa using hr₀
  have hQI : QuantitativeInput d h f :=
    russmannData_input hKB hϑ0 hϑr hss hh hh_real hf hf_per hf_real (min_le_left _ _)
      (fun c hc y hy => hfinB c hc y (subset_closure (hKB hy))) hA (le_max_left _ _)
      (le_max_left _ _) hC (le_max_left _ _)
  have hdom : complexStrip n d.s ×ˢ actionNbhd d.K (2 * d.vartheta) ⊆
      complexStrip n s₀ ×ˢ actionNbhd B r₀ := by
    refine prod_mono (fun θ hθ i => (hθ i).trans_le hss) ?_
    rintro I ⟨J, hJ, hI⟩
    exact ⟨J, hKB hJ, hI.trans hϑr⟩
  obtain ⟨Q, hQlip⟩ := hQ d hd rfl rfl rfl rfl h f hQI ε hε0 (hε.trans (min_le_left _ _))
    fun z hz => hf_bd z (hdom hz)
  -- Step 5: the displacement `Δ(ε) ≤ δ'`
  set Δ : ℝ := p11c_displacement d cΔ ε with hΔdef
  have hΔ0 : 0 ≤ Δ := le_min (by positivity) (by positivity)
  have hΔδ' : Δ ≤ δ' := by
    refine (min_le_right _ _).trans ?_
    have hsq : Real.sqrt ε ≤ δ' * d.gamma / cΔ := by
      rw [← Real.sqrt_sq (show 0 ≤ δ' * d.gamma / cΔ by positivity)]
      exact Real.sqrt_le_sqrt (hε.trans (min_le_right _ _))
    rw [div_le_iff₀ hγ]
    calc cΔ * Real.sqrt ε ≤ cΔ * (δ' * d.gamma / cΔ) := by gcongr
      _ = δ' * d.gamma := by field_simp
  have hΔhalf : 2 * Δ ≤ 1 := by
    have h18 : (2 : ℝ) ^ (-18 : ℤ) ≤ 1 / 2 := by norm_num
    have : Δ ≤ 1 / 2 := (min_le_left _ _).trans h18
    linarith
  have hdisp : ∀ b ∈ Q.good, ∀ θ, ‖Q.torus b θ - (θ, b)‖ ≤ Δ := Q.displacement
  -- Step 6: the global lipeomorphism and the near-full image
  obtain ⟨E, hEbij, hEd, hElip, hEeq⟩ := exists_lipeo_extension
    (A := {z : (Fin n → ℝ) × (Fin n → ℝ) | z.2 ∈ Q.good})
    (u := fun z => Q.torus z.2 z.1 - z) (lam := (2 : ℝ) ^ (-10 : ℤ)) (by positivity)
    (by norm_num) hΔ0 (fun x hx y hy => hQlip x.2 hx y.2 hy x.1 y.1)
    (fun x hx => hdisp x.2 hx x.1)
  have hEA : E '' (unitCube n ×ˢ Q.good) =
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) => Q.torus z.2 z.1) '' (unitCube n ×ˢ Q.good) :=
    image_congr fun z hz => by rw [hEeq z hz.2]; abel
  have hGU : Q.good ⊆ U := fun b hb => hKU (Q.subset hb)
  have hmain := volume_image_cell_lower hEbij.2 hΔhalf hEd hElip hGU
  rw [hEA] at hmain
  have hX : ENNReal.ofReal ((1 - 2 * η) * V) ≤ volume {b | closedBall b Δ ⊆ U} :=
    hUΔ₀.le.trans (measure_mono fun b hb =>
      (closedBall_subset_closedBall (hΔδ'.trans ((min_le_right _ _).trans (min_le_left _ _))))
        |>.trans hb)
  have hKfin : volume K ≠ ⊤ := ((measure_mono hKB).trans_lt hB_bdd.measure_lt_top).ne
  have hgK : Q.good ⊆ K := Q.subset
  have hmeasQ : volume K ≤ volume Q.good + ENNReal.ofReal εs := Q.measure
  have hKgood : volume (K \ Q.good) ≤ ENNReal.ofReal εs := by
    rw [measure_sdiff hgK Q.compact.measurableSet.nullMeasurableSet
      ((measure_mono hgK).trans_lt hKfin.lt_top).ne]
    exact tsub_le_iff_left.2 hmeasQ
  have hZ : volume (U \ Q.good) ≤ ENNReal.ofReal (2 * η * V) := by
    calc volume (U \ Q.good) ≤ volume ((U \ K) ∪ (K \ Q.good)) := by
          refine measure_mono fun b hb => ?_
          by_cases hbK : b ∈ K
          · exact Or.inr ⟨hbK, hb.2⟩
          · exact Or.inl ⟨hb.1, hbK⟩
      _ ≤ volume (U \ K) + volume (K \ Q.good) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (η * V) + ENNReal.ofReal εs := add_le_add hUK hKgood
      _ ≤ ENNReal.ofReal (η * V) + ENNReal.ofReal (η * V) := by gcongr
      _ = ENNReal.ofReal (2 * η * V) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  -- Step 7: into `[0,1)ⁿ × B` modulo `ℤⁿ`
  have hδm : δ' < m := (min_le_left _ _).trans_lt
    ((min_le_right _ _).trans_lt (half_lt_self hm))
  obtain ⟨F, hFm, hFsub, hFvol⟩ := exists_measurableSet_subset_fundamentalDomain_inter Q.borel
    (familyImage_eq_add_angleTranslate Q)
    (familyImage_translate_mem Q hKB hϑr hγ (δ := δ) fun b hb θ =>
      ((hdisp b hb θ).trans hΔδ').trans ((min_le_left _ _).trans (min_le_left _ _)))
    (familyImage_actions_mem Q hmarg hδm fun b hb θ => (hdisp b hb θ).trans hΔδ')
  -- Step 8: the volume bound
  have hpow : 1 - η ≤ (1 - 2 * Δ) ^ n := by
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(2 * Δ) by linarith) n
    have h2 : (n : ℝ) * (2 * Δ) ≤ η := by
      have : Δ ≤ η / (2 * n) := hΔδ'.trans ((min_le_right _ _).trans (min_le_right _ _))
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    have e : 1 + (n : ℝ) * -(2 * Δ) = 1 - n * (2 * Δ) := by ring
    rw [e, ← sub_eq_add_neg] at hb
    linarith
  have harith := strong_volume_arith hV0 hη.le (pow_nonneg (by linarith) n) hpow hL hX hmain
    hZ hFvol
  rw [hκη] at harith
  have hFD : volume (fundamentalDomain B) = ENNReal.ofReal V := by
    rw [volume_fundamentalDomain, hVdef, ENNReal.ofReal_toReal hfin]
  have hFfin : volume F ≠ ⊤ :=
    ((measure_mono (hFsub.trans inter_subset_left)).trans_lt (by
      rw [hFD]; exact ENNReal.ofReal_lt_top)).ne
  calc volume (fundamentalDomain B \ _) ≤ volume (fundamentalDomain B \ F) :=
        measure_mono (sdiff_subset_sdiff_right fun z hz => (hFsub hz).2)
    _ = volume (fundamentalDomain B) - volume F :=
        measure_sdiff (hFsub.trans inter_subset_left) hFm.nullMeasurableSet hFfin
    _ ≤ ENNReal.ofReal κ * volume (fundamentalDomain B) := by
        rw [tsub_le_iff_left, hFD, ← ENNReal.ofReal_mul hκ.le]
        exact harith

/-- If the part of `X` outside `C` has measure at most `(1 - p) μ X`, then `C` fills at least
`p μ X` of `X` (`0 ≤ p ≤ 1`, `μ X < ∞`). No measurability is needed. -/
theorem quarter_le_of_diff_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {X C : Set α}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hX : μ X ≠ ⊤)
    (h : μ (X \ C) ≤ ENNReal.ofReal (1 - p) * μ X) :
    ENNReal.ofReal p * μ X ≤ μ (X ∩ C) := by
  have h1 : μ X ≤ μ (X ∩ C) + μ (X \ C) := by
    calc μ X ≤ μ ((X ∩ C) ∪ (X \ C)) := measure_mono fun x hx => by
          by_cases hxC : x ∈ C
          · exact Or.inl ⟨hx, hxC⟩
          · exact Or.inr ⟨hx, hxC⟩
      _ ≤ μ (X ∩ C) + μ (X \ C) := measure_union_le _ _
  have h2 : ENNReal.ofReal p * μ X + ENNReal.ofReal (1 - p) * μ X = μ X := by
    rw [← add_mul, ← ENNReal.ofReal_add hp0 (sub_nonneg.2 hp1)]
    simp
  refine ENNReal.le_of_add_le_add_right (a := ENNReal.ofReal (1 - p) * μ X)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hX) ?_
  rw [h2]
  exact h1.trans (add_le_add le_rfl h)

/-- **The strong form implies the fixed-fraction form.** `russmann_tori` (the `4⁻ⁿ` form of
R-HEAD v0.1), derived from `russmann_tori_strong` with `κ = 1 - 4⁻ⁿ`. -/
theorem russmann_tori_of_strong (hn : 1 ≤ n) {s₀ r₀ : ℝ} (hs₀ : 0 < s₀) (hr₀ : 0 < r₀)
    {B : Set (Fin n → ℝ)} (hB_open : IsOpen B) (hB_conn : IsConnected B)
    (hB_bdd : Bornology.IsBounded B)
    {h : (Fin n → ℂ) → ℂ} (hh : DifferentiableOn ℂ h (actionNbhd B r₀))
    (hh_real : ∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ actionNbhd B r₀ →
      (h fun i => (I i : ℂ)).im = 0)
    (h_russmann : ∀ c : Fin n → ℝ, c ≠ 0 → ∃ I ∈ B, ∑ i, c i * frequencyMap h I i ≠ 0) :
    ∃ τ : ℝ, (n : ℝ) - 1 < τ ∧ ∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ε : ℝ),
        DifferentiableOn ℂ f (complexStrip n s₀ ×ˢ actionNbhd B r₀) →
        (∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ∀ k : Fin n → ℤ,
          f (z.1 + (fun i => (k i : ℂ)), z.2) = f z) →
        (∀ θ I : Fin n → ℝ,
          ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀ →
          (f ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0) →
        (∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ‖f z‖ ≤ ε) → ε ≤ ε₀ →
        ENNReal.ofReal ((1 / 4 : ℝ) ^ n) * volume (fundamentalDomain B) ≤
          volume (fundamentalDomain B ∩
            {z | ∃ (K : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) (ω : Fin n → ℝ) (γ : ℝ)
              (I₀ : Fin n → ℝ),
              0 < γ ∧ IsDiophantine γ τ ω ∧ IsInvariantLagrangianTorus (realHamiltonian h f) ω K ∧
              (∀ θ, ∃ J ∈ B, ‖(K θ).2 - J‖ < r₀) ∧
              I₀ ∈ B ∧ (∀ θ, ‖K θ - (θ, I₀)‖ ≤ δ) ∧ z ∈ Set.range K}) := by
  obtain ⟨τ, hτ, hS⟩ := russmann_tori_strong hn hs₀ hr₀ hB_open hB_conn hB_bdd hh hh_real
    h_russmann
  have hp0 : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ n := by positivity
  have hp1 : (1 / 4 : ℝ) ^ n < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  refine ⟨τ, hτ, fun δ hδ => ?_⟩
  obtain ⟨ε₀, hε₀, hf⟩ := hS δ hδ (1 - (1 / 4 : ℝ) ^ n) (by linarith)
  refine ⟨ε₀, hε₀, fun f ε h1 h2 h3 h4 h5 => ?_⟩
  have hfin : volume (fundamentalDomain B) ≠ ⊤ := by
    rw [volume_fundamentalDomain]; exact hB_bdd.measure_lt_top.ne
  exact quarter_le_of_diff_le hp0 hp1.le hfin (hf f ε h1 h2 h3 h4 h5)

end KAM.Russmann

end
