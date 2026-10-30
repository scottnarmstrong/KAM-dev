/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Quantitative.Assembly
public import KAM.Planetary.Quantitative.BudgetPositivity
public import KAM.Russmann.Data
public import KAM.Russmann.Domain
public import KAM.Russmann.FamilyVolume
public import KAM.Russmann.Nondegeneracy
public import KAM.Russmann.Torus
public import KAM.Frozen.Defs.FundamentalDomain

/-!
# Track R: Rüssmann's KAM theorem, assembled from track P's quantitative theorem

`russmann_tori` has exactly the hypotheses of the draft headline R-HEAD
(`docs/tracks/R/statement.md`) and its conclusion with the draft cover `russmannCover` written out
as a set-builder: for small perturbations, the points of `[0,1)ⁿ × B` lying on invariant
Lagrangian tori with `(γ, τ)`-Diophantine frequencies, `δ`-close to unperturbed tori, fill at least
the fraction `4⁻ⁿ` of its volume. It refers to no draft definition; once `russmannCover` is frozen
with the approved body, the provider of R-HEAD is this theorem (the two sets are equal by
definition).

Route (`docs/tracks/R/PROOF-ROUTE.md`): Rüssmann's non-degeneracy lemma fixes `μ` and `τ = n μ`;
a compact `K ⊆ B` of almost full measure and the compactness bounds give track P's data;
`KAM.Planetary.weak_kam_quantitative` gives the family of tori; the tori are frozen invariant
Lagrangian tori (`isInvariantLagrangianTorus_of_isLatticeTorus`); their union over
`[0,1)ⁿ × good` has volume `≥ (1 - 2⁻¹⁰)^{2n} meas good` and is moved into `[0,1)ⁿ × B` modulo
`ℤⁿ` without loss.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Russmann

open KAM KAM.Planetary

variable {n : ℕ}

theorem quarter_pow_lt (hn : 1 ≤ n) :
    (1 / 4 : ℝ) ^ n < (1 - (2 : ℝ) ^ (-10 : ℤ)) ^ (2 * n) := by
  have e : (1 / 4 : ℝ) ^ n = (1 / 2 : ℝ) ^ (2 * n) := by rw [pow_mul]; norm_num
  rw [e]
  exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)

/-- **Rüssmann's KAM theorem (maximal case), assembled.** The hypotheses are those of the draft
headline R-HEAD; the conclusion is R-HEAD's with the draft cover written out. -/
theorem russmann_tori (hn : 1 ≤ n) {s₀ r₀ : ℝ} (hs₀ : 0 < s₀) (hr₀ : 0 < r₀)
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
  -- Step 1: the order of non-degeneracy on `closure B` and the exponent `τ = n μ`
  obtain ⟨μ, hμ, β₀, hβ₀, hfinB⟩ :=
    russmann_finite_order_frequencyMap hr₀ hB_conn hB_bdd hh h_russmann
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hμ' : (1 : ℝ) ≤ μ := by exact_mod_cast hμ
  refine ⟨(n : ℝ) * μ, by nlinarith, fun δ hδ => ?_⟩
  -- Step 2: the compact parameter set and the measure budget
  set q : ℝ := (1 - (2 : ℝ) ^ (-10 : ℤ)) ^ (2 * n) with hqdef
  set p : ℝ := (1 / 4 : ℝ) ^ n with hpdef
  have hq : 0 < q := by rw [hqdef]; exact pow_pos (by norm_num) _
  have hp : 0 < p := by rw [hpdef]; positivity
  have hpq : p < q := quarter_pow_lt hn
  obtain ⟨K, hK, hKB, ⟨m, hm, hmarg⟩, εs, hεs, hεK, hbudget⟩ :=
    exists_compact_budget hB_open hB_bdd hB_conn.nonempty (θ := p / q) (by positivity)
      ((div_lt_one hq).2 hpq)
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
  obtain ⟨cΔ, hcΔ, hQ⟩ := weak_kam_quantitative n μ ((n : ℝ) * μ) s (max C 1)
  have hγ : 0 < d.gamma := qbc_gamma_pos hd.1
  have hth : 0 < thresholds d := qbc_thresholds_pos hd.1
  set δ' : ℝ := min δ (m / 2) with hδ'def
  have hδ' : 0 < δ' := lt_min hδ (by positivity)
  refine ⟨min (thresholds d) ((δ' * d.gamma / cΔ) ^ 2), lt_min hth (by positivity), ?_⟩
  intro f ε hf hf_per hf_real hf_bd hε
  -- Step 4: the family of tori
  obtain ⟨b₀, hb₀⟩ := hB_conn.nonempty
  have hε0 : 0 ≤ ε := by
    refine (norm_nonneg _).trans (hf_bd (0, fun i => (b₀ i : ℂ)) ⟨fun i => ?_, b₀, hb₀, ?_⟩)
    · simpa using hs₀
    · simpa using hr₀
  have hQI : QuantitativeInput d h f :=
    russmannData_input hKB hϑ0 hϑr hss hh hh_real hf hf_per hf_real (min_le_left _ _)
      (fun c hc y hy => hfinB c hc y (subset_closure (hKB hy))) hA (le_max_left _ _)
      (le_max_left _ _) hC (le_max_left _ _)
  have hU : complexStrip n d.s ×ˢ actionNbhd d.K (2 * d.vartheta) ⊆
      complexStrip n s₀ ×ˢ actionNbhd B r₀ := by
    refine prod_mono (fun θ hθ i => (hθ i).trans_le hss) ?_
    rintro I ⟨J, hJ, hI⟩
    exact ⟨J, hKB hJ, hI.trans hϑr⟩
  obtain ⟨Q⟩ := hQ d hd rfl rfl rfl rfl h f hQI ε hε0 (hε.trans (min_le_left _ _))
    fun z hz => hf_bd z (hU hz)
  -- Step 5: displacement, cover membership, actions in `B`
  have hdisp : ∀ b ∈ Q.good, ∀ θ, ‖Q.torus b θ - (θ, b)‖ ≤ δ' := by
    intro b hb θ
    refine (Q.displacement b hb θ).trans ((min_le_right _ _).trans ?_)
    have hsq : Real.sqrt ε ≤ δ' * d.gamma / cΔ := by
      rw [← Real.sqrt_sq (show 0 ≤ δ' * d.gamma / cΔ by positivity)]
      exact Real.sqrt_le_sqrt (hε.trans (min_le_right _ _))
    rw [div_le_iff₀ hγ]
    calc cΔ * Real.sqrt ε ≤ cΔ * (δ' * d.gamma / cΔ) := by gcongr
      _ = δ' * d.gamma := by field_simp
  have hmem : ∀ z ∈ (fun z : (Fin n → ℝ) × (Fin n → ℝ) => Q.torus z.2 z.1) ''
      (unitCube n ×ˢ Q.good), ∀ k : Fin n → ℤ, z + angleTranslate k ∈
      {z | ∃ (K : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) (ω : Fin n → ℝ) (γ : ℝ)
        (I₀ : Fin n → ℝ),
        0 < γ ∧ IsDiophantine γ ((n : ℝ) * μ) ω ∧
        IsInvariantLagrangianTorus (realHamiltonian h f) ω K ∧
        (∀ θ, ∃ J ∈ B, ‖(K θ).2 - J‖ < r₀) ∧
        I₀ ∈ B ∧ (∀ θ, ‖K θ - (θ, I₀)‖ ≤ δ) ∧ z ∈ Set.range K} := by
    rintro _ ⟨⟨θ, b⟩, ⟨-, hb⟩, rfl⟩ k
    refine ⟨Q.torus b, Q.freq b, d.gamma, b, hγ, Q.dio b hb,
      isInvariantLagrangianTorus_of_isLatticeTorus (Q.lattice b hb), fun θ' => ?_,
      hKB (Q.subset hb), fun θ' => (hdisp b hb θ').trans (min_le_left _ _),
      ⟨θ + fun i => (k i : ℝ), (Q.lattice b hb).2.1 θ k⟩⟩
    obtain ⟨J, hJ, hlt⟩ := ((Q.lattice b hb).1.2 θ').1
    refine ⟨J, hKB hJ, ?_⟩
    have : ‖realInclusion n (Q.torus b θ').2 - realInclusion n J‖ < 2 * ϑ := hlt
    rw [← map_sub, norm_realInclusion] at this
    exact this.trans hϑr
  have hBz : ∀ z ∈ (fun z : (Fin n → ℝ) × (Fin n → ℝ) => Q.torus z.2 z.1) ''
      (unitCube n ×ˢ Q.good), z.2 ∈ B := by
    rintro _ ⟨⟨θ, b⟩, ⟨-, hb⟩, rfl⟩
    refine hmarg b (Q.subset hb) _ (lt_of_le_of_lt ?_ (half_lt_self hm))
    calc ‖(Q.torus b θ).2 - b‖ ≤ ‖Q.torus b θ - (θ, b)‖ := by
          simpa using norm_snd_le (Q.torus b θ - (θ, b))
      _ ≤ δ' := hdisp b hb θ
      _ ≤ m / 2 := min_le_right _ _
  have hvol := volume_le_volume_fundamentalDomain_inter Q.borel
    (familyImage_eq_add_angleTranslate Q) hmem hBz
  -- Step 6: the volume bound
  have hfin : volume B ≠ ⊤ := hB_bdd.measure_lt_top.ne
  have hFD : ENNReal.ofReal p * volume (fundamentalDomain B) =
      ENNReal.ofReal q * ENNReal.ofReal (p / q * (volume B).toReal) := by
    rw [volume_fundamentalDomain, ← ENNReal.ofReal_mul hq.le, ← mul_assoc,
      mul_div_cancel₀ _ hq.ne', ENNReal.ofReal_mul hp.le, ENNReal.ofReal_toReal hfin]
  calc ENNReal.ofReal p * volume (fundamentalDomain B)
      = ENNReal.ofReal q * ENNReal.ofReal (p / q * (volume B).toReal) := hFD
    _ ≤ ENNReal.ofReal q * volume Q.good := by gcongr; exact hbudget Q.good Q.measure
    _ ≤ _ := familyImage_volume_lower Q
    _ ≤ _ := hvol

end KAM.Russmann

end
