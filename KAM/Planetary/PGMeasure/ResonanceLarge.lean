/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGMeasure.LatticeTail
public import KAM.Planetary.PGMeasure.ResonanceLarge.Sections

/-!
# P Part 4: the large-mode resonances `ℛ^(B)` (`stepP:p4:dm-Bstruct`, `stepP:p4:dm-B`)

Internal helpers for `two_scale_diophantine_measure` (consumed by P4-M). Design
`docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P4-RB.

* `large_mode_structure` (`stepP:p4:dm-Bstruct`): structure of the modes `𝒦_B`.
* `largeSection`, `volume_largeSection_le` (`stepP:p4:dm-B`): slicing in a slow coordinate.
* `large_modes_measure_le` (`stepP:p4:dm-B`, final display; Lemma `lattice-tail`(b)): the union
  of the frequency-coordinate resonant sets `ℛ'_k`, `k ∈ 𝒦_B`, has measure at most
  bound `4b²L_β (2R_y)^a C_T (4Λ_NΛ_g)^{τ+1-n} α₁ μ^{τ-n} λ⁻¹ (2λ)^b`.
  The factor `Λ_g^n` from the Lipschitz image (`stepP:p4:dm-y`) and the division by `vol core` in
  `c₁` are applied by P4-M.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

/-- `stepP:p4:dm-B`: a large mode's resonant set is covered by its slow sections (N3). -/
theorem resonanceSet_subset_largeSection (d : MeasureData a b) {mu : ℝ}
    (hmu : mu ∈ Ioc 0 d.mu1) (Q : Set (Fin b → ℝ)) (k : Fin (a+b) → ℤ) (alpha : ℝ) :
    resonanceSet d mu Q k alpha ⊆ ⋃ j, largeSection d mu Q k alpha j := by
  intro z hz
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ
    (fun j => ‖((d.beta mu (d.g (blockFast z))).transpose.mulVec (kSlow k)) j‖)
    ⟨⟨0, d.hb⟩, Finset.mem_univ _⟩
  have hnorm : ‖(d.beta mu (d.g (blockFast z))).transpose.mulVec (kSlow k)‖ =
      |((d.beta mu (d.g (blockFast z))).transpose.mulVec (kSlow k)) j| := by
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun i => ?_) ?_
    · simpa using hj i (Finset.mem_univ _)
    · simpa using norm_le_pi_norm ((d.beta mu (d.g (blockFast z))).transpose.mulVec (kSlow k)) j
  have hN3 := d.N3 mu hmu (d.g (blockFast z)) (freqCore_spec d hz.1).1 (kSlow k)
  refine mem_iUnion.mpr ⟨j, hz, ?_⟩
  show ‖kSlow k‖ / d.LB ≤ |colCoeff d mu (kSlow k) j z|
  rw [colCoeff_eq, ← hnorm, div_le_iff₀ (by linarith [d.hLB])]
  linarith

theorem latticeWeight_succ_eq (k : Fin (a+b) → ℤ) (tau : ℝ) (hk : 0 < l1 k) :
    latticeWeight (tau + 1) k = (l1 k ^ tau * l1 k)⁻¹ := by
  unfold latticeWeight
  have : (∑ i, |(k i : ℝ)|) = l1 k := rfl
  rw [this, Real.rpow_neg hk.le, Real.rpow_add_one hk.ne']

/-- One large mode: `μ(ℛ'_k) ≤ (8 b² L_β α₁ μ⁻¹ (2R_y)^a (2λ)^(b-1)) · |k|₁^(-τ-1)`
(`stepP:p4:dm-B`, per mode, summed over the `b` slow coordinates). -/
theorem volume_resonanceSet_large_le (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1)
    {lambda : ℝ} (hl : 0 < lambda) (hl0 : lambda ≤ d.lambda0) {Q : Set (Fin b → ℝ)}
    (hQm : MeasurableSet Q) (hQsub : Q ⊆ actionShell b (-lambda) lambda)
    {k : Fin (a+b) → ℤ} (hk : k ∈ largeModes a b mu d.LN d.Lg) {alpha1 : ℝ} (ha : 0 < alpha1) :
    volume (resonanceSet d mu Q k (alpha1 / l1 k ^ d.tau)) ≤
      ENNReal.ofReal (8 * b ^ 2 * d.LB * alpha1 / mu * ((2 * d.Ry) ^ a * (2 * lambda) ^ (b - 1)) *
        latticeWeight (d.tau + 1) k) := by
  have hmu0 := hmu.1
  obtain ⟨h1, -, h3, -⟩ := large_mode_structure d.ha d.hb hmu0 d.hLN d.hLB d.hLg
    (hmu.2.trans d.small) hk
  have hl1 : 0 < l1 k := by
    by_contra hc
    have h0 : l1 k = 0 := le_antisymm (not_lt.mp hc) (l1_nonneg k)
    rw [h0] at h1; linarith
  have hbR : (0:ℝ) < b := by exact_mod_cast d.hb
  have hkS : 0 < ‖kSlow k‖ := by
    by_contra hc
    have h0 : ‖kSlow k‖ = 0 := le_antisymm (not_lt.mp hc) (norm_nonneg _)
    rw [h0] at h3; nlinarith
  have hLB : 0 < d.LB := by linarith [d.hLB]
  have hpow : 0 < l1 k ^ d.tau := Real.rpow_pos_of_pos hl1 _
  have halpha : 0 < alpha1 / l1 k ^ d.tau := by positivity
  have hRy := d.hRy
  refine (measure_mono (resonanceSet_subset_largeSection d hmu Q k _)).trans ?_
  refine (measure_iUnion_fintype_le _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => volume_largeSection_le d hmu hl hl0 hQm hQsub hk halpha
      j).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [latticeWeight_succ_eq k d.tau hl1]
  set B : ℝ := (2 * d.Ry) ^ a * (2 * lambda) ^ (b - 1) with hB
  have hB0 : 0 ≤ B := by positivity
  have hd : 4 * d.LB * (alpha1 / l1 k ^ d.tau) / (mu * ‖kSlow k‖) ≤
      8 * b * d.LB * alpha1 / mu * (l1 k ^ d.tau * l1 k)⁻¹ := by
    rw [div_le_iff₀ (by positivity)]
    have : 8 * b * d.LB * alpha1 / mu * (l1 k ^ d.tau * l1 k)⁻¹ * (mu * ‖kSlow k‖) =
        4 * d.LB * (alpha1 / l1 k ^ d.tau) * (2 * b * ‖kSlow k‖ / l1 k) := by
      field_simp; ring
    rw [this]
    have : 1 ≤ 2 * b * ‖kSlow k‖ / l1 k := by rw [le_div_iff₀ hl1]; linarith
    have h0 : 0 ≤ 4 * d.LB * (alpha1 / l1 k ^ d.tau) := by positivity
    nlinarith
  calc (b : ℝ) * (4 * d.LB * (alpha1 / l1 k ^ d.tau) / (mu * ‖kSlow k‖) * B)
      ≤ b * (8 * b * d.LB * alpha1 / mu * (l1 k ^ d.tau * l1 k)⁻¹ * B) := by gcongr
    _ = _ := by ring

theorem one_le_inv_two_mul {d : MeasureData a b} {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1) :
    1 ≤ (2 * mu * d.LN * d.Lg)⁻¹ := by
  have hmu0 := hmu.1
  have hsm := hmu.2.trans d.small
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast d.ha
  have hM : 0 ≤ 2 * (b : ℝ) * d.LN * d.LB := by have := d.hLN; have := d.hLB; positivity
  have hpos : 0 < 2 * (1 + 2 * (b : ℝ) * d.LN * d.LB) * a * d.LN * d.Lg := by
    have := d.hLN; have := d.hLg; positivity
  have h1 : mu * (2 * (1 + 2 * (b : ℝ) * d.LN * d.LB) * a * d.LN * d.Lg) ≤ 1 := by
    calc _ ≤ (2 * (1 + 2 * (b : ℝ) * d.LN * d.LB) * a * d.LN * d.Lg)⁻¹ *
          (2 * (1 + 2 * (b : ℝ) * d.LN * d.LB) * a * d.LN * d.Lg) := by gcongr
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  have h2 : 2 * mu * d.LN * d.Lg ≤ 1 := by
    have hq : 0 < mu * (2 * d.LN * d.Lg) := by have := d.hLN; have := d.hLg; positivity
    have hf : 1 ≤ (1 + 2 * (b : ℝ) * d.LN * d.LB) * a := by nlinarith
    nlinarith
  rw [one_le_inv₀ (by have := d.hLN; have := d.hLg; positivity)]
  exact h2

/-- Summability of the shifted lattice weight over a real-cutoff tail (from `lattice_tail`). -/
theorem summable_latticeWeight_tail {n : ℕ} (hn : 0 < n) {tau : ℝ} (ht : (n : ℝ) < tau + 1)
    {m : ℝ} (hm : 1 ≤ m) :
    Summable (fun k : {k : Fin n → ℤ // m < ∑ i, |(k i : ℝ)|} => latticeWeight (tau + 1) k.val)
        := by
  have hs := (lattice_tail hn (tau := tau + 1) ht).1
  have hne : ∀ k : {k : Fin n → ℤ // m < ∑ i, |(k i : ℝ)|}, k.1 ≠ 0 := by
    intro k h
    have h2 : m < ∑ i, |((k.1 i : ℤ) : ℝ)| := k.2
    have h3 : ∑ i, |((k.1 i : ℤ) : ℝ)| = 0 := by simp [h]
    linarith
  have hinj : Function.Injective
      (fun k : {k : Fin n → ℤ // m < ∑ i, |(k i : ℝ)|} => (⟨k.1, hne k⟩ : {k : Fin n → ℤ // k ≠
          0})) :=
    fun x y h => Subtype.ext (Subtype.mk.inj h)
  have h2 := Summable.comp_injective hs hinj
  exact h2

/-- `stepP:p4:dm-B` and Lemma `lattice-tail`(b): the union over the large modes of the
frequency-coordinate resonant sets (without the factors `Λ_g^n` and `vol core` of `c₁`). -/
theorem large_modes_measure_le (d : MeasureData a b) {mu : ℝ} (hmu : mu ∈ Ioc 0 d.mu1)
    {lambda : ℝ} (hl : 0 < lambda) (hl0 : lambda ≤ d.lambda0) {Q : Set (Fin b → ℝ)}
    (hQm : MeasurableSet Q) (hQsub : Q ⊆ actionShell b (-lambda) lambda)
    {alpha1 : ℝ} (ha : 0 < alpha1) :
    volume (⋃ k ∈ largeModes a b mu d.LN d.Lg, resonanceSet d mu Q k (alpha1 / l1 k ^ d.tau)) ≤
      ENNReal.ofReal (4 * b ^ 2 * d.LB * (2 * d.Ry) ^ a *
        (2 * 3 ^ (a + b - 1) / (d.tau + 1 - ((a + b : ℕ) : ℝ))) *
        (4 * d.LN * d.Lg) ^ (d.tau + 1 - ((a + b : ℕ) : ℝ)) * alpha1 *
        mu ^ (d.tau - ((a + b : ℕ) : ℝ)) / lambda * (2 * lambda) ^ b) := by
  have hmu0 := hmu.1
  have hn : 0 < a + b := by have := d.ha; omega
  have hLNg : 0 < d.LN * d.Lg := by have := d.hLN; have := d.hLg; positivity
  set m : ℝ := (2 * mu * d.LN * d.Lg)⁻¹ with hm
  have hm1 : 1 ≤ m := one_le_inv_two_mul hmu
  have htail := (lattice_tail (n := a + b) hn (tau := d.tau) d.htau).2.2 m hm1
  set c : ℝ := 8 * b ^ 2 * d.LB * alpha1 / mu * ((2 * d.Ry) ^ a * (2 * lambda) ^ (b - 1)) with hc
  have hc0 : 0 ≤ c := by have := d.hLB; have := d.hRy; positivity
  have hsumm := summable_latticeWeight_tail hn (tau := d.tau) (by
    have := d.htau; push_cast at this ⊢; linarith) hm1
  have hcover : (⋃ k ∈ largeModes a b mu d.LN d.Lg,
      resonanceSet d mu Q k (alpha1 / l1 k ^ d.tau)) ⊆
      ⋃ k : {k : Fin (a+b) → ℤ // m < ∑ i, |(k i : ℝ)|}, ⋃ (_ : k.1 ∈ largeModes a b mu d.LN d.Lg),
        resonanceSet d mu Q k.1 (alpha1 / l1 k.1 ^ d.tau) := by
    intro z hz
    simp only [mem_iUnion] at hz ⊢
    obtain ⟨k, hk, hz⟩ := hz
    have h1 := (large_mode_structure d.ha d.hb hmu0 d.hLN d.hLB d.hLg (hmu.2.trans d.small) hk).1
    refine ⟨⟨k, ?_⟩, hk, hz⟩
    show m < l1 k
    have hpos : 0 < 2 * mu * d.LN * d.Lg := by have := d.hLN; have := d.hLg; positivity
    rw [hm, inv_lt_iff_one_lt_mul₀ hpos]
    nlinarith
  refine (measure_mono hcover).trans ((measure_iUnion_le _).trans ?_)
  have hterm : ∀ k : {k : Fin (a+b) → ℤ // m < ∑ i, |(k i : ℝ)|},
      volume (⋃ (_ : k.1 ∈ largeModes a b mu d.LN d.Lg),
        resonanceSet d mu Q k.1 (alpha1 / l1 k.1 ^ d.tau)) ≤
      ENNReal.ofReal (c * latticeWeight (d.tau + 1) k.1) := by
    intro k
    by_cases hk : k.1 ∈ largeModes a b mu d.LN d.Lg
    · simpa [hk] using volume_resonanceSet_large_le d hmu hl hl0 hQm hQsub hk ha
    · simp [hk]
  refine (ENNReal.tsum_le_tsum hterm).trans ?_
  have hw : ∀ k : {k : Fin (a+b) → ℤ // m < ∑ i, |(k i : ℝ)|}, 0 ≤ latticeWeight (d.tau + 1) k.1 :=
    fun k => Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hc0 (hw k)) (hsumm.mul_left c),
    tsum_mul_left]
  refine ENNReal.ofReal_le_ofReal ?_
  refine (mul_le_mul_of_nonneg_left htail hc0).trans (le_of_eq ?_)
  have hdiv : 2 / m = 4 * mu * d.LN * d.Lg := by
    rw [hm]; field_simp; ring
  rw [hdiv]
  have he : 0 < d.tau + 1 - ((a + b : ℕ) : ℝ) := by have := d.htau; linarith
  have hmpow : (4 * mu * d.LN * d.Lg) ^ (d.tau + 1 - ((a + b : ℕ) : ℝ)) =
      mu ^ (d.tau - ((a + b : ℕ) : ℝ)) * mu * (4 * d.LN * d.Lg) ^ (d.tau + 1 - ((a + b : ℕ) :
          ℝ)) := by
    rw [show 4 * mu * d.LN * d.Lg = mu * (4 * d.LN * d.Lg) by ring,
      Real.mul_rpow hmu0.le (by have := d.hLN; have := d.hLg; positivity)]
    rw [show d.tau + 1 - ((a + b : ℕ) : ℝ) = (d.tau - ((a + b : ℕ) : ℝ)) + 1 by ring,
      Real.rpow_add_one hmu0.ne']
  rw [hmpow, hc]
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by have := d.hb; omega⟩
  generalize (2 * 3 ^ (a + (b' + 1) - 1) / (d.tau + 1 - ((a + (b' + 1) : ℕ) : ℝ))) = Ct
  generalize (4 * d.LN * d.Lg) ^ (d.tau + 1 - ((a + (b' + 1) : ℕ) : ℝ)) = P
  generalize mu ^ (d.tau - ((a + (b' + 1) : ℕ) : ℝ)) = M
  simp only [Nat.add_sub_cancel, pow_succ]
  field_simp
  ring

end KAM.Planetary

end
