/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.ODE.Basic
public import KAM.Measure.Lipschitz

/-!
# Unions of tori over a Lipschitz family

`bpP:p1:torus-union`. For `E ⊆ ℝᵈ` null measurable and `F : Phase d → Phase d` Lipschitz on the
product `E × [0,1)ᵈ`, the image `F (E × [0,1)ᵈ)` is null measurable with volume at most
`Λ ^ (2 d) · vol E` (`torus_union`); it is Borel under σ-compactness of `E` (B1) or Borel `E`
with injectivity (B2); a lower Lipschitz bound gives the matching lower estimate
(`torus_union_lower`); and the union of whole tori is the lattice saturation of the cell image
(`torus_union_saturation`, `nullMeasurableSet_torus_union_saturation`).

Proof plan. The upper bound is `KAM.lip_image_prod` on `E × [0,1)ᵈ`, valid for any sign of `Λ`
(so no McShane extension is needed). Measurability: a null measurable set is a σ-compact set plus
a null set (inner regularity); `F` maps the σ-compact part to a σ-compact (hence Borel) set and
the null part to a null set. The lower bound applies `lip_image_prod` to a left inverse.
-/

@[expose] public noncomputable section

open Set Real MeasureTheory Function

namespace KAM.Planetary

open KAM KAM.ODE

section TorusUnion

variable {d : ℕ}

/-- `[0,1)^d`. -/
def unitCube (d : ℕ) : Set (Fin d → ℝ) := Set.pi univ fun _ => Ico (0 : ℝ) 1

theorem measurableSet_unitCube : MeasurableSet (unitCube d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem volume_unitCube : volume (unitCube d) = 1 := by
  simp [unitCube, Real.volume_pi_Ico]

theorem volume_prod_unitCube (E : Set (Fin d → ℝ)) : volume (E ×ˢ unitCube d) = volume E := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, volume_unitCube, mul_one]

theorem nullMeasurableSet_prod_unitCube {E : Set (Fin d → ℝ)} (hE : NullMeasurableSet E) :
    NullMeasurableSet (E ×ˢ unitCube d) := by
  rw [Measure.volume_eq_prod]
  exact hE.prod measurableSet_unitCube.nullMeasurableSet

theorem isSigmaCompact_unitCube : IsSigmaCompact (unitCube d) := by
  have h : unitCube d = ⋃ m : ℕ, Icc (0 : Fin d → ℝ) (fun _ => 1 - 1 / ((m : ℝ) + 1)) := by
    ext x
    simp only [unitCube, mem_pi, mem_univ, true_implies, mem_Ico, mem_iUnion, mem_Icc, Pi.le_def,
      Pi.zero_apply]
    constructor
    · intro h
      have hm : ∀ i, ∃ m : ℕ, x i ≤ 1 - 1 / ((m : ℝ) + 1) := fun i => by
        obtain ⟨m, hm⟩ := exists_nat_gt (1 / (1 - x i))
        have h1 : 0 < 1 - x i := by linarith [(h i).2]
        rw [div_lt_iff₀ h1] at hm
        refine ⟨m, ?_⟩
        have : 1 / ((m : ℝ) + 1) ≤ 1 - x i :=
          (div_le_iff₀ (by positivity)).2 (by nlinarith [Nat.cast_nonneg (α := ℝ) m])
        linarith
      choose m hm using hm
      obtain ⟨M, hM⟩ := Finite.exists_le m
      refine ⟨M, fun i => (h i).1, fun i => (hm i).trans ?_⟩
      have : (m i : ℝ) ≤ M := by exact_mod_cast hM i
      have := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (m i : ℝ) + 1)
        (by linarith : (m i : ℝ) + 1 ≤ M + 1)
      linarith
    · rintro ⟨m, hm0, hm⟩ i
      refine ⟨hm0 i, lt_of_le_of_lt (hm i) ?_⟩
      have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      linarith
  rw [h]
  exact isSigmaCompact_iUnion_of_isCompact _ fun m => isCompact_Icc

theorem isSigmaCompact_prod_unitCube {E : Set (Fin d → ℝ)} (hE : IsSigmaCompact E) :
    IsSigmaCompact (E ×ˢ unitCube d) := by
  obtain ⟨K, hK, hKE⟩ := hE
  obtain ⟨C, hC, hCE⟩ := (isSigmaCompact_unitCube (d := d))
  have h : E ×ˢ unitCube d = ⋃ p : ℕ × ℕ, K p.1 ×ˢ C p.2 := by
    ext ⟨a, b⟩
    have ha : a ∈ E ↔ ∃ n, a ∈ K n := by rw [← hKE]; simp
    have hb : b ∈ unitCube d ↔ ∃ n, b ∈ C n := by rw [← hCE]; simp
    simp only [mem_prod, mem_iUnion, Prod.exists, ha, hb]
    constructor
    · rintro ⟨⟨n, hn⟩, ⟨m, hm⟩⟩
      exact ⟨n, m, hn, hm⟩
    · rintro ⟨n, m, hn, hm⟩
      exact ⟨⟨n, hn⟩, ⟨m, hm⟩⟩
  rw [h]
  exact isSigmaCompact_iUnion_of_isCompact _ fun p => (hK p.1).prod (hC p.2)

theorem measurableSet_of_isSigmaCompact {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [T2Space X] {s : Set X} (hs : IsSigmaCompact s) :
    MeasurableSet s := by
  obtain ⟨K, hK, rfl⟩ := hs
  exact MeasurableSet.iUnion fun n => (hK n).isClosed.measurableSet

theorem lipschitzOnWith_of_bound {S : Set (Phase d)} {F : Phase d → Phase d} {Λ : ℝ}
    (hF : ∀ x ∈ S, ∀ y ∈ S, ‖F x - F y‖ ≤ Λ * ‖x - y‖) :
    LipschitzOnWith (Real.toNNReal Λ) F S := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [dist_eq_norm, dist_eq_norm]
  exact (hF x hx y hy).trans
    (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal Λ) (norm_nonneg _))

/-- A measurable set is a σ-compact set up to a null set. -/
theorem exists_isSigmaCompact_subset_null {t : Set (Phase d)} (ht : MeasurableSet t) :
    ∃ B, IsSigmaCompact B ∧ B ⊆ t ∧ volume (t \ B) = 0 := by
  have : (volume : Measure (Phase d)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have key : ∀ n m : ℕ, ∃ K, K ⊆ t ∩ Metric.closedBall (0 : Phase d) n ∧ IsCompact K ∧
      volume ((t ∩ Metric.closedBall (0 : Phase d) n) \ K) < (m : ENNReal)⁻¹ := fun n m => by
    have hfin : volume (t ∩ Metric.closedBall (0 : Phase d) n) ≠ ⊤ :=
      ((measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top).ne
    exact (ht.inter Metric.isClosed_closedBall.measurableSet).exists_isCompact_sdiff_lt hfin
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top m))
  choose K hKsub hKc hKm using key
  refine ⟨⋃ p : ℕ × ℕ, K p.1 p.2, isSigmaCompact_iUnion_of_isCompact _ fun p => hKc _ _,
    iUnion_subset fun p => (hKsub _ _).trans inter_subset_left, ?_⟩
  have hsub : t \ ⋃ p : ℕ × ℕ, K p.1 p.2 ⊆
      ⋃ n : ℕ, (t ∩ Metric.closedBall (0 : Phase d) n) \ ⋃ p : ℕ × ℕ, K p.1 p.2 := by
    rintro z ⟨hz, hzB⟩
    obtain ⟨n, hn⟩ := exists_nat_ge ‖z‖
    exact mem_iUnion.2 ⟨n, ⟨hz, by simpa using hn⟩, hzB⟩
  refine measure_mono_null hsub (measure_iUnion_null fun n => ?_)
  refine le_antisymm (ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun m => ?_) bot_le
  refine (measure_mono (sdiff_subset_sdiff_right (subset_iUnion (fun p : ℕ × ℕ => K p.1 p.2)
    (n, m)))).trans (hKm n m).le

/-- The image of a null measurable set under a map Lipschitz on it is null measurable. -/
theorem nullMeasurableSet_image_of_lipschitzOn {S : Set (Phase d)} (hS : NullMeasurableSet S)
    {F : Phase d → Phase d} {Λ : ℝ}
    (hF : ∀ x ∈ S, ∀ y ∈ S, ‖F x - F y‖ ≤ Λ * ‖x - y‖) : NullMeasurableSet (F '' S) := by
  obtain ⟨t, hts, ht, hteq⟩ := hS.exists_measurable_subset_ae_eq
  obtain ⟨B, hB, hBt, hBn⟩ := exists_isSigmaCompact_subset_null ht
  have hcont : ContinuousOn F S := (lipschitzOnWith_of_bound hF).continuousOn
  have hBS : B ⊆ S := hBt.trans hts
  have hSB : volume (S \ B) = 0 := by
    have h1 : volume (S \ t) = 0 := (ae_eq_set.1 hteq).2
    refine measure_mono_null ?_ (measure_union_null h1 hBn)
    intro z ⟨hz, hzB⟩
    by_cases hzt : z ∈ t
    · exact Or.inr ⟨hzt, hzB⟩
    · exact Or.inl ⟨hz, hzt⟩
  have h1 : MeasurableSet (F '' B) :=
    measurableSet_of_isSigmaCompact (hB.image_of_continuousOn (hcont.mono hBS))
  have h2 : volume (F '' (S \ B)) = 0 := by
    refine le_antisymm ((lip_image_prod fun x hx y hy => hF x hx.1 y hy.1).trans ?_) bot_le
    rw [hSB, mul_zero]
  have h3 : F '' S = F '' B ∪ F '' (S \ B) := by
    rw [← image_union, union_sdiff_cancel hBS]
  rw [h3]
  exact h1.nullMeasurableSet.union (NullMeasurableSet.of_null h2)

/-- `bpP:p1:torus-union`: measurability and the upper bound (`tu-ext`, `tu-meas`, `tu-bounds`). -/
theorem torus_union {E : Set (Fin d → ℝ)} (hE : NullMeasurableSet E) {F : Phase d → Phase d}
    {Λ : ℝ} (hF : ∀ x ∈ E ×ˢ unitCube d, ∀ y ∈ E ×ˢ unitCube d, ‖F x - F y‖ ≤ Λ * ‖x - y‖) :
    NullMeasurableSet (F '' (E ×ˢ unitCube d)) ∧
      volume (F '' (E ×ˢ unitCube d)) ≤ ENNReal.ofReal (Λ ^ (2 * d)) * volume E :=
  ⟨nullMeasurableSet_image_of_lipschitzOn (nullMeasurableSet_prod_unitCube hE) hF,
    by simpa only [volume_prod_unitCube] using lip_image_prod hF⟩

/-- (B1): `E` σ-compact gives a σ-compact, hence Borel, image (no injectivity). -/
theorem torus_union_measurableSet_of_sigmaCompact {E : Set (Fin d → ℝ)} (hE : IsSigmaCompact E)
    {F : Phase d → Phase d} {Λ : ℝ}
    (hF : ∀ x ∈ E ×ˢ unitCube d, ∀ y ∈ E ×ˢ unitCube d, ‖F x - F y‖ ≤ Λ * ‖x - y‖) :
    IsSigmaCompact (F '' (E ×ˢ unitCube d)) ∧ MeasurableSet (F '' (E ×ˢ unitCube d)) := by
  have h := (isSigmaCompact_prod_unitCube hE).image_of_continuousOn
    (lipschitzOnWith_of_bound hF).continuousOn
  exact ⟨h, measurableSet_of_isSigmaCompact h⟩

/-- (B2): `E` Borel and `F` injective on `A` give a Borel image. -/
theorem torus_union_measurableSet_of_injOn {E : Set (Fin d → ℝ)} (hE : MeasurableSet E)
    {F : Phase d → Phase d} {Λ : ℝ}
    (hF : ∀ x ∈ E ×ˢ unitCube d, ∀ y ∈ E ×ˢ unitCube d, ‖F x - F y‖ ≤ Λ * ‖x - y‖)
    (hinj : InjOn F (E ×ˢ unitCube d)) : MeasurableSet (F '' (E ×ˢ unitCube d)) :=
  (hE.prod measurableSet_unitCube).image_of_continuousOn_injOn
    (lipschitzOnWith_of_bound hF).continuousOn hinj

/-- Lower bound under a lower Lipschitz bound. -/
theorem torus_union_lower {E : Set (Fin d → ℝ)} (hE : NullMeasurableSet E) {F : Phase d → Phase d}
    {Λ lam : ℝ} (hF : ∀ x ∈ E ×ˢ unitCube d, ∀ y ∈ E ×ˢ unitCube d, ‖F x - F y‖ ≤ Λ * ‖x - y‖)
    (hlam : 0 < lam)
    (hlow : ∀ x ∈ E ×ˢ unitCube d, ∀ y ∈ E ×ˢ unitCube d, lam * ‖x - y‖ ≤ ‖F x - F y‖) :
    ENNReal.ofReal (lam ^ (2 * d)) * volume E ≤ volume (F '' (E ×ˢ unitCube d)) ∧
      (0 < volume (F '' (E ×ˢ unitCube d)) ↔ 0 < volume E) ∧
      (volume (F '' (E ×ˢ unitCube d)) < ⊤ ↔ volume E < ⊤) := by
  have hup := (torus_union hE hF).2
  have hinj : InjOn F (E ×ˢ unitCube d) := fun x hx y hy hxy => by
    have h := hlow x hx y hy
    rw [hxy, sub_self, norm_zero] at h
    have : ‖x - y‖ ≤ 0 := by nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  have hg : ∀ u ∈ F '' (E ×ˢ unitCube d), ∀ v ∈ F '' (E ×ˢ unitCube d),
      ‖invFunOn F (E ×ˢ unitCube d) u - invFunOn F (E ×ˢ unitCube d) v‖ ≤ lam⁻¹ * ‖u - v‖ := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hinj.leftInvOn_invFunOn hx, hinj.leftInvOn_invFunOn hy, inv_mul_eq_div,
      le_div_iff₀ hlam]
    linarith [hlow x hx y hy]
  have himg : invFunOn F (E ×ˢ unitCube d) '' (F '' (E ×ˢ unitCube d)) = E ×ˢ unitCube d :=
    hinj.leftInvOn_invFunOn.image_image
  have h1 := lip_image_prod hg
  rw [himg, volume_prod_unitCube] at h1
  have hlow' : ENNReal.ofReal (lam ^ (2 * d)) * volume E ≤ volume (F '' (E ×ˢ unitCube d)) := by
    calc ENNReal.ofReal (lam ^ (2 * d)) * volume E
        ≤ ENNReal.ofReal (lam ^ (2 * d)) *
            (ENNReal.ofReal ((lam⁻¹) ^ (2 * d)) * volume (F '' (E ×ˢ unitCube d))) := by
          gcongr
      _ = volume (F '' (E ×ˢ unitCube d)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
            mul_inv_cancel₀ hlam.ne', one_pow, ENNReal.ofReal_one, one_mul]
  have hc : ENNReal.ofReal (lam ^ (2 * d)) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hlam _)).ne'
  refine ⟨hlow', ⟨fun hV => ?_, fun hE0 => ?_⟩, ⟨fun hV => ?_, fun hVE => ?_⟩⟩
  · by_contra h
    rw [not_lt, nonpos_iff_eq_zero] at h
    rw [h, mul_zero] at hup
    exact hV.ne' (le_zero_iff.1 hup)
  · exact lt_of_lt_of_le (ENNReal.mul_pos hc hE0.ne') hlow'
  · by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h, ENNReal.mul_top hc] at hlow'
    exact hV.ne (top_le_iff.1 hlow')
  · exact lt_of_le_of_lt hup (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hVE)

/-- Saturation: the union of whole tori is the lattice saturation of the cell image. -/
theorem torus_union_saturation {E : Set (Fin d → ℝ)} {F : Phase d → Phase d}
    (hper : ∀ ω ∈ E, ∀ ϑ (k : Fin d → ℤ),
      F (ω, ϑ + fun i => (k i : ℝ)) = F (ω, ϑ) + angleShift k) :
    (⋃ ω ∈ E, range fun ϑ => F (ω, ϑ)) =
      ⋃ k : Fin d → ℤ, (fun z => z + angleShift k) '' (F '' (E ×ˢ unitCube d)) := by
  ext z
  simp only [mem_iUnion, mem_range, mem_image, exists_prop]
  constructor
  · rintro ⟨ω, hω, ϑ, rfl⟩
    refine ⟨fun i => ⌊ϑ i⌋, F (ω, fun i => Int.fract (ϑ i)),
      ⟨(ω, fun i => Int.fract (ϑ i)), ⟨hω, ?_⟩, rfl⟩, ?_⟩
    · intro i _
      exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    · rw [← hper ω hω]
      congr 2
      funext i
      simp
  · rintro ⟨k, _, ⟨⟨ω, ϑ⟩, ⟨hω, _⟩, rfl⟩, rfl⟩
    exact ⟨ω, hω, ϑ + fun i => (k i : ℝ), (hper ω hω ϑ k)⟩

/-- Saturation is measurable (Lebesgue; Borel if the cell image is). -/
theorem nullMeasurableSet_torus_union_saturation {E : Set (Fin d → ℝ)} (hE : NullMeasurableSet E)
    {F : Phase d → Phase d} {Λ : ℝ}
    (hF : ∀ x ∈ E ×ˢ unitCube d, ∀ y ∈ E ×ˢ unitCube d, ‖F x - F y‖ ≤ Λ * ‖x - y‖)
    (hper : ∀ ω ∈ E, ∀ ϑ (k : Fin d → ℤ),
      F (ω, ϑ + fun i => (k i : ℝ)) = F (ω, ϑ) + angleShift k) :
    NullMeasurableSet (⋃ ω ∈ E, range fun ϑ => F (ω, ϑ)) ∧
      (MeasurableSet (F '' (E ×ˢ unitCube d)) →
        MeasurableSet (⋃ ω ∈ E, range fun ϑ => F (ω, ϑ))) := by
  rw [torus_union_saturation hper]
  have : (volume : Measure (Phase d)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have himg : ∀ (k : Fin d → ℤ) (T : Set (Phase d)),
      (fun z => z + angleShift k) '' T = (fun z => z + -angleShift k) ⁻¹' T := fun k T =>
    image_add_right
  simp only [himg]
  refine ⟨NullMeasurableSet.iUnion fun k => ?_, fun hT => MeasurableSet.iUnion fun k => ?_⟩
  · exact (torus_union hE hF).1.preimage
      (measurePreserving_add_right volume (-angleShift k)).quasiMeasurePreserving
  · exact (measurable_add_const _) hT

end TorusUnion

end KAM.Planetary

end
