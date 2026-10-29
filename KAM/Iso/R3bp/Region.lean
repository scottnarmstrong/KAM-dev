/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Iso.NearCircular

/-!
# The action region and the topology of `𝒩`

Blueprint-I Part 8: `bpI:p8:A`, `bpI:p8:e-vs-k` and `bpI:p8:topology`.

* `R3bpParams`: the six source premises of I-R3BP; `RegionParams`: the weaker parameter shape
  `0 < a₋ < a₊`, `0 < e₋ < e₊ < 1` of the action region (it also holds for the enlarged
  parameters of the safe region).
* `kappa e = √(1 - e²)` and the action regions `actionRegion` (open) and `actionRegionCl`
  (closed), in the coordinates `(L, G) = (x 0, x 1)`.
* `eccOf_mem_Ioo_iff`, `eccOf_mem_Icc_iff`: `e(L, G) ∈ (e', e'')` iff `G / L ∈ (κ e'', κ e')`
  (`eccOf L G = κ (G / L)`, `κ` an involutive strictly decreasing map of `[0, 1]`).
* `isOpen_actionRegion`, `isCompact_actionRegionCl`, `closure_actionRegion_subset`,
  `actionRegionCl_subset_cone`: elementary topology of the regions.
* `mem_actionRegion_iff`, `nearCircular_eq_image_region`, `exists_delaunay_preimage`,
  `isOpen_nearCircular_region`, `nearCircular_nonempty`: the near-circular set `𝒩` is the
  Delaunay image of `ℝ² × A`, is open, and is nonempty.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Iso.R3bp

open KAM KAM.Kepler KAM.Iso

/-- The source premises of I-R3BP, verbatim (frozen binders `ha haa he hee heSmall hinner`). -/
structure R3bpParams (aMinus aPlus eMinus ePlus : ℝ) : Prop where
  ha : 0 < aMinus
  haa : aMinus < aPlus
  he : 0 < eMinus
  hee : eMinus < ePlus
  heSmall : ePlus < 1 / 4
  hinner : aPlus * (1 + ePlus) < 1

/-- The parameter shape of `bpI:p8:A` (`0 < am < ap`, `0 < em < ep < 1`); also holds for the
enlarged parameters of `bpI:p8:safe`, which are NOT `R3bpParams`. -/
structure RegionParams (aMinus aPlus eMinus ePlus : ℝ) : Prop where
  ha : 0 < aMinus
  haa : aMinus < aPlus
  he : 0 < eMinus
  hee : eMinus < ePlus
  he1 : ePlus < 1

theorem R3bpParams.region {am ap em ep : ℝ} (hp : R3bpParams am ap em ep) :
    RegionParams am ap em ep :=
  ⟨hp.ha, hp.haa, hp.he, hp.hee, lt_trans hp.heSmall (by norm_num)⟩

/-- `κ(e) = √(1 - e²)`. -/
def kappa (e : ℝ) : ℝ := Real.sqrt (1 - e ^ 2)

/-- `A(a_±, e_±)`, in `(L, G) = (x 0, x 1)` (`bpI:p8:A`). -/
def actionRegion (aMinus aPlus eMinus ePlus : ℝ) : Set (Fin 2 → ℝ) :=
  {x | Real.sqrt aMinus < x 0 ∧ x 0 < Real.sqrt aPlus ∧ kappa ePlus * x 0 < x 1 ∧
    x 1 < kappa eMinus * x 0}

/-- `A^cl(a_±, e_±)`. -/
def actionRegionCl (aMinus aPlus eMinus ePlus : ℝ) : Set (Fin 2 → ℝ) :=
  {x | Real.sqrt aMinus ≤ x 0 ∧ x 0 ≤ Real.sqrt aPlus ∧ kappa ePlus * x 0 ≤ x 1 ∧
    x 1 ≤ kappa eMinus * x 0}

/-! ### The function `κ` -/

theorem kappa_nonneg (e : ℝ) : 0 ≤ kappa e := Real.sqrt_nonneg _

theorem kappa_mem_Icc (e : ℝ) : kappa e ∈ Icc (0 : ℝ) 1 := by
  refine ⟨kappa_nonneg e, ?_⟩
  unfold kappa
  rw [Real.sqrt_le_one]
  nlinarith [sq_nonneg e]

theorem kappa_kappa {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : kappa (kappa x) = x := by
  obtain ⟨h0, h1⟩ := hx
  have h : 0 ≤ 1 - x ^ 2 := by nlinarith
  unfold kappa
  rw [Real.sq_sqrt h]
  have : 1 - (1 - x ^ 2) = x ^ 2 := by ring
  rw [this]
  exact Real.sqrt_sq h0

theorem kappa_pos {e : ℝ} (h0 : 0 < e) (h1 : e < 1) : 0 < kappa e := by
  unfold kappa
  exact Real.sqrt_pos.mpr (by nlinarith)

theorem kappa_lt_one {e : ℝ} (h0 : 0 < e) : kappa e < 1 := by
  unfold kappa
  rw [Real.sqrt_lt' one_pos]
  nlinarith [pow_pos h0 2]

theorem kappa_strictAntiOn : StrictAntiOn kappa (Icc 0 1) := by
  intro a ha b hb hab
  unfold kappa
  refine Real.sqrt_lt_sqrt ?_ ?_
  · nlinarith [hb.1, hb.2]
  · nlinarith [ha.1, ha.2, hb.1, hb.2]

/-- `eccOf L G = κ (G / L)` for `L > 0`. -/
theorem eccOf_eq_kappa {L G : ℝ} : eccOf L G = kappa (G / L) := by
  unfold eccOf kappa
  rw [div_pow]

/-- For `0 < G < L`, `G / L` lies in `(0, 1)`. -/
private theorem div_mem_Icc {L G : ℝ} (hL : 0 < L) (hG : 0 < G) (hGL : G < L) :
    G / L ∈ Icc (0 : ℝ) 1 :=
  ⟨(div_pos hG hL).le, ((div_lt_one hL).2 hGL).le⟩

/-- `bpI:p8:e-vs-k`: `e(L, G) ∈ (e', e'') ↔ G/L ∈ (κ(e''), κ(e'))`, open form, in `L, G` form. -/
theorem eccOf_mem_Ioo_iff {L G e' e'' : ℝ} (hL : 0 < L) (hG : 0 < G) (hGL : G < L)
    (he' : 0 ≤ e') (hee : e' < e'') (he'' : e'' < 1) :
    (e' < eccOf L G ∧ eccOf L G < e'') ↔ kappa e'' * L < G ∧ G < kappa e' * L := by
  have hx := div_mem_Icc hL hG hGL
  have hk := kappa_mem_Icc (G / L)
  have h1 : e' ∈ Icc (0 : ℝ) 1 := ⟨he', by linarith⟩
  have h2 : e'' ∈ Icc (0 : ℝ) 1 := ⟨he'.trans hee.le, he''.le⟩
  rw [eccOf_eq_kappa, ← lt_div_iff₀ hL, ← div_lt_iff₀ hL]
  have hA : e' < kappa (G / L) ↔ G / L < kappa e' := by
    rw [← kappa_strictAntiOn.lt_iff_gt hk h1, kappa_kappa hx]
  have hB : kappa (G / L) < e'' ↔ kappa e'' < G / L := by
    rw [← kappa_strictAntiOn.lt_iff_gt h2 hk, kappa_kappa hx]
  rw [hA, hB, and_comm]

/-- `bpI:p8:e-vs-k`, closed form. -/
theorem eccOf_mem_Icc_iff {L G e' e'' : ℝ} (hL : 0 < L) (hG : 0 < G) (hGL : G < L)
    (he' : 0 ≤ e') (hee : e' < e'') (he'' : e'' < 1) :
    (e' ≤ eccOf L G ∧ eccOf L G ≤ e'') ↔ kappa e'' * L ≤ G ∧ G ≤ kappa e' * L := by
  have hx := div_mem_Icc hL hG hGL
  have hk := kappa_mem_Icc (G / L)
  have h1 : e' ∈ Icc (0 : ℝ) 1 := ⟨he', by linarith⟩
  have h2 : e'' ∈ Icc (0 : ℝ) 1 := ⟨he'.trans hee.le, he''.le⟩
  rw [eccOf_eq_kappa, ← le_div_iff₀ hL, ← div_le_iff₀ hL]
  have hA : e' ≤ kappa (G / L) ↔ G / L ≤ kappa e' := by
    rw [← kappa_strictAntiOn.le_iff_ge hk h1, kappa_kappa hx]
  have hB : kappa (G / L) ≤ e'' ↔ kappa e'' ≤ G / L := by
    rw [← kappa_strictAntiOn.le_iff_ge h2 hk, kappa_kappa hx]
  rw [hA, hB, and_comm]

/-! ### Topology of the action regions -/

/-- `A ⊆ A^cl ⊆ 𝒞₀ = {0 < G < L}`. -/
theorem actionRegionCl_subset_cone {am ap em ep : ℝ} (hp : RegionParams am ap em ep) :
    actionRegion am ap em ep ⊆ actionRegionCl am ap em ep ∧
      actionRegionCl am ap em ep ⊆ {x | 0 < x 1 ∧ x 1 < x 0} := by
  refine ⟨fun x hx => ⟨hx.1.le, hx.2.1.le, hx.2.2.1.le, hx.2.2.2.le⟩, ?_⟩
  rintro x ⟨h1, -, h3, h4⟩
  have hx0 : 0 < x 0 := lt_of_lt_of_le (Real.sqrt_pos.mpr hp.ha) h1
  have hkep : 0 < kappa ep := kappa_pos (hp.he.trans hp.hee) hp.he1
  exact ⟨lt_of_lt_of_le (mul_pos hkep hx0) h3,
    lt_of_le_of_lt h4 (mul_lt_of_lt_one_left hx0 (kappa_lt_one hp.he))⟩

theorem isOpen_actionRegion (am ap em ep : ℝ) : IsOpen (actionRegion am ap em ep) :=
  (isOpen_lt continuous_const (continuous_apply 0)).and
    ((isOpen_lt (continuous_apply 0) continuous_const).and
      ((isOpen_lt (continuous_const.mul (continuous_apply 0)) (continuous_apply 1)).and
        (isOpen_lt (continuous_apply 1) (continuous_const.mul (continuous_apply 0)))))

/-- `A^cl` is closed. -/
theorem isClosed_actionRegionCl (am ap em ep : ℝ) : IsClosed (actionRegionCl am ap em ep) :=
  (isClosed_le continuous_const (continuous_apply 0)).and
    ((isClosed_le (continuous_apply 0) continuous_const).and
      ((isClosed_le (continuous_const.mul (continuous_apply 0)) (continuous_apply 1)).and
        (isClosed_le (continuous_apply 1) (continuous_const.mul (continuous_apply 0)))))

theorem isCompact_actionRegionCl (am ap em ep : ℝ) : IsCompact (actionRegionCl am ap em ep) := by
  refine IsCompact.of_isClosed_subset
    (isCompact_Icc (a := (0 : Fin 2 → ℝ)) (b := ![Real.sqrt ap, kappa em * Real.sqrt ap]))
    (isClosed_actionRegionCl am ap em ep) ?_
  rintro x ⟨h1, h2, h3, h4⟩
  have hx0 : 0 ≤ x 0 := (Real.sqrt_nonneg _).trans h1
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    · simpa using hx0
    · simpa using (mul_nonneg (kappa_nonneg ep) hx0).trans h3
  · intro i
    fin_cases i
    · simpa using h2
    · simpa using h4.trans (mul_le_mul_of_nonneg_left h2 (kappa_nonneg em))

theorem closure_actionRegion_subset (am ap em ep : ℝ) :
    closure (actionRegion am ap em ep) ⊆ actionRegionCl am ap em ep :=
  closure_minimal (fun _ hx => ⟨hx.1.le, hx.2.1.le, hx.2.2.1.le, hx.2.2.2.le⟩)
    (isClosed_actionRegionCl am ap em ep)

/-! ### The near-circular set -/

/-- `bpI:p8:topology` (a): in the cone, `A` is `am < L² < ap ∧ em < e < ep`. -/
theorem mem_actionRegion_iff {am ap em ep : ℝ} (hp : RegionParams am ap em ep) {x : Fin 2 → ℝ}
    (hx : 0 < x 1 ∧ x 1 < x 0) :
    x ∈ actionRegion am ap em ep ↔
      am < x 0 ^ 2 ∧ x 0 ^ 2 < ap ∧ em < eccOf (x 0) (x 1) ∧ eccOf (x 0) (x 1) < ep := by
  obtain ⟨hG, hGL⟩ := hx
  have hL : 0 < x 0 := hG.trans hGL
  have hecc := eccOf_mem_Ioo_iff hL hG hGL hp.he.le hp.hee hp.he1
  have hs1 : Real.sqrt am < x 0 ↔ am < x 0 ^ 2 := Real.sqrt_lt' hL
  have hs2 : x 0 < Real.sqrt ap ↔ x 0 ^ 2 < ap := Real.lt_sqrt hL.le
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨hs1.1 h1, hs2.1 h2, hecc.2 ⟨h3, h4⟩⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨h3', h4'⟩ := hecc.1 h3
    exact ⟨hs1.2 h1, hs2.2 h2, h3', h4'⟩

/-- `bpI:p8:topology` (a), (b): `𝒩 = 𝖰(ℝ² × A)` (`w = ((ℓ, g), (L, G))`). -/
theorem nearCircular_eq_image_region {am ap em ep : ℝ} (hp : RegionParams am ap em ep) :
    NearCircular am ap em ep = delaunay '' {w | w.2 ∈ actionRegion am ap em ep} := by
  rw [nearCircular_eq_image]
  congr 1
  ext w
  constructor
  · rintro ⟨hw, h1, h2, h3, h4⟩
    exact (mem_actionRegion_iff (x := w.2) hp hw).2 ⟨h1, h2, h3, h4⟩
  · intro hw
    have hcone : 0 < w.2 1 ∧ w.2 1 < w.2 0 :=
      (actionRegionCl_subset_cone hp).2 ((actionRegionCl_subset_cone hp).1 hw)
    exact ⟨hcone, (mem_actionRegion_iff (x := w.2) hp hcone).1 hw⟩

/-- `bpI:p8:topology` (b): every `z₀ ∈ 𝒩` has a Delaunay preimage with `(L₀, G₀) ∈ A`. -/
theorem exists_delaunay_preimage {am ap em ep : ℝ} (hp : RegionParams am ap em ep)
    {z₀ : (Fin 2 → ℝ) × (Fin 2 → ℝ)} (hz₀ : z₀ ∈ NearCircular am ap em ep) :
    ∃ w : (Fin 2 → ℝ) × (Fin 2 → ℝ), w.2 ∈ actionRegion am ap em ep ∧ delaunay w = z₀ := by
  rw [nearCircular_eq_image_region hp] at hz₀
  obtain ⟨w, hw, rfl⟩ := hz₀
  exact ⟨w, hw, rfl⟩

/-- `bpI:p8:topology` (c): `𝒩` is open (`isOpen_nearCircular`). -/
theorem isOpen_nearCircular_region (am ap em ep : ℝ) : IsOpen (NearCircular am ap em ep) :=
  isOpen_nearCircular am ap em ep

/-- `bpI:p8:topology` (d): `𝒩` is nonempty (`L_* = √a_*`, `G_* = L_* κ(e_*)`). -/
theorem nearCircular_nonempty {am ap em ep : ℝ} (hp : RegionParams am ap em ep) :
    (NearCircular am ap em ep).Nonempty := by
  have hem : 0 < em := hp.he
  have hep : em < ep := hp.hee
  have hep1 : ep < 1 := hp.he1
  have hap : am < ap := hp.haa
  have ham : 0 < am := hp.ha
  set L : ℝ := Real.sqrt ((am + ap) / 2) with hLdef
  set e : ℝ := (em + ep) / 2 with hedef
  have hL : 0 < L := Real.sqrt_pos.mpr (by linarith)
  have hemIcc : em ∈ Icc (0 : ℝ) 1 := ⟨hem.le, by linarith⟩
  have heIcc : e ∈ Icc (0 : ℝ) 1 := ⟨by rw [hedef]; linarith, by rw [hedef]; linarith⟩
  have hepIcc : ep ∈ Icc (0 : ℝ) 1 := ⟨by linarith, hep1.le⟩
  have hk1 : kappa ep < kappa e := kappa_strictAntiOn heIcc hepIcc (by rw [hedef]; linarith)
  have hk2 : kappa e < kappa em := kappa_strictAntiOn hemIcc heIcc (by rw [hedef]; linarith)
  have hmem : (![L, L * kappa e] : Fin 2 → ℝ) ∈ actionRegion am ap em ep := by
    have hLlo : Real.sqrt am < L := Real.sqrt_lt_sqrt ham.le (by linarith)
    have hLhi : L < Real.sqrt ap := Real.sqrt_lt_sqrt (by linarith) (by linarith)
    have h3 : kappa ep * L < L * kappa e := by
      rw [mul_comm]; exact mul_lt_mul_of_pos_left hk1 hL
    have h4 : L * kappa e < kappa em * L := by
      rw [mul_comm (kappa em) L]; exact mul_lt_mul_of_pos_left hk2 hL
    exact ⟨hLlo, hLhi, h3, h4⟩
  rw [nearCircular_eq_image_region hp]
  exact ⟨_, (0, ![L, L * kappa e]), hmem, rfl⟩

end KAM.Iso.R3bp

end
