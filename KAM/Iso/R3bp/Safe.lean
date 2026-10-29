/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Iso.ComplexDomain
public import KAM.Iso.R3bp.Region

/-!
# The enlarged safe region

Blueprint-I Part 8: `bpI:p8:safe` and `bpI:p8:safe-region`.

* `safeT`, `safeAminus`, `safeAplus`, `safeEminus`, `safeEplus`: the enlarged parameters
  `a₋' = a₋ / 2`, `a₊' = a₊ (1 + t)`, `e₋' = e₋ / 2`, `e₊' = e₊ + t`.
* `safeU` (open), `safeK` (compact), `safeB = 2π U`, `safeB' = 2π A`.
* `safe_inclusions`, `safe_elements`, `safe_radii`, `safe_domain`: the items (a)–(d) of
  `safe-region`; `kRmin_le`, `le_kRhoMax` are the pointwise bounds on a safe action region.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Iso.R3bp

open KAM KAM.Kepler KAM.Iso

section Safe

variable {am ap em ep : ℝ}

def safeT (ap ep : ℝ) : ℝ := min (1 / 8) ((1 - ap * (1 + ep)) / (6 * ap))
def safeAminus (am : ℝ) : ℝ := am / 2
def safeAplus (ap ep : ℝ) : ℝ := ap * (1 + safeT ap ep)
def safeEminus (em : ℝ) : ℝ := em / 2
def safeEplus (ap ep : ℝ) : ℝ := ep + safeT ap ep

/-- `U = A(a_±', e_±')` (open). -/
def safeU (am ap em ep : ℝ) : Set (Fin 2 → ℝ) :=
  actionRegion (safeAminus am) (safeAplus ap ep) (safeEminus em) (safeEplus ap ep)

/-- `𝒦 = A^cl(a_±', e_±')` (compact). -/
def safeK (am ap em ep : ℝ) : Set (Fin 2 → ℝ) :=
  actionRegionCl (safeAminus am) (safeAplus ap ep) (safeEminus em) (safeEplus ap ep)

/-- `B = 2π U`, the action domain handed to I-HEAD. -/
def safeB (am ap em ep : ℝ) : Set (Fin 2 → ℝ) :=
  (fun x : Fin 2 → ℝ => (2 * Real.pi) • x) '' safeU am ap em ep

/-- `B' = 2π A`. -/
def safeB' (am ap em ep : ℝ) : Set (Fin 2 → ℝ) :=
  (fun x : Fin 2 → ℝ => (2 * Real.pi) • x) '' actionRegion am ap em ep

theorem safeT_pos (hp : R3bpParams am ap em ep) : 0 < safeT ap ep := by
  have hap : 0 < ap := hp.ha.trans hp.haa
  have h : 0 < 1 - ap * (1 + ep) := by linarith [hp.hinner]
  exact lt_min (by norm_num) (div_pos h (by positivity))

theorem safeT_le_eighth (ap ep : ℝ) : safeT ap ep ≤ 1 / 8 := min_le_left _ _

theorem safeT_mul_le (hp : R3bpParams am ap em ep) :
    6 * ap * safeT ap ep ≤ 1 - ap * (1 + ep) := by
  have hap : 0 < ap := hp.ha.trans hp.haa
  have h : safeT ap ep ≤ (1 - ap * (1 + ep)) / (6 * ap) := min_le_right _ _
  rw [le_div_iff₀ (by positivity)] at h
  linarith

theorem safe_regionParams (hp : R3bpParams am ap em ep) :
    RegionParams (safeAminus am) (safeAplus ap ep) (safeEminus em) (safeEplus ap ep) ∧
      safeEplus ap ep < 3 / 8 := by
  have hap : 0 < ap := hp.ha.trans hp.haa
  have ht := safeT_pos hp
  have ht8 := safeT_le_eighth ap ep
  have hs := hp.heSmall
  unfold safeAminus safeAplus safeEminus safeEplus
  refine ⟨⟨by linarith [hp.ha], ?_, by linarith [hp.he], by linarith [hp.hee, hp.he], by linarith⟩,
    by linarith⟩
  nlinarith [hp.ha, hp.haa, mul_pos hap ht]

/-- (a) `Ā ⊆ A^cl ⊆ U ⊆ 𝒦`, `𝒦` compact, nonempty, in the cone: `SafeAction 𝒦`. -/
theorem safe_inclusions (hp : R3bpParams am ap em ep) :
    actionRegionCl am ap em ep ⊆ safeU am ap em ep ∧ safeU am ap em ep ⊆ safeK am ap em ep ∧
      SafeAction (safeK am ap em ep) := by
  have hap : 0 < ap := hp.ha.trans hp.haa
  have ht := safeT_pos hp
  have ht8 := safeT_le_eighth ap ep
  have hs := hp.heSmall
  have hcl : actionRegionCl am ap em ep ⊆ safeU am ap em ep := by
    rintro x ⟨h1, h2, h3, h4⟩
    have hcone := (actionRegionCl_subset_cone hp.region).2 ⟨h1, h2, h3, h4⟩
    have hx0 : 0 < x 0 := hcone.1.trans hcone.2
    have hepI : ep ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hp.he, hp.hee], by linarith⟩
    have hep'I : ep + safeT ap ep ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hp.he, hp.hee], by linarith⟩
    have hemI : em ∈ Icc (0 : ℝ) 1 := ⟨hp.he.le, by linarith [hp.hee]⟩
    have hem2I : em / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hp.he], by linarith [hp.he, hp.hee]⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine lt_of_lt_of_le (Real.sqrt_lt_sqrt ?_ ?_) h1 <;> unfold safeAminus <;>
        linarith [hp.ha]
    · refine lt_of_le_of_lt h2 (Real.sqrt_lt_sqrt hap.le ?_)
      unfold safeAplus; nlinarith [mul_pos hap ht]
    · refine lt_of_lt_of_le ?_ h3
      exact mul_lt_mul_of_pos_right
        (kappa_strictAntiOn hepI hep'I (by unfold safeEplus; linarith)) hx0
    · refine lt_of_le_of_lt h4 ?_
      exact mul_lt_mul_of_pos_right (kappa_strictAntiOn hem2I hemI (by linarith [hp.he])) hx0
  have hUK : safeU am ap em ep ⊆ safeK am ap em ep := fun x hx =>
    ⟨hx.1.le, hx.2.1.le, hx.2.2.1.le, hx.2.2.2.le⟩
  have hrp := (safe_regionParams hp).1
  refine ⟨hcl, hUK, isCompact_actionRegionCl _ _ _ _, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := nearCircular_nonempty hp.region
    rw [nearCircular_eq_image_region hp.region] at hz
    obtain ⟨w, hw, -⟩ := hz
    exact ⟨w.2, hUK (hcl ((actionRegionCl_subset_cone hp.region).1 hw))⟩
  · exact (actionRegionCl_subset_cone hrp).2

/-- (b) elements on `𝒦`: `a_-' ≤ L² ≤ a_+'`, `e_-' ≤ e ≤ e_+'`. -/
theorem safe_elements (hp : R3bpParams am ap em ep) {x : Fin 2 → ℝ} (hx : x ∈ safeK am ap em ep) :
    safeAminus am ≤ x 0 ^ 2 ∧ x 0 ^ 2 ≤ safeAplus ap ep ∧ safeEminus em ≤ eccOf (x 0) (x 1) ∧
      eccOf (x 0) (x 1) ≤ safeEplus ap ep := by
  have hrp := (safe_regionParams hp).1
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have hcone := (actionRegionCl_subset_cone hrp).2 ⟨h1, h2, h3, h4⟩
  have hx0 : 0 < x 0 := hcone.1.trans hcone.2
  have hecc := (eccOf_mem_Icc_iff hx0 hcone.1 hcone.2 hrp.he.le hrp.hee hrp.he1).2 ⟨h3, h4⟩
  refine ⟨?_, ?_, hecc.1, hecc.2⟩
  · exact ((Real.sqrt_le_left hx0.le).1 h1)
  · exact (Real.le_sqrt' hx0).1 h2

/-- The arithmetic of `safe-region` (c): `a_+'(1 + e_+') ≤ (1 + ρ*)/2`. -/
lemma safe_rho_arith {ap ep t : ℝ} (hap : 0 < ap) (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (he : ep < 1 / 4) (h6 : 6 * ap * t ≤ 1 - ap * (1 + ep)) :
    ap * (1 + t) * (1 + (ep + t)) ≤ (1 + ap * (1 + ep)) / 2 := by
  nlinarith [mul_nonneg (mul_pos hap ht).le (by linarith : (0 : ℝ) ≤ 1 - ep - t)]

/-- (c) `ρ_max ≤ a_+'(1 + e_+') ≤ (1 + ρ*)/2 < 1`, `r_min ≥ a_-'(1 - e_+') > 0`, `r_min ≤ ρ_max`;
`ρ* = ap(1 + ep)`. -/
theorem safe_radii (hp : R3bpParams am ap em ep) :
    kRhoMax (safeK am ap em ep) ≤ (1 + ap * (1 + ep)) / 2 ∧ kRhoMax (safeK am ap em ep) < 1 ∧
      safeAminus am * (1 - safeEplus ap ep) ≤ kRmin (safeK am ap em ep) ∧
      0 < kRmin (safeK am ap em ep) ∧ kRmin (safeK am ap em ep) ≤ kRhoMax (safeK am ap em ep) := by
  have hap : 0 < ap := hp.ha.trans hp.haa
  have hK := (safe_inclusions hp).2.2
  have hrp := safe_regionParams hp
  have hmax : kRhoMax (safeK am ap em ep) ≤ (1 + ap * (1 + ep)) / 2 := by
    refine csSup_le (hK.nonempty.image _) ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨-, hL2, he0, he1⟩ := safe_elements hp hx
    have hecc : 0 ≤ eccOf (x 0) (x 1) := Real.sqrt_nonneg _
    calc x 0 ^ 2 * (1 + eccOf (x 0) (x 1))
        ≤ safeAplus ap ep * (1 + safeEplus ap ep) :=
          mul_le_mul hL2 (by linarith) (by linarith)
            (by unfold safeAplus; nlinarith [safeT_pos hp])
      _ ≤ _ := by
          unfold safeAplus safeEplus
          exact safe_rho_arith hap (safeT_pos hp) (safeT_le_eighth ap ep) (by linarith [hp.heSmall])
            (safeT_mul_le hp)
  have hmin : safeAminus am * (1 - safeEplus ap ep) ≤ kRmin (safeK am ap em ep) := by
    refine le_csInf (hK.nonempty.image _) ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hL1, -, -, he1⟩ := safe_elements hp hx
    exact mul_le_mul hL1 (by linarith) (by linarith [hrp.1.he1.le, hrp.1.ha, hrp.1.he, hrp.2])
      (sq_nonneg _)
  have hpos : 0 < safeAminus am * (1 - safeEplus ap ep) :=
    mul_pos hrp.1.ha (by linarith [hrp.2])
  refine ⟨hmax, by linarith [hp.hinner], hmin, hpos.trans_le hmin, ?_⟩
  obtain ⟨x, hx⟩ := hK.nonempty
  have h1 := ComplexDomainAux.sInf_spec hK (ComplexDomainAux.continuousOn_rminFn hK) |>.2 x hx
  have h2 := ComplexDomainAux.sSup_spec hK (ComplexDomainAux.continuousOn_rmaxFn hK) |>.2 x hx
  have hecc : 0 ≤ eccOf (x 0) (x 1) := Real.sqrt_nonneg _
  have h3 : x 0 ^ 2 * (1 - eccOf (x 0) (x 1)) ≤ x 0 ^ 2 * (1 + eccOf (x 0) (x 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  exact h1.trans (h3.trans h2)

/-- `r_min ≤ L²(1 - e)` and `L²(1 + e) ≤ ρ_max` on a safe action region (`csInf_le`, `le_csSup`). -/
theorem kRmin_le {K : Set (Fin 2 → ℝ)} (hK : SafeAction K) {x : Fin 2 → ℝ} (hx : x ∈ K) :
    kRmin K ≤ x 0 ^ 2 * (1 - eccOf (x 0) (x 1)) :=
  (ComplexDomainAux.sInf_spec hK (ComplexDomainAux.continuousOn_rminFn hK)).2 x hx

theorem le_kRhoMax {K : Set (Fin 2 → ℝ)} (hK : SafeAction K) {x : Fin 2 → ℝ} (hx : x ∈ K) :
    x 0 ^ 2 * (1 + eccOf (x 0) (x 1)) ≤ kRhoMax K :=
  (ComplexDomainAux.sSup_spec hK (ComplexDomainAux.continuousOn_rmaxFn hK)).2 x hx

/-- (d) `B = 2πU` open, bounded, nonempty; `B' = 2πA` open, `closure B' = 2π Ā` compact `⊆ B`;
`I ∈ B ⇒ I/(2π) ∈ 𝒦`. -/
theorem safe_domain (hp : R3bpParams am ap em ep) :
    IsOpen (safeB am ap em ep) ∧ Bornology.IsBounded (safeB am ap em ep) ∧
      (safeB am ap em ep).Nonempty ∧ IsOpen (safeB' am ap em ep) ∧
      IsCompact (closure (safeB' am ap em ep)) ∧
      closure (safeB' am ap em ep) ⊆ safeB am ap em ep ∧
      ∀ I ∈ safeB am ap em ep, (fun i => I i / (2 * Real.pi)) ∈ safeK am ap em ep := by
  have hc : (2 * Real.pi) ≠ 0 := by positivity
  set e : (Fin 2 → ℝ) ≃ₜ (Fin 2 → ℝ) := Homeomorph.smulOfNeZero (2 * Real.pi) hc with he
  have hef : ∀ s : Set (Fin 2 → ℝ), (fun x : Fin 2 → ℝ => (2 * Real.pi) • x) '' s = e '' s :=
    fun s => rfl
  obtain ⟨hAU, hUK, hK⟩ := safe_inclusions hp
  have hrp := (safe_regionParams hp).1
  have hcompK : IsCompact ((fun x : Fin 2 → ℝ => (2 * Real.pi) • x) '' safeK am ap em ep) :=
    hK.isCompact.image (continuous_const_smul _)
  have hclA : IsCompact (closure (actionRegion am ap em ep)) :=
    IsCompact.of_isClosed_subset (isCompact_actionRegionCl am ap em ep) isClosed_closure
      (closure_actionRegion_subset am ap em ep)
  have hcl : closure (safeB' am ap em ep) = e '' closure (actionRegion am ap em ep) := by
    unfold safeB'; rw [hef, e.image_closure]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold safeB; rw [hef]; exact e.isOpenMap _ (isOpen_actionRegion _ _ _ _)
  · exact hcompK.isBounded.subset (image_mono hUK)
  · obtain ⟨z, hz⟩ := nearCircular_nonempty hp.region
    rw [nearCircular_eq_image_region hp.region] at hz
    obtain ⟨w, hw, -⟩ := hz
    exact ⟨_, w.2, hAU ((actionRegionCl_subset_cone hp.region).1 hw), rfl⟩
  · unfold safeB'; rw [hef]; exact e.isOpenMap _ (isOpen_actionRegion _ _ _ _)
  · rw [hcl]; exact hclA.image e.continuous
  · rw [hcl]
    refine image_mono ?_
    exact (closure_actionRegion_subset am ap em ep).trans hAU
  · rintro _ ⟨x, hx, rfl⟩
    have : (fun i => ((2 * Real.pi) • x) i / (2 * Real.pi)) = x := by
      funext i; simp [hc]
    rw [this]; exact hUK hx

end Safe

end KAM.Iso.R3bp

end
