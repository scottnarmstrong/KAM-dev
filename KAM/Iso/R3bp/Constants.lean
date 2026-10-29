/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Iso.Collision
public import KAM.Iso.PeriodOne
public import KAM.Iso.R3bp.HeadData

/-!
# The constants and the core of I-R3BP

Blueprint-I Part 8: `bpI:p8:constants`, `pf-small`, `bounds`, `pf-coord`, `pf-sol`, `pf-bounds`,
`pf-dist`.

* `shellNu`, `r3bpMu0`, `r3bpD`, `r3bpR`: the constants `ν₀`, `μ₀`, `d`, `R`.
* `r3bp_constants_pos`, `r3bp_small`: positivity and smallness of the constants.
* `delaunay_radius_bounds`, `delaunay_energy`, `exactMu2_safe_pos`: adapters from the Kepler layer.
* `delaunay_orbit_bounds`: the radius bounds along a Delaunay orbit over `𝒦`.
* `r3bp_core`: everything of I-R3BP that does not use I-HEAD.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Iso.R3bp

open KAM KAM.Kepler KAM.Iso KAM.Iso.Confinement KAM.Planetary

section Data

variable {am ap em ep : ℝ}

/-- `ν₀ = min {r_min, 1 - ρ_max}`. -/
def shellNu (K : Set (Fin 2 → ℝ)) : ℝ := min (kRmin K) (1 - kRhoMax K)

/-- `μ₀ = min {1/2, μ₂, ε_H/(|C_F| + 1), ν₀/2}` (the blueprint's `ε_H/C_F` needs `C_F > 0`; the
Lean form does not). -/
def r3bpMu0 (K : Set (Fin 2 → ℝ)) (εH : ℝ) : ℝ :=
  min (min (1 / 2) (exactMu2 K)) (min (εH / (|exactCF K| + 1)) (shellNu K / 2))

/-- `d = ν₀/2`. -/
def r3bpD (K : Set (Fin 2 → ℝ)) : ℝ := shellNu K / 2

/-- `R = √(2/r_min)`. -/
def r3bpR (K : Set (Fin 2 → ℝ)) : ℝ := Real.sqrt (2 / kRmin K)

/-- `exactMu2 𝒦 > 0` for the safe region (`shiftEps` formula, `safe_radii`): no upstream lemma. -/
theorem exactMu2_safe_pos (hp : R3bpParams am ap em ep) : 0 < exactMu2 (safeK am ap em ep) := by
  obtain ⟨-, h1, -, h3, -⟩ := safe_radii hp
  unfold exactMu2 exactEps shiftEps
  have : 0 < 1 - kRhoMax (safeK am ap em ep) := by linarith
  have := lt_min (pow_pos h3 2) (pow_pos this 2)
  positivity

theorem shellNu_pos (hp : R3bpParams am ap em ep) : 0 < shellNu (safeK am ap em ep) := by
  obtain ⟨-, h1, -, h3, -⟩ := safe_radii hp
  exact lt_min h3 (by linarith)

/-- `bpI:p8:constants`: `0 < μ₀ ≤ 1/2`, `d > 0`, `R > 0`. -/
theorem r3bp_constants_pos (hp : R3bpParams am ap em ep) {εH : ℝ} (hεH : 0 < εH) :
    0 < r3bpMu0 (safeK am ap em ep) εH ∧ r3bpMu0 (safeK am ap em ep) εH ≤ 1 / 2 ∧
      0 < r3bpD (safeK am ap em ep) ∧ 0 < r3bpR (safeK am ap em ep) := by
  have hν := shellNu_pos hp
  refine ⟨?_, ?_, half_pos hν, ?_⟩
  · refine lt_min (lt_min (by norm_num) (exactMu2_safe_pos hp)) (lt_min ?_ (half_pos hν))
    exact div_pos hεH (by positivity)
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact Real.sqrt_pos.2 (div_pos two_pos (safe_radii hp).2.2.2.1)

/-- `bpI:p8:pf-small`: for `0 ≤ μ < μ₀`: `μ < μ₂`, `μ C_F < ε_H` and `|μ| ≤ ν₀/2`. -/
theorem r3bp_small (hp : R3bpParams am ap em ep) {εH μ : ℝ} (hεH : 0 < εH) (h0 : 0 ≤ μ)
    (hμ : μ < r3bpMu0 (safeK am ap em ep) εH) :
    μ < exactMu2 (safeK am ap em ep) ∧ μ * exactCF (safeK am ap em ep) < εH ∧
      |μ| ≤ shellNu (safeK am ap em ep) / 2 := by
  have _ := hεH
  refine ⟨hμ.trans_le ((min_le_left _ _).trans (min_le_right _ _)), ?_,
    (abs_of_nonneg h0).trans_le (hμ.le.trans ((min_le_right _ _).trans (min_le_right _ _)))⟩
  have h1 : μ < εH / (|exactCF (safeK am ap em ep)| + 1) :=
    hμ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  rw [lt_div_iff₀ (by positivity)] at h1
  calc μ * exactCF (safeK am ap em ep) ≤ μ * |exactCF (safeK am ap em ep)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) h0
    _ ≤ μ * (|exactCF (safeK am ap em ep)| + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) h0
    _ < εH := h1

/-- ADAPTER from Kepler `orbitMapR_radius_bounds` (`delaunay` unfolds to `orbitMapR`, `rfl`) and
`eccOf_mem_Ioo`. -/
theorem delaunay_radius_bounds {w : (Fin 2 → ℝ) × (Fin 2 → ℝ)} (hw : w ∈ deDom) :
    w.2 0 ^ 2 * (1 - eccOf (w.2 0) (w.2 1)) ≤ radius (delaunay w).1 ∧
      radius (delaunay w).1 ≤ w.2 0 ^ 2 * (1 + eccOf (w.2 0) (w.2 1)) := by
  obtain ⟨hG, hGL⟩ := hw
  obtain ⟨he0, he1⟩ := ComplexDomainAux.eccOf_pos_lt_one hG hGL
  exact orbitMapR_radius_bounds (hG.trans hGL) he0.le he1

/-- ADAPTER from Kepler `orbitMapR_energy` and `eccOf_mem_Ioo`. -/
theorem delaunay_energy {w : (Fin 2 → ℝ) × (Fin 2 → ℝ)} (hw : w ∈ deDom) :
    kE (delaunay w) = -1 / (2 * w.2 0 ^ 2) := by
  obtain ⟨hG, hGL⟩ := hw
  obtain ⟨he0, he1⟩ := ComplexDomainAux.eccOf_pos_lt_one hG hGL
  exact orbitMapR_energy (hG.trans hGL) he0.le he1

/-- `bpI:p8:bounds`: along a Delaunay orbit over `𝒦`: `r_min ≤ rad q ≤ ρ_max`, `rad p ≤ R`. -/
theorem delaunay_orbit_bounds {K : Set (Fin 2 → ℝ)} (hK : SafeAction K) (hr : 0 < kRmin K)
    {w : (Fin 2 → ℝ) × (Fin 2 → ℝ)} (hw : w ∈ deDom) (hwK : w.2 ∈ K) :
    kRmin K ≤ radius (delaunay w).1 ∧ radius (delaunay w).1 ≤ kRhoMax K ∧
      radius (delaunay w).2 ≤ r3bpR K := by
  obtain ⟨hb1, hb2⟩ := delaunay_radius_bounds hw
  have h1 := (kRmin_le hK hwK).trans hb1
  have h2 := hb2.trans (le_kRhoMax hK hwK)
  refine ⟨h1, h2, ?_⟩
  have hq : 0 < radius (delaunay w).1 := hr.trans_le h1
  have hE := delaunay_energy hw
  unfold kE at hE
  have hL : 0 < w.2 0 := hw.1.trans hw.2
  have hsq : planeSq (delaunay w).2 ≤ 2 / kRmin K := by
    have hinv : 1 / planeLength (delaunay w).1 ≤ 1 / kRmin K :=
      one_div_le_one_div_of_le hr h1
    have hneg : -1 / (2 * w.2 0 ^ 2) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · norm_num
      · positivity
    have : planeSq (delaunay w).2 / 2 ≤ 1 / kRmin K := by linarith
    calc planeSq (delaunay w).2 = 2 * (planeSq (delaunay w).2 / 2) := by ring
      _ ≤ 2 * (1 / kRmin K) := by linarith
      _ = 2 / kRmin K := by ring
  exact Real.sqrt_le_sqrt hsq

/-- `bpI:p8:pf-coord`, `pf-sol`, `pf-bounds`, `pf-dist`: everything of I-R3BP that does not use
I-HEAD. For the data of I-HEAD at `ε_H` (the constant `ε₀` the frozen theorem returns): constants
`μ₀, d, R`; for `μ < μ₀` the I-HEAD hypotheses on `(f̃_μ, C_F μ)` hold with `C_F μ < ε_H`; and every
global Hamiltonian solution `zt` in `B` through the Delaunay preimage of `z₀` (this is where I-HEAD
enters, in the provider) yields the physical solution with the four bounds. -/
theorem r3bp_core (hp : R3bpParams am ap em ep) {εH : ℝ} (hεH : 0 < εH) :
    ∃ μ₀ d R : ℝ, 0 < μ₀ ∧ μ₀ ≤ 1 / 2 ∧ 0 < d ∧ 0 < R ∧ ∀ μ : ℝ, 0 ≤ μ → μ < μ₀ →
      (PerturbData (safeB am ap em ep) (r3bpS₀ am ap em ep) (r3bpR₀ am ap em ep)
          (tildeF (safeK am ap em ep) μ) (μ * exactCF (safeK am ap em ep)) ∧
        μ * exactCF (safeK am ap em ep) < εH) ∧
      ∀ z₀ ∈ NearCircular am ap em ep, ∃ w₀ : (Fin 2 → ℝ) × (Fin 2 → ℝ),
        w₀.2 ∈ safeB' am ap em ep ∧ delaunay (periodOneMap w₀) = z₀ ∧
        ∀ zt : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ), zt 0 = w₀ →
          IsHamiltonianSolutionOn (realHamiltonian r3bpH (tildeF (safeK am ap em ep) μ))
            (safeB am ap em ep) Set.univ zt →
          ∃ z : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ), z 0 = z₀ ∧ IsRestrictedSolutionOn μ Set.univ z ∧
            ∀ t : ℝ, d ≤ radius ((z t).1 - primary₁ μ) ∧ d ≤ radius ((z t).1 - primary₂ μ) ∧
              radius (z t).1 ≤ R ∧ radius (z t).2 ≤ R := by
  obtain ⟨hm0, hm1, hd0, hR0⟩ := r3bp_constants_pos hp hεH
  refine ⟨_, _, _, hm0, hm1, hd0, hR0, fun μ h0 hμ => ?_⟩
  obtain ⟨hμ2, hsmall, hμν⟩ := r3bp_small hp hεH h0 hμ
  refine ⟨⟨r3bp_perturbData hp h0 hμ2, hsmall⟩, fun z₀ hz₀ => ?_⟩
  obtain ⟨w, hw, hwz⟩ := exists_delaunay_preimage hp.region hz₀
  have hpo : periodOneMap (((2 * Real.pi)⁻¹ • w.1, (2 * Real.pi) • w.2) :
      (Fin 2 → ℝ) × (Fin 2 → ℝ)) = w := by
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    ext1
    · simp only [periodOneMap, smul_smul, mul_inv_cancel₀ hpi, one_smul]
    · simp only [periodOneMap, smul_smul, inv_mul_cancel₀ hpi, one_smul]
  refine ⟨((2 * Real.pi)⁻¹ • w.1, (2 * Real.pi) • w.2), ⟨w.2, hw, rfl⟩, by rw [hpo, hwz],
    fun zt hzt0 hzt => ?_⟩
  obtain ⟨-, hρ, -, hrpos, hrle⟩ := safe_radii hp
  have hK := (safe_inclusions hp).2.2
  have hB := (safe_domain hp).2.2.2.2.2.2
  have hμ' : |μ| < exactMu2 (safeK am ap em ep) := by rwa [abs_of_nonneg h0]
  have hsol := (transfer hK hρ hB hμ' (zt := zt) hzt).1
  refine ⟨_, by show delaunay (periodOneMap (zt 0)) = z₀; rw [hzt0, hpo, hwz], hsol, fun t => ?_⟩
  obtain ⟨hBt, -, -⟩ := hzt t (mem_univ t)
  have hx := hB _ hBt
  have hcone := hK.sub_cone _ hx
  have hper : (periodOneMap (zt t)).2 = fun i => (zt t).2 i / (2 * Real.pi) := by
    funext i
    simp [periodOneMap, div_eq_inv_mul]
  have hdom : periodOneMap (zt t) ∈ deDom := by
    show 0 < (periodOneMap (zt t)).2 1 ∧ (periodOneMap (zt t)).2 1 < (periodOneMap (zt t)).2 0
    rw [hper]
    exact hcone
  have hwK : (periodOneMap (zt t)).2 ∈ safeK am ap em ep := by rw [hper]; exact hx
  obtain ⟨b1, b2, b3⟩ := delaunay_orbit_bounds hK hrpos hdom hwK
  obtain ⟨s1, s2⟩ := Collision.shell_exclusion hrpos hrle hρ (μ := μ) hμν ⟨b1, b2⟩
  have hR1 : 1 < r3bpR (safeK am ap em ep) := by
    unfold r3bpR
    rw [Real.lt_sqrt zero_le_one]
    rw [lt_div_iff₀ hrpos]
    linarith
  exact ⟨s1, s2, (b2.trans (hρ.le.trans hR1.le)), b3⟩

end Data

end KAM.Iso.R3bp

end
