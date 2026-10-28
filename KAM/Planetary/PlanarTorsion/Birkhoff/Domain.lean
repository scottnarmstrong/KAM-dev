/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Frame
public import KAM.Planetary.PlanarTorsion.Lift.Defs
public import KAM.Planetary.SecularForm.Symmetry

/-!
# Planar quartic torsion: the physical domain of the Birkhoff map (package T16)

Blueprint P, Part 11b (`stepP:p11b:bt-K`, radius `ρ_K`).  `p11cB_good p` is the open set of phase
points inside the Poincaré chart domain whose image is collision free; the physical perturbations
`p11c_hatFix p`, `p11c_hatMov p` are analytic on it.  Circular points with positive actions in
the frame domain lie in `p11cB_good p`, and a compactness (tube lemma) argument gives a uniform
radius `δ` such that every point over a compact set of actions, with slow part of sup norm `< δ`
and arbitrary angles, lies in `p11cB_good p`.
-/

@[expose] public noncomputable section

open Set Metric Real Function Filter
open scoped Topology

namespace KAM.Planetary

open KAM KAM.Kepler

/-- The open good physical domain: chart domain and collision-free image. -/
def p11cB_good (p : PlanarData) : Set (Phase (2 + 2)) :=
  poincareProdDom 2 ∩ poincareProd p.m p.kappa ⁻¹' collisionFreeDomain 2

theorem p11cB_good_isOpen (p : PlanarData) (hp : p.Valid) : IsOpen (p11cB_good p) :=
  isOpen_poincareProd_preimage hp.2.2 (mul_pos hp.1 hp.2.1)

theorem p11cB_planeLength_pos {v : Fin 2 → ℝ} (hv : v ≠ 0) : 0 < planeLength v := by
  unfold planeLength planeSq
  refine Real.sqrt_pos.2 ?_
  by_contra h
  push Not at h
  apply hv
  have h0 : ∀ k, v k ^ 2 = 0 := fun k => by
    have := Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (v k)) |>.1
      (le_antisymm h (Finset.sum_nonneg fun k _ => sq_nonneg (v k)))
    exact this k (Finset.mem_univ k)
  funext k
  exact pow_eq_zero_iff (two_ne_zero) |>.1 (h0 k)

theorem p11cB_fin2_ne {i j : Fin 2} (h : i ≠ j) : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  fin_cases i <;> fin_cases j <;> simp at h ⊢

/-- Circular points with positive actions in the frame domain are collision free. -/
theorem p11cB_circular_mem (p : PlanarData) (hp : p.Valid) {I : Fin 2 → ℝ}
    (hI : I ∈ p11c_frameActionDomain p) (hpos : ∀ i, 0 < I i) (lam : Fin 2 → ℝ) :
    assemble I lam (0 : Fin 2 → ℝ) (0 : Fin 2 → ℝ) ∈ p11cB_good p := by
  have hκ : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have hax : p.axes I ∈ p11c_axes := hI
  refine ⟨?_, ?_⟩
  · rw [SecularForm.assemble_mem_iff]
    intro i
    refine ⟨hpos i, ?_⟩
    simpa using hpos i
  · show NoCollision (poincareProd p.m p.kappa
      (assemble I lam (0 : Fin 2 → ℝ) (0 : Fin 2 → ℝ))).1
    have hb := poincareProd_block p.m p.kappa (assemble I lam (0 : Fin 2 → ℝ) (0 : Fin 2 → ℝ))
    have hc : ∀ i, (bodyVector (poincareProd p.m p.kappa
        (assemble I lam (0 : Fin 2 → ℝ) (0 : Fin 2 → ℝ))).1 i) =
        (p.axes I i) • (![Real.cos (lam i), Real.sin (lam i)] : Fin 2 → ℝ) := by
      intro i
      have h1 : bodyVector (poincareProd p.m p.kappa
          (assemble I lam (0 : Fin 2 → ℝ) (0 : Fin 2 → ℝ))).1 i =
          (poincare (p.m i) p.kappa (planetBlock
            (assemble I lam (0 : Fin 2 → ℝ) (0 : Fin 2 → ℝ)) i)).1 := congrArg Prod.fst (hb i)
      rw [h1]
      have hpb : planetBlock (assemble I lam (0 : Fin 2 → ℝ) (0 : Fin 2 → ℝ)) i =
          ((![lam i, 0], ![I i, 0]) : Phase 2) := by
        simp [SecularForm.planetBlock_assemble]
      rw [hpb, poincare_circular (hp.2.2 i) hκ (hpos i)]
      simp [PlanarData.axes]
    have hax0 := hax.1
    have hax1 := hax.2
    have hapos : ∀ i, 0 < p.axes I i := by
      intro i; fin_cases i
      · exact hax0
      · exact hax0.trans hax1
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · rw [hc i]
      refine p11cB_planeLength_pos fun h => ?_
      rcases smul_eq_zero.1 h with h | h
      · exact (hapos i).ne' h
      · have h0 := congrFun h 0
        have h1 := congrFun h 1
        simp at h0 h1
        have := Real.sin_sq_add_cos_sq (lam i)
        rw [h0, h1] at this
        norm_num at this
    · rw [hc i, hc j]
      refine p11cB_planeLength_pos fun h => ?_
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [Pi.sub_apply] at h0 h1
      have hs1 := Real.sin_sq_add_cos_sq (lam i)
      have hs2 := Real.sin_sq_add_cos_sq (lam j)
      have key : (p.axes I i * Real.cos (lam i) - p.axes I j * Real.cos (lam j)) ^ 2 +
          (p.axes I i * Real.sin (lam i) - p.axes I j * Real.sin (lam j)) ^ 2 =
          (p.axes I j - p.axes I i) ^ 2 + p.axes I i * p.axes I j *
            ((Real.cos (lam i) - Real.cos (lam j)) ^ 2 +
              (Real.sin (lam i) - Real.sin (lam j)) ^ 2) := by
        linear_combination (p.axes I i ^ 2 - p.axes I i * p.axes I j) * hs1 +
          (p.axes I j ^ 2 - p.axes I i * p.axes I j) * hs2
      rw [h0, h1] at key
      have hne : p.axes I j - p.axes I i ≠ 0 := by
        intro h0
        rcases p11cB_fin2_ne hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
      have hnn : 0 ≤ p.axes I i * p.axes I j * ((Real.cos (lam i) - Real.cos (lam j)) ^ 2 +
          (Real.sin (lam i) - Real.sin (lam j)) ^ 2) := by
        have := hapos i; have := hapos j; positivity
      have : 0 < (p.axes I j - p.axes I i) ^ 2 := by positivity
      nlinarith


private theorem p11cB_continuous_assemble :
    Continuous fun x : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      (assemble x.1 x.2 (0 : Fin 2 → ℝ) (0 : Fin 2 → ℝ) : Phase (2 + 2)) := by
  refine Continuous.prodMk (continuous_pi fun j => ?_) (continuous_pi fun j => ?_)
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [Fin.append_left] <;> fun_prop
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [Fin.append_left] <;> fun_prop

/-- Uniform physical radius: over a compact set of positive frame-domain actions, every point
with slow part of sup norm `< δ` (any angles) is in the good domain. -/
theorem p11cB_domain (p : PlanarData) (hp : p.Valid) {K : Set (Fin 2 → ℝ)} (hK : IsCompact K)
    (hKd : K ⊆ p11c_frameActionDomain p) (hKpos : ∀ I ∈ K, ∀ i, 0 < I i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : Phase (2 + 2), (fun i => w.2 (Fin.castAdd 2 i)) ∈ K →
      (∀ i, |w.1 (Fin.natAdd 2 i)| < δ) → (∀ i, |w.2 (Fin.natAdd 2 i)| < δ) →
      w ∈ p11cB_good p := by
  let S : Set (Phase (2 + 2)) := (fun x : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
    (assemble x.1 x.2 (0 : Fin 2 → ℝ) (0 : Fin 2 → ℝ) : Phase (2 + 2))) ''
      (K ×ˢ Set.pi univ fun _ : Fin 2 => Icc (0 : ℝ) (2 * π))
  have hS : IsCompact S :=
    (hK.prod (isCompact_univ_pi fun _ => isCompact_Icc)).image p11cB_continuous_assemble
  have hSG : S ⊆ p11cB_good p := by
    rintro _ ⟨⟨I, φ⟩, ⟨hI, -⟩, rfl⟩
    exact p11cB_circular_mem p hp (hKd hI) (hKpos I hI) φ
  obtain ⟨δ, hδ, hsub⟩ := hS.exists_thickening_subset_open (p11cB_good_isOpen p hp) hSG
  refine ⟨δ, hδ, fun w hwK hx hy => ?_⟩
  set I : Fin 2 → ℝ := fun i => w.2 (Fin.castAdd 2 i) with hIdef
  set k : Fin 2 → ℤ := fun i => ⌊w.1 (Fin.castAdd 2 i) / (2 * π)⌋ with hk
  set φ : Fin 2 → ℝ := fun i => w.1 (Fin.castAdd 2 i) - 2 * π * k i with hφ
  have hφc : φ ∈ Set.pi univ fun _ : Fin 2 => Icc (0 : ℝ) (2 * π) := by
    intro i _
    have h2π : 0 < 2 * π := by positivity
    have h1 := Int.floor_le (w.1 (Fin.castAdd 2 i) / (2 * π))
    have h2 := Int.lt_floor_add_one (w.1 (Fin.castAdd 2 i) / (2 * π))
    rw [le_div_iff₀ h2π] at h1
    rw [div_lt_iff₀ h2π] at h2
    simp only [hφ, hk]
    constructor <;> nlinarith
  let w' : Phase (2 + 2) := assemble I φ (fun i => w.2 (Fin.natAdd 2 i))
    (fun i => w.1 (Fin.natAdd 2 i))
  have hw' : w' ∈ p11cB_good p := by
    refine hsub (Metric.mem_thickening_iff.2 ⟨assemble I φ (0 : Fin 2 → ℝ) (0 : Fin 2 → ℝ),
      ⟨(I, φ), ⟨hwK, hφc⟩, rfl⟩, ?_⟩)
    rw [Prod.dist_eq]
    refine max_lt ?_ ?_
    · rw [dist_pi_lt_iff hδ]
      intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp [w', assemble, Fin.append_left]
        exact hδ
      · simpa [w', assemble, Fin.append_right, Real.dist_eq] using hx i
    · rw [dist_pi_lt_iff hδ]
      intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp [w', assemble, Fin.append_left]
        exact hδ
      · simpa [w', assemble, Fin.append_right, Real.dist_eq] using hy i
  have hwe : w = w' + fastShift (a := 2) (b := 2) (fun i => k i) := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
        simp [w', assemble, fastShift, Fin.append_left, hφ]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
        simp [w', assemble, fastShift, Fin.append_left, hIdef]
  have hlat := poincareProd_lattice hp.2.2 (mul_pos hp.1 hp.2.1) hw'.1 (fun i => k i)
  rw [hwe]
  refine ⟨hlat.1, ?_⟩
  have hnc : NoCollision (poincareProd p.m (p.G * p.m0) w').1 := hw'.2
  show NoCollision (poincareProd p.m (p.G * p.m0) (w' + fastShift (a := 2) (b := 2)
    (fun i => k i))).1
  rw [hlat.2]
  exact hnc

end KAM.Planetary

end
