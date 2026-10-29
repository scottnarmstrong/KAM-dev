/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Birkhoff.Family
public import KAM.Planetary.PlanarTorsion.Birkhoff.Jets
public import KAM.Planetary.PlanarTorsion.Birkhoff.BetaAvg
public import KAM.Planetary.PlanarTorsion.Quartic

/-!
# Planar quartic torsion: the physical quartic family and restriction (package T16)

Blueprint P, Part 11b (`stepP:p11b:bt-nf`).  `p11cB_family` realises the frame-rotated physical
quartic as a `QuarticFamily` over every set of actions inside the frame domain; the families
restrict to subsets (`p11cB_restrict`), and `p11cB_freq` is analytic on the frame domain.
-/

@[expose] public noncomputable section

open Set Metric Real Function Filter
open scoped Topology

namespace KAM.Planetary

open KAM KAM.Kepler

theorem p11cB_family (p : PlanarData) (hp : p.Valid) {O : Set (Fin 2 → ℝ)}
    (hO : ∀ I ∈ O, I ∈ p11c_frameActionDomain p) :
    ∃ F : QuarticFamily O, ∀ I z, F.eval I z = p11c_quartic (p11c_coeffs p (p.axes I))
      (p11c_rotateSlow (p11c_frame p (p.axes I)) z) := by
  let c : (Fin 2 → ℝ) → Fin 6 → ℝ := fun I =>
    p11cB_rotC (p11c_coeffs p (p.axes I)) (p11c_frame p (p.axes I) 0 0)
      (p11c_frame p (p.axes I) 1 0)
  have han : ∀ k, AnalyticOnNhd ℝ (fun I => c I k) O := by
    intro k I hI
    have hI' := hO I hI
    have hax := p11c_axes_map_analyticAt p hp I
    have hc : ∀ j, AnalyticAt ℝ (fun I => p11c_coeffs p (p.axes I) j) I := fun j =>
      (analyticAt_pi_iff.1 ((quartic_explicit p hp).1 _ hI') j).comp_of_eq hax rfl
    have hU := p11c_frameFamily_analyticOnNhd p hp I hI'
    have hg : AnalyticAt ℝ (fun I => p11c_frame p (p.axes I) 0 0) I :=
      analyticAt_pi_iff.1 (analyticAt_pi_iff.1 hU 0) 0
    have hs : AnalyticAt ℝ (fun I => p11c_frame p (p.axes I) 1 0) I :=
      analyticAt_pi_iff.1 (analyticAt_pi_iff.1 hU 1) 0
    have c0 := hc 0
    have c1 := hc 1
    have c2 := hc 2
    have c3 := hc 3
    have c4 := hc 4
    have c5 := hc 5
    fin_cases k <;> simp only [c, p11cB_rotC, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk] <;> fun_prop
  obtain ⟨F, hF⟩ := p11cB_family_of_coeffs c han
  refine ⟨F, fun I z => ?_⟩
  rw [hF]
  calc p11c_quartic (c I) z = p11c_quartic (p11c_coeffs p (p.axes I))
        (p11c_rotateSlow !![p11c_frame p (p.axes I) 0 0, -p11c_frame p (p.axes I) 1 0;
          p11c_frame p (p.axes I) 1 0, p11c_frame p (p.axes I) 0 0] z) :=
      (p11cB_quartic_rot _ _ _ z).symm
    _ = _ := by rw [← p11cB_frame_eq p (p.axes I)]

/-- Restriction of a quartic family to a subset of its parameter set. -/
def p11cB_restrict {O O' : Set (Fin 2 → ℝ)} (F : QuarticFamily O) (h : O' ⊆ O) :
    QuarticFamily O' :=
  ⟨F.coeff, fun a => (F.analytic a).mono h⟩

theorem p11cB_restrict_eval {O O' : Set (Fin 2 → ℝ)} (F : QuarticFamily O) (h : O' ⊆ O) :
    (p11cB_restrict F h).eval = F.eval := rfl

theorem p11cB_freq_analyticOnNhd (p : PlanarData) (hp : p.Valid) {O : Set (Fin 2 → ℝ)}
    (hO : ∀ I ∈ O, I ∈ p11c_frameActionDomain p) : AnalyticOnNhd ℝ (p11cB_freq p) O := by
  intro I hI
  have hax := p11c_axes_map_analyticAt p hp I
  refine analyticAt_pi_iff.2 fun j => ?_
  exact analyticAt_const.mul ((p11cB_sigma_analyticAt p hp (hO I hI) j).comp_of_eq hax rfl)

theorem p11cB_average_congr {F G : (Fin 2 → ℝ) → Phase 2 → ℝ} {I J : Fin 2 → ℝ}
    (h : F I = G J) (z : Phase 2) : p11c_average F I z = p11c_average G J z := by
  unfold p11c_average p11c_character
  simp only [h]

end KAM.Planetary

end
