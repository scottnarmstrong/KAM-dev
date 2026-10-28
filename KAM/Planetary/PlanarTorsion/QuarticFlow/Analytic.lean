/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.QuarticFlow.Compact
public import KAM.Planetary.PlanarTorsion.QuarticFlow.Spec

/-!
# Planar quartic torsion: analytic dependence of the time-one map (package T9)

Blueprint P, Part 11b (`bpP:p11b:fl-an`).  The parameter `I` is carried by the augmented
autonomous field `p11cQ_aug chi (I, z) = (0, X_I z)` on `(Fin 2 → ℝ) × Phase 2`.  Package R2
(through `p11cQ_flow_compact_nbhd`) gives one short-time flow `Φ`, jointly analytic on a
neighbourhood of the compact set `K₁ × (closed ball)`; the time-one map is the `m`-th iterate of
the time-`1/m` map as long as the trajectory stays in that compact set, which the energy bound
`|z(t)|² ≤ 2 |z|²` guarantees.
-/

@[expose] public noncomputable section

open Set Metric Function
open scoped Topology

namespace KAM.Planetary

open KAM KAM.ODE

/-- The augmented autonomous field: parameters are constants of motion. -/
def p11cQ_aug {O : Set (Fin 2 → ℝ)} (chi : QuarticFamily O) (u : (Fin 2 → ℝ) × Phase 2) :
    (Fin 2 → ℝ) × Phase 2 :=
  (0, hamiltonianVectorField (chi.eval u.1) u.2)

theorem p11cQ_aug_analytic {O : Set (Fin 2 → ℝ)} (chi : QuarticFamily O) :
    AnalyticOnNhd ℝ (p11cQ_aug chi) (O ×ˢ univ) := fun u hu =>
  analyticAt_const.prod (p11cQ_field_analytic chi u hu)

/-- For fixed `I ∈ O` the Hamiltonian field is real analytic, hence `C¹`, on `Phase 2`. -/
theorem p11cQ_field_slice_contDiffOn {O : Set (Fin 2 → ℝ)} (chi : QuarticFamily O)
    {I : Fin 2 → ℝ} (hI : I ∈ O) :
    ContDiffOn ℝ 1 (hamiltonianVectorField (chi.eval I)) univ := by
  have h : AnalyticOnNhd ℝ (hamiltonianVectorField (chi.eval I)) univ := fun z _ =>
    (p11cQ_field_analytic chi (I, z) ⟨hI, mem_univ _⟩).comp
      (g := fun u : (Fin 2 → ℝ) × Phase 2 => hamiltonianVectorField (chi.eval u.1) u.2)
      (analyticAt_const.prod analyticAt_id)
  exact (h.contDiffOn isOpen_univ.uniqueDiffOn).of_le (by norm_cast)

/-- A solution of the augmented field keeps its parameter and solves the `I`-field. -/
theorem p11cQ_aug_solution {O : Set (Fin 2 → ℝ)} (chi : QuarticFamily O) {T : ℝ}
    {Γ : ℝ → (Fin 2 → ℝ) × Phase 2}
    (hΓ : IsSolutionIn (p11cQ_aug chi) (O ×ˢ univ) (Ioo (-T) T) Γ) (h0 : (0 : ℝ) ∈ Ioo (-T) T) :
    ∀ s ∈ Ioo (-T) T, (Γ s).1 = (Γ 0).1 ∧
      HasDerivAt (fun s => (Γ s).2) (hamiltonianVectorField (chi.eval (Γ 0).1) (Γ s).2) s := by
  have h1 : ∀ s ∈ Ioo (-T) T, HasDerivAt (fun s => (Γ s).1) 0 s := fun s hs =>
    (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Phase 2)).hasFDerivAt.comp_hasDerivAt s (hΓ s hs).2
  have hconst : ∀ s ∈ Ioo (-T) T, (Γ s).1 = (Γ 0).1 := fun s hs => by
    have := (convex_Ioo (-T) T).norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun s => (Γ s).1)
      (f' := fun _ => 0) (C := 0) (fun x hx => (h1 x hx).hasDerivWithinAt) (fun _ _ => by simp)
      h0 hs
    simpa [sub_eq_zero] using this
  intro s hs
  refine ⟨hconst s hs, ?_⟩
  have h2 := (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Phase 2)).hasFDerivAt.comp_hasDerivAt s
    (hΓ s hs).2
  refine h2.congr_deriv ?_
  simp [p11cQ_aug, hconst s hs]

/-- One step: the short-time augmented flow agrees with any solution of the `I`-field. -/
theorem p11cQ_step {O : Set (Fin 2 → ℝ)} (chi : QuarticFamily O) {I : Fin 2 → ℝ} {T h c d : ℝ}
    (hI1 : ContDiffOn ℝ 1 (hamiltonianVectorField (chi.eval I)) univ) (hc : c ≤ 0) (hd : 0 ≤ d)
    (hh : h ∈ Icc c d) (hh0 : 0 ≤ h) (hhT : h < T) (hT : 0 < T) {Γ : ℝ → (Fin 2 → ℝ) × Phase 2} {w : Phase 2}
    (hΓ : IsSolutionIn (p11cQ_aug chi) (O ×ˢ univ) (Ioo (-T) T) Γ) (hΓ0 : Γ 0 = (I, w))
    {G : ℝ → Phase 2} (hG : ∀ s ∈ Icc c d, HasDerivAt G (hamiltonianVectorField (chi.eval I) (G s)) s)
    (hG0 : G 0 = w) : Γ h = (I, G h) := by
  have h0 : (0 : ℝ) ∈ Ioo (-T) T := ⟨by linarith, hT⟩
  have hs := p11cQ_aug_solution chi hΓ h0
  have hhJ : h ∈ Ioo (-T) T := ⟨by linarith, hhT⟩
  have hJ : (Ioo (-T) T ∩ Icc c d).OrdConnected := ordConnected_Ioo.inter ordConnected_Icc
  have hsol1 : IsSolutionIn (hamiltonianVectorField (chi.eval I)) univ (Ioo (-T) T ∩ Icc c d)
      (fun s => (Γ s).2) := fun s hs' => by
    refine ⟨mem_univ _, ?_⟩
    have := (hs s hs'.1).2
    rwa [hΓ0] at this
  have hsol2 : IsSolutionIn (hamiltonianVectorField (chi.eval I)) univ (Ioo (-T) T ∩ Icc c d) G :=
    fun s hs' => ⟨mem_univ _, hG s hs'.2⟩
  have heq := gen_uniqueness isOpen_univ hI1 hJ (t₀ := 0) ⟨h0, hc, hd⟩ hsol1 hsol2
    (by simp [hΓ0, hG0]) (show h ∈ Ioo (-T) T ∩ Icc c d from ⟨hhJ, hh⟩)
  refine Prod.ext ?_ heq
  rw [(hs h hhJ).1, hΓ0]

end KAM.Planetary

end
