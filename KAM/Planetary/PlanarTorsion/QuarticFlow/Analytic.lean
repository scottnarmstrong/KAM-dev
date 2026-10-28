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
    (hh : h ∈ Icc c d) (hh0 : 0 ≤ h) (hhT : h < T) (hT : 0 < T)
    {Γ : ℝ → (Fin 2 → ℝ) × Phase 2} {w : Phase 2}
    (hΓ : IsSolutionIn (p11cQ_aug chi) (O ×ˢ univ) (Ioo (-T) T) Γ) (hΓ0 : Γ 0 = (I, w))
    {G : ℝ → Phase 2}
    (hG : ∀ s ∈ Icc c d, HasDerivAt G (hamiltonianVectorField (chi.eval I) (G s)) s)
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

/-- Iterates of a map analytic along the orbit are analytic at the start point. -/
theorem p11cQ_iterate_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : E → E} {U : Set E} (hΨ : AnalyticOnNhd ℝ Ψ U) {u : E} {m : ℕ}
    (horb : ∀ j < m, Ψ^[j] u ∈ U) : AnalyticAt ℝ (Ψ^[m]) u := by
  induction m with
  | zero => exact analyticAt_id
  | succ m ih =>
    have h1 := ih fun j hj => horb j (Nat.lt_succ_of_lt hj)
    have h2 := hΨ _ (horb m (Nat.lt_succ_self m))
    rw [Function.iterate_succ']
    exact h2.comp h1

/-- The squared slow length is continuous. -/
theorem p11cQ_continuous_u : Continuous p11cQ_u := by
  unfold p11cQ_u; fun_prop

/-- Analytic dependence of the time-one map on `(I, z)` over the open set where the flow is
controlled by the energy estimate. -/
theorem p11cQ_time_one_analytic {O : Set (Fin 2 → ℝ)} (hO : IsOpen O) (chi : QuarticFamily O)
    {K₁ : Set (Fin 2 → ℝ)} (hK₁ : IsCompact K₁) (hK₁O : K₁ ⊆ O) {C : ℝ} (hC : 0 < C)
    (hb : ∀ I ∈ K₁, ∀ z, ‖hamiltonianVectorField (chi.eval I) z‖ ≤ C * ‖z‖ ^ 3)
    {Ω : Set (Fin 2 → ℝ)} (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K₁) :
    AnalyticOnNhd ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => p11c_flow chi.eval u.1 1 u.2)
      (Ω ×ˢ {z | 32 * C * p11cQ_u z < 1 / 2}) := by
  set ρ : ℝ := Real.sqrt (1 / (32 * C)) with hρ
  set K₂ : Set ((Fin 2 → ℝ) × Phase 2) := K₁ ×ˢ closedBall (0 : Phase 2) ρ with hK₂
  have hK₂c : IsCompact K₂ := hK₁.prod (isCompact_closedBall _ _)
  obtain ⟨U, hUo, hK₂U, hUW, T, hT, Φ, hΦa, hΦs⟩ := p11cQ_flow_compact_nbhd
    (hO.prod isOpen_univ) (p11cQ_aug_analytic chi) hK₂c (fun u hu => ⟨hK₁O hu.1, mem_univ _⟩)
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / T)
  have hm0 : (0 : ℝ) < m := lt_trans (by positivity) hm
  have hmT : 1 < m * T := (div_lt_iff₀ hT).1 hm
  set hs : ℝ := 1 / m with hhs
  have hs0 : 0 < hs := by positivity
  have hsT : hs < T := by rw [hhs, div_lt_iff₀ hm0]; linarith
  have hmh : (m : ℝ) * hs = 1 := by rw [hhs]; field_simp
  set Ψ : (Fin 2 → ℝ) × Phase 2 → (Fin 2 → ℝ) × Phase 2 := fun y => Φ hs y with hΨdef
  have hΨ : AnalyticOnNhd ℝ Ψ U := fun y hy =>
    (hΦa (hs, y) ⟨⟨by linarith, hsT⟩, hy⟩).comp (analyticAt_const.prod analyticAt_id)
  have key : ∀ I ∈ Ω, ∀ z : Phase 2, 32 * C * p11cQ_u z < 1 / 2 →
      (∀ j ≤ m, Ψ^[j] (I, z) = (I, p11c_flow chi.eval I (j * hs) z)) ∧
      ∀ t ∈ Icc (-1 : ℝ) 1, (I, p11c_flow chi.eval I t z) ∈ U := by
    intro I hI z hz
    have hIO : I ∈ O := hK₁O (hΩK hI)
    have hF1 := p11cQ_field_slice_contDiffOn chi hIO
    obtain ⟨hs0', hsol, hen⟩ := p11cQ_flow_spec (chi := chi.eval) hC hF1 (hb I (hΩK hI))
      (le_of_lt (by linarith : 32 * C * p11cQ_u z < 1))
    have hmem : ∀ t ∈ Icc (-1 : ℝ) 1, (I, p11c_flow chi.eval I t z) ∈ U := fun t ht => by
      refine hK₂U ⟨hΩK hI, ?_⟩
      rw [mem_closedBall_iff_norm, sub_zero]
      refine Real.le_sqrt_of_sq_le ((p11cQ_norm_sq_le _).trans ?_)
      have := hen t ht
      rw [le_div_iff₀ (by positivity)]
      nlinarith [p11cQ_u_nonneg z]
    refine ⟨fun j => ?_, hmem⟩
    induction j with
    | zero => intro _; simp [hs0']
    | succ j ih =>
      intro hj
      have hj' : j ≤ m := Nat.le_of_succ_le hj
      have hjh0 : 0 ≤ (j : ℝ) * hs := by positivity
      have hjh : ((j + 1 : ℕ) : ℝ) * hs ≤ 1 := by
        rw [← hmh]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hs0.le
      push_cast at hjh
      have hjt : (j : ℝ) * hs ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
      rw [Function.iterate_succ_apply', ih hj']
      obtain ⟨h0, hΓ⟩ := hΦs _ (hmem _ hjt)
      have hstep := p11cQ_step chi hF1 (T := T) (h := hs) (c := -1 - j * hs) (d := 1 - j * hs)
        (by linarith) (by linarith) ⟨by linarith, by linarith⟩ hs0.le hsT hT hΓ h0
        (G := fun s => p11c_flow chi.eval I (s + j * hs) z) (fun s hs' => by
          have := (hsol (s + j * hs) ⟨by linarith [hs'.1], by linarith [hs'.2]⟩).2
          exact this.comp_add_const s (j * hs)) (by simp)
      simp only [Ψ, hstep]
      congr 3
      push_cast; ring
  intro ⟨I, z⟩ ⟨hI, hz⟩
  obtain ⟨hit, hmem⟩ := key I hI z hz
  have horb : ∀ j < m, Ψ^[j] (I, z) ∈ U := fun j hj => by
    rw [hit j hj.le]
    refine hmem _ ⟨?_, ?_⟩
    · have : (0 : ℝ) ≤ j * hs := by positivity
      linarith
    · have : (j : ℝ) * hs ≤ m * hs := mul_le_mul_of_nonneg_right (by exact_mod_cast hj.le) hs0.le
      linarith
  have han : AnalyticAt ℝ (fun u => (Ψ^[m] u).2) (I, z) :=
    ((ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Phase 2)).analyticAt _).comp
      (p11cQ_iterate_analyticAt hΨ horb)
  refine han.congr ?_
  have hSo : IsOpen {z : Phase 2 | 32 * C * p11cQ_u z < 1 / 2} :=
    isOpen_lt (continuous_const.mul p11cQ_continuous_u) continuous_const
  filter_upwards [(hΩ.prod hSo).mem_nhds ⟨hI, hz⟩] with u hu
  obtain ⟨hit', -⟩ := key u.1 hu.1 u.2 hu.2
  simp only [hit' m le_rfl, hmh]

end KAM.Planetary

end
