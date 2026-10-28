/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Characters.Defs
public import KAM.Planetary.PlanarTorsion.Setting

/-!
# Planar quartic torsion: the quartic Hamiltonian field (package T9)

Blueprint P, Part 11b (`bpP:p11b:flow`, package T9).  For a quartic family `chi` the Hamiltonian
`chi.eval I z` is jointly analytic in `(I, z)` on `O × Phase 2`, homogeneous of degree four in
`z`, so that its Hamiltonian field is homogeneous cubic and bounded by `C ‖z‖³` uniformly on a
compact parameter set `K ⊆ O` (`p11cQ_field_bound`).
-/

@[expose] public noncomputable section

open Set Metric Function
open scoped Topology

namespace KAM.Planetary

open KAM

/-- Joint real analyticity of a quartic monomial. -/
theorem p11cQ_monomial_analytic (a : Fin 4 → ℕ) :
    AnalyticOnNhd ℝ (fun z : Phase 2 => p11c_monomial a z) univ := by
  intro z _
  have h1 : ∀ i, AnalyticAt ℝ (fun w : Phase 2 => w.1 i) z := fun i =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp
      (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))).analyticAt z
  have h2 : ∀ i, AnalyticAt ℝ (fun w : Phase 2 => w.2 i) z := fun i =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp
      (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))).analyticAt z
  unfold p11c_monomial
  exact ((((h1 0).pow _).mul ((h2 0).pow _)).mul ((h1 1).pow _)).mul ((h2 1).pow _)

/-- A quartic monomial of total degree `4` is homogeneous of degree four. -/
theorem p11cQ_monomial_smul {a : Fin 4 → ℕ} (ha : ∑ i, a i = 4) (s : ℝ) (z : Phase 2) :
    p11c_monomial a (s • z) = s ^ 4 * p11c_monomial a z := by
  have h : ∑ i, a i = a 0 + a 1 + a 2 + a 3 := by simp [Fin.sum_univ_four]
  unfold p11c_monomial
  simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_pow]
  have h4 : s ^ 4 = s ^ a 0 * s ^ a 1 * s ^ a 2 * s ^ a 3 := by
    rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega
  rw [h4]; ring

/-- The quartic Hamiltonian is jointly real analytic on `O × Phase 2`. -/
theorem p11cQ_eval_analytic {O : Set (Fin 2 → ℝ)} (chi : QuarticFamily O) :
    AnalyticOnNhd ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => chi.eval u.1 u.2) (O ×ˢ univ) := by
  intro u hu
  unfold QuarticFamily.eval
  refine Finset.analyticAt_fun_sum _ fun a _ => ?_
  have h1 : AnalyticAt ℝ (fun w : (Fin 2 → ℝ) × Phase 2 =>
      chi.coeff (fun i => (a i).val) w.1) u :=
    ((chi.analytic _ u.1 hu.1).comp (analyticAt_fst (p := u)))
  have h2 : AnalyticAt ℝ (fun w : (Fin 2 → ℝ) × Phase 2 =>
      p11c_monomial (fun i => (a i).val) w.2) u :=
    ((p11cQ_monomial_analytic (fun i => (a i).val) u.2 (mem_univ _)).comp (analyticAt_snd (p := u)))
  exact h1.mul h2

/-- The quartic Hamiltonian is homogeneous of degree four in the phase variable. -/
theorem p11cQ_eval_smul {O : Set (Fin 2 → ℝ)} (chi : QuarticFamily O) (I : Fin 2 → ℝ) (s : ℝ)
    (z : Phase 2) : chi.eval I (s • z) = s ^ 4 * chi.eval I z := by
  unfold QuarticFamily.eval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hd : ∑ i, (fun i => (a i).val) i = 4 := (Finset.mem_filter.1 ha).2
  rw [p11cQ_monomial_smul hd]; ring

/-- `z ↦ f (I, z)` has `z`-derivative `fderiv f (I, z) ∘ inr`; analytic in `(I, z)`. -/
theorem p11cQ_fderiv_slice_analytic {f : (Fin 2 → ℝ) × Phase 2 → ℝ} {u : (Fin 2 → ℝ) × Phase 2}
    (hf : AnalyticAt ℝ f u) (v : Phase 2) :
    AnalyticAt ℝ (fun w : (Fin 2 → ℝ) × Phase 2 =>
      fderiv ℝ (fun z => f (w.1, z)) w.2 v) u := by
  have hD : AnalyticAt ℝ (fderiv ℝ f) u := hf.fderiv
  have hc : AnalyticAt ℝ (fun w : (Fin 2 → ℝ) × Phase 2 => fderiv ℝ f w (0, v)) u :=
    ((ContinuousLinearMap.apply ℝ ℝ ((0 : Fin 2 → ℝ), v)).analyticAt _).comp hD
  refine hc.congr ?_
  filter_upwards [hf.eventually_analyticAt] with w hw
  have hd : HasFDerivAt (fun z : Phase 2 => f (w.1, z))
      ((fderiv ℝ f w).comp (ContinuousLinearMap.inr ℝ (Fin 2 → ℝ) (Phase 2))) w.2 := by
    have h1 : HasFDerivAt (fun z : Phase 2 => ((w.1, z) : (Fin 2 → ℝ) × Phase 2))
        (ContinuousLinearMap.inr ℝ (Fin 2 → ℝ) (Phase 2)) w.2 :=
      (hasFDerivAt_const w.1 w.2).prodMk (hasFDerivAt_id w.2)
    exact (hw.differentiableAt.hasFDerivAt (x := (w.1, w.2))).comp w.2 h1
  rw [hd.fderiv]; rfl

/-- For fixed `I ∈ O` the quartic Hamiltonian is real analytic in the phase variable. -/
theorem p11cQ_eval_slice_analytic {O : Set (Fin 2 → ℝ)} (chi : QuarticFamily O) {I : Fin 2 → ℝ}
    (hI : I ∈ O) (z : Phase 2) : AnalyticAt ℝ (chi.eval I) z :=
  (p11cQ_eval_analytic chi (I, z) ⟨hI, mem_univ _⟩).comp
    (g := fun u : (Fin 2 → ℝ) × Phase 2 => chi.eval u.1 u.2)
    (analyticAt_const.prod analyticAt_id)

/-- The Hamiltonian field of the quartic family is jointly analytic on `O × Phase 2`. -/
theorem p11cQ_field_analytic {O : Set (Fin 2 → ℝ)} (chi : QuarticFamily O) :
    AnalyticOnNhd ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => hamiltonianVectorField (chi.eval u.1) u.2)
      (O ×ˢ univ) := by
  intro u hu
  have hf := p11cQ_eval_analytic chi u hu
  unfold hamiltonianVectorField
  exact AnalyticAt.prod (AnalyticAt.pi fun i => p11cQ_fderiv_slice_analytic hf _)
    (AnalyticAt.pi fun i => (p11cQ_fderiv_slice_analytic hf _).neg)

/-- The derivative of the quartic Hamiltonian is homogeneous of degree three. -/
theorem p11cQ_fderiv_smul {O : Set (Fin 2 → ℝ)} (chi : QuarticFamily O) {I : Fin 2 → ℝ}
    (hI : I ∈ O) {s : ℝ} (hs : s ≠ 0) (z v : Phase 2) :
    fderiv ℝ (chi.eval I) (s • z) v = s ^ 3 * fderiv ℝ (chi.eval I) z v := by
  have h1 : HasFDerivAt (fun w : Phase 2 => chi.eval I (s • w))
      ((fderiv ℝ (chi.eval I) (s • z)).comp (s • ContinuousLinearMap.id ℝ (Phase 2))) z :=
    ((p11cQ_eval_slice_analytic chi hI (s • z)).differentiableAt.hasFDerivAt).comp z
      ((hasFDerivAt_id z).const_smul s)
  have h2 : HasFDerivAt (fun w : Phase 2 => s ^ 4 * chi.eval I w)
      (s ^ 4 • fderiv ℝ (chi.eval I) z) z :=
    (p11cQ_eval_slice_analytic chi hI z).differentiableAt.hasFDerivAt.const_mul (s ^ 4)
  have h3 : (fun w : Phase 2 => chi.eval I (s • w)) = fun w => s ^ 4 * chi.eval I w :=
    funext fun w => p11cQ_eval_smul chi I s w
  rw [h3] at h1
  have := congrArg (fun L : Phase 2 →L[ℝ] ℝ => L v) (h1.unique h2)
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, map_smul] at this
  have h4 : s * (fderiv ℝ (chi.eval I) (s • z)) v = s * (s ^ 3 * fderiv ℝ (chi.eval I) z v) := by
    rw [this]; ring
  exact mul_left_cancel₀ hs h4

/-- The quartic Hamiltonian field is homogeneous of degree three. -/
theorem p11cQ_field_smul {O : Set (Fin 2 → ℝ)} (chi : QuarticFamily O) {I : Fin 2 → ℝ}
    (hI : I ∈ O) {s : ℝ} (hs : s ≠ 0) (z : Phase 2) :
    hamiltonianVectorField (chi.eval I) (s • z) =
      s ^ 3 • hamiltonianVectorField (chi.eval I) z := by
  unfold hamiltonianVectorField
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
    exact p11cQ_fderiv_smul chi hI hs z _
  · simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    rw [p11cQ_fderiv_smul chi hI hs z _]; ring

/-- Uniform cubic bound of the quartic Hamiltonian field on a compact parameter set. -/
theorem p11cQ_field_bound {O : Set (Fin 2 → ℝ)} (chi : QuarticFamily O) {K : Set (Fin 2 → ℝ)}
    (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ C : ℝ, 0 < C ∧ ∀ I ∈ K, ∀ z : Phase 2,
      ‖hamiltonianVectorField (chi.eval I) z‖ ≤ C * ‖z‖ ^ 3 := by
  have hS : IsCompact (K ×ˢ (sphere (0 : Phase 2) 1)) := hK.prod (isCompact_sphere _ _)
  have hc : ContinuousOn (fun u : (Fin 2 → ℝ) × Phase 2 =>
      hamiltonianVectorField (chi.eval u.1) u.2) (K ×ˢ (sphere (0 : Phase 2) 1)) :=
    (p11cQ_field_analytic chi).continuousOn.mono fun u hu => ⟨hKO hu.1, mem_univ _⟩
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hc
  refine ⟨max B 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun I hI z => ?_⟩
  by_cases hz : z = 0
  · subst hz
    have := p11cQ_field_smul chi (hKO hI) (s := 2) two_ne_zero 0
    simp only [smul_zero] at this
    have h0 : hamiltonianVectorField (chi.eval I) 0 = 0 := by
      have h8 : (7 : ℝ) • hamiltonianVectorField (chi.eval I) 0 = 0 := by
        rw [show (7 : ℝ) = 2 ^ 3 - 1 by norm_num, sub_smul, ← this]; simp
      exact (smul_eq_zero.1 h8).resolve_left (by norm_num)
    simp [h0]
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hu : ‖z‖⁻¹ • z ∈ sphere (0 : Phase 2) 1 := by
      simp [norm_smul, hn.ne']
    have := p11cQ_field_smul chi (hKO hI) (s := ‖z‖) hn.ne' (‖z‖⁻¹ • z)
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul] at this
    rw [this, norm_smul, norm_pow, norm_norm]
    have hb := hB (I, ‖z‖⁻¹ • z) ⟨hI, hu⟩
    calc ‖z‖ ^ 3 * ‖hamiltonianVectorField (chi.eval I) (‖z‖⁻¹ • z)‖
        ≤ ‖z‖ ^ 3 * max B 1 := by gcongr; exact hb.trans (le_max_left _ _)
      _ = max B 1 * ‖z‖ ^ 3 := by ring

end KAM.Planetary

end
