/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.QuarticFlow.Analytic

/-!
# Planar quartic torsion: the quartic flow (package T9)

Blueprint P, Part 11b (`bpP:p11b:flow`, with `stepP:p11b:fl-bd` and `stepP:p11b:fl-an`): the
restricted time-one maps `p11c_flow` of the quartic Hamiltonians `chi.eval I` and the theorem
`flow`, with a compact-uniform radius `r` and constant `C`:

* the time-one map is jointly real analytic in `(I, z)` on `K × {|z| < r}`;
* the trajectory is a solution on `[-1, 1]` with `|z(t)|² ≤ 2 |z|²` (energy estimate, obtained
  from the maximal solution and `gen_confinement`; the zero initial datum is covered by uniqueness);
* the cubic displacement `|Φ¹ z - z| ≤ C |z|³`;
* the inverse is the time-one map of `-chi`, defined on the image through the backward trajectory
  (the image need not lie in the original small ball).

Modules: `QuarticFlow/Field` (cubic field bound), `Energy` (Riccati estimate, existence),
`Spec` (the flow and its specification), `Compact`/`Analytic` (analytic dependence).
-/

@[expose] public noncomputable section

open Set Metric Function
open scoped Topology

namespace KAM.Planetary

open KAM KAM.ODE

theorem p11cQ_slowLength_le (z : Phase 2) : p11c_slowLength z ≤ 2 * ‖z‖ := by
  have h : p11cQ_u z ≤ (2 * ‖z‖) ^ 2 := by nlinarith [p11cQ_u_le z]
  exact Real.sqrt_le_iff.2 ⟨by positivity, h⟩

theorem flow {O : Set (Fin 2 → ℝ)} (hO : IsOpen O) (chi : QuarticFamily O)
    (K : Set (Fin 2 → ℝ)) (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧
      AnalyticOnNhd ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => p11c_flow chi.eval u.1 1 u.2)
        (K ×ˢ {z | p11c_slowLength z < r}) ∧
      ∀ I ∈ K, ∀ z : Phase 2, p11c_slowLength z < r →
        p11c_flow chi.eval I 0 z = z ∧
        IsSolutionIn (hamiltonianVectorField (chi.eval I)) univ (Icc (-1) 1)
          (fun t => p11c_flow chi.eval I t z) ∧
        (∀ t ∈ Icc (-1 : ℝ) 1,
          (p11c_slowLength (p11c_flow chi.eval I t z)) ^ 2 ≤ 2 * (p11c_slowLength z) ^ 2) ∧
        p11c_slowLength (p11c_flow chi.eval I 1 z - z) ≤ C * (p11c_slowLength z) ^ 3 ∧
        p11c_flow (fun J w => -chi.eval J w) I 1 (p11c_flow chi.eval I 1 z) = z := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hO hKO
  have hK₁ : IsCompact (cthickening δ K) := hK.cthickening
  obtain ⟨C₀, hC₀, hb⟩ := p11cQ_field_bound chi hK₁ hsub
  have hΩ : IsOpen (thickening δ K) := isOpen_thickening
  have hΩK : thickening δ K ⊆ cthickening δ K := thickening_subset_cthickening δ K
  have hKΩ : K ⊆ thickening δ K := self_subset_thickening hδ K
  have hana := p11cQ_time_one_analytic hO chi hK₁ hsub hC₀ hb hΩ hΩK
  set r : ℝ := Real.sqrt (1 / (64 * C₀)) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hsmall : ∀ z : Phase 2, p11c_slowLength z < r → 64 * C₀ * p11cQ_u z < 1 := by
    intro z hz
    have h1 : p11c_slowLength z ^ 2 < r ^ 2 :=
      pow_lt_pow_left₀ hz (Real.sqrt_nonneg _) two_ne_zero
    rw [hr, Real.sq_sqrt (by positivity), p11cQ_slowLength_sq] at h1
    rw [lt_div_iff₀ (by positivity)] at h1
    linarith
  refine ⟨16 * C₀, r, by positivity, hr0, ?_, ?_⟩
  · refine (hana.mono ?_)
    intro u hu
    exact ⟨hKΩ hu.1, by have := hsmall u.2 hu.2; show 32 * C₀ * p11cQ_u u.2 < 1 / 2; linarith⟩
  intro I hI z hz
  have hIO : I ∈ O := hKO hI
  have hF1 := p11cQ_field_slice_contDiffOn chi hIO
  have hbI : ∀ w, ‖hamiltonianVectorField (chi.eval I) w‖ ≤ C₀ * ‖w‖ ^ 3 :=
    hb I (self_subset_cthickening K (hI))
  have hs := hsmall z hz
  obtain ⟨h0, hsol, hen⟩ := p11cQ_flow_spec (chi := chi.eval) hC₀ hF1 hbI
    (le_of_lt (by linarith : 32 * C₀ * p11cQ_u z < 1))
  refine ⟨h0, hsol, ?_, ?_, ?_⟩
  · intro t ht
    rw [p11cQ_slowLength_sq, p11cQ_slowLength_sq]
    exact hen t ht
  · have hbd : ∀ t ∈ Icc (-1 : ℝ) 1, ‖p11c_flow chi.eval I t z‖ ≤ 2 * p11c_slowLength z := by
      intro t ht
      have h1 : ‖p11c_flow chi.eval I t z‖ ^ 2 ≤ (2 * p11c_slowLength z) ^ 2 := by
        calc _ ≤ p11cQ_u (p11c_flow chi.eval I t z) := p11cQ_norm_sq_le _
          _ ≤ 2 * p11cQ_u z := hen t ht
          _ = 2 * p11c_slowLength z ^ 2 := by rw [p11cQ_slowLength_sq]
          _ ≤ (2 * p11c_slowLength z) ^ 2 := by nlinarith [sq_nonneg (p11c_slowLength z)]
      have h2 : 0 ≤ 2 * p11c_slowLength z := by
        have := Real.sqrt_nonneg (p11cQ_u z)
        unfold p11c_slowLength; positivity
      exact (sq_le_sq₀ (norm_nonneg _) h2).1 h1
    have hmv := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun t => p11c_flow chi.eval I t z)
      (f' := fun t => hamiltonianVectorField (chi.eval I) (p11c_flow chi.eval I t z))
      (C := C₀ * (2 * p11c_slowLength z) ^ 3)
      (fun t ht => (hsol t ⟨by linarith [ht.1], ht.2⟩).2.hasDerivWithinAt)
      (fun t ht => (hbI _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hbd t ⟨by linarith [ht.1], ht.2⟩) 3) hC₀.le))
      (x := 0) (y := 1) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
    simp only [h0, sub_zero, norm_one, mul_one] at hmv
    calc p11c_slowLength (p11c_flow chi.eval I 1 z - z)
        ≤ 2 * ‖p11c_flow chi.eval I 1 z - z‖ := p11cQ_slowLength_le _
      _ ≤ 2 * (C₀ * (2 * p11c_slowLength z) ^ 3) := by gcongr
      _ = 16 * C₀ * p11c_slowLength z ^ 3 := by ring
  · have hwu : 32 * C₀ * p11cQ_u (p11c_flow chi.eval I 1 z) ≤ 1 := by
      have := hen 1 ⟨by norm_num, le_rfl⟩
      nlinarith [p11cQ_u_nonneg z]
    have hF1' : ContDiffOn ℝ 1 (hamiltonianVectorField ((fun J w => -chi.eval J w) I)) univ := by
      show ContDiffOn ℝ 1 (hamiltonianVectorField (fun w => -chi.eval I w)) univ
      rw [p11cQ_ham_neg]; exact hF1.neg
    have hb' : ∀ w', ‖hamiltonianVectorField ((fun J w => -chi.eval J w) I) w'‖ ≤
        C₀ * ‖w'‖ ^ 3 := by
      intro w'
      show ‖hamiltonianVectorField (fun w => -chi.eval I w) w'‖ ≤ _
      rw [p11cQ_ham_neg]; simpa using hbI w'
    obtain ⟨h0', hsol', -⟩ := p11cQ_flow_spec (chi := fun J w => -chi.eval J w) hC₀ hF1' hb' hwu
    have hH : IsSolutionIn (hamiltonianVectorField ((fun J w => -chi.eval J w) I)) univ (Icc 0 1)
        (fun s => p11c_flow chi.eval I (1 - s) z) := by
      intro s hs'
      refine ⟨mem_univ _, ?_⟩
      have := (hsol (1 - s) ⟨by linarith [hs'.2], by linarith [hs'.1]⟩).2.comp_const_sub 1 s
      show HasDerivAt _ (hamiltonianVectorField (fun w => -chi.eval I w) _) s
      rw [p11cQ_ham_neg]
      simpa using this
    have := gen_uniqueness isOpen_univ hF1' ordConnected_Icc (t₀ := 0) ⟨le_rfl, zero_le_one⟩
      (hsol'.mono (Icc_subset_Icc (by norm_num) le_rfl)) hH (by simp [h0'])
      (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
    simpa [h0] using this

end KAM.Planetary

end
