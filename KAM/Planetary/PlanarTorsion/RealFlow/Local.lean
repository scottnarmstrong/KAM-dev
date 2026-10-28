/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.ODE.Existence
public import KAM.ODE.Maximal
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Planetary.Defs.Phase

/-!
# Planar quartic torsion: real local Hamiltonian flow

Blueprint P, Part 11b (`bpP:p11b:e-ode`, package R1): local and maximal existence of solutions of
the real Hamiltonian system `z' = X_H(z)` for a real analytic `H` on an open `W ⊆ Phase d`, with
existence times and confinement radii that are uniform on compact subsets of `W`.  Only the
existing real ODE results `KAM.ODE.gen_uniform_compact`, `gen_uniform_exist` and `gen_maximal`
are used; no complexification and no smallness hypothesis enters.  Analytic dependence,
variational equation and symplecticity are the subject of R2 and R3.
-/

@[expose] public noncomputable section

open Set Metric
open scoped NNReal

namespace KAM.Planetary

open KAM KAM.ODE

variable {d : ℕ}

/-- The Hamiltonian vector field of a `C²` function is `C¹` on the open domain. -/
theorem p11c_hamField_contDiffOn {W : Set (Phase d)} (hW : IsOpen W) {H : Phase d → ℝ}
    (hH : ContDiffOn ℝ 2 H W) : ContDiffOn ℝ 1 (hamiltonianVectorField H) W := by
  have hD : ContDiffOn ℝ 1 (fun z => fderiv ℝ H z) W := hH.fderiv_of_isOpen hW (by norm_num)
  have hc : ∀ v : Phase d, ContDiffOn ℝ 1 (fun z => fderiv ℝ H z v) W := fun v =>
    hD.clm_apply contDiffOn_const
  refine ContDiffOn.prodMk (contDiffOn_pi.2 fun i => hc _) (contDiffOn_pi.2 fun i => ?_)
  exact (hc _).neg

/-- The Hamiltonian vector field of a real analytic function is `C¹` on the open domain. -/
theorem p11c_hamField_contDiffOn_of_analytic {W : Set (Phase d)} (hW : IsOpen W)
    {H : Phase d → ℝ} (hH : AnalyticOnNhd ℝ H W) :
    ContDiffOn ℝ 1 (hamiltonianVectorField H) W :=
  p11c_hamField_contDiffOn hW (hH.contDiffOn hW.uniqueDiffOn)

/-- Uniform local existence for the real Hamiltonian flow on a compact set `K ⊆ W`: there are
`δ, M, ε > 0`-type constants with `M` bounding the field and the closed `δ`-thickening of `K`
compact inside `W`, such that from every `y ∈ K` and every initial time there is a solution on a
time interval of length `2 ε` that stays within `δ` of `y`. -/
theorem p11c_local_flow_uniform {W : Set (Phase d)} (hW : IsOpen W) {H : Phase d → ℝ}
    (hH : AnalyticOnNhd ℝ H W) {K : Set (Phase d)} (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ (δ M ε : ℝ) (L : ℝ≥0), 0 < δ ∧ 0 < ε ∧ 0 ≤ M ∧
      closedThickening K δ ⊆ W ∧ IsCompact (closedThickening K δ) ∧
      (∀ y ∈ closedThickening K δ, ‖hamiltonianVectorField H y‖ ≤ M) ∧
      (∀ y ∈ K, LipschitzOnWith L (hamiltonianVectorField H) (closedBall y δ)) ∧
      ∀ y ∈ K, ∀ t₀ : ℝ, ∃ α : ℝ → Phase d, α t₀ = y ∧
        (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), ‖α t - y‖ < δ) ∧
        IsSolutionIn (hamiltonianVectorField H) W (Ioo (t₀ - ε) (t₀ + ε)) α := by
  obtain ⟨δ, M, L, hU, hTW, hTc⟩ :=
    gen_uniform_compact hW (p11c_hamField_contDiffOn_of_analytic hW hH) hK hKW
  have hM' : 0 < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨δ, M, δ / max M 1, L, hU.delta_pos, div_pos hU.delta_pos hM', hU.M_nonneg, hTW, hTc,
    fun y ⟨x, hx, hxy⟩ => ?_, hU.lipschitz, fun y hy t₀ => gen_uniform_exist hU y hy t₀⟩
  exact hU.norm_le x hx y (by rw [mem_closedBall, dist_eq_norm]; exact hxy)

/-- Local existence of a solution through every point of `W`, uniform on compact sets. -/
theorem p11c_local_flow_compact {W : Set (Phase d)} (hW : IsOpen W) {H : Phase d → ℝ}
    (hH : AnalyticOnNhd ℝ H W) {K : Set (Phase d)} (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ ε > 0, ∀ y ∈ K, ∀ t₀ : ℝ, ∃ α : ℝ → Phase d, α t₀ = y ∧
      IsSolutionIn (hamiltonianVectorField H) W (Ioo (t₀ - ε) (t₀ + ε)) α :=
  (gen_local hW (p11c_hamField_contDiffOn_of_analytic hW hH)).2 K hK hKW

/-- Existence and uniqueness of the maximal real Hamiltonian solution through `y ∈ W`. -/
theorem p11c_maximal_flow {W : Set (Phase d)} (hW : IsOpen W) {H : Phase d → ℝ}
    (hH : AnalyticOnNhd ℝ H W) {y : Phase d} (hy : y ∈ W) :
    (∃ (Tm Tp : EReal) (z : ℝ → Phase d),
      IsMaximalSolution (hamiltonianVectorField H) W y Tm Tp z) ∧
    ∀ (Tm Tp Tm' Tp' : EReal) (z z' : ℝ → Phase d),
      IsMaximalSolution (hamiltonianVectorField H) W y Tm Tp z →
      IsMaximalSolution (hamiltonianVectorField H) W y Tm' Tp' z' →
      Tm = Tm' ∧ Tp = Tp' ∧ EqOn z z' (eIoo Tm Tp) :=
  gen_maximal hW (p11c_hamField_contDiffOn_of_analytic hW hH) hy

end KAM.Planetary
