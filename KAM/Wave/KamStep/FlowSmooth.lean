/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Analytic.Flow.Holomorphic
public import KAM.Wave.Analytic.Cauchy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The flow of a smoothing field (`bpW:w5:flow`, steps `f-flow`, `f-par`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

Abstract form of the smoothing statements of `bpW:w5:flow` (i). `F` is the carrier with the norm
`|·|_{p,r}`, `G` the target space of fields with the norm `|·|_{p_+,r}`, and `ι : G →L F` the
inclusion `𝒫^{p_+} ⊂ 𝒫^p` (norm `≤ 1`; in the concrete model the diagonal embedding `kamEmbed`).
A field `Z : F → G` generates the flow of `X = ι ∘ Z` on `F`; then `φ^t w - w = ι (Ψ^t w)` with
`Ψ^t w = ∫₀ᵗ Z (φ^τ w) dτ` of `G`-norm `≤ |t| M` (`holoFlow_smooth_eq`), and for two fields the
`G`-norm of `Ψ_Z - Ψ_Z'` is at most `|t| N (1 + L e^L)` (`norm_psi_sub_le`, the statement
`‖Δ(φ^t - id)‖ ≤ 2 N₁` of step `f-par`).
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory intervalIntegral Filter Topology
open scoped Interval

namespace KAM.Wave

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

/-- The generating field `X = ι ∘ Z` of the smoothing flow. -/
def smoothField (ι : G →L[ℂ] F) (Z : F → G) : F → F := fun w => ι (Z w)

/-- The `G`-valued displacement `Ψ^t w = ∫₀ᵗ Z (φ^τ w) dτ`. -/
def smoothDisp (ι : G →L[ℂ] F) (Z : F → G) (t : ℝ) (w : F) : G :=
  ∫ τ in (0 : ℝ)..t, Z (holoFlow (smoothField ι Z) τ w)

variable {ι : G →L[ℂ] F} {Z : F → G} {V U : Set F} {M δ : ℝ}

omit [CompleteSpace F] [CompleteSpace G] in
/-- `FlowHyp` for `ι ∘ Z` from the corresponding statement for `Z : F → G` and `‖ι‖ ≤ 1`. -/
theorem flowHyp_smooth (hι : ∀ g, ‖ι g‖ ≤ ‖g‖) (hV : IsOpen V) (hU : IsOpen U)
    (hZ : DifferentiableOn ℂ Z V) (hb : ∀ z ∈ V, ‖Z z‖ ≤ M)
    (hm : ∀ w ∈ U, ball w (2 * δ) ⊆ V) (hM : 0 < M) (hMδ : M < δ) :
    FlowHyp (smoothField ι Z) V U M δ where
  isOpen_V := hV
  isOpen_U := hU
  holo := ι.differentiable.comp_differentiableOn hZ
  bound := fun z hz => (hι _).trans (hb z hz)
  margin := hm
  M_pos := hM
  M_lt := hMδ

section Flow

variable (h : FlowHyp (smoothField ι Z) V U M δ) (hZ : DifferentiableOn ℂ Z V)
include h hZ

omit [CompleteSpace G] in
theorem continuousOn_smooth_integrand {w : F} (hw : w ∈ U) :
    ContinuousOn (fun τ => Z (holoFlow (smoothField ι Z) τ w)) (Icc (-1 : ℝ) 1) := by
  refine hZ.continuousOn.comp (continuousOn_holoFlow_time h hw) fun τ hτ => ?_
  exact h.mem_V_of_ball hw (holoFlow_mem_ball h hw hτ)

/-- **Smoothing of the flow** (`bpW:w5:flow` (i)): `φ^t w = w + ι (Ψ^t w)`. -/
theorem holoFlow_smooth_eq {w : F} (hw : w ∈ U) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    holoFlow (smoothField ι Z) t w = w + ι (smoothDisp ι Z t w) := by
  rw [holoFlow_eq_integral h hw ht]
  congr 1
  unfold smoothDisp
  have hint : IntervalIntegrable (fun τ => Z (holoFlow (smoothField ι Z) τ w)) volume 0 t :=
    ((continuousOn_smooth_integrand h hZ hw).mono (uIcc_subset_Icc' ht)).intervalIntegrable
  have := (ι.restrictScalars ℝ).intervalIntegral_comp_comm hint
  simpa [smoothField] using this

omit [CompleteSpace G] hZ in
/-- The `G`-norm of the displacement is `≤ |t| M`. -/
theorem norm_smoothDisp_le (hb : ∀ z ∈ V, ‖Z z‖ ≤ M) {w : F} (hw : w ∈ U) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) : ‖smoothDisp ι Z t w‖ ≤ M * |t| := by
  unfold smoothDisp
  have e : |t| = |t - 0| := by rw [sub_zero]
  rw [e]
  refine intervalIntegral.norm_integral_le_of_norm_le_const (E := G) fun τ hτ => ?_
  have hτ' : τ ∈ Icc (-1 : ℝ) 1 := uIcc_subset_Icc' ht (uIoc_subset_uIcc hτ)
  exact hb _ (h.mem_V_of_ball hw (holoFlow_mem_ball h hw hτ'))

end Flow

section Param

variable {Z' : F → G} (h : FlowHyp (smoothField ι Z) V U M δ)
  (h' : FlowHyp (smoothField ι Z') V U M δ) (hZ : DifferentiableOn ℂ Z V)
  (hZ' : DifferentiableOn ℂ Z' V) (hι : ∀ g, ‖ι g‖ ≤ ‖g‖)
include h h' hZ hZ' hι

omit [CompleteSpace G] in
/-- **Parameter dependence of the smoothing flow** (`bpW:w5:flow` step `f-par`): if
`‖Z z - Z' z‖ ≤ N` on `V` then `‖Ψ_Z^t w - Ψ_{Z'}^t w‖ ≤ |t| N (1 + L e^L)`, `L = M/δ`. -/
theorem norm_smoothDisp_sub_le (hb' : ∀ z ∈ V, ‖Z' z‖ ≤ M)
    {N : ℝ} (hN : 0 ≤ N) (hZZ : ∀ z ∈ V, ‖Z z - Z' z‖ ≤ N) {w : F} (hw : w ∈ U) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖smoothDisp ι Z t w - smoothDisp ι Z' t w‖ ≤
      |t| * (N * (1 + M / δ * Real.exp (M / δ))) := by
  have hL : 0 ≤ M / δ := div_nonneg h.M_pos.le h.delta_pos.le
  have hXY : ∀ z ∈ V, ‖smoothField ι Z z - smoothField ι Z' z‖ ≤ N := fun z hz => by
    have : smoothField ι Z z - smoothField ι Z' z = ι (Z z - Z' z) := by
      simp [smoothField]
    rw [this]; exact (hι _).trans (hZZ z hz)
  have i1 : IntervalIntegrable (fun τ => Z (holoFlow (smoothField ι Z) τ w)) volume 0 t :=
    ((continuousOn_smooth_integrand h hZ hw).mono (uIcc_subset_Icc' ht)).intervalIntegrable
  have i2 : IntervalIntegrable (fun τ => Z' (holoFlow (smoothField ι Z') τ w)) volume 0 t :=
    ((continuousOn_smooth_integrand h' hZ' hw).mono (uIcc_subset_Icc' ht)).intervalIntegrable
  unfold smoothDisp
  rw [← intervalIntegral.integral_sub i1 i2]
  have hK : 0 ≤ N * (1 + M / δ * Real.exp (M / δ)) := by positivity
  have := intervalIntegral.norm_integral_le_of_norm_le_const (E := G) (a := 0) (b := t)
    (C := N * (1 + M / δ * Real.exp (M / δ)))
    (f := fun τ => Z (holoFlow (smoothField ι Z) τ w) - Z' (holoFlow (smoothField ι Z') τ w))
    fun τ hτ => by
      have hτ' : τ ∈ Icc (-1 : ℝ) 1 := uIcc_subset_Icc' ht (uIoc_subset_uIcc hτ)
      have hτa : |τ| ≤ 1 := abs_le.mpr ⟨hτ'.1, hτ'.2⟩
      have e1 := holoFlow_mem_ball h hw hτ'
      have e2 := holoFlow_mem_ball h' hw hτ'
      have lip := lipschitz_of_margin (f := Z') h.delta_pos h.M_pos.le h.isOpen_V hZ' hb'
        (convex_ball w δ) (fun z hz => h.ball_subset_V hw hz) _ e1 _ e2
      have hΦ := norm_holoFlow_sub_holoFlow_le h h' hN hXY hw hτ'
      have hexp : Real.exp (M / δ * |τ|) ≤ Real.exp (M / δ) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hexp0 := Real.exp_pos (M / δ * |τ|)
      have hexp1 := Real.exp_pos (M / δ)
      have hτe : |τ| * Real.exp (M / δ * |τ|) ≤ Real.exp (M / δ) := by
        nlinarith [abs_nonneg τ]
      have hV1 := h.mem_V_of_ball hw e1
      have step : ‖Z (holoFlow (smoothField ι Z) τ w) - Z' (holoFlow (smoothField ι Z') τ w)‖ ≤
          ‖Z (holoFlow (smoothField ι Z) τ w) - Z' (holoFlow (smoothField ι Z) τ w)‖ +
          ‖Z' (holoFlow (smoothField ι Z) τ w) - Z' (holoFlow (smoothField ι Z') τ w)‖ := by
        have := norm_add_le (Z (holoFlow (smoothField ι Z) τ w) -
            Z' (holoFlow (smoothField ι Z) τ w))
          (Z' (holoFlow (smoothField ι Z) τ w) - Z' (holoFlow (smoothField ι Z') τ w))
        simpa using this
      have s1 := hZZ _ hV1
      have s2 : ‖Z' (holoFlow (smoothField ι Z) τ w) - Z' (holoFlow (smoothField ι Z') τ w)‖ ≤
          M / δ * (Real.exp (M / δ) * N) := by
        refine lip.trans ?_
        refine mul_le_mul_of_nonneg_left (hΦ.trans ?_) hL
        have := mul_le_mul_of_nonneg_right hτe hN
        linarith
      nlinarith
  rw [sub_zero] at this
  rw [mul_comm]; exact this

end Param

end KAM.Wave
