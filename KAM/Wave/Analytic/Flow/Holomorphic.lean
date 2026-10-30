/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Analytic.Flow.Limit
public import KAM.Wave.Analytic.Flow.Gronwall
public import KAM.Wave.Analytic.UniformLimit

/-!
# Holomorphic flows: the conclusions (i)-(iv)

Blueprint-W `bpW:w1:flow` (package W1-ANALYTIC). This is source-faithful infrastructure used by
several nodes; the dependency graph is still being built.

For `h : FlowHyp X V U M δ` and `φ = holoFlow X`:

* (i) `holoFlow_zero`, `norm_holoFlow_sub_le`, `hasDerivWithinAt_holoFlow` (a `C¹` curve with
  `d/dt φ^t(w) = X (φ^t w)`, values in `V`), and uniqueness `eq_holoFlow_of_solution`;
* (ii) `holomorphicOn_holoFlow`, `norm_fderiv_holoFlow_le`;
* (iii) `holoFlow_mem_range` (reality, for a complexification `ι` with left inverse `re`);
* (iv) `norm_holoFlow_sub_holoFlow_le` (Lipschitz dependence on a parameter).
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory intervalIntegral Filter Topology
open scoped Interval

namespace KAM.Wave

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {X : F → F} {V U : Set F} {M δ : ℝ} (h : FlowHyp X V U M δ)
include h

/-- `bpW:w1:flow` (i): the flow is a `C¹` curve solving `φ' = X φ`. -/
theorem hasDerivWithinAt_holoFlow {w : F} (hw : w ∈ U) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    HasDerivWithinAt (fun s => holoFlow X s w) (X (holoFlow X t w)) (Icc (-1) 1) t := by
  set q : ℝ → ℝ := fun σ => max (-1) (min 1 σ) with hqdef
  have hq : Continuous q := by fun_prop
  have hqI : ∀ σ ∈ Icc (-1 : ℝ) 1, q σ = σ := fun σ hσ => by
    simp [q, min_eq_right hσ.2, max_eq_right hσ.1]
  have hqmem : ∀ σ, q σ ∈ Icc (-1 : ℝ) 1 := fun σ =>
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  set g : ℝ → F := fun σ => X (holoFlow X (q σ) w) with hgdef
  have hg : Continuous g := (continuousOn_X_holoFlow h hw).comp_continuous hq hqmem
  have hgt : g t = X (holoFlow X t w) := by simp [g, hqI t ht]
  have key : HasDerivAt (fun u => w + ∫ σ in (0 : ℝ)..u, g σ) (X (holoFlow X t w)) t := by
    rw [← hgt]; exact (hg.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add w
  refine key.hasDerivWithinAt.congr (fun s hs => ?_) ?_
  · rw [holoFlow_eq_integral h hw hs]
    congr 1
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    simp only [g, hqI σ (uIcc_subset_Icc' hs hσ)]
  · rw [holoFlow_eq_integral h hw ht]
    congr 1
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    simp only [g, hqI σ (uIcc_subset_Icc' ht hσ)]

/-- `bpW:w1:flow` (i), uniqueness: any solution with values in `V` is the flow. -/
theorem eq_holoFlow_of_solution {w : F} (hw : w ∈ U) {γ : ℝ → F}
    (hγd : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt γ (X (γ t)) (Icc (-1) 1) t)
    (hγV : ∀ t ∈ Icc (-1 : ℝ) 1, γ t ∈ V) (h0 : γ 0 = w) :
    ∀ t ∈ Icc (-1 : ℝ) 1, γ t = holoFlow X t w := by
  have hL : 0 ≤ M / δ := div_nonneg h.M_pos.le h.delta_pos.le
  have hball : ∀ t ∈ Icc (-1 : ℝ) 1, γ t ∈ ball w δ := fun t ht => by
    have := norm_sub_le_of_deriv_bound hγd (fun t ht => h.bound _ (hγV t ht)) ht
    rw [h0] at this
    rw [mem_ball_iff_norm]
    refine lt_of_le_of_lt this ?_
    have : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    nlinarith [h.M_lt, h.M_pos]
  have key := norm_sub_le_of_solutions (X := X) (Y := X) (B := ball w δ) (L := M / δ) (N := 0)
    hL le_rfl (h.lipschitzOn_ball hw) hγd hball (fun t ht => hasDerivWithinAt_holoFlow h hw ht)
    (fun t ht => holoFlow_mem_ball h hw ht) (fun z _ => by simp)
    (by rw [h0, holoFlow_zero h hw])
  intro t ht
  have := key t ht
  rw [mul_zero] at this
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

/-- `bpW:w1:flow` (ii): `w ↦ φ^t(w)` is holomorphic on `U`. -/
theorem holomorphicOn_holoFlow {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    DifferentiableOn ℂ (holoFlow X t) U :=
  (holomorphic_of_tendstoUniformlyOn h.isOpen_U (fun k => (picard_holo h k).diff t ht)
    (tendstoUniformlyOn_picard_U h ht)).1

/-- `bpW:w1:flow` (ii): `‖Dφ^t(w)‖ ≤ e^{L |t|}` with `L = M / δ`. -/
theorem norm_fderiv_holoFlow_le {w : F} (hw : w ∈ U) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖fderiv ℂ (holoFlow X t) w‖ ≤ Real.exp (M / δ * |t|) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp h.isOpen_U w hw
  have hsub : ball w (2 * (ε / 2)) ⊆ U := by
    rw [show 2 * (ε / 2) = ε by ring]; exact hball
  have hT := (holomorphic_of_tendstoUniformlyOn h.isOpen_U (fun k => (picard_holo h k).diff t ht)
    (tendstoUniformlyOn_picard_U h ht)).2 (by positivity) hsub
  have := hT.tendsto_at (mem_ball_self (by positivity))
  exact le_of_tendsto this.norm
    (Eventually.of_forall fun k => (picard_holo h k).bound t ht w hw)

/-- `bpW:w1:flow` (iii): reality. `ι : G →L[ℝ] F` is a closed-range real subspace of `F` with left
inverse `re` (for `F = E^ℂ`, `ι` the complexification), and `X` maps real points of `V` to real
points. -/
theorem holoFlow_mem_range {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (ι : G →L[ℝ] F) (re : F →L[ℝ] G) (hre : ∀ y, re (ι y) = y)
    (hclosed : IsClosed (range ι)) (hX : ∀ z ∈ V, z ∈ range ι → X z ∈ range ι)
    {w : F} (hw : w ∈ U) (hwR : w ∈ range ι) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    holoFlow X t w ∈ range ι := by
  have hk : ∀ k : ℕ, ∀ t ∈ Icc (-1 : ℝ) 1, wavePicard X w k t ∈ range ι := by
    intro k
    induction k with
    | zero => intro t _; simpa using hwR
    | succ k ih =>
      intro t ht
      obtain ⟨y0, rfl⟩ := hwR
      have hcongr : ∫ σ in (0 : ℝ)..t, X (wavePicard X (ι y0) k σ) =
          ∫ σ in (0 : ℝ)..t, ι (re (X (wavePicard X (ι y0) k σ))) :=
        intervalIntegral.integral_congr fun σ hσ => by
          have hσ' := uIcc_subset_Icc' ht hσ
          obtain ⟨y, hy⟩ := hX _ (h.mem_V_of_ball hw (picard_mem_ball h hw k hσ')) (ih σ hσ')
          rw [← hy, hre]
      have hint : IntervalIntegrable (fun σ => re (X (wavePicard X (ι y0) k σ))) volume 0 t :=
        (re.continuous.comp_continuousOn
          ((continuousOn_X_picard h hw k).mono (uIcc_subset_Icc' ht))).intervalIntegrable
      rw [wavePicard_succ, hcongr, ι.intervalIntegral_comp_comm hint]
      exact ⟨y0 + ∫ σ in (0 : ℝ)..t, re (X (wavePicard X (ι y0) k σ)), by simp⟩
  exact hclosed.mem_of_tendsto (tendsto_picard h hw ht)
    (Eventually.of_forall fun k => hk k t ht)

/-- `bpW:w1:flow` (iv): Lipschitz dependence of the flow on the vector field. -/
theorem norm_holoFlow_sub_holoFlow_le {Y : F → F} (hY : FlowHyp Y V U M δ) {N : ℝ} (hN : 0 ≤ N)
    (hXY : ∀ z ∈ V, ‖X z - Y z‖ ≤ N) {w : F} (hw : w ∈ U) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖holoFlow X t w - holoFlow Y t w‖ ≤ |t| * Real.exp (M / δ * |t|) * N :=
  norm_sub_le_of_solutions (X := X) (Y := Y) (B := ball w δ) (L := M / δ)
    (div_nonneg h.M_pos.le h.delta_pos.le) hN (hY.lipschitzOn_ball hw)
    (fun t ht => hasDerivWithinAt_holoFlow h hw ht) (fun t ht => holoFlow_mem_ball h hw ht)
    (fun t ht => hasDerivWithinAt_holoFlow hY hw ht) (fun t ht => holoFlow_mem_ball hY hw ht)
    (fun z hz => hXY z (h.mem_V_of_ball hw hz))
    (by rw [holoFlow_zero h hw, holoFlow_zero hY hw]) t ht

end KAM.Wave
