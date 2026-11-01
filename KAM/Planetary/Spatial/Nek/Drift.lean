/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Nek.Drift.Kepler
public import KAM.Planetary.Spatial.Nek.Drift.Slow
public import KAM.Planetary.StrongAMD.PlanarSafety.Constants

/-!
# The spatial stopped-drift supplier from the partial-convexity Nekhoroshev theorem (LP3-SP-DRIFT)

Package LP3-SP-DRIFT, `LP:MAIN L14 (468–500)` with `LP:MAIN L18 (595–597)` and the sealed
partial-convexity Nekhoroshev theorem (D58), as planned in `docs/tracks/LP/lp3/LP3-PLAN.md` §2.4
(eight steps) and §2.5 (`k = n + n` slow pairs), track LP, non-frozen. The statement surface is
proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

`spatial_stopped_drift_nek` is the spatial twin of the plan's `lp_stopped_drift_nek`, in the exact
`hstop` shape of `spatialStrongFirstExit_of_stopped_drift` with `r := (B₀ μ)^{b_n}`:
the constants `B₀ ≥ 1` and `μ₀ > 0` depend only on `(n, ν, L, δ, r_g)` (the shared-tube data), and
for `0 < μ ≤ μ₀` and every aligned initial state, spatial lift data with radius `r(μ)`, order-
connected `J ∋ 0`, spatial moving solution and `t ∈ J` with `|t| ≤ T(μ)` on a stopped interval,
the action drift is at most `r(μ)/2`. No Diophantine, drift, AMD, alignment or confinement premise
is added: the alignment is `SpatialLiftData`'s typing datum, and `Λ(z₀) ∈ L` is the typing datum
that places the initial action in the level set.

The proof is the cellwise application of the frozen theorem (via `cell_drift_two_sided`,
`k = n + n`) after the chart lift of SP-LIFT: the lift, the sharpened slow bound
`C < B(c_j) − 3δ/8` (`Drift/Slow.lean`), slow erosion with constant `√(2 · 2n)`, the `V_j`-form of
the solution premise, and the forward/backward drift bound (`Drift/Kepler.lean`).
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM KAM.Planetary KAM.Planetary.StrongAMD Set Metric

variable {n : ℕ}

/-- The drift scale `r(μ) = (B₀ μ)^{b_n}`, `b_n = planetaryDriftExponent n = 3/(6n² − 3n + 14)`. -/
def spatialNekRadius (n : ℕ) (B0 μ : ℝ) : ℝ := (B0 * μ) ^ planetaryDriftExponent n

/-- The time scale `T(μ) = exp ((B₀ μ)^{-a_n})`, `a_n = planetaryTimeExponent n`. -/
def spatialNekHorizon (n : ℕ) (B0 μ : ℝ) : ℝ := Real.exp ((B0 * μ) ^ (-planetaryTimeExponent n))

/-- A positive power is small for small positive bases: `ε < κ^{1/b} → ε^b < κ`. -/
theorem exists_spatialNek_rpow_lt {b κ : ℝ} (hb : 0 < b) (hκ : 0 < κ) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ε ^ b < κ :=
  ⟨κ ^ b⁻¹, Real.rpow_pos_of_pos hκ _, fun ε hε hlt => by
    have := Real.rpow_lt_rpow hε.le hlt hb
    rwa [Real.rpow_inv_rpow hκ.le hb.ne'] at this⟩

/-- **The spatial stopped drift** (`LP3-PLAN` §2.4, §2.5; `LP:MAIN L14 (468–500)`, `d = 3`).
Fix `n ≥ 2`, positive masses, a compact `L ⊆ chamber ν`, `0 < δ` and the shared tube
`IsSharedTube ν L δ r_g`. There are `B₀ ≥ 1` and `μ₀ > 0` such that for `0 < μ ≤ μ₀`, with
`r = (B₀ μ)^{b_n}` and `T = exp ((B₀ μ)^{-a_n})`:

* `0 < r ≤ 4 r_g` and the budget `n r + Ω_B(r) ≤ δ/4` on the shared tube
  (the `hball` and `hbudget` inputs of `spatialStrongFirstExit_of_stopped_drift`);
* the literal `hstop` antecedent of `spatialStrongFirstExit_of_stopped_drift` (with `r := r`,
  `T := T`) for every `z₀` with `Λ(z₀) ∈ L` carrying `SpatialLiftData ν U z₀ δ r`
  (`U = sharedTube ν L δ r_g`): every stopped state drifts by at most `r/2`. -/
theorem spatial_stopped_drift_nek {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    {L : Set (Fin n → ℝ)} (hL : IsCompact L) (hLch : L ⊆ chamber ν) {δ rg : ℝ}
    (hg : IsSharedTube ν L δ rg) (hδ : 0 < δ) :
    ∃ B0 : ℝ, 1 ≤ B0 ∧ ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      0 < spatialNekRadius n B0 μ ∧ spatialNekRadius n B0 μ ≤ 4 * rg ∧
      (n : ℝ) * spatialNekRadius n B0 μ +
          strongThresholdModulus ν (sharedTube ν L δ rg) (spatialNekRadius n B0 μ) ≤ δ / 4 ∧
      ∀ z₀ : Phase (n * 3), spatialActionVector ν z₀ ∈ L →
        SpatialLiftData ν (sharedTube ν L δ rg) z₀ δ (spatialNekRadius n B0 μ) →
        ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z : ℝ → Phase (n * 3),
          IsSpatialMovingSolutionOn ν μ J z → z 0 = z₀ → ∀ t ∈ J,
          |t| ≤ spatialNekHorizon n B0 μ →
          (∀ u ∈ Set.uIcc 0 t, SpatialNegativeEnergy ν (z u) ∧
            ‖spatialActionVector ν (z u) - spatialActionVector ν z₀‖ <
              spatialNekRadius n B0 μ ∧
            spatialStrongAMD ν (z u) <
              strongThreshold ν (spatialActionVector ν (z u)) - δ / 2) →
          ‖spatialActionVector ν (z t) - spatialActionVector ν z₀‖ ≤
            spatialNekRadius n B0 μ / 2 := by
  classical
  have hrg := hg.pos
  obtain ⟨R, hR, B0, hB0, P, hPP, hbun⟩ := exists_spatialNekPerturbation hν hn hL hLch hg hδ
  obtain ⟨s, hcov⟩ := exists_isNekCover hν hn hL hLch (δ := δ) hrg hR
  have hη := nekEta_pos hrg hR
  obtain ⟨εD, hεD, hgap⟩ := exists_spatialNekSlowGap hn hδ s hcov.mem_levelSet
  obtain ⟨r1, hr1, hbud⟩ := exists_budget_radius hν hn hg.compact hg.subset_chamber hδ
  have hcl : ∀ c ∈ s, closedBall c (nekWidth rg R) ⊆ sharedTube ν L δ rg := by
    intro c hc x hx
    exact Metric.mem_cthickening_of_dist_le x c (4 * rg) _ (hcov.mem_levelSet c hc)
      (by have := mem_closedBall.1 hx; linarith [nekWidth_le_four_mul rg R])
  obtain ⟨ε₀, hε₀, hcell⟩ := exists_spatialNek_cell_threshold (δ := δ) hn hν hg.compact
    hg.subset_chamber hrg hR s hcl
  have hb : 0 < planetaryDriftExponent n := planetaryDriftExponent_pos n
  obtain ⟨ε₁, hε₁, hrpow⟩ := exists_spatialNek_rpow_lt hb
    (κ := min (min (nekEta rg R / 4) εD) (min r1 (4 * rg)))
    (lt_min (lt_min (by linarith) hεD) (lt_min hr1 (by linarith)))
  have hB0pos : 0 < B0 := by linarith
  have hεs0 : 0 < min (min ε₀ ε₁) 1 := lt_min (lt_min hε₀ hε₁) one_pos
  refine ⟨B0, hB0, min (min ε₀ ε₁) 1 / (2 * B0), by positivity, fun μ hμ hμμ₀ => ?_⟩
  have hεle : B0 * μ ≤ min (min ε₀ ε₁) 1 / 2 :=
    calc B0 * μ ≤ B0 * (min (min ε₀ ε₁) 1 / (2 * B0)) := mul_le_mul_of_nonneg_left hμμ₀ hB0pos.le
      _ = min (min ε₀ ε₁) 1 / 2 := by field_simp
  have hεpos : 0 < B0 * μ := mul_pos hB0pos hμ
  have hεlt : B0 * μ < min (min ε₀ ε₁) 1 := by linarith
  have hε₀' : B0 * μ < ε₀ := hεlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hε1' : B0 * μ < 1 := hεlt.trans_le (min_le_right _ _)
  have hεrp := hrpow (B0 * μ) hεpos
    (hεlt.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  have hr0 : 0 < (B0 * μ) ^ planetaryDriftExponent n := Real.rpow_pos_of_pos hεpos _
  have hrη : (B0 * μ) ^ planetaryDriftExponent n ≤ nekEta rg R / 4 :=
    (hεrp.trans_le ((min_le_left _ _).trans (min_le_left _ _))).le
  have hrD : (B0 * μ) ^ planetaryDriftExponent n < εD :=
    hεrp.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hrr1 : (B0 * μ) ^ planetaryDriftExponent n ≤ r1 :=
    (hεrp.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hr4 : (B0 * μ) ^ planetaryDriftExponent n ≤ 4 * rg :=
    (hεrp.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  unfold spatialNekRadius spatialNekHorizon
  refine ⟨hr0, hr4, hbud _ hr0 hrr1, ?_⟩
  intro z₀ hz₀L hd J hJ h0 z hz hz0 t ht htT hst
  have hI0 : spatialActionVector ν z₀ ∈ strongLevelSet ν L δ :=
    ⟨hz₀L, by linarith [spatialStrongAMD_nonneg hd.physical, hd.amd]⟩
  -- step 2: the cell
  obtain ⟨c, hcs, hclose, hcore⟩ := hcov.mem_innerCore hη hI0 hrη hr0.le
  have hcL := hcov.mem_levelSet c hcs
  -- step 1: the chart lift
  obtain ⟨w, I, -, -, hsub, hwI, hproj, hw0⟩ :=
    hd.spatialChartLift_of_stopped hJ h0 hz hz0 ht hst
  have hpro := hd.spLift_prograde_of_stopped hJ h0 hz hz0 ht hst
  have hact : ∀ u ∈ uIcc (0 : ℝ) t,
      fast (b := n + n) (w u).2 = spatialActionVector ν (z u) := fun u hu => by
    have := spLiftActionVector_spatialPoincareProd hν
      (spLiftChartSafe_subset_dom ν (hwI u (hsub hu)).1)
    rw [hproj u hu] at this
    exact this.symm
  -- step 3: the fast premises
  have hinner : ∀ u ∈ uIcc (0 : ℝ) t, fast (b := n + n) (w u).2 ∈ nekCellInner rg R c :=
    fun u hu => by
      rw [hact u hu]
      exact nekCell_mem_of_close hclose hrη (hst u hu).2.1.le hη
  -- steps 4 and 5: the sharp slow bound and the slow erosion
  have hamd : ∀ u ∈ uIcc (0 : ℝ) t,
      spatialChartAMD (w u) < strongThreshold ν c - 3 * δ / 8 := fun u hu =>
    spatialNek_chart_amd_lt hν (hwI u (hsub hu)).1 (hproj u hu) (hpro u hu).2.1
      (spatialNek_sharp_slow_bound hν hn hg hd hr4 hI0 hcL hclose hst hu)
  have hslow : ∀ u ∈ uIcc (0 : ℝ) t, (slow (a := n) (w u).1, slow (a := n) (w u).2) ∈
      KAM.Nekhoroshev.innerCore (spatialNekCellSlow ν δ c)
        ((B0 * μ) ^ planetaryDriftExponent n) := fun u hu =>
    spatialNek_slow_mem_innerCore hr0.le (hgap c hcs _ hr0.le hrD) (hamd u hu)
  -- step 6: the solution premise in `V_j` form
  have hreg : ∀ u ∈ uIcc (0 : ℝ) t, w u ∈ spatialNekCellRegion rg R ν δ c := fun u hu =>
    ⟨nekCellInner_subset_outer rg R hrg hR c (hinner u hu), (hslow u hu).1⟩
  have hsol := spatialNek_isSolutionOn_of_region (K := uIcc (0 : ℝ) t)
    (G := nekCellInner rg R c) (P := P) (B0 := B0) (μ := μ)
    (fun x hx => (hbun c hcL μ x hx).2.2) hinner
    (fun u hu => ⟨hreg u hu, (hwI u (hsub hu)).2⟩)
  -- steps 7 and 8: the two-sided cell drift
  have hT' : |t| ≤ (B0 * μ)⁻¹ * Real.exp ((B0 * μ) ^ (-planetaryTimeExponent n)) :=
    htT.trans (le_mul_of_one_le_left (Real.exp_pos _).le ((one_le_inv₀ hεpos).2 hε1'.le))
  have hcore' : fast (b := n + n) (w 0).2 ∈ KAM.Nekhoroshev.innerCore (nekCellInner rg R c)
      ((B0 * μ) ^ planetaryDriftExponent n) := by
    rw [hw0]
    exact hcore
  have hdr := hcell (B0 * μ) hεpos hε₀' c hcs P (hPP c hcL).1 w t hT' hsol hcore' hslow
  rw [hact t right_mem_uIcc, hw0] at hdr
  exact hdr

end KAM.Planetary.Spatial

end
