/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Exponential.Stopped
public import KAM.Planetary.StrongAMD.Nek.Drift.Stopped
public import KAM.Planetary.StrongAMD.PlanarSafety.Constants

/-!
# The planar stopped-drift supplier of LP3 (no Diophantine premise)

Source: MAIN Lemma 14 (`LP:MAIN L14 (468–500)`) with the drift supplied by the sealed
partial-convexity Nekhoroshev theorem (`LP3-PLAN` §2.2–§2.4), track LP, non-frozen.

Every constant is chosen from `(n, ν, L, δ)` only, before `μ` and the orbit: the shared tube radius
`r_g`, the normalization `B₀ ≥ 1` of the perturbation, the finite cover of `𝓛_δ`, the thresholds of
the sealed theorem over the cells (`kepler_cell_drift`), the slow gap `ε_D`, and the budget radius.
With `ε = B₀ μ` the drift scale is `r(μ) = ε ^ b_n` and the time is `exp (ε ^ (-a_n))`.

* `exists_pos_rpow_lt`: a small base has a small power.
* `lp_stopped_drift_nek`: for `0 < μ ≤ μ₀`: `0 < r(μ) ≤ 4 r_g`, the budget
  `n r + Ω_B(r) ≤ δ/4`, and the drift `‖Λ(z t) - Λ(z₀)‖ ≤ r/2` on every stopped interval
  (`StoppedOn`) with `|t| ≤ T(μ)`.  No drift, AMD or confinement premise is assumed; the initial
  action lies in `𝓛_δ` (typing data of the sublevel).
* `lp_stopped_drift_nek_hstop`: the same in the literal `hstop` shape of
  `strongFirstExit_of_stopped_drift` (time `T₀ exp (c μ^{-a_n})`), for the assembly the planar Nekhoroshev safety.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open Set Metric KAM.Nekhoroshev

variable {n : ℕ}

/-- A small enough positive base has a small power: `ε < y → ε ^ b < x`. -/
theorem exists_pos_rpow_lt {x b : ℝ} (hx : 0 < x) (hb : 0 < b) :
    ∃ y : ℝ, 0 < y ∧ ∀ ε : ℝ, 0 < ε → ε < y → ε ^ b < x := by
  refine ⟨x ^ b⁻¹, Real.rpow_pos_of_pos hx _, fun ε hε hlt => ?_⟩
  have := Real.rpow_lt_rpow hε.le hlt hb
  rwa [Real.rpow_inv_rpow hx.le hb.ne'] at this

/-- **The planar stopped-drift supplier of LP3** (`LP:MAIN L14 (468–500)`, `LP3-PLAN` §2.4).
Constants `r_g`, `B₀ ≥ 1`, `μ₀ > 0` depending on `(n, ν, L, δ)` only.  For `0 < μ ≤ μ₀`, with
`ε = B₀ μ` and `r = ε ^ b_n`: `0 < r ≤ 4 r_g`, the budget `n r + Ω_B(r) ≤ δ/4` on the shared tube
holds, and for every initial state of the sublevel carrying `LiftData` for `r`, every moving
solution stopped on `uIcc 0 t` (`StoppedOn`) with `|t| ≤ exp (ε ^ (-a_n))`, the action drift is at
most `r/2`.  Exponents are the frozen `planetary*` names. -/
theorem lp_stopped_drift_nek (hn : 2 ≤ n) {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    {L : Set (Fin n → ℝ)} (hL : IsCompact L) (hLch : L ⊆ chamber ν) {δ : ℝ} (hδ : 0 < δ) :
    ∃ rg B0 μ₀ : ℝ, IsSharedTube ν L δ rg ∧ 1 ≤ B0 ∧ 0 < μ₀ ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
        0 < (B0 * μ) ^ planetaryDriftExponent n ∧
        (B0 * μ) ^ planetaryDriftExponent n ≤ 4 * rg ∧
        (n : ℝ) * (B0 * μ) ^ planetaryDriftExponent n +
          strongThresholdModulus ν (sharedTube ν L δ rg) ((B0 * μ) ^ planetaryDriftExponent n) ≤
            δ / 4 ∧
        ∀ z₀ : Phase (n * 2), actionVector ν z₀ ∈ strongLevelSet ν L δ →
          LiftData ν (sharedTube ν L δ rg) z₀ δ ((B0 * μ) ^ planetaryDriftExponent n) →
          ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z : ℝ → Phase (n * 2),
            IsMovingSolutionOn ν μ J z → z 0 = z₀ → ∀ t ∈ J,
            |t| ≤ Real.exp ((B0 * μ) ^ (-planetaryTimeExponent n)) →
            StoppedOn ν z₀ δ ((B0 * μ) ^ planetaryDriftExponent n) z t →
            ‖actionVector ν (z t) - actionVector ν z₀‖ ≤
              (B0 * μ) ^ planetaryDriftExponent n / 2 := by
  have hn1 : 1 ≤ n := by omega
  have hLδc := isCompact_strongLevelSet hν hn hL hLch δ
  have hLδch : strongLevelSet ν L δ ⊆ chamber ν := strongLevelSet_subset.trans hLch
  -- the Kepler collar bound depends on `(ν, 𝓛_δ)` only; the tube radius is chosen below it
  obtain ⟨ρ₀, hρ₀, hK⟩ := kepler_cell_drift (k := n) hn hn1 hν hLδc hLδch
  obtain ⟨rg₀, hg₀⟩ := exists_isSharedTube hν hn hL hLch hδ
  have hrg : 0 < min rg₀ (ρ₀ / 2) := lt_min hg₀.pos (by positivity)
  have hg : IsSharedTube ν L δ (min rg₀ (ρ₀ / 2)) :=
    isSharedTube_of_le hν hn hg₀ hrg (min_le_left _ _)
  generalize hrgdef : min rg₀ (ρ₀ / 2) = rg at hrg hg
  have hrgρ : rg ≤ ρ₀ / 2 := hrgdef ▸ min_le_right _ _
  -- the global perturbation and the finite cover
  obtain ⟨R, hR, B0, hB0, P, hPP, hident⟩ := exists_nekPerturbation hν hn hL hLch hg hδ
  have hB0pos : 0 < B0 := by linarith
  obtain ⟨s, hcov⟩ : ∃ s : Finset (Fin n → ℝ), IsNekCover ν L δ rg R s :=
    exists_isNekCover hν hn hL hLch hrg hR
  have hη := nekEta_pos hrg hR
  have hηrg : nekEta rg R ≤ rg := nekEta_le
  have hρη : nekRho rg R ≤ nekEta rg R := nekRho_le_eta hrg hR
  -- the threshold of the sealed theorem over the finite cell family
  obtain ⟨μ₁, hμ₁, hcell⟩ := hK (ι := s) (fun j => nekCellInner rg R j.1)
    (fun j => nekCellOuter rg R j.1) (fun j => nekCellSlow ν δ j.1) (fun _ => nekRho rg R)
    (fun j => isOpen_nekCellInner rg R j.1) (fun j => convex_nekCellInner rg R j.1)
    (fun j => isOpen_nekCellOuter rg R j.1) (fun j => convex_nekCellOuter rg R j.1)
    (fun j => isOpen_nekCellSlow ν δ j.1) (fun _ => nekRho_pos hrg hR)
    (fun j _ hI => nekCell_collar hrg hR hI)
    (fun j x hx => mem_cthickening_of_dist_le x j.1 ρ₀ (strongLevelSet ν L δ)
      (hcov.mem_levelSet j.1 j.2) (by
        have : dist x j.1 < 2 * nekEta rg R := mem_ball.1 hx
        linarith))
    (fun _ => by linarith)
  obtain ⟨εD, hεD, hgapf⟩ := exists_nekSlowGap (L := L) hn hδ s hcov.mem_levelSet
  obtain ⟨r1, hr1, hbud⟩ := exists_budget_radius hν hn hg.compact hg.subset_chamber hδ
  have hb : 0 < partialDriftExponent n := by
    rw [← planetaryDriftExponent_eq_partial]
    exact planetaryDriftExponent_pos n
  obtain ⟨y1, hy1, hy1l⟩ := exists_pos_rpow_lt (div_pos hη (by norm_num : (0 : ℝ) < 4)) hb
  obtain ⟨y2, hy2, hy2l⟩ := exists_pos_rpow_lt hεD hb
  obtain ⟨y3, hy3, hy3l⟩ := exists_pos_rpow_lt hr1 hb
  have hε₀pos : 0 < min 1 (min μ₁ (min y1 (min y2 y3))) :=
    lt_min one_pos (lt_min hμ₁ (lt_min hy1 (lt_min hy2 hy3)))
  refine ⟨rg, B0, min 1 (min μ₁ (min y1 (min y2 y3))) / (2 * B0), hg, hB0,
    div_pos hε₀pos (by linarith), ?_⟩
  simp only [planetaryDriftExponent_eq_partial, planetaryTimeExponent_eq_partial]
  intro μ hμ hμle
  have hε0 : 0 < B0 * μ := mul_pos hB0pos hμ
  have hεle : B0 * μ ≤ min 1 (min μ₁ (min y1 (min y2 y3))) / 2 :=
    calc B0 * μ ≤ B0 * (min 1 (min μ₁ (min y1 (min y2 y3))) / (2 * B0)) :=
          mul_le_mul_of_nonneg_left hμle hB0pos.le
      _ = min 1 (min μ₁ (min y1 (min y2 y3))) / 2 := by field_simp
  have hεlt : B0 * μ < min 1 (min μ₁ (min y1 (min y2 y3))) := by linarith
  have hε1 : B0 * μ < 1 := hεlt.trans_le (min_le_left _ _)
  have hεμ₁ : B0 * μ < μ₁ := hεlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεy1 : B0 * μ < y1 :=
    hεlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεy2 : B0 * μ < y2 :=
    hεlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hεy3 : B0 * μ < y3 :=
    hεlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  have hr0 : 0 < (B0 * μ) ^ partialDriftExponent n := Real.rpow_pos_of_pos hε0 _
  have hrη : (B0 * μ) ^ partialDriftExponent n < nekEta rg R / 4 := hy1l _ hε0 hεy1
  have hrεD : (B0 * μ) ^ partialDriftExponent n < εD := hy2l _ hε0 hεy2
  have hrr1 : (B0 * μ) ^ partialDriftExponent n < r1 := hy3l _ hε0 hεy3
  refine ⟨hr0, by linarith, hbud _ hr0 hrr1.le, ?_⟩
  intro z₀ hI0 hd J hJ h0 z hz hz0 t ht htT hs
  obtain ⟨c, hcs, hclose⟩ := hcov.covers _ hI0
  have hc : c ∈ strongLevelSet ν L δ := hcov.mem_levelSet c hcs
  have htT' : |t| ≤ (B0 * μ)⁻¹ * Real.exp ((B0 * μ) ^ (-partialTimeExponent n)) :=
    htT.trans (le_mul_of_one_le_left (Real.exp_pos _).le ((one_le_inv₀ hε0).2 hε1.le))
  exact nek_stopped_drift_core (μ := μ) (ε := B0 * μ) hν hn hR hg hc hd hI0 hclose hrη.le
    (hgapf c hcs _ hr0.le hrεD)
    (fun x hx => ⟨(hident c hc μ x hx).2.2.1, (hident c hc μ x hx).2.2.2⟩)
    (fun w t htT'' hsol hf0 hsl =>
      hcell (B0 * μ) hε0 hεμ₁ ⟨c, hcs⟩ P (hPP c hc).1 w t htT'' hsol hf0 hsl)
    hJ h0 hz hz0 ht htT' hs

/-- **The supplier in the exact `hstop` shape** of `strongFirstExit_of_stopped_drift`, with the
time in LP1's form `T₀ exp (c μ^{-a_n})` (`T₀ = 1`, `c = B₀^{-a_n}`) and the drift scale
`r(μ) = (B₀ μ)^{b_n}`.  The final line of the hypothesis is literally the antecedent of `hstop`
(`StoppedOn` unfolded). -/
theorem lp_stopped_drift_nek_hstop (hn : 2 ≤ n) {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i)
    {L : Set (Fin n → ℝ)} (hL : IsCompact L) (hLch : L ⊆ chamber ν) {δ : ℝ} (hδ : 0 < δ) :
    ∃ rg B0 c T₀ μ₀ : ℝ, IsSharedTube ν L δ rg ∧ 1 ≤ B0 ∧ 0 < c ∧ 0 < T₀ ∧ 0 < μ₀ ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
        0 < (B0 * μ) ^ planetaryDriftExponent n ∧
        (B0 * μ) ^ planetaryDriftExponent n ≤ 4 * rg ∧
        (n : ℝ) * (B0 * μ) ^ planetaryDriftExponent n +
          strongThresholdModulus ν (sharedTube ν L δ rg) ((B0 * μ) ^ planetaryDriftExponent n) ≤
            δ / 4 ∧
        ∀ z₀ : Phase (n * 2), actionVector ν z₀ ∈ strongLevelSet ν L δ →
          LiftData ν (sharedTube ν L δ rg) z₀ δ ((B0 * μ) ^ planetaryDriftExponent n) →
          ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z : ℝ → Phase (n * 2),
            IsMovingSolutionOn ν μ J z → z 0 = z₀ → ∀ t ∈ J,
            |t| ≤ T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n)) →
            (∀ u ∈ Set.uIcc 0 t, IsPhysicalState ν (z u) ∧
              ‖actionVector ν (z u) - actionVector ν z₀‖ < (B0 * μ) ^ planetaryDriftExponent n ∧
              strongAMD ν (z u) < strongThreshold ν (actionVector ν (z u)) - δ / 2) →
            ‖actionVector ν (z t) - actionVector ν z₀‖ ≤
              (B0 * μ) ^ planetaryDriftExponent n / 2 := by
  obtain ⟨rg, B0, μ₀, hg, hB0, hμ₀, H⟩ := lp_stopped_drift_nek hn hν hL hLch hδ
  have hB0pos : 0 < B0 := by linarith
  refine ⟨rg, B0, B0 ^ (-planetaryTimeExponent n), 1, μ₀, hg, hB0,
    Real.rpow_pos_of_pos hB0pos _, one_pos, hμ₀, fun μ hμ hμle => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := H μ hμ hμle
  refine ⟨h1, h2, h3, fun z₀ hI0 hd J hJ h0 z hz hz0 t ht htT hs => ?_⟩
  have hmul : (B0 * μ) ^ (-planetaryTimeExponent n) =
      B0 ^ (-planetaryTimeExponent n) * μ ^ (-planetaryTimeExponent n) :=
    Real.mul_rpow hB0pos.le hμ.le
  have htT' : |t| ≤ Real.exp ((B0 * μ) ^ (-planetaryTimeExponent n)) := by
    rw [hmul]
    simpa using htT
  exact h4 z₀ hI0 hd J hJ h0 z hz hz0 t ht htT' hs

end KAM.Planetary.StrongAMD

end
