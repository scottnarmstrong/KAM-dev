/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Confinement
public import KAM.Planetary.StrongAMD.Osculating
public import KAM.Planetary.StrongAMD.PlanarSafety.Constants
public import KAM.Planetary.StrongAMD.Nek.Drift
public import KAM.Planetary.StrongAMD.Nek.PlanarSafety.Orientation

/-!
# The LP3 planar safety theorem for prograde initial states

Source: (planar theorem the Nekhoroshev part, `LP:MAIN L14 (468–500)`, `T15 (502–506)`,
`L16 (508–529)`), track LP, non-frozen.

`nek_planar_safety_of_prograde` is the Nekhoroshev part for initial states with `0 < L(z₀)`, with
no arithmetic
hypothesis.  It is the LP1 assembly `planar_safety_of_prograde` with exactly one change of
ingredient: the stopped drift `hstop` of the confinement helper is discharged by
`lp_stopped_drift_nek_hstop` with drift
scale `r(μ) = (B₀ μ)^{b_n}` and time `T₀ exp (c μ^{-a_n})`.  The constants are chosen from
`(n, ν, A, δ)` only.

-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary Set

variable {n : ℕ}

/-- **The Nekhoroshev part for `0 < L(z₀)`** (`LP:MAIN T15 (502–506)` with `L14`, `L16`, N2, N6,
N10, and the
Nekhoroshev drift): the solution-level conclusion without the Newtonian reconstruction and without
the orientation reduction.  `0 < totalMomentum z₀` is the orientation of the theorem. -/
theorem nek_planar_safety_of_prograde (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 2),
        (∀ i, 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0) →
        (fun i => keplerAxis ν z₀ i) ∈ A →
        0 < totalMomentum z₀ →
        ∀ hch : (fun i => keplerAction ν z₀ i) ∈ chamber ν,
        strongAMD ν z₀ ≤ orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        ∃ z : ℝ → Phase (n * 2), nekPlanarSol ν μ (μ ^ planetaryDriftExponent n)
          (T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))) hn δ AΛ Aa dStar dPair Aosc Aelem
          z₀ z := by
  have hAo : PositiveStrictlyOrdered A := hAord
  have hL := isCompact_strongLSet (ν := ν) hA
  have hLch := strongLSet_subset_chamber hν hAo
  obtain ⟨rg, B0, c, T₀, μs, hg, hB0, hc, hT₀, hμs, hsup⟩ :=
    lp_stopped_drift_nek_hstop hn hν hL hLch hδ
  have hB0pos : 0 < B0 := by linarith
  have hUc : IsCompact (sharedTube ν (strongLSet ν A) δ rg) := hg.compact
  have hUch : sharedTube ν (strongLSet ν A) δ rg ⊆ chamber ν := hg.subset_chamber
  obtain ⟨dS1, dP1, R1, P1, c1, hdS1, hdP1, -, -, -, -, hgeo⟩ :=
    strongBarrier_physical hν hn hUc hUch (half_pos hδ)
  obtain ⟨dS2, dP2, c2, hdS2, hdP2, hc2, μ2, A2, Aosc, hμ2, hA2, hAosc, hAm1, hAm2, hosc⟩ :=
    osculating_barrier hν hn hUc hUch (half_pos hδ)
  obtain ⟨C, hC⟩ := hUc.isBounded.exists_norm_le
  set S : ℝ := ∑ k, 1 / ν k ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => by have := hν k; positivity
  set μ₀ : ℝ := min (min μs μ2) (min (dS1 / (2 * Aosc)) (dP1 / (4 * Aosc)))
    with hμ₀
  have hμ₀pos : 0 < μ₀ :=
    lt_min (lt_min hμs hμ2) (lt_min (by positivity) (by positivity))
  have hμ₀2 : μ₀ ≤ μ2 := (min_le_left _ _).trans (min_le_right _ _)
  have hS1 : Aosc * μ₀ ≤ dS1 / 2 :=
    calc Aosc * μ₀ ≤ Aosc * (dS1 / (2 * Aosc)) :=
          mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_left _ _)) hAosc.le
      _ = dS1 / 2 := by field_simp
  have hP1 : 2 * (Aosc * μ₀) ≤ dP1 / 2 :=
    calc 2 * (Aosc * μ₀) ≤ 2 * (Aosc * (dP1 / (4 * Aosc))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            ((min_le_right _ _).trans (min_le_right _ _)) hAosc.le) (by norm_num)
      _ = dP1 / 2 := by field_simp; ring
  have hS2 : Aosc * μ₀ ≤ dS2 / 2 := (mul_le_mul_of_nonneg_left hμ₀2 hAosc.le).trans hAm1
  have hP2 : 2 * (Aosc * μ₀) ≤ dP2 / 2 :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hμ₀2 hAosc.le) (by norm_num)).trans hAm2
  have hBb : 0 < B0 ^ planetaryDriftExponent n := Real.rpow_pos_of_pos hB0pos _
  refine ⟨μ₀, c, T₀, B0 ^ planetaryDriftExponent n / 2,
    B0 ^ planetaryDriftExponent n * ((max C 0 + 1) * (S + 1)), min dS1 dS2,
    min dP1 dP2, Aosc, A2, hμ₀pos, hc, hT₀, by positivity, by positivity,
    lt_min hdS1 hdS2, lt_min hdP1 hdP2, hAosc, hA2, ?_, ?_, ?_⟩
  · rcases min_choice dS1 dS2 with h | h <;> rw [h] <;> assumption
  · rcases min_choice dP1 dP2 with h | h <;> rw [h] <;> assumption
  intro μ hμ hμμ₀ z₀ hphys hAz hL0 hch hC0
  have hμs' : μ ≤ μs := hμμ₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hμ2' : μ ≤ μ2 := hμμ₀.trans hμ₀2
  obtain ⟨hr0, hr4, hbudget, hdr⟩ := hsup μ hμ hμs'
  have hphys' : IsPhysicalState ν z₀ := hphys
  have hz : ∀ i, 0 < ν i ∧ 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0 :=
    fun i => ⟨hν i, hphys i⟩
  have hC0' : strongAMD ν z₀ ≤ strongThreshold ν (actionVector ν z₀) - δ := hC0
  have hlevel : δ ≤ strongThreshold ν (actionVector ν z₀) := by
    linarith [strongAMD_nonneg hz]
  have hI0 : actionVector ν z₀ ∈ strongLevelSet ν (strongLSet ν A) δ :=
    ⟨mem_strongLSet_actionVector hν hphys hAz, hlevel⟩
  have hball : ∀ I, ‖I - actionVector ν z₀‖ ≤ (B0 * μ) ^ planetaryDriftExponent n →
      I ∈ sharedTube ν (strongLSet ν A) δ rg := fun I hI =>
    Metric.cthickening_mono hr4 _
      (Metric.mem_cthickening_of_dist_le I (actionVector ν z₀) _
        (strongLevelSet ν (strongLSet ν A) δ) hI0 (by rwa [dist_eq_norm]))
  have hd : LiftData ν (sharedTube ν (strongLSet ν A) δ rg) z₀ δ
      ((B0 * μ) ^ planetaryDriftExponent n) :=
    ⟨hν, hn, hUc, hUch, hδ, hr0, hbudget, hphys', hball, hC0', hL0⟩
  have hT : 0 < T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n)) := by positivity
  have hstop := hdr z₀ hI0 hd
  obtain ⟨z, hz0, hsol, huniq, hall⟩ := strongFirstExit_of_stopped_drift hν hn hUc hUch hδ hr0 hT
    hbudget hphys' hball hC0' hstop
  refine ⟨z, hz0, hsol, huniq, fun t ht => ?_⟩
  obtain ⟨hphysT, hdr1, hamd, hbar⟩ := hall t ht
  have hmul : (B0 * μ) ^ planetaryDriftExponent n =
      B0 ^ planetaryDriftExponent n * μ ^ planetaryDriftExponent n :=
    Real.mul_rpow hB0pos.le hμ.le
  have hdr' : ‖(fun i => keplerAction ν (z t) i) - fun i => keplerAction ν z₀ i‖ ≤
      B0 ^ planetaryDriftExponent n / 2 * μ ^ planetaryDriftExponent n := by
    refine hdr1.trans (le_of_eq ?_)
    rw [hmul]; ring
  have hgeo' := hgeo (z t) hbar
  have hosc' := hosc μ hμ hμ2' (z t) hbar
  have hΛt := hbar.2.1
  refine ⟨hphysT, ⟨hUch hΛt, hamd⟩, hdr', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- axes (MAIN line 497)
    have hCm : ∀ I ∈ sharedTube ν (strongLSet ν A) δ rg, ∀ i, |I i| ≤ max C 0 := fun I hI i =>
      ((norm_le_pi_norm I i).trans (hC I hI)).trans (le_max_left _ _)
    have := norm_axis_sub_le hν (le_max_right C 0) (z := z t) (z' := z₀) hphysT hphys
      (fun i => hCm _ hΛt i) (fun i => hCm (actionVector ν z₀)
        (hball _ (by rw [sub_self, norm_zero]; exact hr0.le)) i) hdr'
    refine this.trans ?_
    have h1 : B0 ^ planetaryDriftExponent n / 2 * μ ^ planetaryDriftExponent n * (2 * max C 0) *
        S = (B0 ^ planetaryDriftExponent n * (max C 0 * S)) * μ ^ planetaryDriftExponent n := by
      ring
    rw [h1]
    have : max C 0 * S ≤ (max C 0 + 1) * (S + 1) := by nlinarith [le_max_right C 0]
    have h2 : B0 ^ planetaryDriftExponent n * (max C 0 * S) ≤
        B0 ^ planetaryDriftExponent n * ((max C 0 + 1) * (S + 1)) :=
      mul_le_mul_of_nonneg_left this hBb.le
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hμ.le _)
  · -- AMD drift (MAIN (13))
    have h0J : (0 : ℝ) ∈ Icc (-(T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))))
        (T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))) :=
      ⟨neg_nonpos.2 hT.le, hT.le⟩
    have hs := strongAMD_sub_eq_sum ordConnected_Icc hsol h0J ht
    rw [hz0] at hs
    rw [hs]
    calc |∑ i, (keplerAction ν (z t) i - keplerAction ν z₀ i)|
        ≤ ∑ i, |keplerAction ν (z t) i - keplerAction ν z₀ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, B0 ^ planetaryDriftExponent n / 2 * μ ^ planetaryDriftExponent n :=
          Finset.sum_le_sum fun i _ => by
            have := (norm_le_pi_norm ((fun i => keplerAction ν (z t) i) -
              fun i => keplerAction ν z₀ i) i).trans hdr'
            simpa using this
      _ = n * (B0 ^ planetaryDriftExponent n / 2) * μ ^ planetaryDriftExponent n := by
          simp; ring
  · exact fun i => (min_le_left _ _).trans (hgeo'.1 i)
  · exact fun a => (min_le_left _ _).trans (hgeo'.2.1 a)
  · exact fun i => (min_le_left _ _).trans (hgeo'.2.2.1 i)
  · exact fun i j hij => (min_le_left _ _).trans (hgeo'.2.2.2.1 i j hij)
  · exact fun i => by
      obtain ⟨hE, hax, hper, hapo, hecc, hsum, -, -⟩ := hosc'.2.1 i
      have hνi := hν i
      have hcν : 0 < c2 / ν i := by positivity
      exact ⟨by linarith, hax, hecc, hper, hapo, hsum⟩
  · exact fun i => by
      obtain ⟨-, -, -, -, -, -, hp, ha⟩ := hosc'.2.1 i
      exact ⟨hp, ha⟩
  · exact fun i => by
      have h1 := hosc'.2.2.1 i
      have h2 := min_le_right dS1 dS2
      linarith
  · exact fun a => by
      have h1 := hosc'.2.2.2 a
      have h2 := min_le_right dP1 dP2
      linarith

end KAM.Planetary.StrongAMD

end
