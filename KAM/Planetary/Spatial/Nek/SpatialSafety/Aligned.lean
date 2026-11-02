/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Nek.Drift
public import KAM.Planetary.Spatial.Nek.SpatialSafety.Orientation
public import KAM.Planetary.Spatial.SpatialSafety.Bridge
public import KAM.Planetary.Spatial.SpatialSafety.Constants
public import KAM.Planetary.Spatial.Confinement
public import KAM.Planetary.Spatial.Osculating

/-!
# The spatial safety theorem for aligned initial states, without arithmetic hypothesis

Source: (spatial theorem the Nekhoroshev part, `LP:MAIN L14 (468–500)`, `L16 (508–529)`,
`L18 (595–597)`, `T19 (599–603)`), track LP, non-frozen.

`spatial_nek_safety_of_aligned` is the LP2 assembly `spatial_safety_of_aligned` with exactly one
change of ingredient: the Diophantine stopped drift `spatial_stopped_drift` is replaced by the
partial-convexity supplier `spatial_stopped_drift_nek`.  The drift scale is
`r = (B₀ μ)^{b_n}`, the horizon is `exp ((B₀ μ)^{-a_n}) = 1 * exp (B₀^{-a_n} μ^{-a_n})`, and the
constants depend on `(n, ν, A, δ)` only.  The orientation datum `L(z₀) = |L(z₀)| e₃` is the typing
datum of `SpatialLiftData`, discharged in `Nek/SpatialSafety/Main` by a rotation.

-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD Set

variable {n : ℕ}

/-- **The Nekhoroshev part for aligned `z₀`** (`LP:MAIN T19 (599–603)`, `L14`, `L16`, `L18`): solution-level
conclusion without Newtonian reconstruction and without rotation; no arithmetic premise. -/
theorem spatial_nek_safety_of_aligned (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 3),
        (∀ i, 0 < spaceLength (bodyVector3 z₀.1 i) ∧ spatialKeplerEnergy ν z₀ i < 0) →
        (fun i => spatialKeplerAxis ν z₀ i) ∈ A →
        angularMomentum3 z₀ = spaceLength (angularMomentum3 z₀) • e₃ →
        ∀ hch : (fun i => spatialKeplerAction ν z₀ i) ∈ chamber ν,
        spatialStrongAMD ν z₀ ≤ orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        ∃ z : ℝ → Phase (n * 3), SpatialNekSafeSol ν μ
          (T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))) hn
          (μ ^ planetaryDriftExponent n) δ AΛ Aa dStar dPair Aosc Aelem z₀ z := by
  have hn0 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hAo : PositiveStrictlyOrdered A := hAord
  have hL := isCompact_strongLSet (ν := ν) hA
  have hLch := strongLSet_subset_chamber hν hAo
  obtain ⟨rg, hg⟩ := exists_isSharedTube hν hn hL hLch hδ
  have hUc : IsCompact (sharedTube ν (strongLSet ν A) δ rg) := hg.compact
  have hUch : sharedTube ν (strongLSet ν A) δ rg ⊆ chamber ν := hg.subset_chamber
  obtain ⟨B0, hB0, μ1, hμ1, hnek⟩ := spatial_stopped_drift_nek hν hn hL hLch hg hδ
  have hB0p : 0 < B0 := by linarith
  obtain ⟨dS1, dP1, R1, P1, c1, hdS1, hdP1, -, -, -, -, hgeo⟩ :=
    spatialStrongBarrier_physical hν hn hUc hUch (half_pos hδ)
  obtain ⟨dS2, dP2, c2, hdS2, hdP2, hc2, μ2, A2, Aosc, hμ2, hA2, hAosc, hAm1, hAm2, hosc⟩ :=
    spatial_osculating_barrier hν hn hUc hUch (half_pos hδ)
  obtain ⟨C, hC⟩ := hUc.isBounded.exists_norm_le
  set S : ℝ := ∑ k, 1 / ν k ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => by have := hν k; positivity
  have hb : 0 < planetaryDriftExponent n := planetaryDriftExponent_pos n
  set Bb : ℝ := B0 ^ planetaryDriftExponent n with hBb
  have hBb0 : 0 < Bb := Real.rpow_pos_of_pos hB0p _
  set μ₀ : ℝ := min (min μ1 μ2) (min (dS1 / (2 * Aosc)) (dP1 / (4 * Aosc))) with hμ₀
  have hμ₀pos : 0 < μ₀ :=
    lt_min (lt_min hμ1 hμ2) (lt_min (by positivity) (by positivity))
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
  refine ⟨μ₀, B0 ^ (-planetaryTimeExponent n), 1, Bb / 2, Bb / 2 * (2 * max C 0 * S + 1),
    min dS1 dS2, min dP1 dP2, Aosc, A2, hμ₀pos, Real.rpow_pos_of_pos hB0p _, one_pos,
    by positivity, by positivity, lt_min hdS1 hdS2, lt_min hdP1 hdP2, hAosc, hA2, ?_, ?_, ?_⟩
  · rcases min_choice dS1 dS2 with h | h <;> rw [h] <;> assumption
  · rcases min_choice dP1 dP2 with h | h <;> rw [h] <;> assumption
  intro μ hμ hμμ₀ z₀ hphys hAz hal hch hC0
  have hμ1' : μ ≤ μ1 := hμμ₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hμ2' : μ ≤ μ2 := hμμ₀.trans hμ₀2
  obtain ⟨hr0, hr4, hbudget, hdrift⟩ := hnek μ hμ hμ1'
  have hrad : spatialNekRadius n B0 μ = Bb * μ ^ planetaryDriftExponent n := by
    unfold spatialNekRadius; rw [Real.mul_rpow hB0p.le hμ.le]
  have hhor : spatialNekHorizon n B0 μ = 1 * Real.exp (B0 ^ (-planetaryTimeExponent n) *
      μ ^ (-planetaryTimeExponent n)) := by
    unfold spatialNekHorizon; rw [Real.mul_rpow hB0p.le hμ.le, one_mul]
  have hphys' : SpatialNegativeEnergy ν z₀ := fun i => ⟨hν i, hphys i⟩
  have hC0' : spatialStrongAMD ν z₀ ≤ strongThreshold ν (spatialActionVector ν z₀) - δ := hC0
  have hlevel : δ ≤ strongThreshold ν (spatialActionVector ν z₀) := by
    linarith [spatialStrongAMD_nonneg hphys']
  have hz₀L := mem_strongLSet_spatialActionVector hAz
  have hI0 : spatialActionVector ν z₀ ∈ strongLevelSet ν (strongLSet ν A) δ := ⟨hz₀L, hlevel⟩
  have hball : ∀ I, ‖I - spatialActionVector ν z₀‖ ≤ spatialNekRadius n B0 μ →
      I ∈ sharedTube ν (strongLSet ν A) δ rg := fun I hI =>
    Metric.cthickening_mono hr4 _
      (Metric.mem_cthickening_of_dist_le I (spatialActionVector ν z₀) _
        (strongLevelSet ν (strongLSet ν A) δ) hI0 (by rwa [dist_eq_norm]))
  have hd : SpatialLiftData ν (sharedTube ν (strongLSet ν A) δ rg) z₀ δ
      (spatialNekRadius n B0 μ) :=
    ⟨hν, hn, hUc, hUch, hδ, hr0, hbudget, hphys', hball, hC0', hal⟩
  have hT : 0 < spatialNekHorizon n B0 μ := Real.exp_pos _
  have hstop := hdrift z₀ hz₀L hd
  obtain ⟨z, hz0, hsol, huniq, hall⟩ :=
    spatialStrongFirstExit_of_stopped_drift hν hn hUc hUch hδ hr0 hT hbudget hphys' hball hC0'
      hstop
  rw [hhor] at hsol huniq hall
  rw [hrad] at hall
  refine ⟨z, hz0, hsol, huniq, fun t ht => ?_⟩
  obtain ⟨hphysT, hdr, hamd, hbar⟩ := hall t ht
  have hdr' : ‖(fun i => spatialKeplerAction ν (z t) i) - fun i => spatialKeplerAction ν z₀ i‖ ≤
      Bb / 2 * μ ^ planetaryDriftExponent n := hdr.trans (le_of_eq (by ring))
  have hgeo' := hgeo (z t) hbar
  have hosc' := hosc μ hμ hμ2' (z t) hbar
  have hΛt := hbar.2.1
  refine ⟨fun i => (hphysT i).2, ⟨hUch hΛt, hamd⟩, hdr', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- axes (MAIN line 497)
    have hCm : ∀ I ∈ sharedTube ν (strongLSet ν A) δ rg, ∀ i, |I i| ≤ max C 0 := fun I hI i =>
      ((norm_le_pi_norm I i).trans (hC I hI)).trans (le_max_left _ _)
    have := spatial_norm_axis_sub_le (le_max_right C 0) (z := z t) (z' := z₀) hphysT hphys'
      (fun i => hCm _ hΛt i) (fun i => hCm (spatialActionVector ν z₀)
        (hball _ (by rw [sub_self, norm_zero]; exact hr0.le)) i) hdr'
    refine this.trans ?_
    have h1 : Bb / 2 * μ ^ planetaryDriftExponent n * (2 * max C 0) * S =
        Bb / 2 * (2 * max C 0 * S) * μ ^ planetaryDriftExponent n := by ring
    rw [h1]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hμ.le _)
    have : 0 ≤ Bb / 2 := by positivity
    nlinarith
  · -- AMD drift (MAIN (13))
    have hT1 : 0 < 1 * Real.exp (B0 ^ (-planetaryTimeExponent n) *
        μ ^ (-planetaryTimeExponent n)) := by positivity
    have h0J : (0 : ℝ) ∈ Icc (-(1 * Real.exp (B0 ^ (-planetaryTimeExponent n) *
        μ ^ (-planetaryTimeExponent n)))) (1 * Real.exp (B0 ^ (-planetaryTimeExponent n) *
        μ ^ (-planetaryTimeExponent n))) := ⟨neg_nonpos.2 hT1.le, hT1.le⟩
    have hs := spatialStrongAMD_sub_eq_sum ordConnected_Icc hsol h0J ht
    rw [hz0] at hs
    rw [hs]
    calc |∑ i, (spatialKeplerAction ν (z t) i - spatialKeplerAction ν z₀ i)|
        ≤ ∑ i, |spatialKeplerAction ν (z t) i - spatialKeplerAction ν z₀ i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, Bb / 2 * μ ^ planetaryDriftExponent n :=
          Finset.sum_le_sum fun i _ => by
            have := (norm_le_pi_norm ((fun i => spatialKeplerAction ν (z t) i) -
              fun i => spatialKeplerAction ν z₀ i) i).trans hdr'
            simpa using this
      _ = n * (Bb / 2) * μ ^ planetaryDriftExponent n := by simp; ring
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

end KAM.Planetary.Spatial

end
