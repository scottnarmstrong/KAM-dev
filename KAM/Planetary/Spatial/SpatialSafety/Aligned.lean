/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Confinement
public import KAM.Planetary.Spatial.ChartLift
public import KAM.Planetary.Spatial.NonresonantReuse
public import KAM.Planetary.Spatial.Osculating
public import KAM.Planetary.Spatial.SpatialSafety.Bridge
public import KAM.Planetary.Spatial.SpatialSafety.Constants
public import KAM.Planetary.Spatial.SpatialSafety.Orientation

/-!
# The spatial safety theorem for aligned initial states

Source: (spatial theorem LP2, `LP:MAIN L14 (468–500)`, `L16 (508–529)`,
`L18 (595–597)`, `T19 (599–603)`), track LP, non-frozen.

`spatial_safety_of_aligned` is MAIN Theorem 19 for initial states whose total angular momentum
points along `e₃`: `L(z₀) = |L(z₀)| e₃` (MAIN L18: "after aligning `e₃` with the initial total
angular momentum"; the alignment by a rotation is carried out in `SpatialSafety/Main`).  The
constants are chosen from `(ν, A, δ, γ, τ)` only (N2, N6, N10): the shared tube `U`, the drift
constants of Lemma 13 with `2n` slow pairs (`D₀ = 1`), the budget radius of (39), and the
barrier and osculating constants for `(U, δ/2)`.  The stopped drift `hstop` of the confinement
helper is discharged by `spatialChartLift_premises_nrr` and `spatial_stopped_drift`.

-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD Set

variable {n : ℕ}

/-- **MAIN Theorem 19 (with Lemma 16) for aligned `z₀`** (`LP:MAIN T19 (599–603)`, `L14`, `L16`,
`L18`, N2, N6, N10): the solution-level conclusion without the Newtonian reconstruction and
without the rotation alignment.  `L(z₀) = |L(z₀)| e₃` is the alignment of the theorem (typing
data, not a conclusion). -/
theorem spatial_safety_of_aligned (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ γ τ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) (hτ : (n : ℝ) - 1 < τ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 3),
        (∀ i, 0 < spaceLength (bodyVector3 z₀.1 i) ∧ spatialKeplerEnergy ν z₀ i < 0) →
        (fun i => spatialKeplerAxis ν z₀ i) ∈ A →
        (∀ k : Fin n → ℤ, k ≠ 0 →
          γ * (KAM.Fourier.modeSize k : ℝ) ^ (-τ) ≤
            |∑ i, (k i : ℝ) * (ν i ^ 3 / spatialKeplerAction ν z₀ i ^ 3)|) →
        angularMomentum3 z₀ = spaceLength (angularMomentum3 z₀) • e₃ →
        ∀ hch : (fun i => spatialKeplerAction ν z₀ i) ∈ chamber ν,
        spatialStrongAMD ν z₀ ≤ orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        ∃ z : ℝ → Phase (n * 3), SpatialSafeSol ν μ
          (T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1)))))) hn δ AΛ Aa dStar dPair Aosc Aelem
          z₀ z := by
  have hn0 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hτ0 : 0 < τ := by linarith
  have hAo : PositiveStrictlyOrdered A := hAord
  have hL := isCompact_strongLSet (ν := ν) hA
  have hLch := strongLSet_subset_chamber hν hAo
  obtain ⟨rg, hg⟩ := exists_isSharedTube hν hn hL hLch hδ
  have hUc : IsCompact (sharedTube ν (strongLSet ν A) δ rg) := hg.compact
  have hUch : sharedTube ν (strongLSet ν A) δ rg ⊆ chamber ν := hg.subset_chamber
  obtain ⟨μ1, c, T₀, -, -, w, hμ1, hc, hT₀, -, -, hw, hdrift⟩ :=
    spatial_stopped_drift hν hn hL hLch hδ (γ := γ) (τ := τ) (D₀ := 1) hγ hτ0 one_pos
  obtain ⟨dS1, dP1, R1, P1, c1, hdS1, hdP1, -, -, -, -, hgeo⟩ :=
    spatialStrongBarrier_physical hν hn hUc hUch (half_pos hδ)
  obtain ⟨dS2, dP2, c2, hdS2, hdP2, hc2, μ2, A2, Aosc, hμ2, hA2, hAosc, hAm1, hAm2, hosc⟩ :=
    spatial_osculating_barrier hν hn hUc hUch (half_pos hδ)
  obtain ⟨r1, hr1, hbud⟩ := exists_spatialBudget_radius hν hn hUc hUch hδ
  obtain ⟨C, hC⟩ := hUc.isBounded.exists_norm_le
  set r2 : ℝ := min r1 rg with hr2
  have hr20 : 0 < r2 := lt_min hr1 hg.pos
  set S : ℝ := ∑ k, 1 / ν k ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => by have := hν k; positivity
  set μ₀ : ℝ := min (min (min μ1 μ2) (r2 ^ 2)) (min (dS1 / (2 * Aosc)) (dP1 / (4 * Aosc)))
    with hμ₀
  have hμ₀pos : 0 < μ₀ :=
    lt_min (lt_min (lt_min hμ1 hμ2) (by positivity)) (lt_min (by positivity) (by positivity))
  have hμ₀2 : μ₀ ≤ μ2 := ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
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
  refine ⟨μ₀, c, T₀, 1 / 2, (max C 0 + 1) * (S + 1), min dS1 dS2,
    min dP1 dP2, Aosc, A2, hμ₀pos, hc, hT₀, by norm_num, by positivity,
    lt_min hdS1 hdS2, lt_min hdP1 hdP2, hAosc, hA2, ?_, ?_, ?_⟩
  · rcases min_choice dS1 dS2 with h | h <;> rw [h] <;> assumption
  · rcases min_choice dP1 dP2 with h | h <;> rw [h] <;> assumption
  intro μ hμ hμμ₀ z₀ hphys hAz hdio hal hch hC0
  have hμ1' : μ ≤ μ1 := hμμ₀.trans
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hμ2' : μ ≤ μ2 := hμμ₀.trans ((hμ₀2))
  have hμr : μ ≤ r2 ^ 2 := hμμ₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hsq : Real.sqrt μ ≤ r2 := by
    have := Real.sqrt_le_sqrt hμr
    rwa [Real.sqrt_sq hr20.le] at this
  have hr0 : 0 < 1 * Real.sqrt μ := by rw [one_mul]; exact Real.sqrt_pos.2 hμ
  have hrle : 1 * Real.sqrt μ ≤ r2 := by rwa [one_mul]
  have hphys' : SpatialNegativeEnergy ν z₀ := fun i => ⟨hν i, hphys i⟩
  have hC0' : spatialStrongAMD ν z₀ ≤ strongThreshold ν (spatialActionVector ν z₀) - δ := hC0
  have hlevel : δ ≤ strongThreshold ν (spatialActionVector ν z₀) := by
    linarith [spatialStrongAMD_nonneg hphys']
  have hI0 : spatialActionVector ν z₀ ∈ strongLevelSet ν (strongLSet ν A) δ :=
    ⟨mem_strongLSet_spatialActionVector hAz, hlevel⟩
  have hball : ∀ I, ‖I - spatialActionVector ν z₀‖ ≤ 1 * Real.sqrt μ →
      I ∈ sharedTube ν (strongLSet ν A) δ rg := fun I hI =>
    Metric.cthickening_mono (by linarith [(min_le_right r1 rg : r2 ≤ rg)]) _
      (Metric.mem_cthickening_of_dist_le I (spatialActionVector ν z₀) (1 * Real.sqrt μ)
        (strongLevelSet ν (strongLSet ν A) δ) hI0 (by rwa [dist_eq_norm]))
  have hbudget := hbud (1 * Real.sqrt μ) hr0 (hrle.trans (min_le_left _ _))
  have hd : SpatialLiftData ν (sharedTube ν (strongLSet ν A) δ rg) z₀ δ (1 * Real.sqrt μ) :=
    ⟨hν, hn, hUc, hUch, hδ, hr0, hbudget, hphys', hball, hC0', hal⟩
  have hT : 0 < T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1))))) := by positivity
  have hstop : ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z : ℝ → Phase (n * 3),
      IsSpatialMovingSolutionOn ν μ J z → z 0 = z₀ → ∀ t ∈ J,
      |t| ≤ T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1))))) →
      (∀ u ∈ uIcc 0 t, SpatialNegativeEnergy ν (z u) ∧
        ‖spatialActionVector ν (z u) - spatialActionVector ν z₀‖ < 1 * Real.sqrt μ ∧
        spatialStrongAMD ν (z u) < strongThreshold ν (spatialActionVector ν (z u)) - δ / 2) →
      ‖spatialActionVector ν (z t) - spatialActionVector ν z₀‖ ≤ 1 * Real.sqrt μ / 2 := by
    intro J hJ h0 z hz' hz0 t ht htT hs
    have hs' : SpatialStoppedOn ν z₀ δ (1 * Real.sqrt μ) z t := hs
    obtain ⟨w', hlift, hmem, hinit, hS'⟩ :=
      hd.spatialChartLift_premises_nrr (wS := w) hJ h0 hz' hz0 ht hs'
    have htT' : |t| ≤ T₀ * Real.exp (c * μ ^ (-scaleExponent τ)) := htT
    exact hdrift μ hμ hμ1' (spatialActionVector ν z₀) hI0 hdio _ rfl (J := uIcc 0 t)
      ordConnected_uIcc left_mem_uIcc z w' hlift hmem hinit right_mem_uIcc htT' hS' t
      right_mem_uIcc
  obtain ⟨z, hz0, hsol, huniq, hall⟩ :=
    spatialStrongFirstExit_of_stopped_drift hν hn hUc hUch hδ hr0 hT hbudget hphys' hball hC0'
      hstop
  refine ⟨z, hz0, hsol, huniq, fun t ht => ?_⟩
  obtain ⟨hphysT, hdr, hamd, hbar⟩ := hall t ht
  have hdr' : ‖(fun i => spatialKeplerAction ν (z t) i) - fun i => spatialKeplerAction ν z₀ i‖ ≤
      1 / 2 * Real.sqrt μ := hdr.trans (le_of_eq (by ring))
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
    have h1 : 1 / 2 * Real.sqrt μ * (2 * max C 0) * S = max C 0 * S * Real.sqrt μ := by ring
    rw [h1]
    have : max C 0 * S ≤ (max C 0 + 1) * (S + 1) := by nlinarith [le_max_right C 0]
    exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
  · -- AMD drift (MAIN (13))
    have h0J : (0 : ℝ) ∈ Icc (-(T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1)))))))
        (T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1)))))) :=
      ⟨neg_nonpos.2 hT.le, hT.le⟩
    have hs := spatialStrongAMD_sub_eq_sum ordConnected_Icc hsol h0J ht
    rw [hz0] at hs
    rw [hs]
    calc |∑ i, (spatialKeplerAction ν (z t) i - spatialKeplerAction ν z₀ i)|
        ≤ ∑ i, |spatialKeplerAction ν (z t) i - spatialKeplerAction ν z₀ i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, 1 / 2 * Real.sqrt μ := Finset.sum_le_sum fun i _ => by
          have := (norm_le_pi_norm ((fun i => spatialKeplerAction ν (z t) i) -
            fun i => spatialKeplerAction ν z₀ i) i).trans hdr'
          simpa using this
      _ = n * (1 / 2) * Real.sqrt μ := by simp; ring
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
