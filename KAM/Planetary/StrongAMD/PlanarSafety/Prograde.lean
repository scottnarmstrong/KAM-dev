/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Confinement
public import KAM.Planetary.StrongAMD.ChartLift
public import KAM.Planetary.StrongAMD.NonresonantReuse
public import KAM.Planetary.StrongAMD.Osculating
public import KAM.Planetary.StrongAMD.PlanarSafety.Constants
public import KAM.Planetary.StrongAMD.PlanarSafety.Orientation

/-!
# The planar safety theorem for prograde initial states

Package LP-PS (planar theorem LP1, `LP:MAIN L14 (468–500)`, `L15 (502–506)`, `L16 (508–529)`),
track LP, non-frozen.

`planar_safety_of_prograde` is MAIN Theorem 15 for initial states with `0 < L(z₀)` (the orientation
reduction of the theorem is in `PlanarSafety/Main`).  The constants are chosen from
`(ν, A, δ, γ, τ)` only (N2, N6, N10): the shared tube `U`, the drift constants of Lemma 13
(with `D₀ = 1`), the budget radius of (39), and the barrier/osculating constants for `(U, δ/2)`.
The stopped drift `hstop` of the confinement helper is discharged by `lpChartLift_premises` and
`lp_stopped_drift`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary Set

variable {n : ℕ}

/-- **MAIN Theorem 15 for `0 < L(z₀)`** (`LP:MAIN L15 (502–506)`, with `L14`, `L16`, N2, N6, N10):
the solution-level conclusion without the Newtonian reconstruction and without the orientation
reduction. `0 < totalMomentum z₀` is the orientation of the theorem (not a conclusion). -/
theorem planar_safety_of_prograde (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ γ τ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) (hτ : (n : ℝ) - 1 < τ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 2),
        (∀ i, 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0) →
        (fun i => keplerAxis ν z₀ i) ∈ A →
        (∀ k : Fin n → ℤ, k ≠ 0 →
          γ * (KAM.Fourier.modeSize k : ℝ) ^ (-τ) ≤
            |∑ i, (k i : ℝ) * (ν i ^ 3 / keplerAction ν z₀ i ^ 3)|) →
        0 < totalMomentum z₀ →
        ∀ hch : (fun i => keplerAction ν z₀ i) ∈ chamber ν,
        strongAMD ν z₀ ≤ orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        ∃ z : ℝ → Phase (n * 2), PlanarSafeSol ν μ
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
    lp_stopped_drift hν hn hL hLch hδ (γ := γ) (τ := τ) (D₀ := 1) hγ hτ0 one_pos
  obtain ⟨dS1, dP1, R1, P1, c1, hdS1, hdP1, -, -, -, -, hgeo⟩ :=
    strongBarrier_physical hν hn hUc hUch (half_pos hδ)
  obtain ⟨dS2, dP2, c2, hdS2, hdP2, hc2, μ2, A2, Aosc, hμ2, hA2, hAosc, hAm1, hAm2, hosc⟩ :=
    osculating_barrier hν hn hUc hUch (half_pos hδ)
  obtain ⟨r1, hr1, hbud⟩ := exists_budget_radius hν hn hUc hUch hδ
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
  intro μ hμ hμμ₀ z₀ hphys hAz hdio hL0 hch hC0
  have hμ1' : μ ≤ μ1 := hμμ₀.trans
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hμ2' : μ ≤ μ2 := hμμ₀.trans ((hμ₀2))
  have hμr : μ ≤ r2 ^ 2 := hμμ₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hsq : Real.sqrt μ ≤ r2 := by
    have := Real.sqrt_le_sqrt hμr
    rwa [Real.sqrt_sq hr20.le] at this
  have hr0 : 0 < 1 * Real.sqrt μ := by rw [one_mul]; exact Real.sqrt_pos.2 hμ
  have hrle : 1 * Real.sqrt μ ≤ r2 := by rwa [one_mul]
  have hphys' : IsPhysicalState ν z₀ := hphys
  have hz : ∀ i, 0 < ν i ∧ 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0 :=
    fun i => ⟨hν i, hphys i⟩
  have hC0' : strongAMD ν z₀ ≤ strongThreshold ν (actionVector ν z₀) - δ := hC0
  have hlevel : δ ≤ strongThreshold ν (actionVector ν z₀) := by
    linarith [strongAMD_nonneg hz]
  have hI0 : actionVector ν z₀ ∈ strongLevelSet ν (strongLSet ν A) δ :=
    ⟨mem_strongLSet_actionVector hν hphys hAz, hlevel⟩
  have hball : ∀ I, ‖I - actionVector ν z₀‖ ≤ 1 * Real.sqrt μ →
      I ∈ sharedTube ν (strongLSet ν A) δ rg := fun I hI =>
    Metric.cthickening_mono (by linarith [(min_le_right r1 rg : r2 ≤ rg)]) _
      (Metric.mem_cthickening_of_dist_le I (actionVector ν z₀) (1 * Real.sqrt μ)
        (strongLevelSet ν (strongLSet ν A) δ) hI0 (by rwa [dist_eq_norm]))
  have hbudget := hbud (1 * Real.sqrt μ) hr0 (hrle.trans (min_le_left _ _))
  have hd : LiftData ν (sharedTube ν (strongLSet ν A) δ rg) z₀ δ (1 * Real.sqrt μ) :=
    ⟨hν, hn, hUc, hUch, hδ, hr0, hbudget, hphys', hball, hC0', hL0⟩
  have hT : 0 < T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1))))) := by positivity
  have hstop : ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z : ℝ → Phase (n * 2),
      IsMovingSolutionOn ν μ J z → z 0 = z₀ → ∀ t ∈ J,
      |t| ≤ T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1))))) →
      (∀ u ∈ uIcc 0 t, IsPhysicalState ν (z u) ∧
        ‖actionVector ν (z u) - actionVector ν z₀‖ < 1 * Real.sqrt μ ∧
        strongAMD ν (z u) < strongThreshold ν (actionVector ν (z u)) - δ / 2) →
      ‖actionVector ν (z t) - actionVector ν z₀‖ ≤ 1 * Real.sqrt μ / 2 := by
    intro J hJ h0 z hz' hz0 t ht htT hs
    have hs' : StoppedOn ν z₀ δ (1 * Real.sqrt μ) z t := hs
    obtain ⟨w', hlift, hmem, hinit, hS'⟩ := lpChartLift_premises (wS := w) hd hJ h0 hz' hz0 ht hs'
    have htT' : |t| ≤ T₀ * Real.exp (c * μ ^ (-scaleExponent τ)) := htT
    exact hdrift μ hμ hμ1' (actionVector ν z₀) hI0 hdio _ rfl (J := uIcc 0 t)
      ordConnected_uIcc left_mem_uIcc z w' hlift hmem hinit right_mem_uIcc htT' hS' t
      right_mem_uIcc
  obtain ⟨z, hz0, hsol, huniq, hall⟩ := strongFirstExit_of_stopped_drift hν hn hUc hUch hδ hr0 hT
    hbudget hphys' hball hC0' hstop
  refine ⟨z, hz0, hsol, huniq, fun t ht => ?_⟩
  obtain ⟨hphysT, hdr, hamd, hbar⟩ := hall t ht
  have hdr' : ‖(fun i => keplerAction ν (z t) i) - fun i => keplerAction ν z₀ i‖ ≤
      1 / 2 * Real.sqrt μ := hdr.trans (le_of_eq (by ring))
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
    have h1 : 1 / 2 * Real.sqrt μ * (2 * max C 0) * S = max C 0 * S * Real.sqrt μ := by ring
    rw [h1]
    have : max C 0 * S ≤ (max C 0 + 1) * (S + 1) := by nlinarith [le_max_right C 0]
    exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
  · -- AMD drift (MAIN (13))
    have h0J : (0 : ℝ) ∈ Icc (-(T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1)))))))
        (T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1)))))) :=
      ⟨neg_nonpos.2 hT.le, hT.le⟩
    have hs := strongAMD_sub_eq_sum ordConnected_Icc hsol h0J ht
    rw [hz0] at hs
    rw [hs]
    calc |∑ i, (keplerAction ν (z t) i - keplerAction ν z₀ i)|
        ≤ ∑ i, |keplerAction ν (z t) i - keplerAction ν z₀ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, 1 / 2 * Real.sqrt μ := Finset.sum_le_sum fun i _ => by
          have := (norm_le_pi_norm ((fun i => keplerAction ν (z t) i) -
            fun i => keplerAction ν z₀ i) i).trans hdr'
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

end KAM.Planetary.StrongAMD

end
