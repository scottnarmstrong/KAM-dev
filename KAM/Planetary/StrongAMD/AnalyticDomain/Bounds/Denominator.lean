/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Geometry
public import KAM.Planetary.StrongAMD.AnalyticDomain.Safety
public import KAM.Planetary.StrongAMD.AnalyticDomain.Bounds.Chart
public import KAM.Planetary.StrongAMD.AnalyticDomain.Bounds.Algebra

/-!
# Newtonian denominators stay away from zero on a thin tube

Package LP-DOMX, `LP:MAIN L8 (266–268)`, track LP, non-frozen.

`exists_tube_re_cDot_ge` is the complex-neighbourhood step of MAIN L8: the complexified chart is
within `ε` of its real trace on a thin tube (Cauchy/Lipschitz from the first-derivative bound), so
`Re (w · w) ≥ d²/2` for every star position `w = q_i` and pair difference `w = q_i - q_j`, using
`|w·w - |w₀|²| ≤ 2Qη + η²` (`re_cDot_ge`).  `exists_strongDenominatorTube` supplies the real
lower/upper bounds `dS, dP, R` from the barrier of LP-GEOMOD on the sharp core.

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary Set Metric

variable {n : ℕ} {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ r : ℝ}

/-- The complex-neighbourhood step (MAIN L8, lines 266–268), for an arbitrary chart extension with
a derivative bound on the quarter tube and real lower/upper bounds on the real trace over `K`. -/
theorem exists_tube_re_cDot_ge (hν : ∀ i, 0 < ν i) {K : Set (Phase (n + n))}
    (hKW : K ⊆ chartSafe ν) {R' C dS dP R : ℝ} (hR' : 0 < R')
    {Ψc : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → (Fin (n * 2) → ℂ) × (Fin (n * 2) → ℂ)}
    (hΨ : IsChartExtension ν K R' Ψc)
    (hC : ∀ z ∈ complexTube K (R' / 4), ‖fderiv ℂ Ψc z‖ ≤ C) (hdS : 0 < dS) (hdP : 0 < dP)
    (hstar : ∀ x ∈ K, ∀ i, dS ≤ planeLength (bodyVector (poincareProd ν 1 x).1 i) ∧
      planeLength (bodyVector (poincareProd ν 1 x).1 i) ≤ R)
    (hpair : ∀ x ∈ K, ∀ i j, i ≠ j →
      dP ≤ planeLength (bodyVector (poincareProd ν 1 x).1 i -
        bodyVector (poincareProd ν 1 x).1 j)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R' / 4 ∧ ∀ z ∈ complexTube K ρ,
      (∀ i, dS ^ 2 / 2 ≤ (cDot (cBody (Ψc z).1 i)).re) ∧
      ∀ i j, i ≠ j → dP ^ 2 / 2 ≤ (cDot (cBody (Ψc z).1 i - cBody (Ψc z).1 j)).re := by
  classical
  set d : ℝ := min dS dP with hd
  have hd0 : 0 < d := lt_min hdS hdP
  have hdS' : d ^ 2 ≤ dS ^ 2 := pow_le_pow_left₀ hd0.le (min_le_left _ _) 2
  have hdP' : d ^ 2 ≤ dP ^ 2 := pow_le_pow_left₀ hd0.le (min_le_right _ _) 2
  set Q : ℝ := 2 * max R 0 with hQ
  have hmax : 0 ≤ max R 0 := le_max_right _ _
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  set ε : ℝ := min 1 (d ^ 2 / (4 + 8 * Q)) with hε
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε ≤ d ^ 2 / (4 + 8 * Q) := min_le_right _ _
  have hsmall : 2 * ε * ε + 4 * Q * ε ≤ d ^ 2 / 2 := by
    have h1 : ε * (4 + 8 * Q) ≤ d ^ 2 := by rwa [le_div_iff₀ (by positivity)] at hε2
    nlinarith [mul_le_mul_of_nonneg_left hε1 hε0.le]
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hC'b : ∀ z ∈ complexTube K (R' / 4), ‖fderiv ℂ Ψc z‖ ≤ C' := fun z hz =>
    (hC z hz).trans (le_max_left _ _)
  set ρ : ℝ := min (R' / 4) (ε / 2 / (C' + 1)) with hρ
  have hρ0 : 0 < ρ := lt_min (by positivity) (by positivity)
  refine ⟨ρ, hρ0, min_le_left _ _, fun z hz => ?_⟩
  obtain ⟨x, ⟨k, x0, hx0, rfl⟩, hzx⟩ := hz
  have hxorb : x0 + fastShift k ∈ periodicOrbitSet K := ⟨k, x0, hx0, rfl⟩
  set cx := KAM.Nekhoroshev.complexifyPhase (x0 + fastShift k) with hcx
  have hzx' : ‖z - cx‖ < R' / 4 := hzx.trans_le (min_le_left _ _)
  have hcxT : cx ∈ complexTube K R' := ⟨_, hxorb, by simp [hcx, hR']⟩
  have hlip := norm_sub_le_of_quarterTube hΨ.holo hC'b hxorb hzx' hR'
  have hdist : ‖Ψc z - Ψc cx‖ ≤ ε / 2 := by
    refine hlip.trans ?_
    have h1 : ‖z - cx‖ ≤ ε / 2 / (C' + 1) := hzx.le.trans (min_le_right _ _)
    calc C' * ‖z - cx‖ ≤ C' * (ε / 2 / (C' + 1)) := by gcongr
      _ ≤ ε / 2 := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith [hε0]
  have hreal := hΨ.real (x0 + fastShift k) hcxT
  have hpp : poincareProd ν 1 (x0 + fastShift k) = poincareProd ν 1 x0 :=
    (poincareProd_lattice hν one_pos (hKW hx0).1 k).2
  set a := poincareProd ν 1 x0 with ha
  have hΨcx : Ψc cx = KAM.Nekhoroshev.complexifyPhase a := by rw [hcx, hreal.2, hpp]
  have hco : ∀ j, ‖(Ψc z).1 j - ((a.1 j : ℝ) : ℂ)‖ ≤ ε / 2 := by
    intro j
    have h1 : ‖(Ψc z).1 - (Ψc cx).1‖ ≤ ‖Ψc z - Ψc cx‖ := by
      simpa using norm_fst_le (Ψc z - Ψc cx)
    have h2 : ‖(Ψc z).1 j - (Ψc cx).1 j‖ ≤ ‖(Ψc z).1 - (Ψc cx).1‖ := by
      simpa using norm_le_pi_norm ((Ψc z).1 - (Ψc cx).1) j
    have h3 : (Ψc cx).1 j = ((a.1 j : ℝ) : ℂ) := by rw [hΨcx]; rfl
    rw [h3] at h2
    linarith
  have hcoord : ∀ (i : Fin n) (k : Fin 2), ‖cBody (Ψc z).1 i k - ((bodyVector a.1 i k : ℝ) : ℂ)‖
      ≤ ε / 2 := fun i k => hco _
  have hbd : ∀ (i : Fin n) (k : Fin 2), |bodyVector a.1 i k| ≤ max R 0 := by
    intro i k
    have h1 : ‖bodyVector a.1 i k‖ ≤ ‖bodyVector a.1 i‖ := norm_le_pi_norm _ k
    have h2 := KAM.Kepler.norm_le_planeLength (bodyVector a.1 i)
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (h2.trans (((hstar x0 hx0 i).2).trans (le_max_left _ _)))
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · have hw : ∀ k, ‖cBody (Ψc z).1 i k - ((bodyVector a.1 i k : ℝ) : ℂ)‖ ≤ ε := fun k =>
      (hcoord i k).trans (by linarith)
    have hu : ∀ k, |bodyVector a.1 i k| ≤ Q := fun k => (hbd i k).trans (by rw [hQ]; linarith)
    have h1 := re_cDot_ge hw hu
    have h2 : dS ^ 2 ≤ planeSq (bodyVector a.1 i) :=
      (Real.le_sqrt' hdS).1 (hstar x0 hx0 i).1
    linarith
  · have hw : ∀ k, ‖(cBody (Ψc z).1 i - cBody (Ψc z).1 j) k -
        ((((bodyVector a.1 i - bodyVector a.1 j) k : ℝ)) : ℂ)‖ ≤ ε := by
      intro k
      have e : (cBody (Ψc z).1 i - cBody (Ψc z).1 j) k -
          ((((bodyVector a.1 i - bodyVector a.1 j) k : ℝ)) : ℂ) =
          (cBody (Ψc z).1 i k - ((bodyVector a.1 i k : ℝ) : ℂ)) -
            (cBody (Ψc z).1 j k - ((bodyVector a.1 j k : ℝ) : ℂ)) := by
        simp only [Pi.sub_apply, Complex.ofReal_sub]; ring
      rw [e]
      exact (norm_sub_le _ _).trans (by linarith [hcoord i k, hcoord j k])
    have hu : ∀ k, |(bodyVector a.1 i - bodyVector a.1 j) k| ≤ Q := fun k => by
      rw [Pi.sub_apply]
      exact (abs_sub _ _).trans (by rw [hQ]; linarith [hbd i k, hbd j k])
    have h1 := re_cDot_ge hw hu
    have h2 : dP ^ 2 ≤ planeSq (bodyVector a.1 i - bodyVector a.1 j) :=
      (Real.le_sqrt' hdP).1 (hpair x0 hx0 i j hij)
    linarith

/-- The denominators of MAIN L8 on a thin tube around the sharp core: positive real bounds
`dS, dP` (from the barrier of LP-GEOMOD) and a tube width `ρ` such that
`Re (w · w) ≥ dS²/2` (stars, `w = q_i`) and `≥ dP²/2` (pairs, `w = q_i - q_j`). -/
theorem exists_strongDenominatorTube (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n)
    (hg : IsSharedTube ν L δ r) (hδ : 0 < δ) {R' C : ℝ} (hR' : 0 < R')
    {Ψc : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → (Fin (n * 2) → ℂ) × (Fin (n * 2) → ℂ)}
    (hΨ : IsChartExtension ν (strongCore ν L δ r) R' Ψc)
    (hC : ∀ z ∈ complexTube (strongCore ν L δ r) (R' / 4), ‖fderiv ℂ Ψc z‖ ≤ C) :
    ∃ dS dP ρ : ℝ, 0 < dS ∧ 0 < dP ∧ 0 < ρ ∧ ρ ≤ R' / 4 ∧
      ∀ z ∈ complexTube (strongCore ν L δ r) ρ,
        (∀ i, dS ^ 2 / 2 ≤ (cDot (cBody (Ψc z).1 i)).re) ∧
        ∀ i j, i ≠ j → dP ^ 2 / 2 ≤ (cDot (cBody (Ψc z).1 i - cBody (Ψc z).1 j)).re := by
  obtain ⟨dS, dP, R, P, c, hdS, hdP, hR, hP, hc, -, hbar⟩ :=
    strongBarrier_physical hν hn hg.compact hg.subset_chamber (m := 3 * δ / 16) (by positivity)
  have hKW : strongCore ν L δ r ⊆ chartSafe ν := strongCore_subset_chartSafe hν hn hg hδ
  have hb := fun x (hx : x ∈ strongCore ν L δ r) =>
    hbar _ (strongCore_barrierState hν hn hg hδ hx)
  obtain ⟨ρ, hρ, hρR, hz⟩ := exists_tube_re_cDot_ge hν hKW hR' hΨ hC hdS hdP
    (fun x hx i => ⟨(hb x hx).2.2.1 i, (hb x hx).2.2.2.2.1 i⟩)
    (fun x hx i j hij => (hb x hx).2.2.2.1 i j hij)
  exact ⟨dS, dP, ρ, hdS, hdP, hρ, hρR, hz⟩

end KAM.Planetary.StrongAMD

end
