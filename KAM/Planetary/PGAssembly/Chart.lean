/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.ChartLoc

/-!
# P Part 5: the chart `phi` and the location of the torus (`bpP:p5:phi-chart`, `bpP:p5:location`)

`phi_chart` shows that `phi = realAverageMap ∘ oscillatorPolar` is a chart on the open set
`phiDomain`, equivariant under the lattice and injective modulo it; `location` places the scaled
action collar inside `phiDomain` and its image inside the cylinder.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-CH.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

theorem phi_chart (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    IsOpen (phiDomain d r mu) ∧ IsChart 1 (phi d r mu h) (phiDomain d r mu) ∧
    (∀ z ∈ phiDomain d r mu, ∀ k : Fin (a+b) → ℤ, z+fullShift k ∈ phiDomain d r mu ∧
      phi d r mu h (z+fullShift k) = phi d r mu h z+fastShift (blockFast k)) ∧
    (∀ z ∈ phiDomain d r mu, ∀ z' ∈ phiDomain d r mu, ∀ k : Fin a → ℤ,
      phi d r mu h z' = phi d r mu h z+fastShift k → ∃ m : Fin (a+b) → ℤ, z'=z+fullShift m) := by
  obtain ⟨-, hinj, -, -, -, -, -, hper, hreal, hchart, -⟩ := (pg_avg d r mu h).choose_spec
  have hshift : ∀ z ∈ phiDomain d r mu, ∀ k : Fin (a+b) → ℤ, z+fullShift k ∈ phiDomain d r mu ∧
      phi d r mu h (z+fullShift k) = phi d r mu h z+fastShift (blockFast k) := fun z hz k => by
    refine ⟨phiDomain_fullShift hz k, ?_⟩
    have hz' := phiDomain_fullShift hz k
    unfold phi
    simp only [Function.comp_apply, oscillatorPolar_fullShift]
    refine realAverageMap_add_fastShift hper hreal (polar_mem_averagingDomain h hz) _ ?_
    have := polar_mem_averagingDomain h hz'
    rwa [oscillatorPolar_fullShift] at this
  refine ⟨isOpen_phiDomain, ?_, hshift, ?_⟩
  · have := (disc_measure_chart.1.mono (fun z hz => phiDomain_slow_pos h hz)).comp hchart
      (fun z hz => polar_mem_averagingDomain h hz)
    rw [one_mul] at this
    exact this
  · intro z hz z' hz' k hk
    have hm0 : blockFast (Fin.append k (0 : Fin b → ℤ)) = k := by
      funext i; simp [blockFast, Fin.append_left]
    obtain ⟨hz1, hphi1⟩ := hshift z hz (Fin.append k (0 : Fin b → ℤ))
    rw [hm0] at hphi1
    have heq : phi d r mu h z' = phi d r mu h (z + fullShift (Fin.append k (0 : Fin b → ℤ))) := by
      rw [hphi1]; exact hk
    have h1 := polar_mem_averagingDomain h hz'
    have h2 := polar_mem_averagingDomain h hz1
    have hp : oscillatorPolar z' =
        oscillatorPolar (z + fullShift (Fin.append k (0 : Fin b → ℤ))) := by
      apply KAM.realInclusion₂_injective
      apply hinj h1 h2
      rw [hreal _ h1, hreal _ h2]
      exact congrArg (KAM.realInclusion₂ (a+b)) heq
    rw [oscillatorPolar_fullShift, hm0] at hp
    exact oscillatorPolar_lattice (phiDomain_slow_pos h hz) (phiDomain_slow_pos h hz') k hp

theorem location (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    (z : Phase (a+b)) (hz : z.2 ∈ realNbhd (pgActionDomain d r mu) (params d r mu).rK) :
    angleScale (2*Real.pi) z ∈ phiDomain d r mu ∧
    phi d r mu h (angleScale (2*Real.pi) z) ∈ cylinder d.V r := by
  obtain ⟨hosc, hD1, hD2, hl1, hrK, hrKb⟩ := chart_dyn h
  have hrKl := chart_rK_lt_half h
  have hr0 : 0 < r := h.1
  obtain ⟨y, hy, hdist⟩ := hz
  have hrK0 : 0 < (params d r mu).rK := lt_of_le_of_lt dist_nonneg hdist
  have hcomp : ∀ i, |z.2 i - y i| < (params d r mu).rK := fun i => by
    have := norm_le_pi_norm (z.2 - y) i
    rw [← dist_eq_norm] at this
    simpa [Real.norm_eq_abs] using lt_of_le_of_lt this hdist
  have hdom : angleScale (2*Real.pi) z ∈ phiDomain d r mu := by
    refine ⟨⟨blockFast y, hy.1, ?_⟩, fun j _ => ?_⟩
    · rw [show (fun i => ((blockFast y i : ℝ) : ℂ)) = KAM.realInclusion a (blockFast y) from rfl,
        ← map_sub, KAM.norm_realInclusion]
      refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg hrK0.le).2 fun i => ?_) hrKb
      exact (hcomp _).le
    · have h1 := hy.2 j (mem_univ j)
      have h2 := abs_lt.1 (hcomp (Fin.natAdd a j))
      rw [params_l2_eq]
      show _ < z.2 (Fin.natAdd a j) ∧ z.2 (Fin.natAdd a j) < _
      have h3 := params_l2top d r mu
      have h4 := pow_pos hr0 2
      have h1' : (params d r mu).l1 < y (Fin.natAdd a j) ∧
          y (Fin.natAdd a j) < (params d r mu).l2top := h1
      constructor <;> linarith [h2.1, h2.2, h1'.1, h1'.2]
  refine ⟨hdom, ?_⟩
  obtain ⟨-, hinj, -, -, -, -, -, hper, hreal, hchart, hdisp⟩ := (pg_avg d r mu h).choose_spec
  have hmem := polar_mem_averagingDomain h hdom
  obtain ⟨hd1, hd2⟩ := hdisp _ hmem
  set A := pgAvg d r mu h with hA
  set w := oscillatorPolar (angleScale (2*Real.pi) z) with hw
  have hbz : blockFast w.2 = blockFast z.2 := by funext i; simp [hw, blockFast, angleScale]
  refine ⟨?_, fun j => ?_⟩
  · obtain ⟨⟨hV, hfront⟩, -⟩ := hy.1
    refine mem_of_dist_lt_innerCore hV hfront ?_
    have h1 : dist (blockFast z.2) (blockFast y) < (params d r mu).rK :=
      lt_of_le_of_lt ((dist_pi_le_iff dist_nonneg).2 fun i => dist_le_pi_dist z.2 y _) hdist
    have h2 : dist (fast (phi d r mu h (angleScale (2*Real.pi) z)).2) (blockFast w.2) ≤
        12*(pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/
          (pgWidth d*(params d r mu).gammaBar) := by
      rw [dist_eq_norm]; exact hd1
    have h3 := dist_triangle (fast (phi d r mu h (angleScale (2*Real.pi) z)).2) (blockFast w.2)
      (blockFast y)
    rw [hbz] at h2 h3
    linarith
  · have h1' : (params d r mu).l1 < y (Fin.natAdd a j) ∧
        y (Fin.natAdd a j) < (params d r mu).l2top := hy.2 j (mem_univ j)
    have h2 := abs_lt.1 (hcomp (Fin.natAdd a j))
    have hl2 := params_l2top d r mu
    have hI0 : 0 < z.2 (Fin.natAdd a j) := by linarith [h2.1, h1'.1]
    set D2 := 18*(pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/
      (pgOscRadius d*(params d r mu).gammaBar) with hD2def
    set E := (pgScales d).k1*r^(3/2:ℝ) with hE
    have hEl : E*r = (params d r mu).l1 := by
      rw [params_l1, hE, mul_assoc, ← Real.rpow_add_one hr0.ne']; norm_num
    have hnn : ∀ i, |(realAverageMap A w).2 (Fin.natAdd a i) - w.2 (Fin.natAdd a i)| ≤ D2 ∧
        |(realAverageMap A w).1 (Fin.natAdd a i) - w.1 (Fin.natAdd a i)| ≤ D2 := fun i => by
      rw [Prod.norm_def] at hd2
      constructor
      · exact (norm_le_pi_norm (blockSlow ((realAverageMap A w).2) - blockSlow w.2) i).trans
          ((le_max_left _ _).trans hd2)
      · exact (norm_le_pi_norm (blockSlow ((realAverageMap A w).1) - blockSlow w.1) i).trans
          ((le_max_right _ _).trans hd2)
    have hD0 : 0 ≤ D2 := (abs_nonneg _).trans (hnn j).1
    have hE0 : 0 ≤ E := (mul_nonneg (Real.sqrt_nonneg 2) hD0).trans hD2
    have hDE : (|(realAverageMap A w).2 (Fin.natAdd a j) - w.2 (Fin.natAdd a j)|)^2 +
        (|(realAverageMap A w).1 (Fin.natAdd a j) - w.1 (Fin.natAdd a j)|)^2 ≤ E^2 := by
      have h5 : (Real.sqrt 2*D2)^2 ≤ E^2 :=
        pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg 2) hD0) hD2 2
      have h6 : (Real.sqrt 2*D2)^2 = 2*D2^2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]
      nlinarith [pow_le_pow_left₀ (abs_nonneg _) (hnn j).1 2,
        pow_le_pow_left₀ (abs_nonneg _) (hnn j).2 2]
    have hs2 : Real.sqrt (2*z.2 (Fin.natAdd a j))^2 = 2*z.2 (Fin.natAdd a j) :=
      Real.sq_sqrt (by linarith)
    have hmar := chart_radial_margin (s := Real.sqrt (2*z.2 (Fin.natAdd a j)))
      (l := (params d r mu).l1)
      hE0 hr0 hEl (by rw [hs2]; linarith [h2.2, h1'.2])
    have := chart_disc_aux (P := w.2 (Fin.natAdd a j)) (Q := w.1 (Fin.natAdd a j))
      (p := (realAverageMap A w).2 (Fin.natAdd a j) - w.2 (Fin.natAdd a j))
      (q := (realAverageMap A w).1 (Fin.natAdd a j) - w.1 (Fin.natAdd a j))
      (Real.sqrt_nonneg _) hE0 (by
        simp only [hw, oscillatorPolar_snd_natAdd, oscillatorPolar_fst_natAdd]
        rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]; rfl)
      (by simpa [sq_abs] using hDE) hmar
    simp only [add_sub_cancel] at this
    exact this

end KAM.Planetary

end
