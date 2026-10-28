/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.AveragingNorm
public import KAM.Planetary.PGAssembly.ExtensionConsts
public import KAM.Planetary.PGAssembly.RealSlice

/-!
# P Part 5: numerical facts for the averaging adapter (`bpP:p5:avg`)

Specializations of the radius thresholds `rstar` and `param_facts` to the quantities that occur in
the hypotheses of `averaged_remainder`, and the dictionary between the P2 domains `oscDom`
and the strips of `averagingDomain`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-AV.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b n : ℕ} {d : PGData a b} {r mu : ℝ}

theorem pgAnalytic_LP_ge_one (d : PGData a b) : 1 ≤ (pgAnalytic d).LP := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := pgAnalytic_spec d
  exact h

theorem pgAnalytic_M0_ge_one (d : PGData a b) : 1 ≤ (pgAnalytic d).M0 := by
  obtain ⟨-, -, -, h, -⟩ := pgAnalytic_spec d
  exact h

theorem pgAnalytic_rho_lt (d : PGData a b) : (pgAnalytic d).rho < (pgExtension d).delta/16 := by
  obtain ⟨-, h, -⟩ := pgAnalytic_spec d
  exact h

theorem pgAnalytic_rho_pos (d : PGData a b) : 0 < (pgAnalytic d).rho := by
  obtain ⟨h, -⟩ := pgAnalytic_spec d
  exact h

theorem pgOscRadius_le_delta (d : PGData a b) : pgOscRadius d ≤ (pgExtension d).delta/4 :=
  min_le_right _ _

theorem pgWidth_eq (d : PGData a b) : pgWidth d = (pgExtension d).delta/2 := rfl

theorem av_r_lt_exp (h : admissible d (pgRstar d) r mu) : r < Real.exp (-1) := by
  obtain ⟨-, -, hRe, hRe1, -⟩ := (rstar d).choose_spec
  exact h.2.1.trans hRe1

theorem av_r_lt_exp_fifth (h : admissible d (pgRstar d) r mu) : r < Real.exp (-1/5) :=
  (av_r_lt_exp h).trans (Real.exp_lt_exp.2 (by norm_num))

theorem av_mu_mem (h : admissible d (pgRstar d) r mu) : mu ∈ Icc 0 d.mu0 :=
  ⟨h.2.2.1.le, h.2.2.2.1.le⟩

theorem av_Kbar_pos (h : admissible d (pgRstar d) r mu) : 0 < (params d r mu).Kbar := by
  rw [params_Kbar]
  have := one_le_log_inv h.1 (av_r_lt_exp h).le
  have := pgWidth_pos d
  positivity

theorem av_Kbar_mul_width (h : admissible d (pgRstar d) r mu) :
    6 ≤ (params d r mu).Kbar * pgWidth d := (param_facts d).2 r mu h |>.2.1

theorem av_Kbar_ge_one (h : admissible d (pgRstar d) r mu) : 1 ≤ (params d r mu).Kbar := by
  have h6 := av_Kbar_mul_width h
  have hw := pgWidth_lt_one d
  have hw0 := pgWidth_pos d
  by_contra hK
  push Not at hK
  nlinarith

theorem av_gamma_pos (h : admissible d (pgRstar d) r mu) : 0 < (params d r mu).gammaBar :=
  gammaBar_pos h.1 (av_r_lt_exp h).le mu

theorem av_rhoBar_pos (h : admissible d (pgRstar d) r mu) : 0 < (params d r mu).rhoBar := by
  rw [params_rhoBar]
  have := av_gamma_pos h
  have := pgAnalytic_M0_ge_one d
  have := Real.rpow_pos_of_pos (av_Kbar_pos h) (pgTau a b + 1)
  positivity

/-- The `hdyn` bundle of `rstar`. -/
theorem av_dyn (h : admissible d (pgRstar d) r mu) :
    r < (pgAnalytic d).r1/2 ∧ r < pgOscRadius d/4 ∧
      (params d r mu).Kbar*r^5 ≤ 1 ∧
      (params d r mu).rhoBar*pgWidth d ≤ (pgOscRadius d)^2 ∧
      (params d r mu).rK + 12*(pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/
        (pgWidth d*(params d r mu).gammaBar) < Real.sqrt r ∧
      Real.sqrt 2 * (18*(pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/
        (pgOscRadius d*(params d r mu).gammaBar)) ≤ (pgScales d).k1*r^(3/2:ℝ) ∧
      0 < (params d r mu).l1 ∧ (params d r mu).ell ≥ r^2/4 ∧
      (params d r mu).rhoBar ≤ (pgAnalytic d).rho ∧
      (params d r mu).l1 ≤ (params d r mu).rhoBar ∧
      mu < (pgAnalytic d).muStar ∧ pgChat a b*(params d r mu).Ehat < 1 ∧
      (params d r mu).rK < min (Real.sqrt r) ((params d r mu).l1) ∧
      (params d r mu).rK < (params d r mu).rhoBar/2 ∧
      ENNReal.ofReal (1/2)*volume d.V ≤ volume (innerCore d.V (Real.sqrt r)) ∧
      ENNReal.ofReal (1/4)*volume d.V ≤ volume (checkedCore d r mu) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hdyn⟩ := (rstar d).choose_spec
  exact hdyn r mu h

theorem av_rhoBar_le_rho (h : admissible d (pgRstar d) r mu) :
    (params d r mu).rhoBar ≤ (pgAnalytic d).rho := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := av_dyn h
  exact h9

theorem av_rhoBar_lt_delta (h : admissible d (pgRstar d) r mu) :
    (params d r mu).rhoBar < (pgExtension d).delta/16 :=
  (av_rhoBar_le_rho h).trans_lt (pgAnalytic_rho_lt d)

theorem av_rhoBar_width (h : admissible d (pgRstar d) r mu) :
    (params d r mu).rhoBar*pgWidth d ≤ (pgOscRadius d)^2 := by
  obtain ⟨-, -, -, h4, -⟩ := av_dyn h
  exact h4

theorem av_K_r5 (h : admissible d (pgRstar d) r mu) : (params d r mu).Kbar*r^5 ≤ 1 := by
  obtain ⟨-, -, h3, -⟩ := av_dyn h
  exact h3

theorem checkedCore_subset_V (d : PGData a b) (r mu : ℝ) :
    checkedCore d r mu ⊆ d.V := fun _ hI => hI.1.1

theorem actionNbhd_mono_left {N : ℕ} {X Y : Set (Fin N → ℝ)} (hXY : X ⊆ Y) (s : ℝ) :
    KAM.actionNbhd X s ⊆ KAM.actionNbhd Y s := fun _ ⟨J, hJ, hI⟩ => ⟨J, hXY hJ, hI⟩

theorem actionNbhd_checkedCore_subset (h : admissible d (pgRstar d) r mu) {s : ℝ}
    (hs : (pgExtension d).delta/16 ≤ s) :
    KAM.actionNbhd (checkedCore d r mu) ((params d r mu).rhoBar/2) ⊆
      KAM.actionNbhd (closure d.V) s := by
  have h1 := av_rhoBar_lt_delta h
  have h2 := av_rhoBar_pos h
  intro I hI
  obtain ⟨J, hJ, hIJ⟩ := hI
  exact ⟨J, subset_closure (checkedCore_subset_V d r mu hJ), hIJ.trans_le (by linarith)⟩

theorem mem_oscDom_pg {D : Set (Fin n → ℝ)} {r rp rq S : ℝ} {z : CPhase (n + b)} :
    z ∈ oscDom D r rp rq S ↔ blockFast z.1 ∈ KAM.complexStrip n S ∧
      blockFast z.2 ∈ KAM.actionNbhd D r ∧ ‖blockSlow z.2‖ < rp ∧ ‖blockSlow z.1‖ < rq :=
  mem_oscDom_iff (m := b)

end KAM.Planetary

end
