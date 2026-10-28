/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.HoloData

/-!
# Shrinking the radius `r_C` of `P11HoloData` (P11A-P2f)

Every clause of `P11HoloData` is monotone in `r_C`, so the interface of `p11_holo_data` restricts
to any smaller positive radius (needed to fit the strip radius `r'` of `hc-strip`).
-/

@[expose] public noncomputable section
open Set Filter Metric
namespace KAM.Planetary

section Shrink

variable {n : ℕ} {D : P11Physical n}

/-- The data `d` with a smaller radius `r_C`; all other fields unchanged. -/
def P11HoloData.shrink (d : P11HoloData D) (r : ℝ) (hr0 : 0 < r) (hr : r ≤ d.rC) :
    P11HoloData D where
  J0 := d.J0
  gamma := d.gamma
  tau := d.tau
  rC := r
  L := d.L
  Brho := d.Brho
  Bdrho := d.Bdrho
  h := d.h
  omega := d.omega
  Omega := d.Omega
  rho := d.rho
  R := d.R
  t1 := d.t1
  t2 := d.t2
  t2_pos := d.t2_pos
  t2_le := d.t2_le
  R_analytic := d.R_analytic
  R_frame := d.R_frame
  rho_diff := d.rho_diff
  rho_real := d.rho_real
  rho_orth_t2 := d.rho_orth_t2
  rC_le_t2 := hr.trans d.rC_le_t2
  nonvanishing := (Metric.ball_subset_ball (by linarith)).trans d.nonvanishing
  freq := fun J hJ => d.freq J (Metric.ball_subset_ball (by linarith) hJ)
  h_re := fun J hJ => d.h_re J (by linarith)
  h_im := fun J hJ => d.h_im J (by linarith)
  Omega_real := fun J hJ => d.Omega_real J (by linarith)
  omega_diff := d.omega_diff.mono (Metric.ball_subset_ball (by linarith))
  Omega_diff := d.Omega_diff.mono (Metric.ball_subset_ball (by linarith))
  tau_eq := d.tau_eq
  h_diff := d.h_diff.mono (Metric.ball_subset_ball (by linarith))
  omega_eq := fun J hJ => d.omega_eq J (Metric.ball_subset_ball (by linarith) hJ)
  jets := fun J hJ => d.jets J (Metric.ball_subset_ball (by linarith) hJ)
  euclid_le := fun J hJ => d.euclid_le J (Metric.ball_subset_ball (by linarith) hJ)
  J0_interior := d.J0_interior
  gamma_pos := d.gamma_pos
  gamma_le := d.gamma_le
  dio := d.dio
  dio_fast := d.dio_fast
  dio_slow := d.dio_slow
  rC_pos := hr0
  rC_le_one := hr.trans d.rC_le_one
  rC_le_delta := hr.trans d.rC_le_delta
  one_le_L := d.one_le_L
  one_le_Brho := d.one_le_Brho
  one_le_Bdrho := d.one_le_Bdrho
  rho_clause := fun L hL => d.rho_clause L
    (hL.trans_le (div_le_div_of_nonneg_right hr Real.pi_pos.le))
  rho_bounds :=
    ⟨d.rho_bounds.1.mono (Metric.ball_subset_ball
        (div_le_div_of_nonneg_right hr Real.pi_pos.le)),
      fun J hJ => d.rho_bounds.2 J (Metric.ball_subset_ball
        (div_le_div_of_nonneg_right hr Real.pi_pos.le) hJ)⟩

end Shrink

end KAM.Planetary

end
