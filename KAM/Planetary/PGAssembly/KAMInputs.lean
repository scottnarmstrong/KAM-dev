/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.Threshold
public import KAM.Planetary.TwoScale.Setting

/-!
# P Part 5: the KAM hypothesis inputs (`bpP:p5:kam-hyp`)

`kamH` is the normalized complex integrable Hamiltonian, `pgKamScale` the exact P3 scale record and
`pg_kam_dictionary` identifies its constants with `params`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-KH.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Planetary

variable {a b : ℕ}

def kamH (d : PGData a b) (mu : ℝ) (J : Fin (a+b) → ℂ) : ℂ :=
  complexIntegrable d mu J/(2*Real.pi)

/-- Exact P3 data; L is initialL, with a separate equality to C1/mu. -/
def pgKamScale (d : PGData a b) (r mu : ℝ) : ScaleData :=
  let C := kam_c1 d
  ⟨pgTau a b,(params d r mu).gamma1,(params d r mu).gamma2,
    pgWidth d/60,(params d r mu).rho,C*mu*r^5,C,C*mu,C/mu,C,C/mu,
    initialL C (C*mu) (C/mu)⟩

theorem mu_lt_one_of_admissible {d : PGData a b} {r mu : ℝ}
    (h : admissible d (pgRstar d) r mu) : mu < 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hdyn⟩ := (rstar d).choose_spec
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hm, -⟩ := hdyn r mu h
  exact hm.trans_le (pgAnalytic_spec d).2.2.2.2.2.2.2.2.1

theorem pgKamScale_L {d : PGData a b} {r mu : ℝ} (h : admissible d (pgRstar d) r mu) :
    (pgKamScale d r mu).L = kam_c1 d/mu := by
  have hmu : 0 < mu := h.2.2.1
  have hC := one_le_kam_c1 d
  have h1 := mu_lt_one_of_admissible h
  show max (kam_c1 d/mu) (max (kam_c1 d)⁻¹ ((kam_c1 d*mu)⁻¹)) = _
  refine max_eq_left (max_le ?_ ?_)
  · rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) hmu]; nlinarith
  · have hCC : 1 ≤ kam_c1 d*kam_c1 d := one_le_mul_of_one_le_of_one_le hC hC
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hmu]
    nlinarith [mul_le_mul_of_nonneg_right hCC hmu.le]

theorem pgKamScale_cutoff {d : PGData a b} {r mu : ℝ} (h : admissible d (pgRstar d) r mu) :
    cutoff (pgKamScale d r mu) = pgK0 d (pgScales d) := by
  have hmu : 0 < mu := h.2.2.1
  have hr : 0 < r := h.1
  have hC : 0 < kam_c1 d := by linarith [one_le_kam_c1 d]
  have hk0 : 0 < (pgScales d).k0 := by
    have := (pgScales_spec d).1
    nlinarith
  have hx : (kam_c1 d*mu*r^5)*(kam_c1 d)^2*(pgKamScale d r mu).L/
      (params d r mu).gamma1^2 = (kam_c1 d)^4/(pgScales d).k0^2 := by
    rw [pgKamScale_L h]
    show _ = _
    have : ((pgScales d).k0*r^(5/2:ℝ))^2 = (pgScales d).k0^2*r^5 := by
      rw [mul_pow]; congr 1
      rw [← Real.rpow_natCast (r^(5/2:ℝ)) 2, ← Real.rpow_mul hr.le]; norm_num
    show (kam_c1 d*mu*r^5)*(kam_c1 d)^2*(kam_c1 d/mu)/((pgScales d).k0*r^(5/2:ℝ))^2 = _
    rw [this]
    field_simp
  show 6/(pgKamScale d r mu).s*max 1 (Real.log (1/((pgKamScale d r mu).E*(pgKamScale d r mu).M^2*
    (pgKamScale d r mu).L/(pgKamScale d r mu).γ₁^2))) = _
  rw [show (pgKamScale d r mu).E*(pgKamScale d r mu).M^2*(pgKamScale d r mu).L/
    (pgKamScale d r mu).γ₁^2 = (kam_c1 d*mu*r^5)*(kam_c1 d)^2*(pgKamScale d r mu).L/
      (params d r mu).gamma1^2 from rfl, hx]
  unfold pgK0
  rw [one_div_div]
  rfl

theorem pgKamScale_rhoHat {d : PGData a b} {r mu : ℝ} (h : admissible d (pgRstar d) r mu) :
    rhoHat (pgKamScale d r mu) = (params d r mu).rhoHat := by
  have hmu : 0 < mu := h.2.2.1
  have hC : 0 < kam_c1 d := by linarith [one_le_kam_c1 d]
  have hK := pgKamScale_cutoff h
  have hR : rhoHat (pgKamScale d r mu) =
      min (min ((params d r mu).gamma1/(3*kam_c1 d*(cutoff (pgKamScale d r mu))^(pgTau a b+1)))
        ((params d r mu).gamma2/(3*(kam_c1 d*mu)*(cutoff (pgKamScale d r mu))^(pgTau a b+1))))
        (params d r mu).rho := rfl
  rw [hR, hK]
  have e : (params d r mu).gamma2/(3*(kam_c1 d*mu)*(pgK0 d (pgScales d))^(pgTau a b+1)) =
      (params d r mu).gamma1/(3*kam_c1 d*(pgK0 d (pgScales d))^(pgTau a b+1)) := by
    have := (pgK0_pos d (pgScales d)).ne'
    show mu*(pgScales d).k0*r^(5/2:ℝ)/_ = _
    field_simp
  rw [e, min_self]
  rfl

end KAM.Planetary

end
