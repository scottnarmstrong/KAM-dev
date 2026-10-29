/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.KAMInputsBase
public import KAM.Planetary.PGAssembly.AveragingFacts

/-!
# P Part 5: literal scale-constant nodes (`stepP:p5:kc-eval`, `kc-small`, `bpP:p5:kam-cond`,
`stepP:p5:rk-dir`)

Unsigned exports stating the literal conclusions of the graph nodes of `bpP:p5:kam-cond` and
`bpP:p5:rK` in terms of the landed `params`, `pgScales` and `pgKamScale`. The `L`, `K`, `ρ̂`, `Ê`
evaluations hold for every `0 < r` and `0 < mu ≤ 1`; `rk_dir` is stated on the admissible range.
-/

@[expose] public noncomputable section

namespace KAM.Planetary

variable {a b : ℕ}

private theorem kcnode_L {d : PGData a b} {r mu : ℝ} (hmu : 0 < mu) (h1 : mu ≤ 1) :
    (pgKamScale d r mu).L = kam_c1 d/mu := by
  have hC := one_le_kam_c1 d
  show max (kam_c1 d/mu) (max (kam_c1 d)⁻¹ ((kam_c1 d*mu)⁻¹)) = _
  refine max_eq_left (max_le ?_ ?_)
  · rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) hmu]; nlinarith
  · have hCC : 1 ≤ kam_c1 d*kam_c1 d := one_le_mul_of_one_le_of_one_le hC hC
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hmu]
    nlinarith [mul_le_mul_of_nonneg_right hCC hmu.le]

private theorem kcnode_x {d : PGData a b} {r mu : ℝ} (hr : 0 < r) (hmu : 0 < mu) (h1 : mu ≤ 1) :
    (pgKamScale d r mu).E*(pgKamScale d r mu).M^2*(pgKamScale d r mu).L/
      (pgKamScale d r mu).γ₁^2 = (kam_c1 d)^4/(pgScales d).k0^2 := by
  have hk0 : 0 < (pgScales d).k0 := pgScales_k0_pos d
  have hC : 0 < kam_c1 d := by linarith [one_le_kam_c1 d]
  have : ((pgScales d).k0*r^(5/2:ℝ))^2 = (pgScales d).k0^2*r^5 := by
    rw [mul_pow]; congr 1
    rw [← Real.rpow_natCast (r^(5/2:ℝ)) 2, ← Real.rpow_mul hr.le]; norm_num
  rw [show (pgKamScale d r mu).E*(pgKamScale d r mu).M^2*(pgKamScale d r mu).L/
    (pgKamScale d r mu).γ₁^2 = (kam_c1 d*mu*r^5)*(kam_c1 d)^2*(pgKamScale d r mu).L/
      ((pgScales d).k0*r^(5/2:ℝ))^2 from rfl, kcnode_L hmu h1, this]
  field_simp

private theorem kcnode_cutoff {d : PGData a b} {r mu : ℝ} (hr : 0 < r) (hmu : 0 < mu)
    (h1 : mu ≤ 1) : cutoff (pgKamScale d r mu) = pgK0 d (pgScales d) := by
  have hx := kcnode_x (d := d) hr hmu h1
  show 6/(pgKamScale d r mu).s*max 1 (Real.log (1/((pgKamScale d r mu).E*
    (pgKamScale d r mu).M^2*(pgKamScale d r mu).L/(pgKamScale d r mu).γ₁^2))) = _
  rw [hx]
  unfold pgK0
  rw [one_div_div]
  rfl

private theorem kcnode_rhoHat {d : PGData a b} {r mu : ℝ} (hr : 0 < r) (hmu : 0 < mu)
    (h1 : mu ≤ 1) : rhoHat (pgKamScale d r mu) = (params d r mu).rhoHat := by
  have hC : 0 < kam_c1 d := by linarith [one_le_kam_c1 d]
  have hK := kcnode_cutoff (d := d) hr hmu h1
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
    rfl
  rw [e, min_self]
  rfl

private theorem kcnode_eHat {d : PGData a b} {r mu : ℝ} (hr : 0 < r) (hmu : 0 < mu)
    (h1 : mu ≤ 1) : eHat (pgKamScale d r mu) = (params d r mu).Ehat := by
  have hR : eHat (pgKamScale d r mu) =
      (kam_c1 d*mu*r^5)*(pgKamScale d r mu).L/(rhoHat (pgKamScale d r mu))^2 := rfl
  rw [hR, kcnode_L hmu h1, kcnode_rhoHat hr hmu h1, params_Ehat]
  field_simp

private theorem kcnode_Ehat_max (d : PGData a b) {r : ℝ} (hr : 0 < r) (mu : ℝ) :
    (params d r mu).Ehat = max (9*(kam_c1 d)^4*(pgK0 d (pgScales d))^(2*pgTau a b+2)/
      (pgScales d).k0^2) (4*(kam_c1 d)^2/(pgScales d).k1^2) := by
  have hc : 0 < kam_c1 d := by linarith [one_le_kam_c1 d]
  have hk0 := pgScales_k0_pos d
  have hk1 := pgScales_k1_pos d
  have hY := pgK0_pos d (pgScales d)
  have hX : (r^(5/2:ℝ))^2 = r^5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; norm_num
  have hY2 : ((pgK0 d (pgScales d))^(pgTau a b+1))^2 = (pgK0 d (pgScales d))^(2*pgTau a b+2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY.le]; congr 1; push_cast; ring
  have h52 : 0 < r^(5/2:ℝ) := Real.rpow_pos_of_pos hr _
  have hYp : 0 < (pgK0 d (pgScales d))^(pgTau a b+1) := Real.rpow_pos_of_pos hY _
  set A := (pgScales d).k0*r^(5/2:ℝ)/(3*kam_c1 d*(pgK0 d (pgScales d))^(pgTau a b+1)) with hA
  set B := (pgScales d).k1*r^(5/2:ℝ)/2 with hB
  have hA0 : 0 < A := by rw [hA]; positivity
  have hB0 : 0 < B := by rw [hB]; positivity
  have e1 : (kam_c1 d)^2*r^5/A^2 =
      9*(kam_c1 d)^4*(pgK0 d (pgScales d))^(2*pgTau a b+2)/(pgScales d).k0^2 := by
    rw [hA, div_pow, mul_pow, mul_pow, hX, hY2]; field_simp; ring
  have e2 : (kam_c1 d)^2*r^5/B^2 = 4*(kam_c1 d)^2/(pgScales d).k1^2 := by
    rw [hB, div_pow, mul_pow, hX]; field_simp; norm_num
  rw [params_Ehat, params_rhoHat, ← hA, ← hB, ← e1, ← e2]
  have hp : 0 ≤ (kam_c1 d)^2*r^5 := by positivity
  rcases le_total A B with h | h
  · rw [min_eq_left h, max_eq_left]
    exact div_le_div_of_nonneg_left hp (by positivity) (pow_le_pow_left₀ hA0.le h 2)
  · rw [min_eq_right h, max_eq_right]
    exact div_le_div_of_nonneg_left hp (by positivity) (pow_le_pow_left₀ hB0.le h 2)

/-- `stepP:p5:kc-eval`: `L = C₁/μ`, `x = C₁⁴/κ₀² ≤ 1`, `K = K₀`, `ρ̂` as displayed, `Ê = E L/ρ̂²
= C₁² r⁵/ρ̂²` and the displayed maximum. -/
theorem kc_eval (d : PGData a b) {r mu : ℝ} (hr : 0 < r) (hmu : 0 < mu) (h1 : mu ≤ 1) :
    (pgKamScale d r mu).L = kam_c1 d/mu ∧
    (pgKamScale d r mu).E*(pgKamScale d r mu).M^2*(pgKamScale d r mu).L/
      (pgKamScale d r mu).γ₁^2 = (kam_c1 d)^4/(pgScales d).k0^2 ∧
    (kam_c1 d)^4/(pgScales d).k0^2 ≤ 1 ∧
    cutoff (pgKamScale d r mu) = pgK0 d (pgScales d) ∧
    (params d r mu).rhoHat =
      min ((pgScales d).k0*r^(5/2:ℝ)/(3*kam_c1 d*(pgK0 d (pgScales d))^(pgTau a b+1)))
        ((pgScales d).k1*r^(5/2:ℝ)/2) ∧
    rhoHat (pgKamScale d r mu) = (params d r mu).rhoHat ∧
    eHat (pgKamScale d r mu) = (params d r mu).Ehat ∧
    (params d r mu).Ehat = (kam_c1 d)^2*r^5/(params d r mu).rhoHat^2 ∧
    (params d r mu).Ehat = max (9*(kam_c1 d)^4*(pgK0 d (pgScales d))^(2*pgTau a b+2)/
      (pgScales d).k0^2) (4*(kam_c1 d)^2/(pgScales d).k1^2) := by
  have hk0 : 0 < (pgScales d).k0 := pgScales_k0_pos d
  have hC := one_le_kam_c1 d
  have hspec := (pgScales_spec d).1
  refine ⟨kcnode_L hmu h1, kcnode_x hr hmu h1, ?_, kcnode_cutoff hr hmu h1,
    params_rhoHat d r mu, kcnode_rhoHat hr hmu h1, kcnode_eHat hr hmu h1, params_Ehat d r mu,
    kcnode_Ehat_max d hr mu⟩
  rw [div_le_one (by positivity)]
  have : (kam_c1 d)^2*(kam_c1 d)^2 ≤ (pgScales d).k0*(pgScales d).k0 :=
    mul_self_le_mul_self (by positivity) hspec
  nlinarith

/-- `stepP:p5:kc-small`: the KAM condition `ĉ Ê < 1` and `γ₂ = μ γ₁ ≤ γ₁`. -/
theorem kc_small (d : PGData a b) {r mu : ℝ} (hr : 0 < r) (_hmu : 0 < mu) (h1 : mu ≤ 1) :
    pgChat a b*(params d r mu).Ehat < 1 ∧
    (params d r mu).gamma2 = mu*(params d r mu).gamma1 ∧
    (params d r mu).gamma2 ≤ (params d r mu).gamma1 := by
  have hk0 := pgScales_k0_pos d
  have h52 : 0 < r^(5/2:ℝ) := Real.rpow_pos_of_pos hr _
  refine ⟨chat_Ehat_lt hr mu, ?_, ?_⟩
  · show mu*(pgScales d).k0*r^(5/2:ℝ) = mu*((pgScales d).k0*r^(5/2:ℝ))
    ring
  · show mu*(pgScales d).k0*r^(5/2:ℝ) ≤ (pgScales d).k0*r^(5/2:ℝ)
    nlinarith [mul_pos hk0 h52]

/-- `bpP:p5:kam-cond`: the evaluations of `kc_eval`, the KAM condition, `γ₁ ≥ γ₂`, and `τ > n`. -/
theorem kam_cond_node (d : PGData a b) {r mu : ℝ} (hr : 0 < r) (hmu : 0 < mu) (h1 : mu ≤ 1) :
    (pgKamScale d r mu).L = kam_c1 d/mu ∧
    (kam_c1 d)^4/(pgScales d).k0^2 ≤ 1 ∧
    cutoff (pgKamScale d r mu) = pgK0 d (pgScales d) ∧
    (params d r mu).Ehat = max (9*(kam_c1 d)^4*(pgK0 d (pgScales d))^(2*pgTau a b+2)/
      (pgScales d).k0^2) (4*(kam_c1 d)^2/(pgScales d).k1^2) ∧
    pgChat a b*(params d r mu).Ehat < 1 ∧
    (params d r mu).gamma2 ≤ (params d r mu).gamma1 ∧
    ((a+b:ℕ):ℝ) < pgTau a b := by
  obtain ⟨hL, -, hx, hK, -, -, -, -, hmax⟩ := kc_eval d hr hmu h1
  obtain ⟨hE, -, hg⟩ := kc_small d hr hmu h1
  exact ⟨hL, hx, hK, hmax, hE, hg, by unfold pgTau; linarith⟩

/-- `stepP:p5:rk-dir`: `Ê < 2⁻¹³/n`, `r_K < ρ̂/(256 n) ≤ λ₁/(512 n)`, `r_K < min{t, λ₁}`,
`r_K < ρ̄/2`, `2 r_K/ℓ ≤ κ₁ √r/(64 n)` and `(1 + 2 r_K/ℓ)^b < 2` for admissible `(r, mu)`. -/
theorem rk_dir (d : PGData a b) {r mu : ℝ} (h : admissible d (pgRstar d) r mu) :
    (params d r mu).Ehat < 1/(2^13*((a+b:ℕ):ℝ)) ∧
    (params d r mu).rK < (params d r mu).rhoHat/(256*((a+b:ℕ):ℝ)) ∧
    (params d r mu).rhoHat/(256*((a+b:ℕ):ℝ)) ≤ (params d r mu).l1/(512*((a+b:ℕ):ℝ)) ∧
    (params d r mu).rK < min (params d r mu).t (params d r mu).l1 ∧
    (params d r mu).rK < (params d r mu).rhoBar/2 ∧
    2*(params d r mu).rK/(params d r mu).ell ≤ (pgScales d).k1/(64*((a+b:ℕ):ℝ))*Real.sqrt r ∧
    (1+2*(params d r mu).rK/(params d r mu).ell)^b < 2 := by
  have hn : (0:ℝ) < ((a+b:ℕ):ℝ) := by
    have := d.ha; exact_mod_cast (by omega : 0 < a+b)
  have hE := chat_Ehat_lt (d := d) h.1 mu
  have hcn : 2^13*((a+b:ℕ):ℝ) ≤ pgChat a b := le_max_left _ _
  have hE0 : 0 ≤ (params d r mu).Ehat := by
    rw [params_Ehat]
    have := params_rhoHat_pos d h.1 mu
    have := h.1
    have := one_le_kam_c1 d
    positivity
  obtain ⟨h1, h2, h3⟩ := r_k d r mu h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hmin, hrb, -⟩ := av_dyn h
  refine ⟨?_, h1, ?_, hmin, hrb, h2, h3⟩
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hcn hE0]
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right (rhoHat_le_l1 d r mu) (by positivity :
      (0:ℝ) ≤ 512*((a+b:ℕ):ℝ))]

end KAM.Planetary

end
