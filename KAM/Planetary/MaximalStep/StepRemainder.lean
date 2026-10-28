/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.StepBound

/-!
# The remainder of the canonical step (P11A-C8, `stepP:p11a:cs-taylor`, `cs-bracket`, `cs-assemble`)

For `b ∈ B` and `z ∈ D(r_+, qs)` the integral Lie identity (`Canonical.taylor_poschel`) gives
`R_+(z) = (R - R_*)(z) + ∫₀¹ {u_t, φ}(X^t z) dt`, and the Cauchy estimates bound the integrand by
`n(4n+5) U A / σ`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Metric
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

variable {n : ℕ}

theorem norm_single_le_one (i : Fin n) : ‖(Pi.single i (1 : ℂ) : P11CVec n)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  by_cases h : j = i <;> simp [Pi.single_apply, h]

theorem strip_of_close {θ x : P11CVec n} {ρ A : ℝ} (hθ : θ ∈ KAM.complexStrip n ρ)
    (hx : ‖x - θ‖ ≤ A) : x ∈ KAM.complexStrip n (ρ + A) := fun j => by
  have h1 : |(x j).im| ≤ |(θ j).im| + ‖x j - θ j‖ := by
    calc |(x j).im| = |(θ j).im + (x j - θ j).im| := by simp
      _ ≤ |(θ j).im| + |(x j - θ j).im| := abs_add_le _ _
      _ ≤ _ := add_le_add le_rfl (Complex.abs_im_le_norm _)
  have h2 : ‖x j - θ j‖ ≤ A := (norm_le_pi_norm (x - θ) j).trans hx
  linarith [hθ j]

theorem strip_add_dir {x : P11CVec n} {ρ σ : ℝ} (hx : x ∈ KAM.complexStrip n ρ) (i : Fin n)
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ σ) : x + ζ • Pi.single i 1 ∈ KAM.complexStrip n (ρ + σ) := fun j => by
  have : |((x + ζ • (Pi.single i 1 : P11CVec n)) j).im| ≤ |(x j).im| + ‖ζ‖ := by
    simp only [Pi.add_apply, Pi.smul_apply, Complex.add_im]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    by_cases h : j = i
    · subst h; simpa using Complex.abs_im_le_norm ζ
    · simp [Pi.single_apply, h]
  linarith [hx j]

theorem poissonBracket_congr {u u' v : P11Phase n → ℂ} {x : P11Phase n}
    (h : u =ᶠ[nhds x] u') :
    KAM.Canonical.poissonBracket u v x = KAM.Canonical.poissonBracket u' v x := by
  unfold KAM.Canonical.poissonBracket
  rw [h.fderiv_eq]

variable {S : P11Step n} {h : P11CVec n → ℂ} {w : P11CVec n → P11CVec n} {R : P11Family n → ℂ}

theorem step_A_le_quarter (H : P11StepHyp S h w R) : p11StepA S ≤ S.sigma / 4 := by
  have := step_small S; have := step_A_nonneg H
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem step_Aeta_le (H : P11StepHyp S h w R) :
    (n + 1) * S.s * p11StepA S / S.sigma ≤ S.s / 4 := by
  have hσ := S.sigma_pos
  rw [div_le_iff₀ hσ]
  have h1 := mul_le_mul_of_nonneg_left (step_small S) S.s_pos.le
  nlinarith

theorem step_z_mem (S : P11Step n) {z : P11Phase n}
    (hz : z ∈ KAM.Weighted.Dom n {0} (S.q * S.s) (S.r - S.d - S.delta - 2 * S.sigma)) :
    z ∈ KAM.Weighted.Dom n {0} (3 * S.s / 4) (S.r - S.d - S.delta - 3 * S.sigma / 2) := by
  obtain ⟨h1, h2⟩ := (mem_Dom_iff z).1 hz
  refine (mem_Dom_iff z).2 ⟨fun i => (h1 i).trans (by linarith [S.sigma_pos]), ?_⟩
  nlinarith [S.q_le, S.s_pos]

/-- The Cauchy bound of the bracket at a point of the trajectory. -/
theorem step_bracket_bound (H : P11StepHyp S h w R) {b : P11CVec n}
    (hb : b ∈ KAM.actionNbhd S.E S.t) {z : P11Phase n}
    (hz : z ∈ KAM.Weighted.Dom n {0} (S.q * S.s) (S.r - S.d - S.delta - 2 * S.sigma))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖KAM.Canonical.poissonBracket (stepU S R b t) (p11StepPhi S w R b)
      (p11Flow (p11StepPhi S w R b) (S.r - S.d - S.delta) S.s S.sigma t z)‖ ≤
      n * (4 * n + 5) * ((5 + 4 * p11Error n S.T S.d) * S.eps) * p11StepA S / S.sigma := by
  have Hb := step_affHyp H hb
  have hzU := step_z_mem S hz
  have ht' : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨hd1, hd2⟩ := flow_displacement_t Hb hzU ht'
  have hxΩ := (KAM.Canonical.flow_b (smallField Hb)).2.2.1 t ht' z (U_sub_half Hb hzU)
  set x := p11Flow (p11StepPhi S w R b) (S.r - S.d - S.delta) S.s S.sigma t z with hx
  obtain ⟨hf1, hf2⟩ := field_bound Hb hxΩ
  obtain ⟨hz1, hz2⟩ := (mem_Dom_iff z).1 hz
  have hA0 := step_A_nonneg H
  have hAq := step_A_le_quarter H
  have hAe := step_Aeta_le H
  have hσ := S.sigma_pos
  have hs := S.s_pos
  have hx1 : x.1 ∈ KAM.complexStrip n (S.r - S.d - S.delta - 2 * S.sigma + p11StepA S) :=
    strip_of_close hz1 hd1
  have hx2 : ‖x.2‖ ≤ ‖z.2‖ + (n + 1) * S.s * p11StepA S / S.sigma :=
    (norm_le_insert' _ _).trans (add_le_add le_rfl hd2)
  have hU0 : 0 ≤ (5 + 4 * p11Error n S.T S.d) * S.eps := by
    have := step_E_nonneg S; have := S.eps_nonneg; positivity
  rw [KAM.Canonical.poissonBracket_eq_fderiv_field]
  have key := norm_fderiv_phase_le (O := KAM.Weighted.Dom n {0} S.s (S.r - S.d))
    (KAM.Weighted.isOpen_Dom _ _ _) (step_U_diff H hb t) (x := x) (σ := S.sigma)
    (ρ := S.s / 4) (U := (5 + 4 * p11Error n S.T S.d) * S.eps) hσ (by linarith)
    (fun i ζ hζ => by
      have hm : (x.1 + ζ • Pi.single i 1, x.2) ∈ KAM.Weighted.Dom n {0} S.s (S.r - S.d) := by
        refine (mem_Dom_iff _).2 ⟨?_, ?_⟩
        · have := strip_add_dir hx1 i hζ
          exact fun j => (this j).trans_le (by linarith [S.delta_pos])
        · show ‖x.2‖ < S.s
          nlinarith [S.q_le]
      exact ⟨hm, step_U_le H hb ht hm⟩)
    (fun i ζ hζ => by
      have hm : (x.1, x.2 + ζ • Pi.single i 1) ∈ KAM.Weighted.Dom n {0} S.s (S.r - S.d) := by
        refine (mem_Dom_iff _).2 ⟨?_, ?_⟩
        · exact fun j => (hx1 j).trans_le (by linarith [S.delta_pos])
        · show ‖x.2 + ζ • (Pi.single i 1 : P11CVec n)‖ < S.s
          have h1 : ‖ζ • (Pi.single i 1 : P11CVec n)‖ ≤ S.s / 4 := by
            rw [norm_smul]
            calc ‖ζ‖ * ‖(Pi.single i 1 : P11CVec n)‖ ≤ ‖ζ‖ * 1 :=
                  mul_le_mul_of_nonneg_left (norm_single_le_one i) (norm_nonneg _)
              _ ≤ S.s / 4 := by linarith
          have := norm_add_le x.2 (ζ • (Pi.single i 1 : P11CVec n))
          nlinarith [S.q_le]
      exact ⟨hm, step_U_le H hb ht hm⟩) (KAM.hamiltonianVectorFieldℂ (p11StepPhi S w R b) x).1
    (KAM.hamiltonianVectorFieldℂ (p11StepPhi S w R b) x).2
  refine key.trans ?_
  have hUσ : 0 ≤ (5 + 4 * p11Error n S.T S.d) * S.eps / S.sigma := by positivity
  have hUs : 0 ≤ (5 + 4 * p11Error n S.T S.d) * S.eps / (S.s / 4) := by positivity
  have h3 : (n : ℝ) * ‖(KAM.hamiltonianVectorFieldℂ (p11StepPhi S w R b) x).1‖ *
        ((5 + 4 * p11Error n S.T S.d) * S.eps / S.sigma) ≤
      n * p11StepA S * ((5 + 4 * p11Error n S.T S.d) * S.eps / S.sigma) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf1 (Nat.cast_nonneg n)) hUσ
  have h4 : (n : ℝ) * ‖(KAM.hamiltonianVectorFieldℂ (p11StepPhi S w R b) x).2‖ *
        ((5 + 4 * p11Error n S.T S.d) * S.eps / (S.s / 4)) ≤
      n * ((n + 1) * S.s * p11StepA S / S.sigma) *
        ((5 + 4 * p11Error n S.T S.d) * S.eps / (S.s / 4)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf2 (Nat.cast_nonneg n)) hUs
  have h5 : (n : ℝ) * p11StepA S * ((5 + 4 * p11Error n S.T S.d) * S.eps / S.sigma) +
      n * ((n + 1) * S.s * p11StepA S / S.sigma) *
        ((5 + 4 * p11Error n S.T S.d) * S.eps / (S.s / 4)) =
      n * (4 * n + 5) * ((5 + 4 * p11Error n S.T S.d) * S.eps) * p11StepA S / S.sigma := by
    field_simp; ring
  linarith

end KAM.Planetary

end
