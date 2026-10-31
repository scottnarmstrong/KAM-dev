/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.ComponentsAngleQ
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Assembly of the field norm from component bounds (`bpW:w4:lemma1`, step *Assembly*)

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

`homXnorm_le_of_components`: if the components of `T ∈ 𝒯_s` at `θ` satisfy the bounds of
`bpW:w4:components` with the scale `E₀` and the operator constant `K ≥ 1` (that is `|b| ≤ 2πE₀`,
`‖c^±‖ ≤ rE₀/√2`, `‖2P‖,‖Q‖,‖Q^T‖,‖2P'‖ ≤ KE₀`, `|∂_ia| ≤ 2πr²E₀`, `|⟨∂_ib,y⟩| ≤ 2πE₀|y|`,
`‖∂_ic^±‖_* ≤ 2√2π r E₀`, `‖Λ∂_iP‖,‖Λ∂_iP'‖ ≤ 4πKE₀`, `‖Λ∂_iQ‖ ≤ 16πKE₀`), then at every point of
`D(·,r)` over `θ`: `|X_T|_r ≤ (7 + 10K)E₀` (`C₁ = 7+10K_S`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p s : ℝ}

/-- The component hypotheses at one `θ`. -/
structure HomCompBounds {a p s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (r K E0 : ℝ)
    (T : HomTaylor a p s) (θ : Fin 2 → ℂ) : Prop where
  b : ‖T.b θ‖ ≤ 2 * Real.pi * E0
  cp : ‖T.cp θ‖ ≤ r * E0 / Real.sqrt 2
  cm : ‖T.cm θ‖ ≤ r * E0 / Real.sqrt 2
  P : ‖(2 : ℂ) • T.P θ‖ ≤ K * E0
  Q : ‖T.Q θ‖ ≤ K * E0
  Qt : ‖T.Qt θ‖ ≤ K * E0
  P' : ‖(2 : ℂ) • T.P' θ‖ ≤ K * E0
  da : ∀ i, ‖homPartial i T.a0 θ‖ ≤ 2 * Real.pi * r ^ 2 * E0
  db : ∀ i (y : Fin 2 → ℂ), ‖∑ k, homPartial i T.b θ k * y k‖ ≤ 2 * Real.pi * E0 * ‖y‖
  dcp : ∀ i, homDualNorm ha hp (homPartial i T.cp θ) ≤ 2 * Real.sqrt 2 * Real.pi * r * E0
  dcm : ∀ i, homDualNorm ha hp (homPartial i T.cm θ) ≤ 2 * Real.sqrt 2 * Real.pi * r * E0
  dP : ∀ i, ‖homLamCLM ha hp (homPartial i T.P θ)‖ ≤ K * (4 * Real.pi * E0)
  dP' : ∀ i, ‖homLamCLM ha hp (homPartial i T.P' θ)‖ ≤ K * (4 * Real.pi * E0)
  dQ : ∀ i, ‖homLamCLM ha hp (homPartial i T.Q θ)‖ ≤ K * (16 * Real.pi * E0)


theorem norm_homPairRep_le {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (c z : HomL2) :
    ‖homPairRep ha hp c z‖ ≤ homDualNorm ha hp c * ‖z‖ := by
  have := norm_homPairF_le (homLamDiag ha hp c) z
  simpa [homPairRep, homPairF, homDualNorm] using this

theorem norm_homPairRep_op_le {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (M : HomOp) (z z' : HomL2) :
    ‖homPairRep ha hp (M z) z'‖ ≤ ‖homLamCLM ha hp M‖ * ‖z‖ * ‖z'‖ := by
  have h1 := norm_homPairF_le ((homLamCLM ha hp M) z) z'
  have h2 : ‖(homLamCLM ha hp M) z‖ ≤ ‖homLamCLM ha hp M‖ * ‖z‖ :=
    (homLamCLM ha hp M).le_opNorm z
  have h3 : homPairRep ha hp (M z) z' = homPairF ((homLamCLM ha hp M) z) z' := rfl
  rw [h3]
  refine h1.trans ?_
  rw [one_mul]
  exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

theorem norm_le_of_domain {r : ℝ} {z zb : HomL2} (h : ‖homU z zb‖ + ‖homV z zb‖ < r) :
    ‖z‖ ≤ r / Real.sqrt 2 ∧ ‖zb‖ ≤ r / Real.sqrt 2 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨h1, h2⟩ := homNorm_le_uv z zb
  exact ⟨h1.trans (div_le_div_of_nonneg_right h.le hs.le),
    h2.trans (div_le_div_of_nonneg_right h.le hs.le)⟩


theorem norm_add7_le {E : Type*} [SeminormedAddCommGroup E] (a b c d e f g : E) :
    ‖a + b + c + d + e + f + g‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ + ‖g‖ := by
  calc ‖a + b + c + d + e + f + g‖ ≤ ‖a + b + c + d + e + f‖ + ‖g‖ := norm_add_le _ _
    _ ≤ (‖a + b + c + d + e‖ + ‖f‖) + ‖g‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((‖a + b + c + d‖ + ‖e‖) + ‖f‖) + ‖g‖ := by gcongr; exact norm_add_le _ _
    _ ≤ (((‖a + b + c‖ + ‖d‖) + ‖e‖) + ‖f‖) + ‖g‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((((‖a + b‖ + ‖c‖) + ‖d‖) + ‖e‖) + ‖f‖) + ‖g‖ := by gcongr; exact norm_add_le _ _
    _ ≤ (((((‖a‖ + ‖b‖) + ‖c‖) + ‖d‖) + ‖e‖) + ‖f‖) + ‖g‖ := by gcongr; exact norm_add_le _ _
    _ = _ := by ring

/-- **Assembly** (`bpW:w4:lemma1`, step *Assembly*): `|X_T|_r ≤ (7 + 10K) E₀` at a point of the domain
over `θ`. -/
theorem homXnorm_le_of_components {a p s : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) {r K E0 : ℝ}
    (hr : 0 < r) (hK : 1 ≤ K) (hE0 : 0 ≤ E0) (T : HomTaylor a p s) {θ y : Fin 2 → ℂ}
    {z zb : HomL2} (hb : HomCompBounds ha hp r K E0 T θ) (hy : ‖y‖ ≤ r ^ 2)
    (hdom : ‖homU z zb‖ + ‖homV z zb‖ < r) :
    homXnorm ha hp r T θ y z zb ≤ (7 + 10 * K) * E0 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hπ := Real.pi_pos
  obtain ⟨hzq, hzbq⟩ := norm_le_of_domain hdom
  set q : ℝ := r / Real.sqrt 2 with hq
  have hq0 : 0 ≤ q := by positivity
  have hq2 : q * q = r ^ 2 / 2 := by
    rw [hq]; field_simp; nlinarith [hs2]
  have hzz : ‖z‖ * ‖z‖ ≤ r ^ 2 / 2 := by
    rw [← hq2]; exact mul_le_mul hzq hzq (norm_nonneg _) hq0
  have hzzb : ‖z‖ * ‖zb‖ ≤ r ^ 2 / 2 := by
    rw [← hq2]; exact mul_le_mul hzq hzbq (norm_nonneg _) hq0
  have hzbzb : ‖zb‖ * ‖zb‖ ≤ r ^ 2 / 2 := by
    rw [← hq2]; exact mul_le_mul hzbq hzbq (norm_nonneg _) hq0
  have hK0 : 0 ≤ K := by linarith
  have hKE : 0 ≤ K * E0 := mul_nonneg hK0 hE0
  -- the angle derivatives
  have hRth : ‖fun i => homRtheta ha hp T i θ y z zb‖ ≤ (4 + 6 * K) * (2 * Real.pi * r ^ 2 * E0) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    have e1 := hb.da i
    have e2 : ‖∑ k, homPartial i T.b θ k * y k‖ ≤ 2 * Real.pi * E0 * r ^ 2 :=
      (hb.db i y).trans (mul_le_mul_of_nonneg_left hy (by positivity))
    have e3 : ‖homPairRep ha hp (homPartial i T.cp θ) z‖ ≤ 2 * Real.pi * r ^ 2 * E0 := by
      refine (norm_homPairRep_le ha hp _ _).trans ?_
      calc homDualNorm ha hp (homPartial i T.cp θ) * ‖z‖
          ≤ (2 * Real.sqrt 2 * Real.pi * r * E0) * q :=
            mul_le_mul (hb.dcp i) hzq (norm_nonneg _) (by positivity)
        _ = 2 * Real.pi * r ^ 2 * E0 := by rw [hq]; field_simp
    have e4 : ‖homPairRep ha hp (homPartial i T.cm θ) zb‖ ≤ 2 * Real.pi * r ^ 2 * E0 := by
      refine (norm_homPairRep_le ha hp _ _).trans ?_
      calc homDualNorm ha hp (homPartial i T.cm θ) * ‖zb‖
          ≤ (2 * Real.sqrt 2 * Real.pi * r * E0) * q :=
            mul_le_mul (hb.dcm i) hzbq (norm_nonneg _) (by positivity)
        _ = 2 * Real.pi * r ^ 2 * E0 := by rw [hq]; field_simp
    have e5 : ‖homPairRep ha hp (homPartial i T.P θ z) z‖ ≤ K * (2 * Real.pi * r ^ 2 * E0) := by
      refine (norm_homPairRep_op_le ha hp _ _ _).trans ?_
      calc ‖homLamCLM ha hp (homPartial i T.P θ)‖ * ‖z‖ * ‖z‖
          ≤ (K * (4 * Real.pi * E0)) * (‖z‖ * ‖z‖) := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (hb.dP i) (by positivity)
        _ ≤ (K * (4 * Real.pi * E0)) * (r ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left hzz (by positivity)
        _ = _ := by ring
    have e6 : ‖homPairRep ha hp (homPartial i T.Q θ z) zb‖ ≤ K * (2 * Real.pi * r ^ 2 * E0) * 4 := by
      refine (norm_homPairRep_op_le ha hp _ _ _).trans ?_
      calc ‖homLamCLM ha hp (homPartial i T.Q θ)‖ * ‖z‖ * ‖zb‖
          ≤ (K * (16 * Real.pi * E0)) * (‖z‖ * ‖zb‖) := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (hb.dQ i) (by positivity)
        _ ≤ (K * (16 * Real.pi * E0)) * (r ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left hzzb (by positivity)
        _ = _ := by ring
    have e7 : ‖homPairRep ha hp (homPartial i T.P' θ zb) zb‖ ≤ K * (2 * Real.pi * r ^ 2 * E0) := by
      refine (norm_homPairRep_op_le ha hp _ _ _).trans ?_
      calc ‖homLamCLM ha hp (homPartial i T.P' θ)‖ * ‖zb‖ * ‖zb‖
          ≤ (K * (4 * Real.pi * E0)) * (‖zb‖ * ‖zb‖) := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (hb.dP' i) (by positivity)
        _ ≤ (K * (4 * Real.pi * E0)) * (r ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left hzbzb (by positivity)
        _ = _ := by ring
    unfold homRtheta
    refine le_trans (norm_add7_le _ _ _ _ _ _ _) ?_
    have := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add e1 e2) e3) e4) e5) e6) e7
    refine this.trans (le_of_eq ?_)
    ring
  -- the normal components
  have hn2 : ∀ x : HomL2, ‖x‖ ≤ q → ∀ M : HomOp, ‖(2 : ℂ) • M‖ ≤ K * E0 →
      ‖((2 : ℂ) • M) x‖ ≤ K * E0 * q := fun x hx M hM =>
    ((((2 : ℂ) • M).le_opNorm x).trans (mul_le_mul hM hx (norm_nonneg _) hKE))
  have hn1 : ∀ x : HomL2, ‖x‖ ≤ q → ∀ M : HomOp, ‖M‖ ≤ K * E0 →
      ‖M x‖ ≤ K * E0 * q := fun x hx M hM =>
    ((M.le_opNorm x).trans (mul_le_mul hM hx (norm_nonneg _) hKE))
  have hRz : ‖homRz T θ z zb‖ ≤ (r * E0 / Real.sqrt 2) * (1 + 2 * K) := by
    have h1 := hn2 z hzq _ hb.P
    have h2 := hn1 zb hzbq _ hb.Qt
    have e : homRz T θ z zb = T.cp θ + ((2 : ℂ) • T.P θ) z + T.Qt θ zb := by
      simp [homRz]
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hb.cp h1)) h2)
      |>.trans (le_of_eq ?_)
    rw [hq]; field_simp; ring
  have hRzb : ‖homRzb T θ z zb‖ ≤ (r * E0 / Real.sqrt 2) * (1 + 2 * K) := by
    have h1 := hn1 z hzq _ hb.Q
    have h2 := hn2 zb hzbq _ hb.P'
    have e : homRzb T θ z zb = T.cm θ + T.Q θ z + ((2 : ℂ) • T.P' θ) zb := by
      simp [homRzb]
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hb.cm h1)) h2)
      |>.trans (le_of_eq ?_)
    rw [hq]; field_simp; ring
  have hn : ‖homSqrt2⁻¹‖ = (Real.sqrt 2)⁻¹ := by rw [norm_inv, norm_homSqrt2]
  have hRuv : ‖homRu T θ z zb‖ + ‖homRv T θ z zb‖ ≤
      Real.sqrt 2 * (‖homRz T θ z zb‖ + ‖homRzb T θ z zb‖) := by
    have hu : ‖homRu T θ z zb‖ ≤ (Real.sqrt 2)⁻¹ * (‖homRz T θ z zb‖ + ‖homRzb T θ z zb‖) := by
      unfold homRu; rw [norm_smul, hn]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    have hv : ‖homRv T θ z zb‖ ≤ (Real.sqrt 2)⁻¹ * (‖homRz T θ z zb‖ + ‖homRzb T θ z zb‖) := by
      unfold homRv; rw [norm_smul, norm_mul, Complex.norm_I, one_mul, hn]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    have : (Real.sqrt 2)⁻¹ + (Real.sqrt 2)⁻¹ = Real.sqrt 2 := by field_simp; linarith
    nlinarith [norm_nonneg (homRz T θ z zb), norm_nonneg (homRzb T θ z zb)]
  have hN : ‖homRu T θ z zb‖ + ‖homRv T θ z zb‖ ≤ 2 * r * E0 * (1 + 2 * K) := by
    refine hRuv.trans ?_
    have := add_le_add hRz hRzb
    calc Real.sqrt 2 * (‖homRz T θ z zb‖ + ‖homRzb T θ z zb‖)
        ≤ Real.sqrt 2 * ((r * E0 / Real.sqrt 2) * (1 + 2 * K) +
          (r * E0 / Real.sqrt 2) * (1 + 2 * K)) := mul_le_mul_of_nonneg_left this hs.le
      _ = _ := by field_simp; ring
  unfold homXnorm
  have t1 : (2 * Real.pi)⁻¹ * ‖homRy T θ‖ ≤ E0 := by
    have : ‖homRy T θ‖ ≤ 2 * Real.pi * E0 := hb.b
    calc (2 * Real.pi)⁻¹ * ‖homRy T θ‖ ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * E0) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = E0 := by field_simp
  have t2 : (2 * Real.pi * r ^ 2)⁻¹ * ‖fun i => homRtheta ha hp T i θ y z zb‖ ≤ (4 + 6 * K) * E0 := by
    calc _ ≤ (2 * Real.pi * r ^ 2)⁻¹ * ((4 + 6 * K) * (2 * Real.pi * r ^ 2 * E0)) :=
          mul_le_mul_of_nonneg_left hRth (by positivity)
      _ = _ := by field_simp
  have t3 : r⁻¹ * (‖homRu T θ z zb‖ + ‖homRv T θ z zb‖) ≤ 2 * (1 + 2 * K) * E0 := by
    calc _ ≤ r⁻¹ * (2 * r * E0 * (1 + 2 * K)) := mul_le_mul_of_nonneg_left hN (by positivity)
      _ = _ := by field_simp
  linarith

end KAM.Wave
