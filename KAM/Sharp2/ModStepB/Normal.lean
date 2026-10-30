/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.ModStepB.Geo
public import KAM.Apost.Periodicity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The normal correction and the intermediate torus (step `step:p2s2:st-n`)

Under `ModStepB.Hyp` and the standing data:

* `tri`: the triangular objects of v1 (`KAM.Apost.triangular`) for `ηᴸ, ηᴺ, T`: regularity,
  periodicity, `∂_ω ξᴺ = -ηᴺ`, `∂_ω ξᴸ = T ξᴺ - ηᴸ`, reality; `modXiN0 = triXi0` etc.;
* `u_le`, `u_real_le`: `|𝓡ηᴺ| ≤ c μ` on `T_{r-δ}` and `≤ c_avg μ` at real points (the full-bite
  certificate, `c_b (δ/b)^κ ≤ c_avg`);
* `xi0_le`, `xiN_le`: `|ξᴺ₀| ≤ C_0 μ`, `|ξᴺ| ≤ C_ξN μ` on `T_{r-δ}`;
* `Kt_sub_le`, `Kt_mem`, `Kt_holo`, `Kt_primary`, `Kt_real`: `K̃ = K + N ξᴺ`;
* `dNxi_col`: the columns of `D(N ξᴺ)` are `≤ σ_N (C_0 + c₁) μ/δ` on `T_{r-δ}` (Cauchy on
  `N ξᴺ₀`; the solution clause at the split bite `sδ` and Cauchy with the bite `(1-s)δ` on
  `N 𝓡ηᴺ`), hence `Lt_sub_le`, `LtT_sub_le`, `Lt_le`, `LtT_le` (the intermediate frame).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2

open KAM KAM.Torus KAM.Apost KAM.Sharp

variable {n : ℕ}

namespace ModStepB

/-- The entries of `L_F - L_G`. -/
theorem tangentMat_sub_apply {F G : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}
    (hF : DifferentiableAt ℂ F θ) (hG : DifferentiableAt ℂ G θ) (s : Fin n ⊕ Fin n)
    (j : Fin n) : (tangentMat F θ - tangentMat G θ) s j =
      fderiv ℂ (fun y => sumVec n (F y - G y)) θ (Pi.single j 1) s := by
  rw [Matrix.sub_apply, tangentMat, tangentMat, Identities.colMat_apply,
    Identities.colMat_apply, fderiv_sumVec_apply, fderiv_fun_sub hF hG,
    _root_.sub_apply, map_sub, Pi.sub_apply]

/-- `|L_F - L_G| ≤ n e` and `|(L_F - L_G)ᵀ| ≤ 2n e` when every column of `D(F - G)` is `≤ e`. -/
theorem tangentMat_sub_le {F G : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}
    {e : ℝ} (hF : DifferentiableAt ℂ F θ) (hG : DifferentiableAt ℂ G θ) (he : 0 ≤ e)
    (hc : ∀ j : Fin n, ‖fderiv ℂ (fun y => sumVec n (F y - G y)) θ (Pi.single j 1)‖ ≤ e) :
    ‖tangentMat F θ - tangentMat G θ‖ ≤ n * e ∧
      ‖(tangentMat F θ - tangentMat G θ)ᵀ‖ ≤ 2 * n * e := by
  have hent : ∀ s j, ‖(tangentMat F θ - tangentMat G θ) s j‖ ≤ e := fun s j => by
    rw [tangentMat_sub_apply hF hG]
    exact (norm_le_pi_norm _ s).trans (hc j)
  refine ⟨norm_le_of_col he hent, (norm_transpose_le_of_col he hent).trans (le_of_eq ?_)⟩
  rw [Fintype.card_sum, Fintype.card_fin]; push_cast; ring

namespace Hyp

variable {p : StepInB} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {Ω : Set (Fin n → ℝ)}
  {γ β εL εN δ r s c' b cb : ℝ} {m : Fin 5 → ℝ}
  (H : Hyp p 𝔅 h K ω Ω γ β εL εN δ r s c' b cb m)
  {τ M γ₀ : ℝ} (hS : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ₀)
include H hS

/-! ### The data of the triangular system -/

theorem eta_props : DifferentiableOn ℂ (etaL h K ω) (complexStrip n r) ∧
    DifferentiableOn ℂ (etaN h K ω) (complexStrip n r) ∧ IsPeriodicOn (etaL h K ω) r ∧
    IsPeriodicOn (etaN h K ω) r ∧ IsRealVec (etaL h K ω) ∧ IsRealVec (etaN h K ω) ∧
    avg (etaN h K ω) = 0 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, hηd, -, -⟩, -, -, -⟩ :=
    frame_basic hS H.r_pos H.β_pos H.holo H.ball H.fderiv_le H.gramB
  obtain ⟨-, hper, hre⟩ := periodicity hS H.r_pos H.holo H.primary H.K_mem
  obtain ⟨-, -, -, -, -, -, hηp⟩ := hper H.gram
  have hηr := (hre H.gram H.real).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact ⟨Correction.diffOn_etaL hηd, Correction.diffOn_etaN hηd, Correction.periodic_etaL hηp,
    Correction.periodic_etaN hηp, Correction.isRealVec_etaL hηr, Correction.isRealVec_etaN hηr,
    (exactness hS H.r_pos H.holo H.primary H.K_mem).2⟩

theorem T_props : DifferentiableOn ℂ (torsion h K ω) (complexStrip n r) ∧
    IsPeriodicOn (torsion h K ω) r ∧ IsRealMat (torsion h K ω) ∧
    torsionAverage h K ω = avg (torsion h K ω) := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, hTd, -, -, -, -, hTc⟩, -, -, -⟩ :=
    frame_basic hS H.r_pos H.β_pos H.holo H.ball H.fderiv_le H.gramB
  obtain ⟨-, hper, hre⟩ := periodicity hS H.r_pos H.holo H.primary H.K_mem
  obtain ⟨-, -, -, -, hTp, -, -⟩ := hper H.gram
  exact ⟨hTd, hTp, (hre H.gram H.real).2.2.2.2.2.2.2.2.2.2.2.2.1,
    torsionAverage_eq_avg h K ω hTc⟩

/-- The triangular system of v1 for `ηᴸ, ηᴺ, T` (`bp:p2:triangular`): regularity,
periodicity, the two cohomological equations and reality. -/
theorem tri :
    avg (triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω)) = 0 ∧
    DifferentiableOn ℂ (triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω))
      (complexStrip n (r - δ)) ∧
    IsPeriodicOn (triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω)) (r - δ) ∧
    DifferentiableOn ℂ (triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω))
      (complexStrip n (r - δ)) ∧
    IsPeriodicOn (triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω)) (r - δ) ∧
    DifferentiableOn ℂ (triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω))
      (complexStrip n (r - 2 * δ)) ∧
    IsPeriodicOn (triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω)) (r - 2 * δ) ∧
    (∀ θ ∈ complexStrip n (r - δ), fderiv ℂ (triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω))
      θ (fun l => (ω l : ℂ)) = -etaN h K ω θ) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ), fderiv ℂ (triXiL ω (etaL h K ω) (etaN h K ω)
      (torsion h K ω)) θ (fun l => (ω l : ℂ)) =
        triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ) ∧
    IsRealVec (triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω)) ∧
    IsRealVec (triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω)) ∧
    IsRealVec (triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω)) := by
  obtain ⟨hη1, hη2, hη3, hη4, hη5, hη6, hη7⟩ := H.eta_props hS
  obtain ⟨hT1, hT2, hT3, hT4⟩ := H.T_props hS
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7⟩, ⟨b1, b2⟩, -, hre⟩ :=
    triangular hS H.r_pos H.δ_pos (by linarith [H.three, H.δ_pos]) hη1 hη3 hη2 hη4 H.ηL H.ηN hη7
      hT1 hT2 H.T (hT4 ▸ H.Ta.1) (hT4 ▸ H.Ta.2)
  obtain ⟨-, c2, c3, c4⟩ := hre hη5 hη6 hT3
  exact ⟨a1, a2, a3, a4, a5, a6, a7, b1, b2, c2, c3, c4⟩

/-- `𝓡ηᴺ` on `T_{r-δ}`. -/
theorem u_props : DifferentiableOn ℂ (cohR ω (etaN h K ω)) (complexStrip n (r - δ)) ∧
    IsPeriodicOn (cohR ω (etaN h K ω)) (r - δ) ∧ IsRealVec (cohR ω (etaN h K ω)) := by
  obtain ⟨hvec, -⟩ := Apost.cohomological hS H.r_pos H.δ_pos H.δ_lt_r
  obtain ⟨hd, hp, -, -, -, hre, -⟩ := hvec (etaN h K ω) εN (H.eta_props hS).2.1
    (H.eta_props hS).2.2.2.1 H.ηN (H.eta_props hS).2.2.2.2.2.2
  exact ⟨hd, hp, hre (H.eta_props hS).2.2.2.2.2.1⟩

theorem xi0_eq : modXiN0 h K ω = triXi0 ω (etaL h K ω) (etaN h K ω) (torsion h K ω) := by
  have hr1 := H.r1_pos
  refine modXiN0_eq (Triangular.continuous_ofReal_comp H.r_pos (H.eta_props hS).1) ?_
    (H.T_props hS).2.2.2
  exact (Triangular.continuous_ofReal_comp hr1 ((H.T_props hS).1.mono H.sub1)).matrix_mulVec
    (Triangular.continuous_ofReal_comp hr1 (H.u_props hS).1)

theorem xiN_eq : modXiN h K ω = triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω) :=
  modXiN_eq (H.xi0_eq hS)

theorem xiL_eq : modXiL h K ω = triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) :=
  modXiL_eq (H.xi0_eq hS)

/-- `ξᴺ` is holomorphic, periodic and real, and `∂_ω ξᴺ = -ηᴺ`, on `T_{r-δ}`. -/
theorem xiN_props : DifferentiableOn ℂ (modXiN h K ω) (complexStrip n (r - δ)) ∧
    IsPeriodicOn (modXiN h K ω) (r - δ) ∧ IsRealVec (modXiN h K ω) ∧
    ∀ θ ∈ complexStrip n (r - δ),
      fderiv ℂ (modXiN h K ω) θ (fun l => (ω l : ℂ)) = -etaN h K ω θ := by
  obtain ⟨-, hd, hp, -, -, -, -, hdω, -, -, hr, -⟩ := H.tri hS
  rw [H.xiN_eq hS]
  exact ⟨hd, hp, hr, hdω⟩

/-! ### The bounds of the normal correction -/

theorem u_le : ∀ θ ∈ complexStrip n (r - δ),
    ‖cohR ω (etaN h K ω) θ‖ ≤ p.c * mu p γ εL εN δ := fun θ hθ => by
  have h1 := H.cert.sol ω H.mem H.δ_lt_r (etaN h K ω) εN (H.eta_props hS).2.1
    (H.eta_props hS).2.2.2.1 H.ηN (H.eta_props hS).2.2.2.2.2.2 θ hθ
  refine h1.trans ?_
  have hc := H.ok.sd.1
  have e : p.c * γ⁻¹ * δ ^ (-p.κ) * εN = p.c * (εN / (γ * δ ^ p.κ)) := by
    rw [Real.rpow_neg H.δ_pos.le]; field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hc.le

theorem u_real_le : ∀ x : Fin n → ℝ,
    ‖cohR ω (etaN h K ω) (fun i => (x i : ℂ))‖ ≤ p.cavg * mu p γ εL εN δ := fun x => by
  have hb0 : 0 < b := H.δ_pos.trans_le H.b_ge
  have h1 := H.certb.real ω H.mem H.b_le (etaN h K ω) εN (H.eta_props hS).2.1
    (H.eta_props hS).2.2.2.1 H.ηN (H.eta_props hS).2.2.2.2.2.2 x
  refine h1.trans ?_
  have hcb := H.certb.c_pos
  have e : cb * γ⁻¹ * b ^ (-p.κ) * (γ * δ ^ p.κ * mu p γ εL εN δ) =
      cb * (δ / b) ^ p.κ * mu p γ εL εN δ := by
    rw [Real.rpow_neg hb0.le, Real.div_rpow H.δ_pos.le hb0.le]
    field_simp [H.γ_pos.ne']
  have h2 : cb * γ⁻¹ * b ^ (-p.κ) * εN ≤
      cb * γ⁻¹ * b ^ (-p.κ) * (γ * δ ^ p.κ * mu p γ εL εN δ) :=
    mul_le_mul_of_nonneg_left H.εN_le (by
      have := Real.rpow_nonneg hb0.le (-p.κ)
      have := inv_nonneg.2 H.γ_pos.le
      positivity)
  rw [e] at h2
  exact h2.trans (mul_le_mul_of_nonneg_right H.cavg_le H.mu_nonneg)

/-- `bp:p2s2:step`, step `st-n`: `|ξᴺ₀| ≤ C_0 μ`. -/
theorem xi0_le : ‖modXiN0 h K ω‖ ≤ sC0 p * mu p γ εL εN δ := by
  have hr1 := H.r1_pos
  have hT0 : 0 ≤ st p := nn_st H.ok
  have havg : ‖avg (fun θ => etaL h K ω θ + torsion h K ω θ *ᵥ cohR ω (etaN h K ω) θ)‖ ≤
      p.lam * mu p γ εL εN δ + st p * (p.cavg * mu p γ εL εN δ) := by
    refine norm_torusAverage_le fun x _ => ?_
    have hx := ofReal_mem_complexStrip hr1 x
    refine (norm_add_le _ _).trans (add_le_add ((H.ηL _ (H.sub1 hx)).trans H.εL_le) ?_)
    exact (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul (H.T _ hx) (H.u_real_le hS x)
      (norm_nonneg _) hT0)
  refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
  calc _ ≤ p.sT * (p.lam * mu p γ εL εN δ + st p * (p.cavg * mu p γ εL εN δ)) :=
        mul_le_mul H.Ta.2 havg (norm_nonneg _) H.ok.caps.2.2.2.2.2.le
    _ = sC0 p * mu p γ εL εN δ := by
        rw [sC0]; simp only [H.fix, Bool.false_eq_true, ↓reduceIte]; ring

theorem xiN_le : ∀ θ ∈ complexStrip n (r - δ),
    ‖modXiN h K ω θ‖ ≤ sCxiN p * mu p γ εL εN δ := fun θ hθ => by
  refine (norm_sub_le _ _).trans ((add_le_add (H.xi0_le hS) (H.u_le hS θ hθ)).trans
    (le_of_eq ?_))
  rw [sCxiN]; ring

/-! ### The intermediate torus `K̃ = K + N ξᴺ` -/

theorem Kt_sub_le : ∀ θ ∈ complexStrip n (r - δ),
    ‖modKtilde h K ω θ - K θ‖ ≤ sCKt p * mu p γ εL εN δ := fun θ hθ => by
  rw [← norm_sumVec, sumVec_modKtilde_sub]
  refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
  calc _ ≤ p.sN * (sCxiN p * mu p γ εL εN δ) :=
        mul_le_mul (H.N' θ (H.sub1 hθ)) (H.xiN_le hS θ hθ) (norm_nonneg _)
          H.ok.caps.2.2.2.1.le
    _ = sCKt p * mu p γ εL εN δ := by rw [sCKt]; ring

omit hS in
/-- `C_K̃ μ ≤ C_ΔK μ/(γ δ^κ) < β`. -/
theorem Kt_scale : sCKt p * mu p γ εL εN δ < β := by
  have h1 : sCKt p * mu p γ εL εN δ ≤ sCDK p * (mu p γ εL εN δ / (γ * δ ^ p.κ)) := by
    have hgK : sg p * sCKt p ≤ sCDK p := by
      rw [sCDK]
      have := mul_nonneg (nn_sKt H.ok) (nn_sCxiL H.ok)
      linarith
    calc sCKt p * mu p γ εL εN δ ≤ sCKt p * (sg p * (mu p γ εL εN δ / (γ * δ ^ p.κ))) :=
          mul_le_mul_of_nonneg_left H.mu_le_g_mu_div (nn_sCKt H.ok)
      _ = sg p * sCKt p * (mu p γ εL εN δ / (γ * δ ^ p.κ)) := by ring
      _ ≤ sCDK p * (mu p γ εL εN δ / (γ * δ ^ p.κ)) :=
          mul_le_mul_of_nonneg_right hgK (div_nonneg H.mu_nonneg H.gd_pos.le)
  refine lt_of_le_of_lt h1 ?_
  have := H.β_gt
  rw [mul_div_assoc']
  exact this

theorem Kt_mem : ∀ θ ∈ complexStrip n (r - δ), modKtilde h K ω θ ∈ Metric.ball (K θ) β :=
  fun θ hθ => by
  rw [Metric.mem_ball, dist_eq_norm]
  exact lt_of_le_of_lt (H.Kt_sub_le hS θ hθ) H.Kt_scale

theorem Kt_mem𝔅 : ∀ θ ∈ complexStrip n (r - δ), modKtilde h K ω θ ∈ 𝔅 := fun θ hθ =>
  H.ball θ (H.sub1 hθ) (H.Kt_mem hS θ hθ)

theorem N_props : DifferentiableOn ℂ (normalMat K) (complexStrip n r) ∧
    IsPeriodicOn (normalMat K) r ∧ IsRealMat (normalMat K) := by
  obtain ⟨⟨-, -, -, -, -, -, hNd, -⟩, -⟩ :=
    frame_basic hS H.r_pos H.β_pos H.holo H.ball H.fderiv_le H.gramB
  obtain ⟨-, hper, hre⟩ := periodicity hS H.r_pos H.holo H.primary H.K_mem
  exact ⟨hNd, (hper H.gram).2.1, (hre H.gram H.real).2.2.2.2.2.2.2.2.2.1⟩

theorem Kt_holo : DifferentiableOn ℂ (modKtilde h K ω) (complexStrip n (r - δ)) := by
  have hv : DifferentiableOn ℂ (fun θ => normalMat K θ *ᵥ modXiN h K ω θ)
      (complexStrip n (r - δ)) :=
    ((H.N_props hS).1.mono H.sub1).matrix_mulVec (H.xiN_props hS).1
  exact (H.holo.mono H.sub1).add ((sumVecIso n).symm.differentiable.comp_differentiableOn hv)

theorem Kt_primary : IsPrimaryOnStrip (modKtilde h K ω) (r - δ) := by
  intro θ hθ k
  have hN := periodic_int_shift (fun i z hz => (H.N_props hS).2.1 i z (H.sub1 hz)) k hθ
  have hξ := periodic_int_shift (H.xiN_props hS).2.1 k hθ
  simp only [modKtilde]
  rw [H.primary θ (H.sub1 hθ) k, hN, hξ]
  abel

theorem Kt_real : IsRealOnReals (modKtilde h K ω) := by
  rw [← isRealVec_sumVec_iff]
  intro x s
  show (sumVec n (modKtilde h K ω (fun i => (x i : ℂ))) s).im = 0
  have e : sumVec n (modKtilde h K ω (fun i => (x i : ℂ))) =
      sumVec n (K (fun i => (x i : ℂ))) +
        normalMat K (fun i => (x i : ℂ)) *ᵥ modXiN h K ω (fun i => (x i : ℂ)) := by
    rw [modKtilde, map_add, LinearEquiv.apply_symm_apply]
  rw [e, Pi.add_apply, Complex.add_im, (isRealVec_sumVec_iff.2 H.real) x s,
    Triangular.mulVec_im_eq_zero ((H.N_props hS).2.2 x) ((H.xiN_props hS).2.2.1 x) s, add_zero]

/-! ### The intermediate frame `L̃` -/

omit H hS in
theorem split_strip : r - s * δ - (1 - s) * δ = r - δ := by ring

/-- The columns of `D(N ξᴺ)` on `T_{r-δ}`. -/
theorem dNxi_col : ∀ θ ∈ complexStrip n (r - δ), ∀ j : Fin n,
    ‖fderiv ℂ (fun y => normalMat K y *ᵥ modXiN h K ω y) θ (Pi.single j 1)‖ ≤
      p.sN * (sC0 p + p.c1) * (mu p γ εL εN δ / δ) := by
  intro θ hθ j
  have hsδ : 0 < s * δ := mul_pos H.s_pos H.δ_pos
  have hsδr : s * δ < r := by nlinarith [H.s_lt, H.δ_pos, H.three]
  have h1s : 0 < (1 - s) * δ := mul_pos (by linarith [H.s_lt]) H.δ_pos
  have hsub_s : complexStrip n (r - s * δ) ⊆ complexStrip n r :=
    strip_sub (by linarith [hsδ])
  have hθs : θ ∈ complexStrip n (r - s * δ) :=
    strip_sub (by nlinarith [H.s_lt, H.δ_pos]) hθ
  -- `u` on the larger strip `T_{r - sδ}`
  obtain ⟨hvec, -⟩ := Apost.cohomological hS H.r_pos hsδ hsδr
  obtain ⟨hud, -⟩ := hvec (etaN h K ω) εN (H.eta_props hS).2.1 (H.eta_props hS).2.2.2.1 H.ηN
    (H.eta_props hS).2.2.2.2.2.2
  have hub := H.cert'.sol ω H.mem hsδr (etaN h K ω) εN (H.eta_props hS).2.1
    (H.eta_props hS).2.2.2.1 H.ηN (H.eta_props hS).2.2.2.2.2.2
  set w1 : (Fin n → ℂ) → Fin n ⊕ Fin n → ℂ := fun y => normalMat K y *ᵥ modXiN0 h K ω
  set w2 : (Fin n → ℂ) → Fin n ⊕ Fin n → ℂ := fun y => normalMat K y *ᵥ cohR ω (etaN h K ω) y
  have hNd := (H.N_props hS).1
  have hw1 : DifferentiableOn ℂ w1 (complexStrip n r) := hNd.matrix_mulVec (differentiableOn_const _)
  have hw2 : DifferentiableOn ℂ w2 (complexStrip n (r - s * δ)) :=
    (hNd.mono hsub_s).matrix_mulVec hud
  have hfun : (fun y => normalMat K y *ᵥ modXiN h K ω y) = fun y => w1 y - w2 y := by
    funext y; simp only [w1, w2, modXiN, Matrix.mulVec_sub]
  have hθr := H.sub1 hθ
  have hd1 : DifferentiableAt ℂ w1 θ := hw1.differentiableAt
    ((isOpen_complexStrip n r).mem_nhds hθr)
  have hd2 : DifferentiableAt ℂ w2 θ := hw2.differentiableAt
    ((isOpen_complexStrip n (r - s * δ)).mem_nhds hθs)
  rw [hfun, fderiv_fun_sub hd1 hd2, _root_.sub_apply]
  have hb1 : ∀ y ∈ complexStrip n r, ‖w1 y‖ ≤ p.sN * (sC0 p * mu p γ εL εN δ) := fun y hy =>
    (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul (H.N' y hy) (H.xi0_le hS) (norm_nonneg _)
      H.ok.caps.2.2.2.1.le)
  have hb2 : ∀ y ∈ complexStrip n (r - s * δ),
      ‖w2 y‖ ≤ p.sN * (c' * γ⁻¹ * (s * δ) ^ (-p.κ) * εN) := fun y hy =>
    (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul (H.N' y (hsub_s hy)) (hub y hy)
      (norm_nonneg _) H.ok.caps.2.2.2.1.le)
  have hc1 := (cauchy_strip hw1 hb1 H.δ_pos).1 j θ hθ
  have hc2 := (cauchy_strip hw2 hb2 h1s).1 j θ (by rw [split_strip]; exact hθ)
  refine (norm_sub_le _ _).trans ((add_le_add hc1 hc2).trans ?_)
  -- arithmetic
  have hsκ : 0 < s ^ p.κ := Real.rpow_pos_of_pos H.s_pos _
  have h1s' : 0 < 1 - s := by linarith [H.s_lt]
  have e2 : ((1 - s) * δ)⁻¹ * (p.sN * (c' * γ⁻¹ * (s * δ) ^ (-p.κ) * εN)) =
      p.sN * (c' / (s ^ p.κ * (1 - s))) * (γ⁻¹ * δ ^ (-(p.κ + 1)) * εN) := by
    rw [Real.mul_rpow H.s_pos.le H.δ_pos.le, Real.rpow_neg H.s_pos.le, Real.rpow_neg H.δ_pos.le,
      Real.rpow_neg H.δ_pos.le, Real.rpow_add H.δ_pos, Real.rpow_one]
    have h1 : s ^ p.κ ≠ 0 := hsκ.ne'
    have h2 : δ ^ p.κ ≠ 0 := (Real.rpow_pos_of_pos H.δ_pos _).ne'
    have h3 : (1 - s) ≠ 0 := h1s'.ne'
    have h4 : δ ≠ 0 := H.δ_pos.ne'
    have h5 : γ ≠ 0 := H.γ_pos.ne'
    field_simp
  rw [e2]
  have hY0 : 0 ≤ γ⁻¹ * δ ^ (-(p.κ + 1)) * εN :=
    mul_nonneg (mul_nonneg (inv_nonneg.2 H.γ_pos.le) (Real.rpow_nonneg H.δ_pos.le _))
      H.εN_nonneg
  have hsN := H.ok.caps.2.2.2.1.le
  have hc1' : p.sN * (c' / (s ^ p.κ * (1 - s))) * (γ⁻¹ * δ ^ (-(p.κ + 1)) * εN) ≤
      p.sN * p.c1 * (mu p γ εL εN δ / δ) :=
    mul_le_mul (mul_le_mul_of_nonneg_left H.c1_le hsN) H.εN_scale hY0
      (mul_nonneg hsN H.ok.sd.2.1.le)
  have e1 : δ⁻¹ * (p.sN * (sC0 p * mu p γ εL εN δ)) = p.sN * sC0 p * (mu p γ εL εN δ / δ) := by
    rw [div_eq_mul_inv]; ring
  rw [e1]
  calc _ ≤ p.sN * sC0 p * (mu p γ εL εN δ / δ) + p.sN * p.c1 * (mu p γ εL εN δ / δ) :=
        add_le_add le_rfl hc1'
    _ = _ := by ring

theorem Kt_diffAt : ∀ θ ∈ complexStrip n (r - δ), DifferentiableAt ℂ (modKtilde h K ω) θ :=
  fun _ hθ => (H.Kt_holo hS).differentiableAt ((isOpen_complexStrip n (r - δ)).mem_nhds hθ)

omit hS in
theorem K_diffAt : ∀ θ ∈ complexStrip n r, DifferentiableAt ℂ K θ := fun _ hθ =>
  H.holo.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθ)

/-- `|L̃ - L| ≤ C_DL̃ μ/δ`, `|(L̃ - L)ᵀ| ≤ C_DL̃ᵀ μ/δ` on `T_{r-δ}`. -/
theorem Lt_sub_le : ∀ θ ∈ complexStrip n (r - δ),
    ‖tangentMat (modKtilde h K ω) θ - tangentMat K θ‖ ≤ sCDLt p * (mu p γ εL εN δ / δ) ∧
      ‖(tangentMat (modKtilde h K ω) θ - tangentMat K θ)ᵀ‖ ≤
        sCDLtT p * (mu p γ εL εN δ / δ) := fun θ hθ => by
  have he : 0 ≤ p.sN * (sC0 p + p.c1) * (mu p γ εL εN δ / δ) := by
    have := H.ok.caps.2.2.2.1
    have := nn_sC0 H.ok
    have := H.ok.sd.2.1
    have := H.mu_nonneg
    have := H.δ_pos
    positivity
  have hfun : (fun y => sumVec n (modKtilde h K ω y - K y)) =
      fun y => normalMat K y *ᵥ modXiN h K ω y := funext fun y => sumVec_modKtilde_sub y
  obtain ⟨h1, h2⟩ := tangentMat_sub_le (H.Kt_diffAt hS θ hθ) (H.K_diffAt θ (H.sub1 hθ)) he
    (fun j => by rw [hfun]; exact H.dNxi_col hS θ hθ j)
  refine ⟨h1.trans (le_of_eq ?_), h2.trans (le_of_eq ?_)⟩
  · rw [sCDLt, H.pn_real]; ring
  · rw [sCDLtT, H.pn_real]; ring

/-- The intermediate frame: `|L̃| ≤ σ̃_K = (1+ϑ) σ_K`, `|L̃ᵀ| ≤ (1+ϑ) σ_{Lᵀ}` on `T_{r-δ}`. -/
theorem Lt_le : ∀ θ ∈ complexStrip n (r - δ),
    ‖tangentMat (modKtilde h K ω) θ‖ ≤ sKt p ∧
      ‖(tangentMat (modKtilde h K ω) θ)ᵀ‖ ≤ (1 + p.θ) * p.sLt := fun θ hθ => by
  obtain ⟨h1, h2⟩ := H.Lt_sub_le hS θ hθ
  have hθr := H.sub1 hθ
  have hs1 : sCDLt p * (mu p γ εL εN δ / δ) ≤ p.θ * p.sK :=
    (mul_le_mul_of_nonneg_left H.mu_div_δ_le (nn_sCDLt H.ok)).trans
      (by rw [← mul_assoc]; exact H.c_DLt)
  have hs2 : sCDLtT p * (mu p γ εL εN δ / δ) ≤ p.θ * p.sLt :=
    (mul_le_mul_of_nonneg_left H.mu_div_δ_le (nn_sCDLtT H.ok)).trans
      (by rw [← mul_assoc]; exact H.c_DLtT)
  constructor
  · calc _ = ‖tangentMat K θ + (tangentMat (modKtilde h K ω) θ - tangentMat K θ)‖ := by
          rw [add_sub_cancel]
      _ ≤ p.sK + p.θ * p.sK := (norm_add_le _ _).trans (add_le_add (H.L' θ hθr) (h1.trans hs1))
      _ = sKt p := by rw [sKt]; ring
  · calc _ = ‖(tangentMat K θ)ᵀ + (tangentMat (modKtilde h K ω) θ - tangentMat K θ)ᵀ‖ := by
          rw [← Matrix.transpose_add, add_sub_cancel]
      _ ≤ p.sLt + p.θ * p.sLt :=
          (norm_add_le _ _).trans (add_le_add (H.Lt' θ hθr) (h2.trans hs2))
      _ = (1 + p.θ) * p.sLt := by ring

end Hyp

end ModStepB

end KAM.Sharp2

end
