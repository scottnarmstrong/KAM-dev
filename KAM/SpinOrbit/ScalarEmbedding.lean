/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Hamiltonian
public import KAM.Frozen.Defs.InvarianceError
public import KAM.Frozen.Defs.IsPrimaryOnStrip
public import KAM.Frozen.Defs.ComplexStrip
public import KAM.Strip.Analytic

/-!
# The scalar embedding of a lunar torus (track SO, package SO-MODEL)

Proposal §5.1-5.2, in the conventions of `KAM.Iso.Charts.IG1Body`: angle order `(q, φ)`, action
order `(p, J)`, `K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)`, error
`E = KAM.invarianceError 𝓗 K ω` with `ω = (ν, 1)`.

For a function `u : (Fin 2 → ℂ) → ℂ` (any function; the identities at `θ` assume `u` is `C²` at
`θ`, which holds for every holomorphic `u` on an open set, `contDiffAt_of_differentiableOn`):

* `soK ν u θ = ((θ₁ + u, θ₂), (ν + D_ν u, -p²/2 - V(θ₁ + u, θ₂)))`, `D_ν = ν ∂₁ + ∂₂`;
* `soDnu_q`, `soDnu_φ`: `D_ν q = p`, `D_ν φ = 1`; `soHC_soK`: `𝓗 ∘ K = 0`;
* `fderiv_soK_dir`: `DK(θ)(ν, 1)`; `invarianceError_soK`:
  `E = ((0, 0), (-r, p r))`, `r = D_ν² u + ∂_q V(θ₁ + u, θ₂)` (`soResidual`);
* `norm_invarianceError_soK_le`, `norm_invarianceError_soK_le_strip`:
  `‖E‖ ≤ max (1, ‖p‖) ‖r‖` pointwise and as a bound over a strip (the strip norm `‖·‖_ρ` of the
  campaign is the supremum over `complexStrip n ρ`, as in `IG1Body`);
* `soK_primary`: `K` is primary when `u` is `ℤ²`-periodic;
* the π-free form (plan, "π-free arithmetic"): `u = soUofW w`, `w(x) = 2π u(x/2π)` in the phase
  variable `x = 2πθ`; `soResidual_soUofW`: `r(θ) = 2π · soRW w (2πθ)` with
  `soRW w x = D_ν² w(x) + 2ε Σ A_m sin(2 w(x) + 2 x₁ - m x₂)`, which contains no `π`.
-/

@[expose] public noncomputable section

open Real

namespace KAM.SpinOrbit

/-! ### Definitions -/

/-- The frequency direction `(ν, 1)` in `ℂ²`. -/
def soDir (ν : ℝ) : Fin 2 → ℂ := ![(ν : ℂ), 1]

/-- The flow frequency `ω = (ν, 1)` in `ℝ²` (as in `invarianceError`). -/
def soOmega (ν : ℝ) : Fin 2 → ℝ := ![ν, 1]

theorem soOmega_cast (ν : ℝ) : (fun i => (soOmega ν i : ℂ)) = soDir ν := by
  funext i; fin_cases i <;> simp [soOmega, soDir]

/-- `D_ν f = ν ∂_{θ₁} f + ∂_{θ₂} f`. -/
def soDnu (ν : ℝ) (f : (Fin 2 → ℂ) → ℂ) (θ : Fin 2 → ℂ) : ℂ := fderiv ℂ f θ (soDir ν)

/-- The momentum `p = ν + D_ν u`. -/
def soP (ν : ℝ) (u : (Fin 2 → ℂ) → ℂ) (θ : Fin 2 → ℂ) : ℂ := ν + soDnu ν u θ

/-- The action `J = -p²/2 - V(θ₁ + u, θ₂)`. -/
def soJ (ν : ℝ) (u : (Fin 2 → ℂ) → ℂ) (θ : Fin 2 → ℂ) : ℂ :=
  -(soP ν u θ) ^ 2 / 2 - soVC (θ 0 + u θ) (θ 1)

/-- The embedding `K_u` of proposal §5.1 in angle-action order `((q, φ), (p, J))`. -/
def soK (ν : ℝ) (u : (Fin 2 → ℂ) → ℂ) (θ : Fin 2 → ℂ) : (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  (![θ 0 + u θ, θ 1], ![soP ν u θ, soJ ν u θ])

/-- The scalar residual `r = D_ν² u + ∂_q V(θ₁ + u, θ₂)`. -/
def soResidual (ν : ℝ) (u : (Fin 2 → ℂ) → ℂ) (θ : Fin 2 → ℂ) : ℂ :=
  soDnu ν (soDnu ν u) θ + soVqC (θ 0 + u θ) (θ 1)

/-! ### Regularity -/

theorem differentiableAt_soDnu {ν : ℝ} {u : (Fin 2 → ℂ) → ℂ} {θ : Fin 2 → ℂ}
    (hu : ContDiffAt ℂ 2 u θ) : DifferentiableAt ℂ (soDnu ν u) θ := by
  have h1 : ContDiffAt ℂ 1 (fderiv ℂ u) θ := hu.fderiv_right (by norm_num)
  exact (h1.clm_apply contDiffAt_const).differentiableAt (by norm_num)

theorem contDiffAt_of_differentiableOn {u : (Fin 2 → ℂ) → ℂ} {U : Set (Fin 2 → ℂ)}
    (hU : IsOpen U) (hu : DifferentiableOn ℂ u U) {θ : Fin 2 → ℂ} (hθ : θ ∈ U) :
    ContDiffAt ℂ 2 u θ :=
  (KAM.analyticOnNhd_of_differentiableOn hU hu θ hθ).contDiffAt

theorem differentiableAt_soK {ν : ℝ} {u : (Fin 2 → ℂ) → ℂ} {θ : Fin 2 → ℂ}
    (hu : ContDiffAt ℂ 2 u θ) : DifferentiableAt ℂ (soK ν u) θ := by
  have h0 : DifferentiableAt ℂ u θ := hu.differentiableAt (by norm_num)
  have hD := differentiableAt_soDnu (ν := ν) hu
  have hp : DifferentiableAt ℂ (soP ν u) θ := by unfold soP; fun_prop
  have hq : DifferentiableAt ℂ (fun θ : Fin 2 → ℂ => soVC (θ 0 + u θ) (θ 1)) θ := by
    unfold soVC; fun_prop
  have hJ : DifferentiableAt ℂ (soJ ν u) θ := by unfold soJ; fun_prop
  unfold soK
  refine DifferentiableAt.prodMk ?_ ?_
  · refine differentiableAt_pi.2 fun i => ?_
    fin_cases i
    · change DifferentiableAt ℂ (fun θ : Fin 2 → ℂ => θ 0 + u θ) θ
      fun_prop
    · change DifferentiableAt ℂ (fun θ : Fin 2 → ℂ => θ 1) θ
      fun_prop
  · refine differentiableAt_pi.2 fun i => ?_
    fin_cases i
    · simpa using hp
    · simpa using hJ

/-! ### The exact identities -/

/-- `𝓗 ∘ K = 0`, for every `u` (by construction of `J`). -/
theorem soHC_soK (ν : ℝ) (u : (Fin 2 → ℂ) → ℂ) (θ : Fin 2 → ℂ) : soHC (soK ν u θ) = 0 := by
  simp [soHC, soK, soJ]
  ring

/-- `D_ν q = p` for `q = θ₁ + u`. -/
theorem soDnu_q {ν : ℝ} {u : (Fin 2 → ℂ) → ℂ} {θ : Fin 2 → ℂ} (hu : ContDiffAt ℂ 2 u θ) :
    soDnu ν (fun θ => θ 0 + u θ) θ = soP ν u θ := by
  have h0 : DifferentiableAt ℂ u θ := hu.differentiableAt (by norm_num)
  have : HasDerivAt (fun t : ℂ => (θ + t • soDir ν) 0 + u (θ + t • soDir ν))
      (soDnu ν (fun θ => θ 0 + u θ) θ) 0 :=
    soHasDerivAt_line (𝕜 := ℂ) (f := fun θ : Fin 2 → ℂ => θ 0 + u θ) (z := θ)
      (by change DifferentiableAt ℂ (fun θ : Fin 2 → ℂ => θ 0 + u θ) θ; fun_prop) (soDir ν)
  have h1 : HasDerivAt (fun t : ℂ => (θ + t • soDir ν) 0 + u (θ + t • soDir ν))
      (ν + soDnu ν u θ) 0 := by
    have ha : HasDerivAt (fun t : ℂ => (θ + t • soDir ν) 0) (ν : ℂ) 0 := by
      simpa [soDir] using ((hasDerivAt_id (0 : ℂ)).mul_const (ν : ℂ)).const_add (θ 0)
    exact ha.add (soHasDerivAt_line h0 (soDir ν))
  exact this.unique h1

/-- `D_ν φ = 1` for `φ = θ₂`. -/
theorem soDnu_φ (ν : ℝ) (θ : Fin 2 → ℂ) : soDnu ν (fun θ => θ 1) θ = 1 := by
  have : HasDerivAt (fun t : ℂ => (θ + t • soDir ν) 1) (soDnu ν (fun θ => θ 1) θ) 0 :=
    soHasDerivAt_line (𝕜 := ℂ) (f := fun θ : Fin 2 → ℂ => θ 1) (z := θ)
      (by change DifferentiableAt ℂ (fun θ : Fin 2 → ℂ => θ 1) θ; fun_prop) (soDir ν)
  have h1 : HasDerivAt (fun t : ℂ => (θ + t • soDir ν) 1) (1 : ℂ) 0 := by
    simpa [soDir] using ((hasDerivAt_id (0 : ℂ)).mul_const (1 : ℂ)).const_add (θ 1)
  exact this.unique h1

/-- The derivative of `K` in the direction `(ν, 1)`. -/
theorem fderiv_soK_dir {ν : ℝ} {u : (Fin 2 → ℂ) → ℂ} {θ : Fin 2 → ℂ}
    (hu : ContDiffAt ℂ 2 u θ) :
    fderiv ℂ (soK ν u) θ (soDir ν) =
      (![soP ν u θ, 1],
        ![soDnu ν (soDnu ν u) θ,
          -(soP ν u θ * soDnu ν (soDnu ν u) θ) -
            (soVqC (θ 0 + u θ) (θ 1) * soP ν u θ + soVφC (θ 0 + u θ) (θ 1))]) := by
  have h0 : DifferentiableAt ℂ u θ := hu.differentiableAt (by norm_num)
  have hD := differentiableAt_soDnu (ν := ν) hu
  have hK := soHasDerivAt_line (differentiableAt_soK (ν := ν) hu) (soDir ν)
  have ha : ∀ j : Fin 2, HasDerivAt (fun t : ℂ => (θ + t • soDir ν) j) (soDir ν j) 0 := fun j => by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (soDir ν j)).const_add (θ j)
  have hu' := soHasDerivAt_line h0 (soDir ν)
  have hDu : HasDerivAt (fun t : ℂ => soDnu ν u (θ + t • soDir ν)) (soDnu ν (soDnu ν u) θ) 0 :=
    soHasDerivAt_line hD (soDir ν)
  have hq : HasDerivAt (fun t : ℂ => (θ + t • soDir ν) 0 + u (θ + t • soDir ν))
      (soP ν u θ) 0 := by
    exact ((ha 0).add hu').congr_deriv (by simp [soP, soDir, soDnu])
  have hf : HasDerivAt (fun t : ℂ => (θ + t • soDir ν) 1) 1 0 := by simpa [soDir] using ha 1
  have hp : HasDerivAt (fun t : ℂ => soP ν u (θ + t • soDir ν)) (soDnu ν (soDnu ν u) θ) 0 := by
    unfold soP
    simpa using hDu.const_add (ν : ℂ)
  have hV := hasDerivAt_soVC_comp hq hf
  have hJ : HasDerivAt (fun t : ℂ => soJ ν u (θ + t • soDir ν))
      (-(soP ν u θ * soDnu ν (soDnu ν u) θ) -
        (soVqC (θ 0 + u θ) (θ 1) * soP ν u θ + soVφC (θ 0 + u θ) (θ 1))) 0 := by
    unfold soJ
    simp only [zero_smul, add_zero] at hV
    exact (((hp.pow 2).neg.div_const 2).sub hV).congr_deriv (by norm_num; ring)
  have hpair : HasDerivAt (fun t : ℂ => soK ν u (θ + t • soDir ν))
      (![soP ν u θ, 1], ![soDnu ν (soDnu ν u) θ,
        -(soP ν u θ * soDnu ν (soDnu ν u) θ) -
            (soVqC (θ 0 + u θ) (θ 1) * soP ν u θ + soVφC (θ 0 + u θ) (θ 1))]) 0 := by
    unfold soK
    refine HasDerivAt.prodMk ?_ ?_
    · rw [hasDerivAt_pi]
      intro i; fin_cases i
      · simpa using hq
      · simpa using hf
    · rw [hasDerivAt_pi]
      intro i; fin_cases i
      · simpa [soP] using hp
      · simpa using hJ
  exact hK.unique hpair

/-- The invariance error of the embedding: `E = ((0, 0), (-r, p r))`. -/
theorem invarianceError_soK {ν : ℝ} {u : (Fin 2 → ℂ) → ℂ} {θ : Fin 2 → ℂ}
    (hu : ContDiffAt ℂ 2 u θ) :
    invarianceError soHC (soK ν u) (soOmega ν) θ =
      (![0, 0], ![-soResidual ν u θ, soP ν u θ * soResidual ν u θ]) := by
  unfold invarianceError
  rw [hamiltonianVectorFieldℂ_soHC, soOmega_cast, fderiv_soK_dir hu]
  unfold soExtFieldC soResidual
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp [soK] <;> ring

/-- Pointwise `‖E‖ ≤ max (1, ‖p‖) ‖r‖` for the error of the form `((0, 0), (-r, p r))`. -/
theorem norm_error_form_le (p r : ℂ) :
    ‖((![0, 0] : Fin 2 → ℂ), (![-r, p * r] : Fin 2 → ℂ))‖ ≤ max 1 ‖p‖ * ‖r‖ := by
  have hr := norm_nonneg r
  have hm : 0 ≤ max 1 ‖p‖ * ‖r‖ := by positivity
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg hm]; intro i; fin_cases i <;> simp
  · rw [pi_norm_le_iff_of_nonneg hm]
    intro i; fin_cases i
    · simpa using le_mul_of_one_le_left hr (le_max_left 1 ‖p‖)
    · simpa [norm_mul] using mul_le_mul_of_nonneg_right (le_max_right 1 ‖p‖) hr

/-- `‖E(θ)‖ ≤ max (1, ‖p(θ)‖) ‖r(θ)‖`. -/
theorem norm_invarianceError_soK_le {ν : ℝ} {u : (Fin 2 → ℂ) → ℂ} {θ : Fin 2 → ℂ}
    (hu : ContDiffAt ℂ 2 u θ) :
    ‖invarianceError soHC (soK ν u) (soOmega ν) θ‖ ≤
      max 1 ‖soP ν u θ‖ * ‖soResidual ν u θ‖ := by
  rw [invarianceError_soK hu]; exact norm_error_form_le _ _

/-- The strip form: bounds `‖p‖ ≤ Bp`, `‖r‖ ≤ Br` on a set give `‖E‖ ≤ max (1, Bp) Br` there
(`‖·‖_ρ` is the supremum over `complexStrip 2 ρ`). -/
theorem norm_invarianceError_soK_le_strip {ν : ℝ} {u : (Fin 2 → ℂ) → ℂ} {S : Set (Fin 2 → ℂ)}
    (hu : ∀ θ ∈ S, ContDiffAt ℂ 2 u θ) {Bp Br : ℝ} (hp : ∀ θ ∈ S, ‖soP ν u θ‖ ≤ Bp)
    (hr : ∀ θ ∈ S, ‖soResidual ν u θ‖ ≤ Br) :
    ∀ θ ∈ S, ‖invarianceError soHC (soK ν u) (soOmega ν) θ‖ ≤ max 1 Bp * Br := fun θ hθ =>
  (norm_invarianceError_soK_le (hu θ hθ)).trans
    (mul_le_mul (max_le_max le_rfl (hp θ hθ)) (hr θ hθ) (norm_nonneg _)
      ((zero_le_one).trans (le_max_left _ _)))

/-- For a `ℤ²`-periodic `u`, the embedding is primary. -/
theorem soK_primary {ν : ℝ} {u : (Fin 2 → ℂ) → ℂ}
    (hper : ∀ (θ : Fin 2 → ℂ) (k : Fin 2 → ℤ), u (θ + fun i => (k i : ℂ)) = u θ) (ρ : ℝ) :
    IsPrimaryOnStrip (soK ν u) ρ := by
  intro θ _ k
  have hd : fderiv ℂ u (θ + fun i => (k i : ℂ)) = fderiv ℂ u θ := by
    have h : (fun x : Fin 2 → ℂ => u (x + fun i => (k i : ℂ))) = u := funext fun x => hper x k
    have := fderiv_comp_add_right (𝕜 := ℂ) (f := u) (fun i => (k i : ℂ)) (x := θ)
    rw [h] at this
    exact this.symm
  have hp : soP ν u (θ + fun i => (k i : ℂ)) = soP ν u θ := by simp [soP, soDnu, hd]
  have hV := soVC_add_int (θ 0 + u θ) (θ 1) (k 0) (k 1)
  unfold soK
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i
  · simp [hper θ k, Matrix.vecHead]; ring
  · simp [Matrix.vecHead, Matrix.vecTail]
  · simp [hp]
  · simp only [soJ, hp, hper θ k]
    simp only [Pi.add_apply]
    rw [show θ 0 + (k 0 : ℂ) + u θ = θ 0 + u θ + (k 0 : ℂ) by ring,
      show θ 1 + (k 1 : ℂ) = θ 1 + (k 1 : ℂ) from rfl, hV]
    simp

/-! ### The π-free form -/

/-- The scalar `u` attached to `w`: `u(θ) = w(2πθ)/(2π)` (so `w = 2π u` in the phase variable
`x = 2πθ`). -/
def soUofW (w : (Fin 2 → ℂ) → ℂ) (θ : Fin 2 → ℂ) : ℂ := w ((2 * (π : ℂ)) • θ) / (2 * π)

/-- The π-free residual `R(w)(x) = D_ν² w(x) + 2ε Σ_m A_m sin (2 w(x) + 2 x₁ - m x₂)`. -/
def soRW (ν : ℝ) (w : (Fin 2 → ℂ) → ℂ) (x : Fin 2 → ℂ) : ℂ :=
  soDnu ν (soDnu ν w) x +
    2 * soEps * ∑ m ∈ soModes, (soA m : ℂ) * Complex.sin (2 * w x + 2 * x 0 - m * x 1)

theorem soDnu_comp_smul {ν : ℝ} {g : (Fin 2 → ℂ) → ℂ} {θ : Fin 2 → ℂ} {c : ℂ}
    (hg : DifferentiableAt ℂ g (c • θ)) :
    soDnu ν (fun θ => g (c • θ)) θ = c * soDnu ν g (c • θ) := by
  have h := hg.hasFDerivAt.comp θ ((hasFDerivAt_id θ).const_smul c)
  unfold soDnu
  have h' : HasFDerivAt (fun θ => g (c • θ)) _ θ := h
  rw [h'.fderiv]
  simp

theorem soDnu_soUofW {ν : ℝ} {w : (Fin 2 → ℂ) → ℂ} {θ : Fin 2 → ℂ}
    (hw : DifferentiableAt ℂ w ((2 * (π : ℂ)) • θ)) :
    soDnu ν (soUofW w) θ = soDnu ν w ((2 * (π : ℂ)) • θ) := by
  have h2 : (2 * (π : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  have hg : soUofW w = fun θ => (2 * (π : ℂ))⁻¹ * w ((2 * (π : ℂ)) • θ) := by
    funext θ; simp [soUofW, div_eq_inv_mul]
  have hd : DifferentiableAt ℂ (fun θ => w ((2 * (π : ℂ)) • θ)) θ :=
    hw.comp θ (by fun_prop)
  unfold soDnu
  rw [hg, fderiv_const_mul hd]
  have := soDnu_comp_smul (ν := ν) hw
  unfold soDnu at this
  simp only [smul_apply, smul_eq_mul, this]
  field_simp

theorem soDnu_soDnu_soUofW {ν : ℝ} {w : (Fin 2 → ℂ) → ℂ} {θ : Fin 2 → ℂ}
    (hw : ContDiffAt ℂ 2 w ((2 * (π : ℂ)) • θ)) :
    soDnu ν (soDnu ν (soUofW w)) θ = (2 * (π : ℂ)) * soDnu ν (soDnu ν w) ((2 * (π : ℂ)) • θ) := by
  have hev : soDnu ν (soUofW w) =ᶠ[nhds θ] fun θ' => soDnu ν w ((2 * (π : ℂ)) • θ') := by
    have hcont : Filter.Tendsto (fun θ' : Fin 2 → ℂ => (2 * (π : ℂ)) • θ') (nhds θ)
        (nhds ((2 * (π : ℂ)) • θ)) := (continuous_const_smul _).tendsto θ
    have hE := hw.eventually (by simp)
    filter_upwards [hcont.eventually hE] with θ' hθ'
    exact soDnu_soUofW (hθ'.differentiableAt (by norm_num))
  have hD := differentiableAt_soDnu (ν := ν) hw
  unfold soDnu at hev ⊢
  rw [hev.fderiv_eq]
  have := soDnu_comp_smul (ν := ν) (g := fun x => fderiv ℂ w x (soDir ν)) (θ := θ)
    (c := 2 * (π : ℂ)) hD
  unfold soDnu at this
  exact this

/-- The π-free scalar reduction: `r(θ) = 2π · R(w)(2πθ)`, where `u = w(2π ·)/(2π)`. -/
theorem soResidual_soUofW {ν : ℝ} {w : (Fin 2 → ℂ) → ℂ} {θ : Fin 2 → ℂ}
    (hw : ContDiffAt ℂ 2 w ((2 * (π : ℂ)) • θ)) :
    soResidual ν (soUofW w) θ = (2 * (π : ℂ)) * soRW ν w ((2 * (π : ℂ)) • θ) := by
  have h2 : (2 * (π : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  unfold soResidual soRW soVqC
  rw [soDnu_soDnu_soUofW hw]
  have hs : ∑ m ∈ soModes, (soA m : ℂ) *
      Complex.sin (2 * π * (2 * (θ 0 + soUofW w θ) - m * θ 1)) =
      ∑ m ∈ soModes, (soA m : ℂ) * Complex.sin (2 * w ((2 * (π : ℂ)) • θ) +
        2 * ((2 * (π : ℂ)) • θ) 0 - m * ((2 * (π : ℂ)) • θ) 1) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    simp only [soUofW, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring_nf
  rw [hs]; ring

end KAM.SpinOrbit

end
