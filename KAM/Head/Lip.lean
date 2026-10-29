/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.LipError
import KAM.Head.H1
import KAM.Head.InverseFrequency
import KAM.Head.Parameters
import KAM.Head.Shift
import KAM.Head.Stab
import KAM.Strip.Averages
import KAM.Strip.Increments

/-!
# LIP: Lipschitz dependence of the normalized tori on the frequency

Blueprint Part 4, `bp:p4:lip`. Under `(SA)`, for all `ω, ω' ∈ Ω_γ` and all
`θ ∈ T_{s/32}`,
`|W_{ω'}(θ) - W_ω(θ)| ≤ A₃ ε γ⁻⁴ |ω' - ω|`.

The proof splits into far pairs and close pairs (`|ω' - ω| ≤ λ_* γ²`). The frozen G1 and G2 enter
only through the premise `KAM.Head.GValid` (`GValid.g1b` and `GValid.g2`).

* `step:p4:lip-far`: `KAM.Head.Lip.far_case`, from `|W_ω| ≤ η₀` (`KAM.Head.normalize`) and the
  arithmetic lemma `KAM.Head.Lip.far_arith`.
* `step:p4:lip-g1`: `KAM.Head.Lip.g1_step`. The hypotheses of the second G1 tuple at the shifted
  torus `K'` (`KAM.Head.shiftedTorus`) are `KAM.Head.h1`, the H2-H4 clause of `KAM.Head.stab` at
  `I_* = I_{ω'}`, `ρ = s/8`, `δ = s/32` (after `s/8 - s/32 = 3s/32`), and the error bound of
  `KAM.Head.lip_error`; the smallness is (s4).
* `step:p4:lip-g2`: `KAM.Head.Lip.g2_step`. The reference torus is `K_{ω'}` (`stab` at
  `δ = s/16`), the second torus is the output `K̃` of G1, and the closeness is (s5)
  (`KAM.Head.Lip.close_arith`).
* `step:p4:lip-phase`: `KAM.Head.Lip.norm_phi_le`, through the Lipschitz bound of the phase
  average `KAM.Head.Lip.norm_phaseAverage_sub_le`.
* `step:p4:lip-close`: `KAM.Head.Lip.close_case`, with the arithmetic of
  `KAM.Head.Lip.final_arith`.

No constant is unfolded: the estimates between constants are the abstract real lemmas
`far_arith`, `err_le`, `close_arith`, `final_arith` and the items of `KAM.Head.smallness`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open MeasureTheory

namespace KAM.Head

namespace Lip

variable {n : ℕ} {τ s₀ r₀ Lh : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}
  {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε γ : ℝ} {gc : GConsts}

/-! ### Arithmetic between the constants -/

/-- Step `step:p4:lip-far`: `2 η₀ = 2 A₀ ε γ⁻² ≤ (2 A₀ / λ_*) ε γ⁻⁴ |Δω| ≤ A₃ ε γ⁻⁴ |Δω|`
when `|Δω| > λ_* γ²`. -/
theorem far_arith {A0 lam A3 d : ℝ} (hA0 : 0 ≤ A0) (hlam : 0 < lam) (hγ : 0 < γ)
    (hε : 0 ≤ ε) (hd : lam * γ ^ 2 < d) (hA3 : 2 * A0 / lam ≤ A3) :
    2 * (A0 * ε / γ ^ 2) ≤ A3 * ε / γ ^ 4 * d := by
  have hγ2 : 0 < γ ^ 2 := by positivity
  have hγ4 : 0 < γ ^ 4 := by positivity
  have hA3' : 0 ≤ A3 := le_trans (by positivity) hA3
  have h1 : 2 * (A0 * ε / γ ^ 2) = (2 * A0 / lam) * (lam * γ ^ 2) * (ε / γ ^ 4) := by
    field_simp
  rw [h1]
  have h2 : (2 * A0 / lam) * (lam * γ ^ 2) ≤ A3 * d := by
    calc (2 * A0 / lam) * (lam * γ ^ 2) ≤ A3 * (lam * γ ^ 2) :=
          mul_le_mul_of_nonneg_right hA3 (by positivity)
      _ ≤ A3 * d := mul_le_mul_of_nonneg_left hd.le hA3'
  calc (2 * A0 / lam) * (lam * γ ^ 2) * (ε / γ ^ 4) ≤ A3 * d * (ε / γ ^ 4) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = A3 * ε / γ ^ 4 * d := by ring

/-- Step `step:p4:lip-g1`: the invariance error of the shifted torus is at most
`A₁ λ_* ε` for a close pair: `A₁ ε γ⁻² |Δω| ≤ A₁ λ_* ε` when `|Δω| ≤ λ_* γ²`. -/
theorem err_le {A1 lam d : ℝ} (hA1 : 0 ≤ A1) (hε : 0 ≤ ε) (hγ : 0 < γ)
    (hd : d ≤ lam * γ ^ 2) : A1 * ε / γ ^ 2 * d ≤ A1 * lam * ε := by
  have hγ2 : 0 < γ ^ 2 := by positivity
  calc A1 * ε / γ ^ 2 * d ≤ A1 * ε / γ ^ 2 * (lam * γ ^ 2) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
    _ = A1 * lam * ε := by field_simp

/-- Step `step:p4:lip-g1`: the smallness of the G1 hypothesis at the second tuple, from (s4). -/
theorem g1_small {C12 A1 lam X4 d : ℝ} (hγ : 0 < γ) (hX4 : 0 < X4) (hC12 : 0 ≤ C12)
    (hA1 : 0 ≤ A1) (hε : 0 ≤ ε) (hd : d ≤ lam * γ ^ 2)
    (hs4 : C12 * (A1 * lam * ε) / (γ ^ 4 * X4) ≤ 1 / 2) :
    C12 * (A1 * ε / γ ^ 2 * d) / (γ ^ 4 * X4) < 1 := by
  have hden : 0 < γ ^ 4 * X4 := by positivity
  have h1 : C12 * (A1 * ε / γ ^ 2 * d) / (γ ^ 4 * X4) ≤ C12 * (A1 * lam * ε) / (γ ^ 4 * X4) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (err_le hA1 hε hγ hd) hC12) hden.le
  linarith

/-- Step `step:p4:lip-g2`: the closeness of `K_{ω'}` and `K̃` is at most
`2 η₀ + d₁ ≤ c_G γ² (s/16)^{2τ}`, from (s5). Here `d₁ = C₂⁽²⁾ e' / (γ² (3s/32)^{2τ})`,
`e' = A₁ ε γ⁻² |Δω|`. -/
theorem close_arith {A0 A1 C22 lam X2 cG Y d : ℝ} (hγ : 0 < γ) (hX2 : 0 < X2)
    (hC22 : 0 ≤ C22) (hA1 : 0 ≤ A1) (hε : 0 ≤ ε) (hd : d ≤ lam * γ ^ 2)
    (hs5 : (2 * A0 + C22 * A1 * lam / X2) * (ε / γ ^ 2) ≤ cG * γ ^ 2 * Y) :
    2 * (A0 * ε / γ ^ 2) + C22 * (A1 * ε / γ ^ 2 * d) / (γ ^ 2 * X2) ≤ cG * γ ^ 2 * Y := by
  have hγ2 : 0 < γ ^ 2 := by positivity
  have hden : 0 < γ ^ 2 * X2 := by positivity
  have h1 : C22 * (A1 * ε / γ ^ 2 * d) / (γ ^ 2 * X2) ≤ C22 * (A1 * lam * ε) / (γ ^ 2 * X2) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (err_le hA1 hε hγ hd) hC22) hden.le
  have h2 : 2 * (A0 * ε / γ ^ 2) + C22 * (A1 * lam * ε) / (γ ^ 2 * X2) =
      (2 * A0 + C22 * A1 * lam / X2) * (ε / γ ^ 2) := by
    field_simp
  linarith

/-- Step `step:p4:lip-close`: `(σ_K + 1) d₁ = A₂ ε γ⁻⁴ |Δω|`, with
`A₂ = (σ_K + 1) C₂⁽²⁾ A₁ / (3s/32)^{2τ}`. -/
theorem final_arith {σK C22 A1 X2 d : ℝ} (hγ : 0 < γ) (hX2 : 0 < X2) :
    (σK + 1) * (C22 * (A1 * ε / γ ^ 2 * d) / (γ ^ 2 * X2)) =
      (σK + 1) * C22 * A1 / X2 * ε / γ ^ 4 * d := by
  field_simp

/-! ### Phase average -/

/-- The phase average is Lipschitz for the sup norm on real points:
`‖ph(K₁) - ph(K₂)‖ ≤ C` when `‖K₁(ιx) - K₂(ιx)‖ ≤ C` for all real `x`. -/
theorem norm_phaseAverage_sub_le {ρ : ℝ} (hρ : 0 < ρ)
    {K₁ K₂ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (h₁ : DifferentiableOn ℂ K₁ (complexStrip n ρ)) (h₂ : DifferentiableOn ℂ K₂ (complexStrip n ρ))
    {C : ℝ} (hC : ∀ x : Fin n → ℝ,
      ‖K₁ (fun l => (x l : ℂ)) - K₂ (fun l => (x l : ℂ))‖ ≤ C) :
    ‖phaseAverage K₁ - phaseAverage K₂‖ ≤ C := by
  refine (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hC 0))).2 fun i => ?_
  have c1 : Continuous fun x : Fin n → ℝ => (angleDisplacement K₁ (fun l => (x l : ℂ)) i).re :=
    Complex.continuous_re.comp
      ((continuous_apply i).comp (continuous_angleDisplacement_ofReal hρ h₁))
  have c2 : Continuous fun x : Fin n → ℝ => (angleDisplacement K₂ (fun l => (x l : ℂ)) i).re :=
    Complex.continuous_re.comp
      ((continuous_apply i).comp (continuous_angleDisplacement_ofReal hρ h₂))
  have hsub : (phaseAverage K₁ - phaseAverage K₂) i =
      torusAverage fun x : Fin n → ℝ => (angleDisplacement K₁ (fun l => (x l : ℂ)) i).re -
        (angleDisplacement K₂ (fun l => (x l : ℂ)) i).re := by
    simp only [Pi.sub_apply, phaseAverage, torusAverage]
    exact (integral_sub (integrableOn_unitCube_of_continuous c1)
      (integrableOn_unitCube_of_continuous c2)).symm
  rw [hsub]
  refine norm_torusAverage_le fun x _ => ?_
  have e : (angleDisplacement K₁ (fun l => (x l : ℂ)) i).re -
      (angleDisplacement K₂ (fun l => (x l : ℂ)) i).re =
      (((K₁ (fun l => (x l : ℂ)) - K₂ (fun l => (x l : ℂ))).1) i).re := by
    simp [angleDisplacement]
  rw [e]
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (norm_le_pi_norm _ i).trans ?_
  exact (norm_fst_le _).trans (hC x)

/-- Step `step:p4:lip-phase`: if `K̃(ιx) = K₁(ιx + ιφ)` at real points, `K₁` and `K'` are
normalized, `K₁` is holomorphic and primary, and `‖K̃ - K'‖ ≤ d` at real points, then `‖φ‖ ≤ d`
(`ph(K̃) = φ`). -/
theorem norm_phi_le {ρ ρ₁ : ℝ} (hρ : 0 < ρ) (hρ₁ : 0 < ρ₁)
    {K₁ K' Kt : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {φ : Fin n → ℝ}
    (hK₁ : DifferentiableOn ℂ K₁ (complexStrip n ρ₁)) (hK₁p : IsPrimaryOnStrip K₁ ρ₁)
    (hK₁n : IsNormalized K₁) (hKt : DifferentiableOn ℂ Kt (complexStrip n ρ))
    (hK' : DifferentiableOn ℂ K' (complexStrip n ρ)) (hK'n : IsNormalized K')
    (hrel : ∀ x : Fin n → ℝ,
      Kt (fun l => (x l : ℂ)) = K₁ ((fun l => (x l : ℂ)) + fun l => (φ l : ℂ)))
    {d : ℝ} (hd : ∀ x : Fin n → ℝ, ‖Kt (fun l => (x l : ℂ)) - K' (fun l => (x l : ℂ))‖ ≤ d) :
    ‖φ‖ ≤ d := by
  have h1 : phaseAverage Kt = φ := by
    have hc : phaseAverage Kt = phaseAverage (phaseShift K₁ φ) := by
      funext i
      unfold phaseAverage
      congr 1
      funext x
      simp only [angleDisplacement_apply, phaseShift_apply, hrel x]
    rw [hc, phaseAverage_phaseShift hρ₁ hK₁ hK₁p φ, hK₁n, zero_add]
  have := norm_phaseAverage_sub_le hρ hKt hK' hd
  rwa [h1, hK'n, sub_zero] at this

/-- `ph(K') = ph(K_ω)`: the shift `(0, ι ΔI)` does not change the angle displacement. -/
theorem phaseAverage_shiftedTorus {ω ω' : Fin n → ℝ} :
    phaseAverage (shiftedTorus τ s₀ r₀ B h f gc ε γ ω ω') =
      phaseAverage (normTorus τ s₀ r₀ B h f gc ε γ ω) := by
  funext i
  unfold phaseAverage
  congr 1
  funext x
  simp [angleDisplacement, shiftedTorus]

/-! ### Far pairs (`step:p4:lip-far`) -/

/-- Step `step:p4:lip-far`: if `|Δω| > λ_* γ²`, then `|W_{ω'} - W_ω| ≤ 2 η₀ ≤ A₃ ε γ⁻⁴ |Δω|`. -/
theorem far_case (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    (hgc : GValid τ s₀ r₀ B h Lh gc) (hSA : SA τ s₀ r₀ B h Lh gc ε γ) {ω ω' : Fin n → ℝ}
    (hω : ω ∈ OmegaGamma h B τ γ) (hω' : ω' ∈ OmegaGamma h B τ γ)
    (hfar : lamStar Lh s₀ r₀ * γ ^ 2 < ‖ω' - ω‖) :
    ∀ θ ∈ complexStrip n (stripWidth s₀ / 32),
      ‖normDisp τ s₀ r₀ B h f gc ε γ ω' θ - normDisp τ s₀ r₀ B h f gc ε γ ω θ‖ ≤
        A3 τ s₀ r₀ B h Lh gc * ε / γ ^ 4 * ‖ω' - ω‖ := by
  intro θ hθ
  have hs₀ := hD.s₀_pos
  have hr₀ := hD.r₀_pos
  have hθ8 : θ ∈ complexStrip n (stripWidth s₀ / 8) :=
    complexStrip_mono (by have := stripWidth_pos hs₀; linarith) hθ
  have hW := (normalize hD hP hgc hSA hω).2.2.2.2.2.2.2 θ hθ8
  have hW' := (normalize hD hP hgc hSA hω').2.2.2.2.2.2.2 θ hθ8
  have hA0 : 0 < A0 n τ s₀ r₀ gc := Parameters.A0_pos hs₀ hr₀ hgc.toPos
  have hlam := Parameters.lamStar_pos (Lh := Lh) hs₀ hr₀
  have hA3 : 2 * A0 n τ s₀ r₀ gc / lamStar Lh s₀ r₀ ≤ A3 τ s₀ r₀ B h Lh gc := le_max_right _ _
  have hfin := far_arith hA0.le hlam hSA.gamma_pos hSA.eps_nonneg hfar hA3
  have hη : eta0 n τ s₀ r₀ gc ε γ = A0 n τ s₀ r₀ gc * ε / γ ^ 2 := rfl
  calc _ ≤ ‖normDisp τ s₀ r₀ B h f gc ε γ ω' θ‖ + ‖normDisp τ s₀ r₀ B h f gc ε γ ω θ‖ :=
        norm_sub_le _ _
    _ ≤ eta0 n τ s₀ r₀ gc ε γ + eta0 n τ s₀ r₀ gc ε γ := add_le_add hW' hW
    _ = 2 * (A0 n τ s₀ r₀ gc * ε / γ ^ 2) := by rw [hη]; ring
    _ ≤ _ := hfin

/-! ### Close pairs: the second application of G1 (`step:p4:lip-g1`) -/

/-- Step `step:p4:lip-g1`: the frozen G1 at the second tuple `(ρ, ρ_∞) = (3s/32, s/16)`, at the
shifted torus `K'` and the frequency `ω'`. -/
theorem g1_step (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    (hgc : GValid τ s₀ r₀ B h Lh gc) (hSA : SA τ s₀ r₀ B h Lh gc ε γ) {ω ω' : Fin n → ℝ}
    (hω : ω ∈ OmegaGamma h B τ γ) (hω' : ω' ∈ OmegaGamma h B τ γ)
    (hclose : ‖ω' - ω‖ ≤ lamStar Lh s₀ r₀ * γ ^ 2) :
    ∃ Kt : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ),
      DifferentiableOn ℂ Kt (complexStrip n (stripWidth s₀ / 16)) ∧
      IsPrimaryOnStrip Kt (stripWidth s₀ / 16) ∧ IsRealOnReals Kt ∧
      (∀ θ ∈ complexStrip n (stripWidth s₀ / 16),
        invarianceError (hbold h f) Kt ω' θ = 0) ∧
      (∀ θ ∈ complexStrip n (stripWidth s₀ / 16),
        Metric.ball (Kt θ) (muParam s₀ r₀ / 2) ⊆ domainD n s₀ r₀ B) ∧
      (∀ θ ∈ complexStrip n (stripWidth s₀ / 16),
        ‖fderiv ℂ Kt θ‖ ≤ sigmaK s₀ r₀ - muParam s₀ r₀ / 2) ∧
      ∀ θ ∈ complexStrip n (stripWidth s₀ / 16),
        ‖Kt θ - shiftedTorus τ s₀ r₀ B h f gc ε γ ω ω' θ‖ ≤
          gc.C22 * (A1 τ s₀ r₀ B h Lh gc * ε / γ ^ 2 * ‖ω' - ω‖) /
            (γ ^ 2 * (3 * stripWidth s₀ / 32) ^ (2 * τ)) := by
  have hs := stripWidth_pos hD.s₀_pos
  have hS := smallness hD hgc.toPos hSA
  obtain ⟨⟨hε1, hεF⟩, -, ⟨hη32, -, -, -⟩, hs4, -⟩ := hS
  obtain ⟨hIB', -, hWinf'⟩ := (inverse_freq hD).2.2.1 ω' hω'.1
  obtain ⟨hLd, hLp, hLr, -, hLclose, hLerr⟩ := lip_error hD hP hgc hSA hω hω' hclose
  have H := (stab hD hP hε1 hεF hIB' hWinf' (δ := stripWidth s₀ / 32) (ρ := stripWidth s₀ / 8)
    (η := eta0 n τ s₀ r₀ gc ε γ) (by positivity) (by linarith) (by linarith) hLd hLclose
    hη32).2.2 hLp hLr
  rw [show stripWidth s₀ / 8 - stripWidth s₀ / 32 = 3 * stripWidth s₀ / 32 by ring] at H
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := h1 hD hP hε1
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := H
  have hsmall : gc.C12 * (A1 τ s₀ r₀ B h Lh gc * ε / γ ^ 2 * ‖ω' - ω‖) /
      (γ ^ 4 * (3 * stripWidth s₀ / 32) ^ (4 * τ)) < 1 :=
    g1_small hSA.gamma_pos (Real.rpow_pos_of_pos (by positivity) _) hgc.toPos.C12_pos.le
      (Parameters.A1_pos hD.s₀_pos hD.r₀_pos hgc.toPos).le hSA.eps_nonneg hclose
      (by simpa only [mul_assoc] using hs4)
  obtain ⟨Kt, c1, c2, c3, c4, c5, c6, c7⟩ := hgc.g1b _ _
    (shiftedTorus τ s₀ r₀ B h f gc ε γ ω ω') ω' γ
    (A1 τ s₀ r₀ B h Lh gc * ε / γ ^ 2 * ‖ω' - ω‖) o1 o2 o3 o4 o5 o6 k1 k2 k3 k4 k5 k6 k7 k8
    hSA.gamma_pos hSA.gamma_le hω'.2 hLerr hsmall
  exact ⟨Kt, c1, c2, c3, c4, c5, c6, c7⟩

/-! ### Close pairs: local uniqueness (`step:p4:lip-g2`) -/

/-- Step `step:p4:lip-g2`: the frozen G2 at `ρ = s/16`, with reference torus `K_{ω'}` and second
torus the output `K̃` of G1. It gives a phase `φ ∈ ℝⁿ` with `K̃(θ) = K_{ω'}(θ + ι φ)` on
`T_{s/32}`. -/
theorem g2_step (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    (hgc : GValid τ s₀ r₀ B h Lh gc) (hSA : SA τ s₀ r₀ B h Lh gc ε γ) {ω ω' : Fin n → ℝ}
    (hω : ω ∈ OmegaGamma h B τ γ) (hω' : ω' ∈ OmegaGamma h B τ γ)
    (hclose : ‖ω' - ω‖ ≤ lamStar Lh s₀ r₀ * γ ^ 2)
    {Kt : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hKd : DifferentiableOn ℂ Kt (complexStrip n (stripWidth s₀ / 16)))
    (hKp : IsPrimaryOnStrip Kt (stripWidth s₀ / 16)) (hKr : IsRealOnReals Kt)
    (hKE : ∀ θ ∈ complexStrip n (stripWidth s₀ / 16), invarianceError (hbold h f) Kt ω' θ = 0)
    (hKball : ∀ θ ∈ complexStrip n (stripWidth s₀ / 16),
      Metric.ball (Kt θ) (muParam s₀ r₀ / 2) ⊆ domainD n s₀ r₀ B)
    (hKclose : ∀ θ ∈ complexStrip n (stripWidth s₀ / 16),
      ‖Kt θ - shiftedTorus τ s₀ r₀ B h f gc ε γ ω ω' θ‖ ≤
        gc.C22 * (A1 τ s₀ r₀ B h Lh gc * ε / γ ^ 2 * ‖ω' - ω‖) /
          (γ ^ 2 * (3 * stripWidth s₀ / 32) ^ (2 * τ))) :
    ∃ φ : Fin n → ℝ, ∀ θ ∈ complexStrip n (stripWidth s₀ / 32),
      Kt θ = normTorus τ s₀ r₀ B h f gc ε γ ω' (θ + fun i => (φ i : ℂ)) := by
  have hs := stripWidth_pos hD.s₀_pos
  have hr₀ := hD.r₀_pos
  have hS := smallness hD hgc.toPos hSA
  obtain ⟨⟨hε1, hεF⟩, -, ⟨hη32, hη3216, -, -⟩, -, hs5, -⟩ := hS
  obtain ⟨hIB', -, hWinf'⟩ := (inverse_freq hD).2.2.1 ω' hω'.1
  obtain ⟨-, -, -, -, hLclose, -⟩ := lip_error hD hP hgc hSA hω hω' hclose
  obtain ⟨hNd, hNp, hNr, hNE, -, -, -, hNW⟩ := normalize hD hP hgc hSA hω'
  have hη16 : eta0 n τ s₀ r₀ gc ε γ ≤ etaStar s₀ r₀ B h Lh (stripWidth s₀ / 16) :=
    hη32.trans hη3216
  have H := (stab hD hP hε1 hεF hIB' hWinf' (δ := stripWidth s₀ / 16) (ρ := stripWidth s₀ / 8)
    (η := eta0 n τ s₀ r₀ gc ε γ) (by positivity) (by linarith) (by linarith) hNd
    (fun θ hθ => hNW θ hθ) hη16).2.2 hNp hNr
  rw [show stripWidth s₀ / 8 - stripWidth s₀ / 16 = stripWidth s₀ / 16 by ring] at H
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := h1 hD hP hε1
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := H
  have hsub : complexStrip n (stripWidth s₀ / 16) ⊆ complexStrip n (stripWidth s₀ / 8) :=
    complexStrip_mono (by linarith)
  have hcl : ∀ θ ∈ complexStrip n (stripWidth s₀ / 16),
      ‖normTorus τ s₀ r₀ B h f gc ε γ ω' θ - Kt θ‖ ≤
        gc.cG * γ ^ 2 * (stripWidth s₀ / 16) ^ (2 * τ) := by
    intro θ hθ
    have hX2 : 0 < (3 * stripWidth s₀ / 32) ^ (2 * τ) := Real.rpow_pos_of_pos (by positivity) _
    have hA := close_arith (A0 := A0 n τ s₀ r₀ gc) (A1 := A1 τ s₀ r₀ B h Lh gc)
      (C22 := gc.C22) (lam := lamStar Lh s₀ r₀) (cG := gc.cG)
      (Y := (stripWidth s₀ / 16) ^ (2 * τ)) hSA.gamma_pos hX2 hgc.toPos.C22_pos.le
      (Parameters.A1_pos hD.s₀_pos hr₀ hgc.toPos).le hSA.eps_nonneg hclose hs5
    have e : normTorus τ s₀ r₀ B h f gc ε γ ω' θ - Kt θ =
        normDisp τ s₀ r₀ B h f gc ε γ ω' θ -
          (shiftedTorus τ s₀ r₀ B h f gc ε γ ω ω' θ -
            unperturbedTorus (invFreq h B ω') θ) +
        (shiftedTorus τ s₀ r₀ B h f gc ε γ ω ω' θ - Kt θ) := by
      simp only [normDisp]; abel
    have h1' := hNW θ (hsub hθ)
    have h2' := hLclose θ (hsub hθ)
    have h3' := hKclose θ hθ
    have h4' : ‖normDisp τ s₀ r₀ B h f gc ε γ ω' θ -
        (shiftedTorus τ s₀ r₀ B h f gc ε γ ω ω' θ - unperturbedTorus (invFreq h B ω') θ)‖ ≤
        eta0 n τ s₀ r₀ gc ε γ + eta0 n τ s₀ r₀ gc ε γ :=
      (norm_sub_le _ _).trans (add_le_add h1' h2')
    have h5' : ‖shiftedTorus τ s₀ r₀ B h f gc ε γ ω ω' θ - Kt θ‖ ≤
        gc.C22 * (A1 τ s₀ r₀ B h Lh gc * ε / γ ^ 2 * ‖ω' - ω‖) /
          (γ ^ 2 * (3 * stripWidth s₀ / 32) ^ (2 * τ)) := by
      rw [norm_sub_rev]; exact h3'
    have hη2 : eta0 n τ s₀ r₀ gc ε γ + eta0 n τ s₀ r₀ gc ε γ =
        2 * (A0 n τ s₀ r₀ gc * ε / γ ^ 2) := by
      unfold eta0; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    linarith
  obtain ⟨φ, hφ⟩ := hgc.g2 _ _ (normTorus τ s₀ r₀ B h f gc ε γ ω') Kt ω' γ o1 o2 o3 o4 o5 o6
    k1 k2 k3 k4 k5 k6 k7 k8 hSA.gamma_pos hω'.2 (fun θ hθ => hNE θ (hsub hθ)) hKd hKp hKr
    (fun θ hθ => hKball θ hθ (Metric.mem_ball_self (muParam_pos hD.s₀_pos hr₀ |> half_pos)))
    hKE hcl
  refine ⟨φ, fun θ hθ => ?_⟩
  have hd := hφ θ (by rw [show stripWidth s₀ / 16 / 2 = stripWidth s₀ / 32 by ring]; exact hθ)
  exact hd

/-! ### Close pairs: phase and conclusion (`step:p4:lip-phase`, `step:p4:lip-close`) -/

/-- `‖ι φ‖ = ‖φ‖` up to `≤`: the real vector `φ` viewed in `ℂⁿ` has the same sup norm. -/
theorem norm_ofReal_vec_le (φ : Fin n → ℝ) : ‖fun i => (φ i : ℂ)‖ ≤ ‖φ‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by
    simpa using norm_le_pi_norm φ i

/-- Steps `step:p4:lip-phase` and `step:p4:lip-close`: for a close pair,
`|W_{ω'} - W_ω| ≤ (σ_K + 1) d₁ = A₂ ε γ⁻⁴ |Δω| ≤ A₃ ε γ⁻⁴ |Δω|` on `T_{s/32}`. -/
theorem close_case (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    (hgc : GValid τ s₀ r₀ B h Lh gc) (hSA : SA τ s₀ r₀ B h Lh gc ε γ) {ω ω' : Fin n → ℝ}
    (hω : ω ∈ OmegaGamma h B τ γ) (hω' : ω' ∈ OmegaGamma h B τ γ)
    (hclose : ‖ω' - ω‖ ≤ lamStar Lh s₀ r₀ * γ ^ 2) :
    ∀ θ ∈ complexStrip n (stripWidth s₀ / 32),
      ‖normDisp τ s₀ r₀ B h f gc ε γ ω' θ - normDisp τ s₀ r₀ B h f gc ε γ ω θ‖ ≤
        A3 τ s₀ r₀ B h Lh gc * ε / γ ^ 4 * ‖ω' - ω‖ := by
  have hs := stripWidth_pos hD.s₀_pos
  have hr₀ := hD.r₀_pos
  obtain ⟨Kt, hKd, hKp, hKr, hKE, hKball, hKL, hKclose⟩ :=
    g1_step hD hP hgc hSA hω hω' hclose
  obtain ⟨φ, hφ⟩ := g2_step hD hP hgc hSA hω hω' hclose hKd hKp hKr hKE hKball hKclose
  obtain ⟨hLd, -, -, hLdisp, -, -⟩ := lip_error hD hP hgc hSA hω hω' hclose
  obtain ⟨hNd, hNp, -, -, hNn, -⟩ := normalize hD hP hgc hSA hω'
  obtain ⟨-, -, -, -, hNn0, -⟩ := normalize hD hP hgc hSA hω
  set d1 : ℝ := gc.C22 * (A1 τ s₀ r₀ B h Lh gc * ε / γ ^ 2 * ‖ω' - ω‖) /
    (γ ^ 2 * (3 * stripWidth s₀ / 32) ^ (2 * τ)) with hd1
  have h16 : (0 : ℝ) < stripWidth s₀ / 16 := by positivity
  have h32 : (0 : ℝ) < stripWidth s₀ / 32 := by positivity
  have h8 : (0 : ℝ) < stripWidth s₀ / 8 := by positivity
  have hsub16 : complexStrip n (stripWidth s₀ / 16) ⊆ complexStrip n (stripWidth s₀ / 8) :=
    complexStrip_mono (by linarith)
  have hsub32 : complexStrip n (stripWidth s₀ / 32) ⊆ complexStrip n (stripWidth s₀ / 16) :=
    complexStrip_mono (by linarith)
  -- the phase
  have hφd : ‖φ‖ ≤ d1 :=
    norm_phi_le (K' := shiftedTorus τ s₀ r₀ B h f gc ε γ ω ω') h16 h8 hNd hNp hNn hKd
      (hLd.mono hsub16) (by rw [IsNormalized, phaseAverage_shiftedTorus]; exact hNn0)
      (fun x => hφ _ (ofReal_mem_complexStrip h32 x))
      (fun x => hKclose _ (ofReal_mem_complexStrip h16 x))
  intro θ hθ
  have hθ16 := hsub32 hθ
  have hθφ : θ - (fun i => (φ i : ℂ)) ∈ complexStrip n (stripWidth s₀ / 32) := by
    intro i
    simpa using hθ i
  -- the difference of the displacements is `K_{ω'} - K'`
  have hW : normDisp τ s₀ r₀ B h f gc ε γ ω' θ - normDisp τ s₀ r₀ B h f gc ε γ ω θ =
      normTorus τ s₀ r₀ B h f gc ε γ ω' θ -
        shiftedTorus τ s₀ r₀ B h f gc ε γ ω ω' θ := by
    rw [← hLdisp θ]
    simp only [normDisp]
    abel
  have hKθ : normTorus τ s₀ r₀ B h f gc ε γ ω' θ = Kt (θ - fun i => (φ i : ℂ)) := by
    rw [hφ _ hθφ, sub_add_cancel]
  -- the increment of `K̃` along the real segment
  have hinc : ‖Kt θ - Kt (θ - fun i => (φ i : ℂ))‖ ≤ sigmaK s₀ r₀ * ‖φ‖ := by
    have hB : ∀ x ∈ complexStrip n (stripWidth s₀ / 16 - stripWidth s₀ / 32),
        ‖fderiv ℂ Kt x‖ ≤ sigmaK s₀ r₀ := by
      intro x hx
      rw [show stripWidth s₀ / 16 - stripWidth s₀ / 32 = stripWidth s₀ / 32 by ring] at hx
      have := hKL x (hsub32 hx)
      have hμ := muParam_pos hD.s₀_pos hr₀
      linarith
    have := increments_mvt hKd (δ := stripWidth s₀ / 32) h32 hB
      (θ := θ - fun i => (φ i : ℂ)) (v := fun i => (φ i : ℂ))
      (by rw [show stripWidth s₀ / 16 - stripWidth s₀ / 32 = stripWidth s₀ / 32 by ring]; exact hθφ)
      (by
        rw [show stripWidth s₀ / 16 - stripWidth s₀ / 32 = stripWidth s₀ / 32 by ring,
          sub_add_cancel]; exact hθ)
    rw [sub_add_cancel] at this
    exact this.trans (mul_le_mul_of_nonneg_left (norm_ofReal_vec_le φ) (by
      have := Parameters.sigmaK_pos (s₀ := s₀) (r₀ := r₀) hD.s₀_pos hr₀
      linarith))
  have hσ := Parameters.sigmaK_pos (s₀ := s₀) (r₀ := r₀) hD.s₀_pos hr₀
  have hd1' := hKclose θ hθ16
  have hX2 : 0 < (3 * stripWidth s₀ / 32) ^ (2 * τ) := Real.rpow_pos_of_pos (by positivity) _
  have hA23 : A2 τ s₀ r₀ B h Lh gc ≤ A3 τ s₀ r₀ B h Lh gc := le_max_left _ _
  have hfinal := final_arith (σK := sigmaK s₀ r₀) (C22 := gc.C22)
    (A1 := A1 τ s₀ r₀ B h Lh gc) (d := ‖ω' - ω‖) hSA.gamma_pos hX2 (ε := ε)
  rw [hW, hKθ]
  calc ‖Kt (θ - fun i => (φ i : ℂ)) - shiftedTorus τ s₀ r₀ B h f gc ε γ ω ω' θ‖
      = ‖(Kt (θ - fun i => (φ i : ℂ)) - Kt θ) +
          (Kt θ - shiftedTorus τ s₀ r₀ B h f gc ε γ ω ω' θ)‖ := by
        congr 1; abel
    _ ≤ ‖Kt (θ - fun i => (φ i : ℂ)) - Kt θ‖ +
          ‖Kt θ - shiftedTorus τ s₀ r₀ B h f gc ε γ ω ω' θ‖ := norm_add_le _ _
    _ ≤ sigmaK s₀ r₀ * ‖φ‖ + d1 := by
        rw [norm_sub_rev (Kt (θ - fun i => (φ i : ℂ))) (Kt θ)]
        exact add_le_add hinc hd1'
    _ ≤ sigmaK s₀ r₀ * d1 + d1 := by
        have := mul_le_mul_of_nonneg_left hφd hσ.le
        linarith
    _ = (sigmaK s₀ r₀ + 1) * d1 := by ring
    _ = A2 τ s₀ r₀ B h Lh gc * ε / γ ^ 4 * ‖ω' - ω‖ := by
        rw [hd1]; exact hfinal
    _ ≤ A3 τ s₀ r₀ B h Lh gc * ε / γ ^ 4 * ‖ω' - ω‖ := by
        have hγ4 : 0 < γ ^ 4 := pow_pos hSA.gamma_pos 4
        have hε := hSA.eps_nonneg
        gcongr

end Lip

variable {n : ℕ} {τ s₀ r₀ Lh : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}
  {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε γ : ℝ} {gc : GConsts}

/-- Blueprint `bp:p4:lip` (LIP). -/
theorem lip (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    (hgc : GValid τ s₀ r₀ B h Lh gc) (hSA : SA τ s₀ r₀ B h Lh gc ε γ) :
    ∀ ω ∈ OmegaGamma h B τ γ, ∀ ω' ∈ OmegaGamma h B τ γ,
      ∀ θ ∈ complexStrip n (stripWidth s₀ / 32),
        ‖normDisp τ s₀ r₀ B h f gc ε γ ω' θ - normDisp τ s₀ r₀ B h f gc ε γ ω θ‖ ≤
          A3 τ s₀ r₀ B h Lh gc * ε / γ ^ 4 * ‖ω' - ω‖ := by
  intro ω hω ω' hω'
  by_cases hfar : lamStar Lh s₀ r₀ * γ ^ 2 < ‖ω' - ω‖
  · exact Lip.far_case hD hP hgc hSA hω hω' hfar
  · exact Lip.close_case hD hP hgc hSA hω hω' (not_lt.1 hfar)

end KAM.Head

end
