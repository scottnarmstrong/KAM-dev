/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.Defs
import KAM.Head.H1
import KAM.Head.InverseFrequency
import KAM.Head.Parameters
import KAM.Head.Unperturbed
public import KAM.Matrix.Norms

/-!
# APPLY: a torus for every Diophantine frequency

Blueprint Part 4, `bp:p4:apply`. Under the standing assumption
`(SA)` and for `ω ∈ Ω_γ = ∇h(B) ∩ Dio_{γ,τ}`, the frozen G1 is applied at the first tuple of
Definition `bp:p4:parameters`, `(ρ, ρ_∞) = (s/4, s/8)`, at the unperturbed torus `K⁰_{I_ω}`.
G1 enters only through the premise `GValid.g1a`. The conclusion clauses are the predicate
`KAM.Head.IsApplyTorus`.

The proof is step `step:p4:apply-g1`, one frozen hypothesis at a time.

* H1: `KAM.Head.h1` with `ε ≤ 1` from `(s1)` of `KAM.Head.smallness`.
* H2: `KAM.Head.unperturbed` (a), and (g) with `μ = δ_*/2 < δ_*`; `‖DK⁰‖ = 1 ≤ 2 = σ_K - μ`.
* H3: `KAM.Head.unperturbed` (b); the row sums of `G⁻¹ = Id` are `1 ≤ 2 = σ_B - μ`.
* H4: `KAM.Head.unperturbed` (e) with `(s1)`; the operator-norm bound `2 L₊` becomes the
  row-sum bound `4 L₊ = σ_T - μ` by `KAM.norm_le_iff_forall_rowSum`.
* H5: the hypotheses `0 < γ ≤ 1` and `ω ∈ Dio_{γ,τ}`.
* Error: `KAM.Head.unperturbed` (f) at `I_* = I_ω`, `∇h(I_ω) = ω`
  (`KAM.Head.inverse_freq`), and `(s2)`.

The output bound is `C₂⁽¹⁾ F₁ ε / (γ² (s/4)^{2τ}) = η₀ / 2`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.Head

variable {n : ℕ} {τ s₀ r₀ Lh : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}
  {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε γ : ℝ} {gc : GConsts}

/-! ### Small arithmetic facts used by the G1 call -/

/-- `μ ≤ δ_*`: the balls of radius `μ` lie in the balls of radius `δ_*` of `unperturbed` (g). -/
theorem muParam_le_deltaStar (hs₀ : 0 < s₀) (hr₀ : 0 < r₀) :
    muParam s₀ r₀ ≤ deltaStar s₀ r₀ := by
  have := deltaStar_pos hs₀ hr₀
  unfold muParam
  linarith

/-- The G1 closeness bound is half of `η₀`: `C₂⁽¹⁾ F₁ ε / (γ² (s/4)^{2τ}) = η₀ / 2`. -/
theorem apply_closeness_eq :
    gc.C21 * (Fconst n s₀ r₀ 1 * ε) / (γ ^ 2 * (stripWidth s₀ / 4) ^ (2 * τ)) =
      eta0 n τ s₀ r₀ gc ε γ / 2 := by
  unfold eta0 A0
  ring

/-- A row-sum bound from an operator-norm bound, for the targets `σ - μ`. -/
theorem rowSum_le_of_norm_le {p : ℕ} {M : Matrix (Fin p) (Fin p) ℂ} {b c : ℝ} (hb : b ≤ c)
    (hM : ‖M‖ ≤ b) (hb0 : 0 ≤ b) : ∀ i, ∑ j, ‖M i j‖ ≤ c :=
  (norm_le_iff_forall_rowSum (hb0.trans hb)).1 (hM.trans hb)

/-! ### The node -/

/-- Blueprint `bp:p4:apply` (APPLY). -/
theorem apply (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    (hgc : GValid τ s₀ r₀ B h Lh gc) (hSA : SA τ s₀ r₀ B h Lh gc ε γ) {ω : Fin n → ℝ}
    (hω : ω ∈ OmegaGamma h B τ γ) :
    ∃ K, IsApplyTorus τ s₀ r₀ B h f gc ε γ ω K := by
  obtain ⟨hωB, hdio⟩ := hω
  have hS := smallness hD hgc.toPos hSA
  obtain ⟨hI, hfreq, -⟩ := (inverse_freq hD).2.2.1 ω hωB
  have hpar := (parameters hD).2.1
  have hμδ := muParam_le_deltaStar hD.s₀_pos hD.r₀_pos
  have hL := one_le_Lplus Lh
  obtain ⟨ho, hi, hd, hp, hr, hb⟩ := h1 hD hP hS.1.1
  obtain ⟨⟨hKd, hKp, hKr, hKL⟩, hG, -, -, -, -, -, -, hTw, hE, hball⟩ :=
    unperturbed hD hP hS.1.1 hI ω
  obtain ⟨hTu, hTn⟩ := hTw hS.1.2
  have hstrip : complexStrip n (stripWidth s₀ / 4) ⊆ complexStrip n (stripWidth s₀ / 2) :=
    complexStrip_mono (by linarith [stripWidth_pos hD.s₀_pos])
  obtain ⟨Kinf, k1, k2, k3, k4, k5, k6, k7⟩ := hgc.g1a (domainD n s₀ r₀ B) (hbold h f)
    (unperturbedTorus (invFreq h B ω)) ω γ (Fconst n s₀ r₀ 1 * ε) ho hi hd hp hr hb
    hKd.differentiableOn (hKp _) hKr
    (fun θ hθ => (Metric.ball_subset_ball hμδ).trans (hball θ hθ))
    (fun θ _ => by rw [hpar.1, (hKL θ).2]; norm_num)
    (fun θ _ => ⟨(hG θ).2.1, rowSum_le_of_norm_le (b := 1) (by rw [hpar.2.1]; norm_num)
      (le_of_eq (hG θ).2.2) zero_le_one⟩)
    hTu
    (rowSum_le_of_norm_le (b := 2 * Lplus Lh) (by rw [hpar.2.2]; linarith) hTn
      (by linarith))
    hSA.gamma_pos hSA.gamma_le hdio
    (fun θ hθ => (hE hfreq.symm θ (hstrip hθ)).2)
    (hS.2.1.trans_lt (by norm_num))
  refine ⟨Kinf, k1, k2, k3, k4, k5, k6, fun θ hθ => ?_⟩
  exact (k7 θ hθ).trans (le_of_eq apply_closeness_eq)

end KAM.Head

end
