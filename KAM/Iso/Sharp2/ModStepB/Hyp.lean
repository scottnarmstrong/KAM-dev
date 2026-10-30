/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.ModStepB.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The hypotheses of the bordered modified step, bundled

`ModStepB.Hyp` collects the hypotheses of `KAM.Iso.Sharp2.modified_stepIB`, as
`KAM.Sharp2.ModStepB.Hyp` does for `modified_stepB`: the bordered average `⟨𝖳⟩` replaces `⟨T⟩`
(which may be singular), and the bound of `Y`, of `ω` and of `D²H` and the energy error are added.
This is why the fixed-frequency lemmas, stated under their `Hyp` (with an invertible `⟨T⟩`), are not
applied here but repeated in this namespace, generic lemmas excepted.

The weighted error is `μ = mu p γ εL εN δ`, the two-term maximum of `KAM.Sharp2.ModStepB.mu`: the
step is applied with `εL = λ μ`, `εN = γ δ^κ μ` for the three-term maximum of `bpI:p2s2:step`, and
the energy error is `|E^ω| ≤ λ_ω μ` (`Hyp.ηω`).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Iso.Sharp2

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Iso.Linear KAM.Iso.Apost
open KAM.Sharp2.ModStepB (mu xX)

variable {n : ℕ}

namespace ModStepB

/-- The hypotheses of the bordered modified step (`bpI:p2s2:step`). -/
structure Hyp (p : StepInB) (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (E₀ : ℝ) (Ω : Set (Fin n → ℝ)) (γ β εL εN δ r s c' b cb : ℝ)
    (m : Fin 5 → ℝ) :
    Prop where
  ok : p.Ok
  pn : p.n = n
  iso : p.iso = true
  γ_pos : 0 < γ
  γ_le : γ ≤ p.γb
  δ_pos : 0 < δ
  δ_le : δ ≤ p.δ
  three : 3 * δ < r
  mem : ω ∈ Ω
  cert : SDConst n p.κ γ δ p.c Ω
  s_pos : 0 < s
  s_lt : s < 1
  cert' : SDConst n p.κ γ (s * δ) c' Ω
  c1_le : c' / (s ^ p.κ * (1 - s)) ≤ p.c1
  b_ge : δ ≤ b
  b_le : b ≤ r
  certb : SDConst n p.κ γ b cb Ω
  cavg_le : cb * (δ / b) ^ p.κ ≤ p.cavg
  std : ∃ τ M γ₀ : ℝ, Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ₀
  dX : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ p.M1
  d2X : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ p.M2
  comm : ∀ z ∈ 𝔅, ‖hamComm h z‖ ≤ p.cTh
  lip : ∀ z ∈ 𝔅, ∀ z' ∈ 𝔅, segment ℝ z z' ⊆ 𝔅 →
    ‖hamComm h z - hamComm h z'‖ ≤ p.cDTh * ‖z - z'‖
  holo : DifferentiableOn ℂ K (complexStrip n r)
  primary : IsPrimaryOnStrip K r
  real : IsRealOnReals K
  ball : ∀ θ ∈ complexStrip n r, Metric.ball (K θ) β ⊆ 𝔅
  L : ∀ θ ∈ complexStrip n r, ‖tangentMat K θ‖ ≤ m 0
  Lt : ∀ θ ∈ complexStrip n r, ‖(tangentMat K θ)ᵀ‖ ≤ m 1
  G : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ m 2
  N : ∀ θ ∈ complexStrip n r, ‖normalMat K θ‖ ≤ m 3
  Nt : ∀ θ ∈ complexStrip n r, ‖(normalMat K θ)ᵀ‖ ≤ m 4
  T : ∀ θ ∈ complexStrip n (r - δ), ‖torsion h K ω θ‖ ≤ p.cTh * p.sNt * p.sN + p.ts
  Ta : IsUnit (bordAvg ω (isoBordData h K ω E₀)).det ∧
    ‖(bordAvg ω (isoBordData h K ω E₀))⁻¹‖ ≤ p.sT
  Y : ∀ θ ∈ complexStrip n (r - δ), ∑ b, ‖energyRow h K θ b‖ ≤ p.y0
  Θ : ‖ω‖ ≤ p.Θ
  dH : ∃ A : ℝ, ∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ A
  d2H : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 h z‖ ≤ p.Mh2
  ηω : ‖KAM.Iso.energyAverage h K - (E₀ : ℂ)‖ ≤ p.lamW * mu p γ εL εN δ
  ηL : ∀ θ ∈ complexStrip n r, ‖etaL h K ω θ‖ ≤ εL
  ηN : ∀ θ ∈ complexStrip n r, ‖etaN h K ω θ‖ ≤ εN
  E0 : p.stage0 = true →
    ∀ θ ∈ complexStrip n r, ‖invarianceError h K ω θ‖ ≤ p.ePer * mu p γ εL εN δ
  cond : stepCondB p (xX p γ εL εN δ)
  β_gt : (stepConstsB p).CDK * mu p γ εL εN δ / (γ * δ ^ p.κ) < β
  room : m 0 + p.n * (stepConstsB p).CDK * xX p γ εL εN δ ≤ p.sK ∧
    m 1 + 2 * p.n * (stepConstsB p).CDK * xX p γ εL εN δ ≤ p.sLt ∧
    m 2 + (stepConstsB p).CBb * xX p γ εL εN δ ≤ p.sB ∧
    m 3 + (stepConstsB p).CNb * xX p γ εL εN δ ≤ p.sN ∧
    m 4 + (stepConstsB p).CNbT * xX p γ εL εN δ ≤ p.sNt

namespace Hyp

variable {p : StepInB} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {Ω : Set (Fin n → ℝ)}
  {E₀ γ β εL εN δ r s c' b cb : ℝ} {m : Fin 5 → ℝ}
  (H : Hyp p 𝔅 h K ω E₀ Ω γ β εL εN δ r s c' b cb m)
include H

/-! ### Strips and dimensions -/

theorem n_pos : 0 < n := by have := H.ok.one_le_n; rw [H.pn] at this; omega

theorem one_le_n : (1 : ℝ) ≤ n := by exact_mod_cast H.n_pos

theorem pn_real : (p.n : ℝ) = n := by rw [H.pn]

theorem r_pos : 0 < r := by linarith [H.δ_pos, H.three]

theorem δ_lt_r : δ < r := by linarith [H.δ_pos, H.three]

theorem r1_pos : 0 < r - δ := by linarith [H.δ_pos, H.three]

theorem r2_pos : 0 < r - 2 * δ := by linarith [H.δ_pos, H.three]

theorem r3_pos : 0 < r - 3 * δ := by linarith [H.δ_pos, H.three]

theorem δ_lt_r1 : δ < r - δ := by linarith [H.δ_pos, H.three]

theorem δ_le_one : δ ≤ 1 := H.δ_le.trans H.ok.δ_le

omit H in
theorem strip_sub {a b' : ℝ} (hab : a ≤ b') : complexStrip n a ⊆ complexStrip n b' :=
  Triangular.strip_mono hab

theorem zero_mem : (0 : Fin n → ℂ) ∈ complexStrip n r := fun i => by simpa using H.r_pos

/-! ### Signs of the data -/

theorem β_pos : 0 < β := by
  have h0 := H.ηL 0 H.zero_mem
  have h1 := H.ηN 0 H.zero_mem
  have hl := H.ok.lam.1
  have hgd : 0 < γ * δ ^ p.κ := mul_pos H.γ_pos (Real.rpow_pos_of_pos H.δ_pos _)
  have hμ : 0 ≤ mu p γ εL εN δ :=
    le_max_of_le_left (div_nonneg ((norm_nonneg _).trans h0) hl.le)
  have hC := (stepConstsB_nonneg H.ok).2.1
  exact lt_of_le_of_lt (div_nonneg (mul_nonneg hC hμ) hgd.le) H.β_gt

theorem K_mem : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅 := fun θ hθ =>
  H.ball θ hθ (Metric.mem_ball_self H.β_pos)

theorem εL_nonneg : 0 ≤ εL := (norm_nonneg _).trans (H.ηL 0 H.zero_mem)

theorem εN_nonneg : 0 ≤ εN := (norm_nonneg _).trans (H.ηN 0 H.zero_mem)

theorem gd_pos : 0 < γ * δ ^ p.κ := mul_pos H.γ_pos (Real.rpow_pos_of_pos H.δ_pos _)

theorem gd1_pos : 0 < γ * δ ^ (p.κ + 1) := mul_pos H.γ_pos (Real.rpow_pos_of_pos H.δ_pos _)

theorem mu_nonneg : 0 ≤ mu p γ εL εN δ :=
  le_max_of_le_left (div_nonneg H.εL_nonneg H.ok.lam.1.le)

theorem X_nonneg : 0 ≤ xX p γ εL εN δ := div_nonneg H.mu_nonneg H.gd1_pos.le

theorem εL_le : εL ≤ p.lam * mu p γ εL εN δ := by
  have hl := H.ok.lam.1
  have : εL / p.lam ≤ mu p γ εL εN δ := le_max_left _ _
  rw [div_le_iff₀ hl] at this
  linarith

theorem εN_le : εN ≤ γ * δ ^ p.κ * mu p γ εL εN δ := by
  have : εN / (γ * δ ^ p.κ) ≤ mu p γ εL εN δ := le_max_right _ _
  rw [div_le_iff₀ H.gd_pos] at this
  linarith

/-! ### Scales -/

theorem rpow_succ : δ ^ (p.κ + 1) = δ ^ p.κ * δ := by
  rw [Real.rpow_add H.δ_pos, Real.rpow_one]

theorem gd_le : γ * δ ^ p.κ ≤ sg p := by
  have hκ : 0 ≤ p.κ := by linarith [H.ok.one_le_κ]
  exact mul_le_mul H.γ_le (Real.rpow_le_rpow H.δ_pos.le H.δ_le hκ)
    (Real.rpow_nonneg H.δ_pos.le _) H.ok.γb_pos.le

theorem gd1_le : γ * δ ^ (p.κ + 1) ≤ sg1 p := by
  rw [H.rpow_succ, ← mul_assoc]
  exact mul_le_mul H.gd_le H.δ_le H.δ_pos.le
    ((mul_pos H.γ_pos (Real.rpow_pos_of_pos H.δ_pos _)).le.trans H.gd_le)

theorem g_nonneg : 0 ≤ sg p := H.gd_pos.le.trans H.gd_le

/-- `μ = γ δ^{κ+1} X`. -/
theorem mu_eq : mu p γ εL εN δ = γ * δ ^ (p.κ + 1) * xX p γ εL εN δ := by
  rw [xX, mul_div_assoc', eq_div_iff H.gd1_pos.ne']
  ring

/-- `μ/δ = γ δ^κ X`. -/
theorem mu_div_δ : mu p γ εL εN δ / δ = γ * δ ^ p.κ * xX p γ εL εN δ := by
  rw [H.mu_eq, H.rpow_succ, div_eq_iff H.δ_pos.ne']
  ring

/-- `μ/(γ δ^κ) = δ X`. -/
theorem mu_div_gd : mu p γ εL εN δ / (γ * δ ^ p.κ) = δ * xX p γ εL εN δ := by
  rw [H.mu_eq, H.rpow_succ, div_eq_iff H.gd_pos.ne']
  ring

theorem mu_div_δ_le : mu p γ εL εN δ / δ ≤ sg p * xX p γ εL εN δ := by
  rw [H.mu_div_δ]
  exact mul_le_mul_of_nonneg_right H.gd_le H.X_nonneg

theorem mu_le : mu p γ εL εN δ ≤ sg1 p * xX p γ εL εN δ := by
  rw [H.mu_eq]
  exact mul_le_mul_of_nonneg_right H.gd1_le H.X_nonneg

theorem mu_div_gd_le : mu p γ εL εN δ / (γ * δ ^ p.κ) ≤ p.δ * xX p γ εL εN δ := by
  rw [H.mu_div_gd]
  exact mul_le_mul_of_nonneg_right H.δ_le H.X_nonneg

/-- `μ ≤ g · μ/(γ δ^κ)`. -/
theorem mu_le_g_mu_div : mu p γ εL εN δ ≤ sg p * (mu p γ εL εN δ / (γ * δ ^ p.κ)) := by
  rw [mul_div_assoc', le_div_iff₀ H.gd_pos, mul_comm (sg p)]
  exact mul_le_mul_of_nonneg_left H.gd_le H.mu_nonneg

/-! ### The caps -/

theorem caps : m 0 ≤ p.sK ∧ m 1 ≤ p.sLt ∧ m 2 ≤ p.sB ∧ m 3 ≤ p.sN ∧ m 4 ≤ p.sNt := by
  obtain ⟨-, hDK, hBb, hNb, hNbT, -⟩ := stepConstsB_nonneg H.ok
  have hX := H.X_nonneg
  have hn : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  obtain ⟨h0, h1, h2, h3, h4⟩ := H.room
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : 0 ≤ (p.n : ℝ) * (stepConstsB p).CDK * xX p γ εL εN δ := by positivity
    linarith
  · have : 0 ≤ 2 * (p.n : ℝ) * (stepConstsB p).CDK * xX p γ εL εN δ := by positivity
    linarith
  · have : 0 ≤ (stepConstsB p).CBb * xX p γ εL εN δ := by positivity
    linarith
  · have : 0 ≤ (stepConstsB p).CNb * xX p γ εL εN δ := by positivity
    linarith
  · have : 0 ≤ (stepConstsB p).CNbT * xX p γ εL εN δ := by positivity
    linarith

theorem L' : ∀ θ ∈ complexStrip n r, ‖tangentMat K θ‖ ≤ p.sK := fun θ hθ =>
  (H.L θ hθ).trans H.caps.1

theorem Lt' : ∀ θ ∈ complexStrip n r, ‖(tangentMat K θ)ᵀ‖ ≤ p.sLt := fun θ hθ =>
  (H.Lt θ hθ).trans H.caps.2.1

theorem B' : ∀ θ ∈ complexStrip n r, ‖(gramMatrix K θ)⁻¹‖ ≤ p.sB := fun θ hθ =>
  (H.G θ hθ).2.trans H.caps.2.2.1

theorem N' : ∀ θ ∈ complexStrip n r, ‖normalMat K θ‖ ≤ p.sN := fun θ hθ =>
  (H.N θ hθ).trans H.caps.2.2.2.1

theorem Nt' : ∀ θ ∈ complexStrip n r, ‖(normalMat K θ)ᵀ‖ ≤ p.sNt := fun θ hθ =>
  (H.Nt θ hθ).trans H.caps.2.2.2.2

theorem gram : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ =>
  (H.G θ hθ).1

/-- The standing data at the caps of the step. -/
theorem standing : ∃ τ M γ₀ : ℝ, Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ₀ := H.std

/-! ### The step conditions -/

theorem c_q : max 1 (p.sB ^ 2) * sCΩ p * sg p * xX p γ εL εN δ ≤ p.q := H.cond.1

theorem c_DE : sCDE p * sg p * xX p γ εL εN δ ≤ p.n := H.cond.2.1

theorem c_xiL : sCxiL p * xX p γ εL εN δ ≤ p.θξ := H.cond.2.2.1

theorem c_Ω : sCΩ p * sCgL p * xX p γ εL εN δ ≤ p.θΩ := H.cond.2.2.2.1

theorem c_Kt : sCKt p * (sg p * p.δ) * xX p γ εL εN δ ≤ 1 := H.cond.2.2.2.2.1

theorem c_DLt : sCDLt p * sg p * xX p γ εL εN δ ≤ p.θ * p.sK := H.cond.2.2.2.2.2.1

theorem c_DLtT : sCDLtT p * sg p * xX p γ εL εN δ ≤ p.θ * p.sLt := H.cond.2.2.2.2.2.2.1

theorem c_G : p.sB * sCG p * sCDK p * xX p γ εL εN δ ≤ p.θ := H.cond.2.2.2.2.2.2.2.1

theorem c_Bsup : sBsup p * xX p γ εL εN δ ≤ p.ts := H.cond.2.2.2.2.2.2.2.2.1

theorem c_ω : sC0 p * (sg p * p.δ) * xX p γ εL εN δ ≤ p.θω :=
  H.cond.2.2.2.2.2.2.2.2.2.2.1 H.iso

theorem c_L10 : p.selfcons = true → sCNbT p * sCEL p * xX p γ εL εN δ ≤ p.θN ∧
    max 1 (p.sB ^ 2) * (1 + p.n * p.θξ) ^ 2 * sCΩ p * sQtN p * sg p *
      xX p γ εL εN δ ^ 2 ≤ p.q :=
  H.cond.2.2.2.2.2.2.2.2.2.2.2

/-- `|Ω_K|`, `|Ω_N|` against `q`: the constant `C_Ω g X ≤ q`. -/
theorem c_q' : sCΩ p * sg p * xX p γ εL εN δ ≤ p.q ∧
    p.sB ^ 2 * (sCΩ p * sg p * xX p γ εL εN δ) ≤ p.q := by
  have h := H.c_q
  have h0 : 0 ≤ sCΩ p * sg p * xX p γ εL εN δ :=
    mul_nonneg (mul_nonneg (nn_sCΩ H.ok) H.g_nonneg) H.X_nonneg
  constructor
  · calc _ = 1 * (sCΩ p * sg p * xX p γ εL εN δ) := by ring
      _ ≤ max 1 (p.sB ^ 2) * (sCΩ p * sg p * xX p γ εL εN δ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h0
      _ ≤ p.q := by linarith
  · calc _ ≤ max 1 (p.sB ^ 2) * (sCΩ p * sg p * xX p γ εL εN δ) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) h0
      _ ≤ p.q := by linarith

end Hyp

end ModStepB

end KAM.Iso.Sharp2

end
