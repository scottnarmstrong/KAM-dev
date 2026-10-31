/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteB.Sched
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The local geometry of a stage torus, without the torsion data

`RouteB.LocHyp` is `ModStepB.Hyp` (SHARP2-B4B) without the torsion bound, the torsion average, the
actual-bite and full-bite certificates and the Hamiltonian data not used by the geometry, with the
caps and `β > 0` given directly. On it, SHARP2-B4B's geometry of the current torus
(`ModStepB/Geo.lean`) holds verbatim; in particular `LocHyp.torsion_sub_le`:
`|T - 𝒯_ab| ≤ B_sup X` on `T_{r-δ}` (`bp:p2s2:torsion-local`), and `LocHyp.E_le`:
`|E| ≤ C_E μ` (`bp:p2s2:recovery`). These are what the reference torsion
(`bp:p2s2:torsion-ref`) needs at entry to each stage, before the step: the torsion bound and the
average there are consequences, not hypotheses.

The proofs are those of `ModStepB.Hyp` (`Hyp.lean`, `Geo.lean`), with the structure renamed.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2.RouteB

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.ModStepB

variable {n : ℕ}

/-- The local data of a stage torus (`ModStepB.Hyp` without the torsion data). -/
structure LocHyp (p : StepInB) (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (Ω : Set (Fin n → ℝ)) (γ β εL εN δ r s c' : ℝ) (m : Fin 5 → ℝ) : Prop where
  ok : p.Ok
  pn : p.n = n
  γ_pos : 0 < γ
  γ_le : γ ≤ p.γb
  δ_pos : 0 < δ
  δ_le : δ ≤ p.δ
  three : 3 * δ < r
  mem : ω ∈ Ω
  s_pos : 0 < s
  s_lt : s < 1
  cert' : SDConst n p.κ γ (s * δ) c' Ω
  c1_le : c' / (s ^ p.κ * (1 - s)) ≤ p.c1
  std : ∃ τ M γ₀ : ℝ, Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ₀
  dX : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ p.M1
  holo : DifferentiableOn ℂ K (complexStrip n r)
  primary : IsPrimaryOnStrip K r
  ball : ∀ θ ∈ complexStrip n r, Metric.ball (K θ) β ⊆ 𝔅
  β_pos' : 0 < β
  L : ∀ θ ∈ complexStrip n r, ‖tangentMat K θ‖ ≤ m 0
  Lt : ∀ θ ∈ complexStrip n r, ‖(tangentMat K θ)ᵀ‖ ≤ m 1
  G : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ m 2
  N : ∀ θ ∈ complexStrip n r, ‖normalMat K θ‖ ≤ m 3
  Nt : ∀ θ ∈ complexStrip n r, ‖(normalMat K θ)ᵀ‖ ≤ m 4
  ηL : ∀ θ ∈ complexStrip n r, ‖etaL h K ω θ‖ ≤ εL
  ηN : ∀ θ ∈ complexStrip n r, ‖etaN h K ω θ‖ ≤ εN
  E0 : p.stage0 = true →
    ∀ θ ∈ complexStrip n r, ‖invarianceError h K ω θ‖ ≤ p.ePer * mu p γ εL εN δ
  cond : stepCondB p (xX p γ εL εN δ)
  caps' : m 0 ≤ p.sK ∧ m 1 ≤ p.sLt ∧ m 2 ≤ p.sB ∧ m 3 ≤ p.sN ∧ m 4 ≤ p.sNt

namespace LocHyp

variable {p : StepInB} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {Ω : Set (Fin n → ℝ)}
  {γ β εL εN δ r s c' : ℝ} {m : Fin 5 → ℝ}
  (H : LocHyp p 𝔅 h K ω Ω γ β εL εN δ r s c' m)
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

theorem β_pos : 0 < β := H.β_pos'

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

theorem caps : m 0 ≤ p.sK ∧ m 1 ≤ p.sLt ∧ m 2 ≤ p.sB ∧ m 3 ≤ p.sN ∧ m 4 ≤ p.sNt := H.caps'

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

end LocHyp

namespace LocHyp

variable {p : StepInB} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {Ω : Set (Fin n → ℝ)}
  {γ β εL εN δ r s c' : ℝ} {m : Fin 5 → ℝ}
  (H : LocHyp p 𝔅 h K ω Ω γ β εL εN δ r s c' m)
  {τ M γ₀ : ℝ} (hS : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ₀)
include H

theorem fderiv_le : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ p.sK := fun θ hθ => by
  rw [← norm_colMat]; exact H.L' θ hθ

theorem gramB : ∀ θ ∈ complexStrip n r,
    IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ p.sB := fun θ hθ =>
  ⟨H.gram θ hθ, H.B' θ hθ⟩

theorem sub1 : complexStrip n (r - δ) ⊆ complexStrip n r := strip_sub (by linarith [H.δ_pos])

/-- `γ⁻¹ δ^{-(κ+1)} εN ≤ μ/δ`. -/
theorem εN_scale : γ⁻¹ * δ ^ (-(p.κ + 1)) * εN ≤ mu p γ εL εN δ / δ := by
  have e1 : γ⁻¹ * δ ^ (-(p.κ + 1)) * εN = εN / (γ * δ ^ (p.κ + 1)) := by
    rw [Real.rpow_neg H.δ_pos.le]; field_simp
  rw [e1, div_le_iff₀ H.gd1_pos, H.rpow_succ]
  have := H.εN_le
  have e2 : mu p γ εL εN δ / δ * (γ * (δ ^ p.κ * δ)) = γ * δ ^ p.κ * mu p γ εL εN δ := by
    field_simp [H.δ_pos.ne']
  rw [e2]; exact this

/-! ### The Lagrangian defects -/

include hS in
/-- `bp:p2s2:omega`: `|Ω_K| ≤ C_Ω μ/δ` on `T_{r-δ}`. -/
theorem omegaK : ∀ θ ∈ complexStrip n (r - δ),
    ‖lagrangeMat K θ‖ ≤ sCΩ p * (mu p γ εL εN δ / δ) := by
  intro θ hθ
  have hn : 1 ≤ n := H.n_pos
  have h1 := norm_lagrangeMat_le_etaN_of_standing hn H.cert' H.mem H.s_pos H.s_lt H.δ_lt_r hS
    H.holo H.primary H.K_mem H.ηN θ hθ
  have hn1 : (0 : ℝ) ≤ 2 * ((n : ℝ) - 1) := by linarith [H.one_le_n]
  have hY0 : 0 ≤ γ⁻¹ * δ ^ (-(p.κ + 1)) * εN :=
    mul_nonneg (mul_nonneg (inv_nonneg.2 H.γ_pos.le) (Real.rpow_nonneg H.δ_pos.le _))
      H.εN_nonneg
  have hc1 : 0 ≤ p.c1 := H.ok.sd.2.1.le
  calc _ ≤ _ := h1
    _ = 2 * ((n : ℝ) - 1) * (c' / (s ^ p.κ * (1 - s))) * (γ⁻¹ * δ ^ (-(p.κ + 1)) * εN) := by
        ring
    _ ≤ 2 * ((n : ℝ) - 1) * p.c1 * (mu p γ εL εN δ / δ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left H.c1_le hn1) H.εN_scale hY0 (mul_nonneg hn1 hc1)
    _ = sCΩ p * (mu p γ εL εN δ / δ) := by rw [sCΩ, H.pn_real]

/-- `C_Ω μ/δ ≤ C_Ω g X`. -/
theorem omega_scale : sCΩ p * (mu p γ εL εN δ / δ) ≤ sCΩ p * sg p * xX p γ εL εN δ := by
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left H.mu_div_δ_le (nn_sCΩ H.ok)

include hS in
theorem omegaK_q : ∀ θ ∈ complexStrip n (r - δ), ‖lagrangeMat K θ‖ ≤ p.q := fun θ hθ =>
  ((H.omegaK hS θ hθ).trans H.omega_scale).trans H.c_q'.1

include hS in
/-- `|Ω_N| = |B Ω_K B| ≤ σ_B² C_Ω μ/δ` on `T_{r-δ}`. -/
theorem omegaN : ∀ θ ∈ complexStrip n (r - δ),
    ‖(normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ‖ ≤
      p.sB ^ 2 * (sCΩ p * (mu p γ εL εN δ / δ)) := by
  intro θ hθ
  rw [Identities.fi_NtON]
  have hB := H.B' θ (H.sub1 hθ)
  have nm := @FrameSharp.norm_mul_le_of_le
  calc _ ≤ p.sB * (sCΩ p * (mu p γ εL εN δ / δ)) * p.sB := nm (nm hB (H.omegaK hS θ hθ)) hB
    _ = _ := by ring

include hS in
theorem omegaN_q : ∀ θ ∈ complexStrip n (r - δ),
    ‖(normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ‖ ≤ p.q := fun θ hθ =>
  (H.omegaN hS θ hθ).trans ((mul_le_mul_of_nonneg_left H.omega_scale (sq_nonneg _)).trans
    H.c_q'.2)

/-! ### The invariance error -/

theorem max_le_mu : max εL εN ≤ max p.lam (sg p) * mu p γ εL εN δ := by
  have hμ := H.mu_nonneg
  refine max_le (H.εL_le.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hμ))
    (H.εN_le.trans ((mul_le_mul_of_nonneg_right H.gd_le hμ).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hμ)))

include hS in
/-- `bp:p2s2:recovery`: `|E| ≤ C_E μ` on `T_{r-δ}`. -/
theorem E_le : ∀ θ ∈ complexStrip n (r - δ),
    ‖invarianceError h K ω θ‖ ≤ sCE p * mu p γ εL εN δ := by
  intro θ hθ
  have hrec := norm_invarianceError_le_eta (r := r - δ) H.ok.ratios.2.2.2.2.2.2.2.1
    (fun θ hθ => H.L' θ (H.sub1 hθ)) (fun θ hθ => H.N' θ (H.sub1 hθ))
    (fun θ hθ => H.gram θ (H.sub1 hθ)) (H.omegaK_q hS) (H.omegaN_q hS)
    (fun θ hθ => H.ηL θ (H.sub1 hθ)) (fun θ hθ => H.ηN θ (H.sub1 hθ)) θ hθ
  have h0 : ‖invarianceError h K ω θ‖ ≤ sCE0 p * mu p γ εL εN δ := by
    have hL := mul_le_mul_of_nonneg_left H.εL_le (nn_sCEL H.ok)
    have hN := mul_le_mul_of_nonneg_left (H.εN_le.trans (mul_le_mul_of_nonneg_right H.gd_le
      H.mu_nonneg)) (nn_sCEN H.ok)
    calc _ ≤ sCEL p * εL + sCEN p * εN := hrec
      _ ≤ sCEL p * (p.lam * mu p γ εL εN δ) + sCEN p * (sg p * mu p γ εL εN δ) :=
          add_le_add hL hN
      _ = sCE0 p * mu p γ εL εN δ := by rw [sCE0]; ring
  by_cases hs0 : p.stage0 = true
  · simp only [sCE, hs0, ↓reduceIte]
    rw [min_mul_of_nonneg _ _ H.mu_nonneg]
    exact le_min h0 (H.E0 hs0 θ (H.sub1 hθ))
  · simp only [sCE, hs0]
    exact h0

/-! ### The derivative of the invariance error -/

include hS in
/-- FH24's route for one column of `DE`: `|∂_j E| ≤ (σ_K+σ_N)/(1-q) (max{εL,εN} +
(σ_{Lᵀ}+σ_{Nᵀ}) |E|)/δ`. -/
theorem DE_col_fh : ∀ θ ∈ complexStrip n (r - δ), ∀ j : Fin n,
    ‖fderiv ℂ (fun y => sumVec n (invarianceError h K ω y)) θ (Pi.single j 1)‖ ≤
      sCDE0 p / p.n * (mu p γ εL εN δ / δ) := by
  intro θ hθ j
  have hθr := H.sub1 hθ
  have hq1 := H.ok.ratios.2.2.2.2.2.2.2.1
  have hq0 := H.ok.ratios.2.2.2.2.2.2.1
  have hδ0 := H.δ_pos
  have hsLt := H.ok.caps.2.1
  have hsNt := H.ok.caps.2.2.2.2.1
  have hsCE := nn_sCE H.ok
  have hμ0 := H.mu_nonneg
  obtain ⟨⟨-, -, hEd, -, -, -, -, -, -, -, -, hRd, hηd, -, -⟩, -, -, -⟩ :=
    frame_basic hS H.r_pos H.β_pos H.holo H.ball H.fderiv_le H.gramB
  have hnhds := (isOpen_complexStrip n r).mem_nhds hθr
  set e : (Fin n → ℂ) → Fin n ⊕ Fin n → ℂ := fun y => sumVec n (invarianceError h K ω y) with he
  have hed : DifferentiableAt ℂ e θ :=
    differentiableAt_sumVec_iff.2 (hEd.differentiableAt hnhds)
  have hRθ : DifferentiableAt ℂ (reducer K) θ := hRd.differentiableAt hnhds
  set v : Fin n → ℂ := Pi.single j 1
  -- `R e = -η`, differentiated
  have hfun : (fun y => reducer K y *ᵥ e y) = fun y => -eta h K ω y :=
    funext fun y => Identities.fi_QE h K ω (θ := y)
  have hprod := fderiv_matrix_mulVec_apply hRθ hed v
  rw [hfun, fderiv_fun_neg] at hprod
  have hRe : reducer K θ *ᵥ fderiv ℂ e θ v =
      -fderiv ℂ (eta h K ω) θ v - fderiv ℂ (reducer K) θ v *ᵥ e θ := by
    rw [_root_.neg_apply] at hprod
    rw [hprod]; abel
  -- `R P = S`, `S` invertible
  set S := 1 - omegaZeroMatrix n * symDefect K θ with hSdef
  have hRP : reducer K θ * frameMat K θ = S := Identities.fi_QP K (θ := θ)
  have hEs : ‖omegaZeroMatrix n * symDefect K θ‖ ≤ p.q := by
    rw [norm_omegaZeroMatrix_mul, Identities.fi_symDefect K (H.gram θ hθr),
      Tools.norm_fromBlocks_diagonal, ← Identities.fi_NtON]
    exact max_le (H.omegaK_q hS θ hθ) (H.omegaN_q hS θ hθ)
  have h1n : ‖(1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)⁻¹‖ ≤ 1 := by
    rw [inv_one]
    exact (norm_le_iff_forall_rowSum zero_le_one).2 fun i => by
      rw [Finset.sum_eq_single i (fun j _ hji => by rw [Matrix.one_apply_ne' hji, norm_zero])
        (by simp)]
      simp
  obtain ⟨hSu, hSinv, -⟩ := neumann_ratio (A := (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ))
    (Δ := -(omegaZeroMatrix n * symDefect K θ)) isUnit_one hq1
    (by rw [norm_neg]; exact (mul_le_of_le_one_left (norm_nonneg _) h1n).trans hEs)
  rw [← sub_eq_add_neg] at hSu hSinv
  have hSinv' : ‖S⁻¹‖ ≤ 1 / (1 - p.q) :=
    hSinv.trans (div_le_div_of_nonneg_right h1n (by linarith))
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hSu
  have hleft : (S⁻¹ * reducer K θ) * frameMat K θ = 1 := by
    rw [Matrix.mul_assoc, hRP, Matrix.nonsing_inv_mul _ hSdet]
  have hright : frameMat K θ * (S⁻¹ * reducer K θ) = 1 := mul_eq_one_comm.1 hleft
  have hDe : fderiv ℂ e θ v = (frameMat K θ * S⁻¹) *ᵥ
      (-fderiv ℂ (eta h K ω) θ v - fderiv ℂ (reducer K) θ v *ᵥ e θ) := by
    have h1 : fderiv ℂ e θ v = (frameMat K θ * S⁻¹) *ᵥ (reducer K θ *ᵥ fderiv ℂ e θ v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hright, Matrix.one_mulVec]
    rw [hRe] at h1
    exact h1
  -- the norms
  have hP : ‖frameMat K θ‖ ≤ p.sK + p.sN :=
    (Tools.norm_fromCols_le_add _ _).trans (add_le_add (H.L' θ hθr) (H.N' θ hθr))
  have hηb : ∀ y ∈ complexStrip n r, ‖eta h K ω y‖ ≤ max εL εN := fun y hy => by
    rw [eta_eq_sumElim]
    exact Correction.norm_sumElim_le ((H.ηL y hy).trans (le_max_left _ _))
      ((H.ηN y hy).trans (le_max_right _ _))
  have hRb : ∀ y ∈ complexStrip n r, ‖reducer K y‖ ≤ p.sLt + p.sNt := fun y hy => by
    rw [reducer, norm_neg, norm_mul_omegaZeroMatrix, norm_omegaZeroMatrix_mul, frameMat,
      Matrix.transpose_fromCols]
    exact (norm_fromRows_le_add _ _).trans (add_le_add (H.Lt' y hy) (H.Nt' y hy))
  have hdη := (cauchy_strip hηd hηb H.δ_pos).1 j θ hθ
  have hdR := (cauchy_strip hRd hRb H.δ_pos).1 j θ hθ
  have heθ : ‖e θ‖ ≤ sCE p * mu p γ εL εN δ := by
    rw [he, norm_sumVec]; exact H.E_le hS θ hθ
  have hw : ‖-fderiv ℂ (eta h K ω) θ v - fderiv ℂ (reducer K) θ v *ᵥ e θ‖ ≤
      δ⁻¹ * max εL εN + δ⁻¹ * (p.sLt + p.sNt) * (sCE p * mu p γ εL εN δ) := by
    refine (norm_sub_le _ _).trans (add_le_add (by rw [norm_neg]; exact hdη) ?_)
    exact (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul hdR heθ (norm_nonneg _)
      (by positivity))
  have hPS : ‖frameMat K θ * S⁻¹‖ ≤ (p.sK + p.sN) / (1 - p.q) := by
    rw [div_eq_mul_one_div]
    exact FrameSharp.norm_mul_le_of_le hP hSinv'
  have hδi : 0 ≤ δ⁻¹ := inv_nonneg.2 H.δ_pos.le
  rw [hDe]
  refine (Matrix.linfty_opNorm_mulVec _ _).trans ((mul_le_mul hPS hw (norm_nonneg _)
    (div_nonneg (add_nonneg H.ok.caps.1.le H.ok.caps.2.2.2.1.le) (by linarith))).trans ?_)
  -- arithmetic
  have hmax := H.max_le_mu
  have hn0 : (0 : ℝ) < p.n := by rw [H.pn_real]; exact_mod_cast H.n_pos
  have hsc : 0 ≤ (p.sLt + p.sNt) * sCE p :=
    mul_nonneg (add_nonneg H.ok.caps.2.1.le H.ok.caps.2.2.2.2.1.le) (nn_sCE H.ok)
  have hA : δ⁻¹ * max εL εN + δ⁻¹ * (p.sLt + p.sNt) * (sCE p * mu p γ εL εN δ) ≤
      (max p.lam (sg p) + (p.sLt + p.sNt) * sCE p) * (mu p γ εL εN δ / δ) := by
    have : δ⁻¹ * max εL εN ≤ δ⁻¹ * (max p.lam (sg p) * mu p γ εL εN δ) :=
      mul_le_mul_of_nonneg_left hmax hδi
    calc _ ≤ δ⁻¹ * (max p.lam (sg p) * mu p γ εL εN δ) +
          δ⁻¹ * (p.sLt + p.sNt) * (sCE p * mu p γ εL εN δ) := by linarith
      _ = _ := by rw [div_eq_mul_inv]; ring
  calc (p.sK + p.sN) / (1 - p.q) *
        (δ⁻¹ * max εL εN + δ⁻¹ * (p.sLt + p.sNt) * (sCE p * mu p γ εL εN δ))
      ≤ (p.sK + p.sN) / (1 - p.q) *
        ((max p.lam (sg p) + (p.sLt + p.sNt) * sCE p) * (mu p γ εL εN δ / δ)) :=
        mul_le_mul_of_nonneg_left hA
          (div_nonneg (add_nonneg H.ok.caps.1.le H.ok.caps.2.2.2.1.le) (by linarith))
    _ = sCDE0 p / p.n * (mu p γ εL εN δ / δ) := by
        rw [sCDE0]; field_simp

include hS in
/-- Every column of `DE` has sup norm `≤ (C_DE/n) μ/δ` on `T_{r-δ}`. -/
theorem DE_col : ∀ θ ∈ complexStrip n (r - δ), ∀ j : Fin n,
    ‖fderiv ℂ (fun y => sumVec n (invarianceError h K ω y)) θ (Pi.single j 1)‖ ≤
      sCDE p / p.n * (mu p γ εL εN δ / δ) := by
  intro θ hθ j
  have h0 := H.DE_col_fh hS θ hθ j
  by_cases hs0 : p.stage0 = true
  · obtain ⟨⟨-, -, hEd, -⟩, -⟩ := frame_basic hS H.r_pos H.β_pos H.holo H.ball H.fderiv_le
      H.gramB
    have hed : DifferentiableOn ℂ (fun y => sumVec n (invarianceError h K ω y))
        (complexStrip n r) := (sumVecIso n).differentiable.comp_differentiableOn hEd
    have hb : ∀ y ∈ complexStrip n r,
        ‖sumVec n (invarianceError h K ω y)‖ ≤ p.ePer * mu p γ εL εN δ := fun y hy => by
      rw [norm_sumVec]; exact H.E0 hs0 y hy
    have h1 := (cauchy_strip hed hb H.δ_pos).1 j θ hθ
    have hn0 : (0 : ℝ) < p.n := by rw [H.pn_real]; exact_mod_cast H.n_pos
    simp only [sCDE, hs0, ↓reduceIte]
    rw [← min_div_div_right hn0.le, min_mul_of_nonneg _ _ (div_nonneg H.mu_nonneg H.δ_pos.le)]
    refine le_min h0 (h1.trans (le_of_eq ?_))
    field_simp
  · simp only [sCDE, hs0]
    exact h0

include hS in
theorem DE_entry : ∀ θ ∈ complexStrip n (r - δ), ∀ s' j,
    ‖errDerivMat h K ω θ s' j‖ ≤ sCDE p / p.n * (mu p γ εL εN δ / δ) := fun θ hθ s' j => by
  rw [Geometry.errDerivMat_eq_of, Matrix.of_apply]
  exact (norm_le_pi_norm _ s').trans (H.DE_col hS θ hθ j)

theorem DE_e_nonneg : 0 ≤ sCDE p / p.n * (mu p γ εL εN δ / δ) :=
  mul_nonneg (div_nonneg (nn_sCDE H.ok) (Nat.cast_nonneg _))
    (div_nonneg H.mu_nonneg H.δ_pos.le)

include hS in
theorem DE_le : ∀ θ ∈ complexStrip n (r - δ),
    ‖errDerivMat h K ω θ‖ ≤ sCDE p * (mu p γ εL εN δ / δ) := fun θ hθ => by
  refine (norm_le_of_col H.DE_e_nonneg (H.DE_entry hS θ hθ)).trans (le_of_eq ?_)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast H.n_pos.ne'
  rw [H.pn_real]; field_simp

include hS in
theorem DEt_le : ∀ θ ∈ complexStrip n (r - δ),
    ‖(errDerivMat h K ω θ)ᵀ‖ ≤ 2 * sCDE p * (mu p γ εL εN δ / δ) := fun θ hθ => by
  refine (norm_transpose_le_of_col H.DE_e_nonneg (H.DE_entry hS θ hθ)).trans (le_of_eq ?_)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast H.n_pos.ne'
  rw [Fintype.card_sum, Fintype.card_fin, H.pn_real]; push_cast; field_simp; ring

/-- `C_DE μ/δ ≤ n` (second step condition). -/
theorem DE_scale : sCDE p * (mu p γ εL εN δ / δ) ≤ n := by
  rw [← H.pn_real]
  calc _ ≤ sCDE p * (sg p * xX p γ εL εN δ) :=
        mul_le_mul_of_nonneg_left H.mu_div_δ_le (nn_sCDE H.ok)
    _ = sCDE p * sg p * xX p γ εL εN δ := by ring
    _ ≤ p.n := H.c_DE

include hS in
theorem DE_n : ∀ θ ∈ complexStrip n (r - δ), ‖errDerivMat h K ω θ‖ ≤ n := fun θ hθ =>
  (H.DE_le hS θ hθ).trans H.DE_scale

include hS in
theorem DEt_n : ∀ θ ∈ complexStrip n (r - δ), ‖(errDerivMat h K ω θ)ᵀ‖ ≤ 2 * n :=
  fun θ hθ => (H.DEt_le hS θ hθ).trans (by rw [mul_assoc]; linarith [H.DE_scale])

include hS in
/-- `|(Nᵀ Ω₀ DE)ᵀ| ≤ C_NN μ/δ` on `T_{r-δ}`. -/
theorem NtODE_le : ∀ θ ∈ complexStrip n (r - δ),
    ‖((normalMat K θ)ᵀ * omegaZeroMatrix n * errDerivMat h K ω θ)ᵀ‖ ≤
      sCNN p * (mu p γ εL εN δ / δ) := by
  intro θ hθ
  have hθr := H.sub1 hθ
  obtain ⟨⟨-, -, hEd, -, -, -, hNd, -, -, -, -, -, hηd, -, -⟩, -, -, -⟩ :=
    frame_basic hS H.r_pos H.β_pos H.holo H.ball H.fderiv_le H.gramB
  have hnhds := (isOpen_complexStrip n r).mem_nhds hθr
  set e : (Fin n → ℂ) → Fin n ⊕ Fin n → ℂ := fun y => sumVec n (invarianceError h K ω y) with he
  have hed : DifferentiableAt ℂ e θ :=
    differentiableAt_sumVec_iff.2 (hEd.differentiableAt hnhds)
  have hYd : DifferentiableOn ℂ (fun y => (normalMat K y)ᵀ * omegaZeroMatrix n)
      (complexStrip n r) := hNd.matrix_transpose.matrix_mul (differentiableOn_const _)
  have hYb : ∀ y ∈ complexStrip n r, ‖(normalMat K y)ᵀ * omegaZeroMatrix n‖ ≤ p.sNt :=
    fun y hy => by rw [norm_mul_omegaZeroMatrix]; exact H.Nt' y hy
  have hLd := Correction.diffOn_etaL hηd
  have heθ : ‖e θ‖ ≤ sCE p * mu p γ εL εN δ := by
    rw [he, norm_sumVec]; exact H.E_le hS θ hθ
  set Y : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ := (normalMat K θ)ᵀ * omegaZeroMatrix n with hY
  have hδ0 := H.δ_pos
  have hsNt := H.ok.caps.2.2.2.2.1
  -- column `j`
  have hcol : ∀ i, ∀ j : Fin n, ‖(Y * errDerivMat h K ω θ) i j‖ ≤
      δ⁻¹ * εL + δ⁻¹ * p.sNt * (sCE p * mu p γ εL εN δ) := by
    intro i j
    set v : Fin n → ℂ := Pi.single j 1
    set dY := fderiv ℂ (fun y => (normalMat K y)ᵀ * omegaZeroMatrix n) θ v with hdY
    have hfun : etaL h K ω = fun y => -(((normalMat K y)ᵀ * omegaZeroMatrix n) *ᵥ e y) := rfl
    have hprod := fderiv_matrix_mulVec_apply (hYd.differentiableAt hnhds) hed v
    have hdL : fderiv ℂ (etaL h K ω) θ v = -(dY *ᵥ e θ + Y *ᵥ fderiv ℂ e θ v) := by
      rw [hfun, fderiv_fun_neg, _root_.neg_apply, hprod]
    have hcolj : (Y * errDerivMat h K ω θ) i j = (Y *ᵥ fderiv ℂ e θ v) i := by
      rw [Geometry.errDerivMat_eq_of, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rfl
    have hYv : Y *ᵥ fderiv ℂ e θ v = -fderiv ℂ (etaL h K ω) θ v - dY *ᵥ e θ := by
      rw [hdL]; abel
    have hb1 := (cauchy_strip hLd H.ηL H.δ_pos).1 j θ hθ
    have hb2 : ‖dY‖ ≤ δ⁻¹ * p.sNt := (cauchy_strip hYd hYb H.δ_pos).1 j θ hθ
    rw [hcolj]
    refine (norm_le_pi_norm _ i).trans ?_
    rw [hYv]
    refine (norm_sub_le _ _).trans (add_le_add (by rw [norm_neg]; exact hb1) ?_)
    exact (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul hb2 heθ (norm_nonneg _)
      (by positivity))
  have hδi : 0 ≤ δ⁻¹ := inv_nonneg.2 H.δ_pos.le
  have he0 : 0 ≤ δ⁻¹ * εL + δ⁻¹ * p.sNt * (sCE p * mu p γ εL εN δ) := by
    have := nn_sCE H.ok
    have := H.εL_nonneg
    have := H.mu_nonneg
    positivity
  refine (norm_transpose_le_of_col he0 hcol).trans ?_
  rw [Fintype.card_fin, ← H.pn_real]
  have hL := H.εL_le
  calc (p.n : ℝ) * (δ⁻¹ * εL + δ⁻¹ * p.sNt * (sCE p * mu p γ εL εN δ))
      ≤ (p.n : ℝ) * (δ⁻¹ * (p.lam * mu p γ εL εN δ) +
          δ⁻¹ * p.sNt * (sCE p * mu p γ εL εN δ)) := by
        exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hL hδi) le_rfl)
          (Nat.cast_nonneg _)
    _ = sCNN p * (mu p γ εL εN δ / δ) := by rw [sCNN, div_eq_mul_inv]; ring

/-! ### The Hamiltonian matrix and the torsion -/

omit H in
include hS in
theorem A_le' (hd : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ p.M1) {θ : Fin n → ℂ}
    (hK : K θ ∈ 𝔅) : ‖linMat h K θ‖ ≤ p.M1 ∧ ‖(linMat h K θ)ᵀ‖ ≤ p.M1 := by
  have h1 : ‖linMat h K θ‖ ≤ p.M1 := by rw [linMat, norm_sqMat]; exact hd _ hK
  refine ⟨h1, ?_⟩
  rw [FrameSharp.linMat_transpose hS hK, norm_mul_omegaZeroMatrix, norm_omegaZeroMatrix_mul]
  exact h1

include hS in
/-- `|W| ≤ w` on `T_{r-δ}`, `W = Lᵀ (Aᵀ + A) L - (DE)ᵀ L - Lᵀ DE`. -/
theorem W_le : ∀ θ ∈ complexStrip n (r - δ),
    ‖(tangentMat K θ)ᵀ * ((linMat h K θ)ᵀ + linMat h K θ) * tangentMat K θ -
      (errDerivMat h K ω θ)ᵀ * tangentMat K θ - (tangentMat K θ)ᵀ * errDerivMat h K ω θ‖ ≤
      sw p := fun θ hθ => by
  have hθr := H.sub1 hθ
  obtain ⟨hA, hAt⟩ := A_le' hS H.dX (H.K_mem θ hθr)
  refine (norm_W_le hA hAt (H.L' θ hθr) (H.Lt' θ hθr) (H.DE_n hS θ hθ)
    (H.DEt_n hS θ hθ)).trans (le_of_eq ?_)
  rw [sw, H.pn_real]; ring

include hS in
/-- `bp:p2s2:torsion-local`: `|T - 𝒯_ab| ≤ B_sup X` on `T_{r-δ}`. -/
theorem torsion_sub_le : ∀ θ ∈ complexStrip n (r - δ),
    ‖torsion h K ω θ - torsionAB h K θ‖ ≤ sBsup p * xX p γ εL εN δ := fun θ hθ => by
  have hθr := H.sub1 hθ
  refine (norm_torsion_sub_torsionAB_le hS H.r_pos H.holo H.K_mem H.gram hθr (H.B' θ hθr)
    (H.Nt' θ hθr) (H.DE_le hS θ hθ) (H.W_le hS θ hθ) (H.omegaK hS θ hθ)).trans ?_
  have hc : 0 ≤ p.sNt * p.sB * sCDE p + p.sB ^ 3 * sw p * sCΩ p := by
    have := H.ok.caps.2.2.2.2.1
    have := H.ok.caps.2.2.1
    have := nn_sCDE H.ok
    have := nn_sw H.ok
    have := nn_sCΩ H.ok
    positivity
  calc _ = (p.sNt * p.sB * sCDE p + p.sB ^ 3 * sw p * sCΩ p) * (mu p γ εL εN δ / δ) := by ring
    _ ≤ (p.sNt * p.sB * sCDE p + p.sB ^ 3 * sw p * sCΩ p) * (sg p * xX p γ εL εN δ) :=
        mul_le_mul_of_nonneg_left H.mu_div_δ_le hc
    _ = sBsup p * xX p γ εL εN δ := by rw [sBsup]; ring

include hS in
/-- `|∂_ω N| ≤ C_dN` on `T_{r-δ}`. -/
theorem dN_le : ∀ θ ∈ complexStrip n (r - δ),
    ‖fderiv ℂ (normalMat K) θ (fun l => (ω l : ℂ))‖ ≤ sCdN p := fun θ hθ => by
  have hθr := H.sub1 hθ
  rw [((torsion_identity hS H.r_pos H.holo H.K_mem H.gram ω) θ hθr).2.1]
  obtain ⟨hA, hAt⟩ := A_le' hS H.dX (H.K_mem θ hθr)
  have hL := H.L' θ hθr
  have hLt := H.Lt' θ hθr
  have hB := H.B' θ hθr
  have hN := H.N' θ hθr
  have hF := H.DE_n hS θ hθ
  have hFt := H.DEt_n hS θ hθ
  have nm := @FrameSharp.norm_mul_le_of_le
  have hALF : ‖linMat h K θ * tangentMat K θ - errDerivMat h K ω θ‖ ≤ p.M1 * p.sK + n :=
    (norm_sub_le _ _).trans (add_le_add (nm hA hL) hF)
  have hALFt : ‖(linMat h K θ * tangentMat K θ - errDerivMat h K ω θ)ᵀ‖ ≤
      p.sLt * p.M1 + 2 * n := by
    rw [Matrix.transpose_sub, Matrix.transpose_mul]
    exact (norm_sub_le _ _).trans (add_le_add (nm hLt hAt) hFt)
  have h1 : ‖omegaZeroMatrix n * (linMat h K θ * tangentMat K θ - errDerivMat h K ω θ) *
      (gramMatrix K θ)⁻¹‖ ≤ (p.M1 * p.sK + n) * p.sB := by
    rw [Matrix.mul_assoc, norm_omegaZeroMatrix_mul]; exact nm hALF hB
  have h2 : ‖normalMat K θ *
      ((linMat h K θ * tangentMat K θ - errDerivMat h K ω θ)ᵀ * tangentMat K θ +
        (tangentMat K θ)ᵀ * (linMat h K θ * tangentMat K θ - errDerivMat h K ω θ)) *
      (gramMatrix K θ)⁻¹‖ ≤
      p.sN * ((p.sLt * p.M1 + 2 * n) * p.sK + p.sLt * (p.M1 * p.sK + n)) * p.sB :=
    nm (nm hN ((norm_add_le _ _).trans (add_le_add (nm hALFt hL) (nm hLt hALF)))) hB
  refine (norm_sub_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
  rw [sCdN, H.pn_real]

include hS in
/-- `|X_N| ≤ C_XN` on `T_{r-δ}`. -/
theorem XN_le : ∀ θ ∈ complexStrip n (r - δ), ‖normalFieldMat h K ω θ‖ ≤ sCXN p :=
  fun θ hθ => by
  have hθr := H.sub1 hθ
  obtain ⟨hA, -⟩ := A_le' hS H.dX (H.K_mem θ hθr)
  refine (norm_sub_le _ _).trans ((add_le_add (FrameSharp.norm_mul_le_of_le hA (H.N' θ hθr))
    (H.dN_le hS θ hθ)).trans (le_of_eq ?_))
  rw [sCXN]

end LocHyp

end KAM.Sharp2.RouteB

end
