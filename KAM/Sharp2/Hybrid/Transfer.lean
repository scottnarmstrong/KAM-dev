/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.Hybrid.Data
public import KAM.Sharp2.Hybrid.Integrable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The hypotheses for the new torus, from the step bounds (step `step:p2s2hc:g-hyp`)

`StepHyp` collects what the transfer takes: the data of `K` on `T_{ρ₀}`, a step with the bounds
`(S1)–(S7)`, and the Neumann conditions. `K` has the frequency `ω`, `K₁ = K + ΔK` the frequency
`ω₁`; `ω₁ = ω` at fixed frequency, and `s ω*`, `s₁ ω*` in the isoenergetic form. Under `StepHyp`:

* `StepHyp.struct`, `frames`, `framesR`: the structure of `K₁` and its frames on `T_{ρ₁}` and `ℝⁿ`;
* `StepHyp.err`, `errDeriv`: the new error and, by Cauchy, its derivative;
* `StepHyp.tors₁`, `torsR`: the bound `t₁` on `T'` and the increment `t_A` on `ℝⁿ`, through
  `local_le` (the local part of the torsion, with the bound `wB` of `W`);
* `StepHyp.twist`: the torsion average of `K₁`, at fixed frequency.

The lemmas use the numbers of `StepNum`, so the two theorems of `KAM/Sharp2/Hybrid/G1.lean` and
`KAM/Iso/Sharp2/Hybrid/G1.lean` read their hypotheses for `K₁` from here.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory

namespace KAM.Sharp2.Hybrid

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2

variable {n : ℕ}

/-- `|Fᵀ| ≤ 2n |F|` for a `2n × n` matrix. -/
theorem norm_transpose_le_two_mul (F : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ) :
    ‖Fᵀ‖ ≤ 2 * n * ‖F‖ := by
  refine (norm_le_iff_forall_rowSum (by positivity)).2 fun j => ?_
  have hs : ∀ s, ‖Fᵀ j s‖ ≤ ‖F‖ := fun s =>
    (Finset.single_le_sum (f := fun j' => ‖F s j'‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)).trans (sum_norm_row_le F s)
  calc ∑ s, ‖Fᵀ j s‖ ≤ ∑ _s : Fin n ⊕ Fin n, ‖F‖ := Finset.sum_le_sum fun s _ => hs s
    _ = 2 * n * ‖F‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- The local part of the torsion (`KAM.Sharp2.norm_torsion_sub_torsionAB_le`) with the bound
`wB` of `W`, for `|Fᵀ| ≤ 2n |F|` and `|Aᵀ + A| ≤ 2 M₁ ≤ 4n M₁`. -/
theorem local_le {τ M σK σB σT γ : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ}
    (hS : Standing n τ M σK σB σT 𝔅 h ω γ) {r M1 l lt β νt dE o : ℝ} (hn : 1 ≤ n) (hr : 0 < r)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det)
    (hdX : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ M1) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n r) (hL : ‖tangentMat K θ‖ ≤ l) (hLt : ‖(tangentMat K θ)ᵀ‖ ≤ lt)
    (hB : ‖(gramMatrix K θ)⁻¹‖ ≤ β) (hNt : ‖(normalMat K θ)ᵀ‖ ≤ νt)
    (hDE : ‖errDerivMat h K ω θ‖ ≤ dE) (hΩ : ‖lagrangeMat K θ‖ ≤ o) :
    ‖torsion h K ω θ - torsionAB h K θ‖ ≤ νt * β * dE + β ^ 3 * StepNum.wB n M1 l lt dE * o := by
  have hA : ‖linMat h K θ‖ ≤ M1 := by
    rw [FrameAux.norm_linMat]; exact hdX _ (hK𝔅 θ hθ)
  have hAt : ‖(linMat h K θ)ᵀ‖ ≤ M1 := by
    rw [FrameSharp.linMat_transpose hS (hK𝔅 θ hθ), norm_mul_omegaZeroMatrix,
      norm_omegaZeroMatrix_mul]
    exact hA
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdE0 : 0 ≤ dE := (norm_nonneg _).trans hDE
  have hFt : ‖(errDerivMat h K ω θ)ᵀ‖ ≤ 2 * n * dE :=
    (norm_transpose_le_two_mul _).trans (mul_le_mul_of_nonneg_left hDE (by positivity))
  have hW := norm_W_le hA hAt hL hLt hDE hFt
  have hM1 : 0 ≤ M1 := (norm_nonneg _).trans hA
  have hl0 : 0 ≤ l := (norm_nonneg _).trans hL
  have hlt0 : 0 ≤ lt := (norm_nonneg _).trans hLt
  refine norm_torsion_sub_torsionAB_le hS hr hK hK𝔅 hG hθ hB hNt hDE (hW.trans ?_) hΩ
  have h1 : lt * (2 * M1) * l ≤ lt * (4 * n * M1) * l := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hlt0) hl0
    nlinarith
  have e : StepNum.wB n M1 l lt dE = lt * (4 * n * M1) * l + 2 * n * dE * l + lt * dE := by
    unfold StepNum.wB
    ring
  rw [e]
  linarith

/-- What the transfer takes (Assumption `bp:p2s2hc:standing` and the step bounds): the data `k` of
`K` on `T_{ρ₀}`, a step with the bounds `b`, the margins and the Neumann conditions. `δ` is the
bite of the torsion strip `T' = T_{ρ₁-δ}`. -/
structure StepHyp (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))) (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω ω₁ : Fin n → ℝ)
    (ρ₀ ρ₁ ρinf δ M1 M2 cTh μ μ₁ : ℝ) (k : KData) (b : StepNum) : Prop where
  one_le : 1 ≤ n
  std : ∃ τ M σK σB σT γ, Standing n τ M σK σB σT 𝔅 h ω γ
  std₁ : ∃ τ M σK σB σT γ, Standing n τ M σK σB σT 𝔅 h ω₁ γ
  δ_pos : 0 < δ
  ρδ_pos : 0 < ρ₁ - δ
  ρ_le : ρ₁ ≤ ρ₀
  holo : DifferentiableOn ℂ K (complexStrip n ρ₀)
  ball : ∀ θ ∈ complexStrip n ρ₀, Metric.ball (K θ) μ ⊆ 𝔅
  L : ∀ θ ∈ complexStrip n ρ₀, ‖tangentMat K θ‖ ≤ k.ℓ
  Lt : ∀ θ ∈ complexStrip n ρ₀, ‖(tangentMat K θ)ᵀ‖ ≤ k.ℓt
  gram : ∀ θ ∈ complexStrip n ρ₀, IsUnit (gramMatrix K θ).det
  B : ∀ θ ∈ complexStrip n ρ₀, ‖(gramMatrix K θ)⁻¹‖ ≤ k.β
  Nm : ∀ θ ∈ complexStrip n ρ₀, ‖normalMat K θ‖ ≤ k.ν
  Nt : ∀ θ ∈ complexStrip n ρ₀, ‖(normalMat K θ)ᵀ‖ ≤ k.νt
  step : IsStep ΔK ρ₀
  bd : StepBounds h K ΔK ω ω₁ ρ₁ ρinf (ρ₁ - δ) b
  dX : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ M1
  d2X : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M2
  comm : ∀ z ∈ 𝔅, ‖hamComm h z‖ ≤ cTh
  m1 : b.d0 + μ₁ ≤ μ
  μ₁_pos : 0 < μ₁
  gS : k.β * (b.frS k).g < 1
  gR : k.β * (b.frR k).g < 1

namespace StepHyp

variable {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω ω₁ : Fin n → ℝ}
  {ρ₀ ρ₁ ρinf δ M1 M2 cTh μ μ₁ : ℝ} {k : KData} {b : StepNum}
  (H : StepHyp 𝔅 h K ΔK ω ω₁ ρ₀ ρ₁ ρinf δ M1 M2 cTh μ μ₁ k b)
include H

theorem ρ₁_pos : 0 < ρ₁ := by linarith [H.ρδ_pos, H.δ_pos]

theorem sub : complexStrip n ρ₁ ⊆ complexStrip n ρ₀ := strip_le H.ρ_le

theorem subT : complexStrip n (ρ₁ - δ) ⊆ complexStrip n ρ₁ := strip_le (by linarith [H.δ_pos])

theorem real₁ (x : Fin n → ℝ) : (fun l => (x l : ℂ)) ∈ complexStrip n ρ₁ :=
  ofReal_mem_complexStrip H.ρ₁_pos x

theorem realT (x : Fin n → ℝ) : (fun l => (x l : ℂ)) ∈ complexStrip n (ρ₁ - δ) :=
  ofReal_mem_complexStrip H.ρδ_pos x

theorem diffK {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρ₁) : DifferentiableAt ℂ K θ :=
  H.holo.differentiableAt ((isOpen_complexStrip n ρ₀).mem_nhds (H.sub hθ))

theorem diffΔ {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρ₁) : DifferentiableAt ℂ ΔK θ :=
  H.step.holo.differentiableAt ((isOpen_complexStrip n ρ₀).mem_nhds (H.sub hθ))

theorem d0_lt : b.d0 < μ := by linarith [H.m1, H.μ₁_pos]

theorem Δ_lt {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρ₁) : ‖ΔK θ‖ < μ :=
  (H.bd.d0 θ hθ).trans_lt H.d0_lt

theorem μ_pos : 0 < μ := by
  have h0 : (fun _ => (0 : ℂ)) ∈ complexStrip n ρ₁ := H.real₁ 0 |> fun h => by simpa using h
  exact (norm_nonneg _).trans_lt (H.Δ_lt h0)

theorem mem {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρ₀) : K θ ∈ 𝔅 :=
  H.ball θ hθ (Metric.mem_ball_self H.μ_pos)

/-- Lemma `bp:p2s2hc:struct` for the step. -/
theorem struct (hKp : IsPrimaryOnStrip K ρ₀) (hKr : IsRealOnReals K) :
    DifferentiableOn ℂ (K + ΔK) (complexStrip n ρ₁) ∧ IsPrimaryOnStrip (K + ΔK) ρ₁ ∧
      IsRealOnReals (K + ΔK) ∧ (∀ θ ∈ complexStrip n ρ₁, Metric.ball ((K + ΔK) θ) μ₁ ⊆ 𝔅) ∧
      ∀ θ ∈ complexStrip n ρ₁, ‖fderiv ℂ (K + ΔK) θ‖ ≤ k.ℓ + b.d1 :=
  step_struct H.holo hKp hKr H.ball (fun θ hθ => by rw [← FrameAux.norm_tangentMat]; exact H.L θ hθ)
    H.step H.ρ_le H.bd.d0 (fun θ hθ => by rw [← FrameAux.norm_tangentMat]; exact (H.bd.d1 θ hθ).1)
    H.m1

theorem holo₁ : DifferentiableOn ℂ (K + ΔK) (complexStrip n ρ₁) :=
  (H.holo.mono H.sub).add (H.step.holo.mono H.sub)

theorem mem₁ {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρ₁) : (K + ΔK) θ ∈ 𝔅 :=
  H.ball θ (H.sub hθ) (Metric.mem_ball.2 (by simpa [dist_eq_norm] using H.Δ_lt hθ))

/-- Lemma `bp:p2s2hc:frames` on `T_{ρ₁}`. -/
theorem frames {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρ₁) :
    IsUnit (gramMatrix (K + ΔK) θ).det ∧ ‖(tangentMat (K + ΔK) θ)ᵀ‖ ≤ k.ℓt + b.d1t ∧
      ‖(gramMatrix (K + ΔK) θ)⁻¹‖ ≤ (b.frS k).β1 ∧
      ‖(gramMatrix (K + ΔK) θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤ (b.frS k).b ∧
      ‖normalMat (K + ΔK) θ - normalMat K θ‖ ≤ (b.frS k).nΔ ∧
      ‖(normalMat (K + ΔK) θ)ᵀ - (normalMat K θ)ᵀ‖ ≤ (b.frS k).nΔt ∧
      ‖normalMat (K + ΔK) θ‖ ≤ k.ν + (b.frS k).nΔ ∧
      ‖(normalMat (K + ΔK) θ)ᵀ‖ ≤ k.νt + (b.frS k).nΔt :=
  frames_step (F := b.frS k) (H.diffK hθ) (H.diffΔ hθ) (H.gram θ (H.sub hθ)) (H.L θ (H.sub hθ))
    (H.Lt θ (H.sub hθ)) (H.B θ (H.sub hθ)) (H.Nm θ (H.sub hθ)) (H.Nt θ (H.sub hθ))
    (H.bd.d1 θ hθ).1 (H.bd.d1 θ hθ).2 H.gS

/-- Lemma `bp:p2s2hc:frames` on `ℝⁿ`. -/
theorem framesR (x : Fin n → ℝ) :
    IsUnit (gramMatrix (K + ΔK) (fun l => (x l : ℂ))).det ∧
      ‖(tangentMat (K + ΔK) (fun l => (x l : ℂ)))ᵀ‖ ≤ k.ℓt + b.d1tR ∧
      ‖(gramMatrix (K + ΔK) (fun l => (x l : ℂ)))⁻¹‖ ≤ (b.frR k).β1 ∧
      ‖(gramMatrix (K + ΔK) (fun l => (x l : ℂ)))⁻¹ -
        (gramMatrix K (fun l => (x l : ℂ)))⁻¹‖ ≤ (b.frR k).b ∧
      ‖normalMat (K + ΔK) (fun l => (x l : ℂ)) - normalMat K (fun l => (x l : ℂ))‖ ≤ (b.frR k).nΔ ∧
      ‖(normalMat (K + ΔK) (fun l => (x l : ℂ)))ᵀ - (normalMat K (fun l => (x l : ℂ)))ᵀ‖ ≤
        (b.frR k).nΔt ∧
      ‖normalMat (K + ΔK) (fun l => (x l : ℂ))‖ ≤ k.ν + (b.frR k).nΔ ∧
      ‖(normalMat (K + ΔK) (fun l => (x l : ℂ)))ᵀ‖ ≤ k.νt + (b.frR k).nΔt :=
  have hx := H.real₁ x
  frames_step (F := b.frR k) (H.diffK hx) (H.diffΔ hx) (H.gram _ (H.sub hx)) (H.L _ (H.sub hx))
    (H.Lt _ (H.sub hx)) (H.B _ (H.sub hx)) (H.Nm _ (H.sub hx)) (H.Nt _ (H.sub hx))
    (H.bd.real x).2.1 (H.bd.real x).2.2 H.gR

theorem gram₁ : ∀ θ ∈ complexStrip n ρ₁, IsUnit (gramMatrix (K + ΔK) θ).det :=
  fun _ hθ => (H.frames hθ).1

/-- Lemma `bp:p2s2hc:error`, at the frequency `ω₁`. -/
theorem err : ∀ θ ∈ complexStrip n ρ₁, ‖invarianceError h (K + ΔK) ω₁ θ‖ ≤ b.e1 M2 := by
  obtain ⟨τ, M, σK, σB, σT, γ, hS⟩ := H.std
  exact invarianceError_step_le hS.isOpen (differentiableOn_ham hS) H.d2X H.holo H.step H.ρ_le
    (fun θ hθ => H.ball θ (H.sub hθ)) H.bd.d0 H.d0_lt H.bd.lin

/-- Lemma `bp:p2s2hc:torsion`(e), at the frequency `ω₁`. -/
theorem errDeriv : ∀ θ ∈ complexStrip n (ρ₁ - δ),
    ‖errDerivMat h (K + ΔK) ω₁ θ‖ ≤ n * δ⁻¹ * b.e1 M2 := by
  obtain ⟨τ, M, σK, σB, σT, γ, hS⟩ := H.std
  exact errDerivMat_step_le
    (diffOn_invarianceError_any hS H.holo₁ (fun θ hθ => H.mem₁ hθ) ω₁) H.err H.δ_pos

/-- The local part of `K` on `T'`. -/
theorem loc0 {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (ρ₁ - δ)) :
    ‖torsion h K ω θ - torsionAB h K θ‖ ≤ b.lam0 k n M1 false := by
  obtain ⟨τ, M, σK, σB, σT, γ, hS⟩ := H.std
  have hθ₀ := H.sub (H.subT hθ)
  exact local_le hS H.one_le (H.ρ₁_pos.trans_le H.ρ_le) H.holo (fun θ hθ => H.mem hθ) H.gram H.dX
    hθ₀ (H.L θ hθ₀) (H.Lt θ hθ₀) (H.B θ hθ₀) (H.Nt θ hθ₀) (H.bd.loc0 θ hθ).1 (H.bd.loc0 θ hθ).2

/-- The local part of `K` on `ℝⁿ`. -/
theorem loc0R (x : Fin n → ℝ) :
    ‖torsion h K ω (fun l => (x l : ℂ)) - torsionAB h K (fun l => (x l : ℂ))‖ ≤
      b.lam0 k n M1 true := by
  obtain ⟨τ, M, σK, σB, σT, γ, hS⟩ := H.std
  have hθ₀ := H.sub (H.real₁ x)
  exact local_le hS H.one_le (H.ρ₁_pos.trans_le H.ρ_le) H.holo (fun θ hθ => H.mem hθ) H.gram H.dX
    hθ₀ (H.L _ hθ₀) (H.Lt _ hθ₀) (H.B _ hθ₀) (H.Nt _ hθ₀) (H.bd.loc0R x).1 (H.bd.loc0R x).2

/-- The local part of `K₁` on `T'`. -/
theorem loc1 {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (ρ₁ - δ)) :
    ‖torsion h (K + ΔK) ω₁ θ - torsionAB h (K + ΔK) θ‖ ≤ b.lam1 k n M1 M2 δ false := by
  obtain ⟨τ, M, σK, σB, σT, γ, hS⟩ := H.std₁
  have hθ₁ := H.subT hθ
  obtain ⟨-, h2, h3, -, -, -, -, h8⟩ := H.frames hθ₁
  have hL₁ : ‖tangentMat (K + ΔK) θ‖ ≤ k.ℓ + b.d1 := by
    rw [tangentMat_add_step (H.diffK hθ₁) (H.diffΔ hθ₁)]
    exact (norm_add_le _ _).trans (add_le_add (H.L θ (H.sub hθ₁)) (H.bd.d1 θ hθ₁).1)
  exact local_le hS H.one_le H.ρ₁_pos H.holo₁ (fun θ hθ => H.mem₁ hθ) H.gram₁ H.dX hθ₁ hL₁ h2 h3
    h8 (H.errDeriv θ hθ) (H.bd.loc1 θ hθ)

/-- The local part of `K₁` on `ℝⁿ`. -/
theorem loc1R (x : Fin n → ℝ) :
    ‖torsion h (K + ΔK) ω₁ (fun l => (x l : ℂ)) - torsionAB h (K + ΔK) (fun l => (x l : ℂ))‖ ≤
      b.lam1 k n M1 M2 δ true := by
  obtain ⟨τ, M, σK, σB, σT, γ, hS⟩ := H.std₁
  have hx := H.real₁ x
  obtain ⟨-, h2, h3, -, -, -, -, h8⟩ := H.framesR x
  have hL₁ : ‖tangentMat (K + ΔK) (fun l => (x l : ℂ))‖ ≤ k.ℓ + b.d1R := by
    rw [tangentMat_add_step (H.diffK hx) (H.diffΔ hx)]
    exact (norm_add_le _ _).trans (add_le_add (H.L _ (H.sub hx)) (H.bd.real x).2.1)
  exact local_le hS H.one_le H.ρ₁_pos H.holo₁ (fun θ hθ => H.mem₁ hθ) H.gram₁ H.dX hx hL₁ h2 h3
    h8 (H.errDeriv _ (H.realT x)) (H.bd.loc1R x)

/-- The increment of `A Ω₀ - Ω₀ A` along the step. -/
theorem comm_sub {θ : Fin n → ℂ} {d : ℝ} (hθ : θ ∈ complexStrip n ρ₁) (hd : ‖ΔK θ‖ ≤ d) :
    ‖hamComm h ((K + ΔK) θ) - hamComm h (K θ)‖ ≤ 2 * M2 * d := by
  obtain ⟨τ, M, σK, σB, σT, γ, hS⟩ := H.std
  have hK := H.mem (H.sub hθ)
  exact norm_hamComm_step_le hS.isOpen (differentiableOn_fderiv_ham hS) H.d2X (H.ball θ (H.sub hθ))
    hd (H.Δ_lt hθ) ((norm_nonneg _).trans (H.d2X _ hK))

/-- Lemma `bp:p2s2hc:torsion`(a), (c) on `T'`: the bound `t₁`. -/
theorem tors₁ (hT : ∀ θ ∈ complexStrip n (ρ₁ - δ), ‖torsion h K ω θ‖ ≤ k.t) :
    ∀ θ ∈ complexStrip n (ρ₁ - δ), ‖torsion h (K + ΔK) ω₁ θ‖ ≤ b.t1 k n M1 M2 δ cTh :=
    fun θ hθ => by
  have hθ₁ := H.subT hθ
  have hθ₀ := H.sub hθ₁
  obtain ⟨hG₁, -, -, -, hdN, hdNt, hN₁, hNt₁⟩ := H.frames hθ₁
  have hab := torsionAB_step_sub_le (F := b.frS k) (hG := H.gram θ hθ₀) (hG₁ := hG₁)
    (hN := H.Nm θ hθ₀) (hNt := H.Nt θ hθ₀) (hdN := hdN) (hdNt := hdNt) (hc := H.comm _ (H.mem hθ₀))
    (hc₁ := H.comm _ (H.mem₁ hθ₁)) (hcd := H.comm_sub hθ₁ (H.bd.d0 θ hθ₁))
  exact (torsion_step_le (hT θ hθ) hab (norm_torsionAB_le hG₁ hN₁ hNt₁ (H.comm _ (H.mem₁ hθ₁)))
    (H.loc0 hθ) (H.loc1 hθ)).1

/-- Lemma `bp:p2s2hc:torsion`(a), (c) on `ℝⁿ`: the increment `t_A`. -/
theorem torsR (x : Fin n → ℝ) :
    ‖torsion h (K + ΔK) ω₁ (fun l => (x l : ℂ)) - torsion h K ω (fun l => (x l : ℂ))‖ ≤
      b.tA k n M1 M2 δ cTh := by
  have hx := H.real₁ x
  have hx₀ := H.sub hx
  obtain ⟨hG₁, -, -, -, hdN, hdNt, hN₁, hNt₁⟩ := H.framesR x
  have hab := torsionAB_step_sub_le (F := b.frR k) (hG := H.gram _ hx₀) (hG₁ := hG₁)
    (hN := H.Nm _ hx₀) (hNt := H.Nt _ hx₀) (hdN := hdN) (hdNt := hdNt) (hc := H.comm _ (H.mem hx₀))
    (hc₁ := H.comm _ (H.mem₁ hx)) (hcd := H.comm_sub hx (H.bd.real x).1)
  exact (torsion_step_le (t := ‖torsion h K ω (fun l => (x l : ℂ))‖) le_rfl hab
    (norm_torsionAB_le hG₁ hN₁ hNt₁ (H.comm _ (H.mem₁ hx))) (H.loc0R x) (H.loc1R x)).2

/-- Lemma `bp:p2s2hc:frames` for the Gram matrix of `K₁`, in row sums. -/
theorem gramRow {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρ₁) :
    IsUnit (gramMatrix (K + ΔK) θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix (K + ΔK) θ)⁻¹ i j‖ ≤ (b.frS k).β1 :=
  ⟨(H.frames hθ).1, fun i => (sum_norm_row_le _ i).trans (H.frames hθ).2.2.1⟩

end StepHyp

/-- Lemma `bp:p2s2hc:torsion`(d) for the step, with the integrability from holomorphy. -/
theorem StepHyp.twist {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ}
    {ρ₀ ρ₁ ρinf δ M1 M2 cTh μ μ₁ : ℝ} {k : KData} {b : StepNum}
    (H : StepHyp 𝔅 h K ΔK ω ω ρ₀ ρ₁ ρinf δ M1 M2 cTh μ μ₁ k b)
    (hTu : IsUnit (torsionAverage h K ω).det) (hm : ‖(torsionAverage h K ω)⁻¹‖ ≤ k.m)
    (hm0 : 0 < k.m) (htA : k.m * b.tA k n M1 M2 δ cTh < 1) :
    IsUnit (torsionAverage h (K + ΔK) ω).det ∧
      ∀ i, ∑ j, ‖(torsionAverage h (K + ΔK) ω)⁻¹ i j‖ ≤
        k.m / (1 - k.m * b.tA k n M1 M2 δ cTh) := by
  obtain ⟨τ, M, σK, σB, σT, γ, hS⟩ := H.std
  obtain ⟨hU, hN⟩ := torsionAverage_step (K₁ := K + ΔK)
    (integrableOn_torsion ω hS.isOpen hS.holo (H.ρ₁_pos.trans_le H.ρ_le) H.holo
      (fun θ hθ => H.mem hθ) H.gram)
    (integrableOn_torsion ω hS.isOpen hS.holo H.ρ₁_pos H.holo₁ (fun θ hθ => H.mem₁ hθ) H.gram₁)
    H.torsR hTu hm hm0 ((norm_nonneg _).trans (H.torsR 0)) htA
  exact ⟨hU, fun i => (sum_norm_row_le _ i).trans hN⟩

end KAM.Sharp2.Hybrid

end
