/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Torus.Objects
public import KAM.Frozen.Defs.ComplexStrip
public import KAM.Frozen.Defs.IsPrimaryOnStrip
public import KAM.Frozen.Defs.IsRealOnReals
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# The restart of the certified first step (`bp:p2s2hc:restart`, `bpI:p2s2hc:restart`)

The hybrid applies a proved v2 branch theorem to the new torus `K₁ = K + ΔK` and transfers its
conclusion back to `K`. No hypothesis of the restarted theorem is used here, so any theorem that
concludes the frozen body can be restarted.

* `G1Concl`, `IG1Concl`: the conclusions of the frozen G1 and I-G1 (`G1Body`, `IG1Body` after their
  hypotheses), with a free closeness bound;
* `restart_close`: the closeness and the ball;
* `concl_restart`, `iconcl_restart`: the frozen conclusion for any `K₁` near `K` transfers to `K`.
-/

@[expose] public noncomputable section

namespace KAM.Sharp2.Hybrid

open KAM

variable {n : ℕ}

/-- The conclusion of the frozen G1 (`G1Body` after its hypotheses) for `K`, with the closeness
bound `D`. -/
def G1Concl (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))) (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) (ρinf μ σK D : ℝ) : Prop :=
  ∃ Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ),
    DifferentiableOn ℂ Kinf (complexStrip n ρinf) ∧ IsPrimaryOnStrip Kinf ρinf ∧
    IsRealOnReals Kinf ∧
    (∀ θ ∈ complexStrip n ρinf, invarianceError h Kinf ω θ = 0) ∧
    (∀ θ ∈ complexStrip n ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ 𝔅) ∧
    (∀ θ ∈ complexStrip n ρinf, ‖fderiv ℂ Kinf θ‖ ≤ σK - μ / 2) ∧
    ∀ θ ∈ complexStrip n ρinf, ‖Kinf θ - K θ‖ ≤ D

/-- The closeness and the ball of the restart (`step:p2s2hc:rs-ball`). -/
theorem restart_close {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {K K₁ Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ρinf μ D₁ dinf : ℝ}
    (hball : ∀ θ ∈ complexStrip n ρinf, Metric.ball (K θ) μ ⊆ 𝔅)
    (hd : ∀ θ ∈ complexStrip n ρinf, ‖K₁ θ - K θ‖ ≤ dinf) (hbud : dinf + D₁ ≤ μ / 2)
    (h7 : ∀ θ ∈ complexStrip n ρinf, ‖Kinf θ - K₁ θ‖ ≤ D₁) :
    (∀ θ ∈ complexStrip n ρinf, ‖Kinf θ - K θ‖ ≤ dinf + D₁) ∧
      ∀ θ ∈ complexStrip n ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ 𝔅 := by
  have hc : ∀ θ ∈ complexStrip n ρinf, ‖Kinf θ - K θ‖ ≤ dinf + D₁ := fun θ hθ => by
    have e : Kinf θ - K θ = (Kinf θ - K₁ θ) + (K₁ θ - K θ) := by abel
    rw [e, add_comm dinf]
    exact (norm_add_le _ _).trans (add_le_add (h7 θ hθ) (hd θ hθ))
  refine ⟨hc, fun θ hθ z hz => hball θ hθ ?_⟩
  rw [Metric.mem_ball] at hz ⊢
  calc dist z (K θ) ≤ dist z (Kinf θ) + dist (Kinf θ) (K θ) := dist_triangle _ _ _
    _ < μ / 2 + μ / 2 :=
        add_lt_add_of_lt_of_le hz (by rw [dist_eq_norm]; exact (hc θ hθ).trans hbud)
    _ = μ := by ring

/-- Proposition `bp:p2s2hc:restart`: the frozen conclusion for any `K₁` near `K` transfers to
`K`. -/
theorem concl_restart {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K K₁ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {ω : Fin n → ℝ} {ρinf μ μ₁ σK σK₁ D₁ dinf : ℝ}
    (hball : ∀ θ ∈ complexStrip n ρinf, Metric.ball (K θ) μ ⊆ 𝔅)
    (hd : ∀ θ ∈ complexStrip n ρinf, ‖K₁ θ - K θ‖ ≤ dinf) (hbud : dinf + D₁ ≤ μ / 2)
    (hσ : σK₁ - μ₁ / 2 ≤ σK - μ / 2) (h1 : G1Concl 𝔅 h K₁ ω ρinf μ₁ σK₁ D₁) :
    G1Concl 𝔅 h K ω ρinf μ σK (dinf + D₁) := by
  obtain ⟨Kinf, h1, h2, h3, h4, -, h6, h7⟩ := h1
  obtain ⟨hc, hb⟩ := restart_close hball hd hbud h7
  exact ⟨Kinf, h1, h2, h3, h4, hb, fun θ hθ => (h6 θ hθ).trans hσ, hc⟩

/-- The conclusion of the frozen I-G1 (`IG1Body` after its hypotheses) for `(K, s)`, with the
closeness bounds `D` (torus) and `Dω` (frequency). -/
def IG1Concl (D : Set ((Fin n → ℂ) × (Fin n → ℂ))) (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ωstar : Fin n → ℝ)
    (s E₀ ρinf μ σK σω Dk Dω : ℝ) : Prop :=
  ∃ (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (sinf : ℝ),
    1 < sinf ∧ sinf < σω ∧ DifferentiableOn ℂ Kinf (complexStrip n ρinf) ∧
    IsPrimaryOnStrip Kinf ρinf ∧ IsRealOnReals Kinf ∧
    (∀ θ ∈ complexStrip n ρinf, invarianceError H Kinf (sinf • ωstar) θ = 0) ∧
    (∀ θ ∈ complexStrip n ρinf, H (Kinf θ) = (E₀ : ℂ)) ∧
    (∀ θ ∈ complexStrip n ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ D) ∧
    (∀ θ ∈ complexStrip n ρinf, ‖fderiv ℂ Kinf θ‖ ≤ σK - μ / 2) ∧
    (∀ θ ∈ complexStrip n ρinf, ‖Kinf θ - K θ‖ ≤ Dk) ∧
    ‖sinf • ωstar - s • ωstar‖ ≤ Dω

/-- Proposition `bpI:p2s2hc:restart`. -/
theorem iconcl_restart {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K K₁ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {ωstar : Fin n → ℝ} {s s₁ E₀ ρinf μ μ₁ σK σK₁ σω D₁ D₁ω dinf dω : ℝ}
    (hball : ∀ θ ∈ complexStrip n ρinf, Metric.ball (K θ) μ ⊆ D)
    (hd : ∀ θ ∈ complexStrip n ρinf, ‖K₁ θ - K θ‖ ≤ dinf) (hdω : ‖s₁ • ωstar - s • ωstar‖ ≤ dω)
    (hbud : dinf + D₁ ≤ μ / 2) (hσ : σK₁ - μ₁ / 2 ≤ σK - μ / 2)
    (h1 : IG1Concl D H K₁ ωstar s₁ E₀ ρinf μ₁ σK₁ σω D₁ D₁ω) :
    IG1Concl D H K ωstar s E₀ ρinf μ σK σω (dinf + D₁) (dω + D₁ω) := by
  obtain ⟨Kinf, sinf, hs1, hs2, h1, h2, h3, h4, h5, -, h7, h8, h9⟩ := h1
  obtain ⟨hc, hb⟩ := restart_close hball hd hbud h8
  refine ⟨Kinf, sinf, hs1, hs2, h1, h2, h3, h4, h5, hb, fun θ hθ => (h7 θ hθ).trans hσ, hc, ?_⟩
  have e : sinf • ωstar - s • ωstar = (sinf • ωstar - s₁ • ωstar) + (s₁ • ωstar - s • ωstar) := by
    abel
  rw [e, add_comm dω]
  exact (norm_add_le _ _).trans (add_le_add h9 hdω)

end KAM.Sharp2.Hybrid

end
