/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.BoxTorsion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# One certificate covers a parameter box (fixed frequency)

`KAM.Sharp.g1_box`: let `h : Λ → (ℂⁿ × ℂⁿ → ℂ)` be a family of Hamiltonians on a pseudo-metric space
`Λ` (the parameter), `l₀ ∈ Λ`, and suppose that on a set `S ∋ l₀` every `h l` satisfies the standing
hypotheses H1 (`KAM.Sharp.BoxH1`) and, on the domain `𝔅`,
`‖X_{h l} - X_{h l₀}‖ ≤ L₀ dist l l₀` and `‖DX_{h l} - DX_{h l₀}‖ ≤ L₁ dist l l₀`.
If `K` satisfies H2–H3, the invariance bound `e` and the twist bound `‖⟨T⟩⁻¹‖ ≤ b₀` at `l₀`, then
  for
every `l ∈ S` with `dist l l₀ ≤ d`, where `d` is such that

* `C₁ (e + L₀ d)/(γ⁴ ρ^{4τ}) < 1`,
* with `Δ = 2n ((σ_K-μ)(σ_B-μ))² L₁ d` (`KAM.Sharp.torsionShift`): `b₀ Δ ≤ 1/2` and
  `b₀ ≤ (σ_T-μ)(1 - b₀ Δ)`,

the conclusion of `KAM.Apost.g1_explicit` holds for `h l` with the same `K`, `ω`, `γ`, and with the
error `e + L₀ dist l l₀`: the invariance error satisfies `E_l = E_{l₀} + (X_{h l} - X_{h l₀}) ∘
  K`, the
torsion average moves by at most `Δ` (`N` depends on `K` only), and the Neumann series keeps the
inverse bound `σ_T - μ`. All other hypotheses do not depend on `l`.

`Λ` is an arbitrary pseudo-metric space: only the triangle-free bounds `dist l l₀` are used, so the
statement holds for `Fin m → ℝ` with the sup norm (or any other norm) at no extra cost.
-/

public section

open scoped Matrix.Norms.Operator

namespace KAM.Sharp

open KAM KAM.Apost KAM.Torus

/-- H1 for one Hamiltonian `h` (the first nine hypotheses of `KAM.Apost.g1_explicit`): open
translation-invariant domain `𝔅`, holomorphy, periodicity, realness, and the four `M`-bounds. -/
def BoxH1 {n : ℕ} (M : ℝ) (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : Prop :=
  IsOpen 𝔅 ∧
  (∀ z ∈ 𝔅, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ 𝔅) ∧
  DifferentiableOn ℂ h 𝔅 ∧
  (∀ z ∈ 𝔅, ∀ k : Fin n → ℤ, h (z.1 + (fun i => (k i : ℂ)), z.2) = h z) ∧
  (∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ 𝔅 →
    (h ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0) ∧
  (∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ h z‖ ≤ M ∧
    ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ M ∧
    ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M)

/-- The bound `Δ = 2n ((σ_K-μ)(σ_B-μ))² L₁ d` for the change of the averaged torsion. -/
@[expose] def torsionShift (n : ℕ) (σK σB μ L₁ d : ℝ) : ℝ :=
  2 * n * ((σK - μ) * (σB - μ)) ^ 2 * (L₁ * d)

/-- **One certificate covers a parameter box** (fixed frequency; see the module docstring). -/
theorem g1_box {n : ℕ} (hn : 2 ≤ n) {τ : ℝ} (hτ : (n : ℝ) - 1 ≤ τ)
    {ρ ρinf : ℝ} (hρinf : 0 < ρinf) (hρinfρ : ρinf < ρ)
    {M σK σB σT μ : ℝ} (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB) (hσT : 0 < σT) (hμ : 0 < μ)
    {γbar : ℝ} (hγbar : 0 < γbar)
    {Λ : Type*} [PseudoMetricSpace Λ] (𝔥 : Λ → (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (l₀ : Λ)
    (S : Set Λ) (hl₀ : l₀ ∈ S) {L₀ L₁ : ℝ} (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) :
    ∀ (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ)))
      (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) (γ e b₀ d : ℝ),
      (∀ l ∈ S, BoxH1 M 𝔅 (𝔥 l)) →
      (∀ l ∈ S, ∀ z ∈ 𝔅, ‖hamiltonianVectorFieldℂ (𝔥 l) z - hamiltonianVectorFieldℂ (𝔥 l₀) z‖ ≤
        L₀ * dist l l₀) →
      (∀ l ∈ S, ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ (𝔥 l)) z -
        fderiv ℂ (hamiltonianVectorFieldℂ (𝔥 l₀)) z‖ ≤ L₁ * dist l l₀) →
      DifferentiableOn ℂ K (complexStrip n ρ) → IsPrimaryOnStrip K ρ → IsRealOnReals K →
      (∀ θ ∈ complexStrip n ρ, Metric.ball (K θ) μ ⊆ 𝔅) →
      (∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ K θ‖ ≤ σK - μ) →
      (∀ θ ∈ complexStrip n ρ, IsUnit (gramMatrix K θ).det ∧
        ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ σB - μ) →
      IsUnit (torsionAverage (𝔥 l₀) K ω).det →
      (∀ i, ∑ j, ‖(torsionAverage (𝔥 l₀) K ω)⁻¹ i j‖ ≤ b₀) →
      0 < γ → γ ≤ γbar → IsDiophantine γ τ ω →
      (∀ θ ∈ complexStrip n ρ, ‖invarianceError (𝔥 l₀) K ω θ‖ ≤ e) →
      0 ≤ d →
      b₀ * torsionShift n σK σB μ L₁ d ≤ 1 / 2 →
      b₀ ≤ (σT - μ) * (1 - b₀ * torsionShift n σK σB μ L₁ d) →
      C_1 n τ ρ ρinf M σK σB σT μ γbar * (e + L₀ * d) / (γ ^ 4 * ρ ^ (4 * τ)) < 1 →
      ∀ l ∈ S, dist l l₀ ≤ d →
        ∃ Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ),
          DifferentiableOn ℂ Kinf (complexStrip n ρinf) ∧ IsPrimaryOnStrip Kinf ρinf ∧
          IsRealOnReals Kinf ∧
          (∀ θ ∈ complexStrip n ρinf, invarianceError (𝔥 l) Kinf ω θ = 0) ∧
          (∀ θ ∈ complexStrip n ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ 𝔅) ∧
          (∀ θ ∈ complexStrip n ρinf, ‖fderiv ℂ Kinf θ‖ ≤ σK - μ / 2) ∧
          ∀ θ ∈ complexStrip n ρinf, ‖Kinf θ - K θ‖ ≤
            C_2 n τ ρ ρinf M σK σB σT * (e + L₀ * dist l l₀) / (γ ^ 2 * ρ ^ (2 * τ)) := by
  intro 𝔅 K ω γ e b₀ d hH1 hX hDX hK hKp hKr hball hDK hG hTu hTb hγ hγγbar hdio hE hd hb₀Δ hbT hC1
    l hlS hld
  have hP : Params n τ M σK σB σT := ⟨hn, hτ, hM, hσK, hσB, hσT⟩
  have hρ0 : 0 < ρ := hρinf.trans hρinfρ
  obtain ⟨hopen, htransl, hholo, hper, hreal, hbd⟩ := hH1 l hlS
  obtain ⟨hopen₀, htransl₀, hholo₀, hper₀, hreal₀, hbd₀⟩ := hH1 l₀ hl₀
  have hdist : 0 ≤ dist l l₀ := dist_nonneg
  have hK𝔅 : ∀ θ ∈ complexStrip n ρ, K θ ∈ 𝔅 := fun θ hθ =>
    hball θ hθ (Metric.mem_ball_self hμ)
  -- the standing assumptions at `l` and `l₀`
  have hS : ∀ l' ∈ S, Standing n τ M σK σB σT 𝔅 (𝔥 l') ω γ := fun l' hl' => by
    obtain ⟨ho, ht, hh, hp, hr, hb⟩ := hH1 l' hl'
    exact
      { toParams := hP
        isOpen := ho
        transl_mem := ht
        holo := hh
        periodic := hp
        real := hr
        bounds := fun z hz => ⟨(hb z hz).2.1, (hb z hz).2.2.1, (hb z hz).2.2.2⟩
        gamma_pos := hγ
        dio := hdio }
  have hGu : ∀ θ ∈ complexStrip n ρ, IsUnit (gramMatrix K θ).det := fun θ hθ => (hG θ hθ).1
  have hNd := differentiableOn_normalMat hK hGu
  have hcont : ∀ l' ∈ S, Continuous (fun x : Fin n → ℝ =>
      torsion (𝔥 l') K ω (fun i => (x i : ℂ))) := fun l' hl' =>
    FrameAux.continuous_torsion_real hρ0
      (PerturbationAux.differentiableOn_torsion_of (hS l' hl') hK hK𝔅 hGu)
  -- the averaged torsion moves by at most `Δ`
  set Δ : ℝ := torsionShift n σK σB μ L₁ d with hΔdef
  have hΔl : 2 * n * ((σK - μ) * (σB - μ)) ^ 2 * (L₁ * dist l l₀) ≤ Δ := by
    rw [hΔdef, torsionShift]
    gcongr
  have hTavg : ‖torsionAverage (𝔥 l) K ω - torsionAverage (𝔥 l₀) K ω‖ ≤ Δ :=
    (norm_torsionAverage_sub_param_le (𝔥 l₀) (𝔥 l) K ω (hcont l₀ hl₀) (hcont l hlS) fun x =>
      (norm_torsion_sub_param_le (𝔥 l₀) (𝔥 l) K ω
        ((hNd.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds
          (ofReal_mem_complexStrip hρ0 x))))
        (hDK _ (ofReal_mem_complexStrip hρ0 x))
        (norm_le_of_rowSum_le hn (hG _ (ofReal_mem_complexStrip hρ0 x)).2)
        ((hDX l hlS _ (hK𝔅 _ (ofReal_mem_complexStrip hρ0 x))))).trans hΔl)
  have hb₀ : 0 ≤ b₀ := (Finset.sum_nonneg fun j _ => norm_nonneg
    ((torsionAverage (𝔥 l₀) K ω)⁻¹ ⟨0, by omega⟩ j)).trans (hTb ⟨0, by omega⟩)
  have hΔ0 : 0 ≤ Δ := (norm_nonneg _).trans hTavg
  have hpos : 0 < 1 - b₀ * Δ := by linarith
  have hσ0 : 0 ≤ σT - μ := by
    by_contra hneg
    push Not at hneg
    nlinarith
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨hTu', hTb'⟩ := inv_rowSum_of_perturb hTu hTb hTavg hb₀Δ hbT
  -- the invariance error
  have hEl : ∀ θ ∈ complexStrip n ρ, ‖invarianceError (𝔥 l) K ω θ‖ ≤ e + L₀ * dist l l₀ := by
    intro θ hθ
    have hsplit : invarianceError (𝔥 l) K ω θ = invarianceError (𝔥 l₀) K ω θ +
        (hamiltonianVectorFieldℂ (𝔥 l) (K θ) - hamiltonianVectorFieldℂ (𝔥 l₀) (K θ)) := by
      unfold invarianceError; abel
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add (hE θ hθ) (hX l hlS _ (hK𝔅 θ hθ)))
  have hC1l : C_1 n τ ρ ρinf M σK σB σT μ γbar * (e + L₀ * dist l l₀) /
      (γ ^ 4 * ρ ^ (4 * τ)) < 1 := by
    refine lt_of_le_of_lt ?_ hC1
    have hC := (C_1_pos (n := n) (τ := τ) (ρinf := ρinf) (M := M) (σK := σK) (σB := σB)
      (σT := σT) (μ := μ) hρ0 hγbar).le
    have hden : 0 < γ ^ 4 * ρ ^ (4 * τ) := mul_pos (pow_pos hγ 4) (Real.rpow_pos_of_pos hρ0 _)
    gcongr
  obtain ⟨-, -, hmain⟩ := g1_explicit hn hτ hρinf hρinfρ hM hσK hσB hσT hμ hγbar
  exact hmain 𝔅 (𝔥 l) K ω γ (e + L₀ * dist l l₀) hopen htransl hholo hper hreal hbd hK hKp hKr
    hball hDK hG hTu' hTb' hγ hγγbar hdio hEl hC1l

end KAM.Sharp

end
