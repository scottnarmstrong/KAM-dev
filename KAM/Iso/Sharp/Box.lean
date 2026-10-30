/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp.BoxLemmas
public import KAM.Sharp.Box
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# One certificate covers a parameter box (isoenergetic)

`KAM.Iso.Sharp.g1_box`: the isoenergetic analogue of `KAM.Sharp.g1_box`, a corollary of
`KAM.Iso.Apost.g1_explicit` (the body `KAM.Iso.Charts.IG1Body`).

Let `𝔥 : Λ → (ℂⁿ × ℂⁿ → ℂ)` be a family of Hamiltonians on a pseudo-metric space `Λ`, `l₀ ∈ S ⊆ Λ`,
and suppose each `𝔥 l`, `l ∈ S`, satisfies H1 (`KAM.Iso.Sharp.BoxH1`, with the five `M`-bounds) on
  the
domain `D`, and on `D`, with `δ = dist l l₀`,

* `‖X_{𝔥 l} - X_{𝔥 l₀}‖ ≤ L₀ δ`, `‖DX_{𝔥 l} - DX_{𝔥 l₀}‖ ≤ L₁ δ`,
* `|𝔥 l - 𝔥 l₀| ≤ L_E δ` (the energy), `‖D𝔥 l - D𝔥 l₀‖ ≤ L_Y δ` (the last row of the bordered
  torsion).

If `K` satisfies the hypotheses of `g1_explicit` at `𝔥 l₀`, with the invariance and energy errors
`e` and the bordered twist bound `‖⟨𝖳⟩⁻¹‖ ≤ b₀`, then for every `l ∈ S` with `dist l l₀ ≤ d`,
  where `d`
is such that `C₁ (e + L d)/(γ⁴ ρ^{4τ}) < 1` (`L = max {L₀, L_E}`) and, with
`Δ = max {2n ((σ_K-μ)(σ_B-μ))² L₁ d, (σ_K-μ)(σ_B-μ) L_Y d}` (`KAM.Iso.Sharp.extShift`),
`b₀ Δ ≤ 1/2` and `b₀ ≤ (σ_T-μ)(1 - b₀ Δ)`, the full conclusion of `g1_explicit` holds for `𝔥 l`,
  with
the same `K`, `s`, `γ`, `E₀` and the error `e + L dist l l₀` in place of `e`:

* invariance error: `E_l = E_{l₀} + (X_{𝔥 l} - X_{𝔥 l₀}) ∘ K`;
* energy: `|Ē_{𝔥 l}(K) - E₀| ≤ |Ē_{𝔥 l₀}(K) - E₀| + L_E δ`;
* bordered twist: `𝖳_{𝔥 l} - 𝖳_{𝔥 l₀} = (T_{𝔥 l} - T_{𝔥 l₀}, 0; Y_{𝔥 l} - Y_{𝔥 l₀}, 0)`, the
  frequency
  column being unchanged, and the Neumann series keeps the inverse bound `σ_T - μ`.
-/

public section

open scoped Matrix.Norms.Operator

namespace KAM.Iso.Sharp

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost

/-- H1 for one Hamiltonian in the isoenergetic setting (the first nine hypotheses of `IG1Body`,
with the five `M`-bounds). -/
def BoxH1 {n : ℕ} (M : ℝ) (D : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : Prop :=
  IsOpen D ∧
  (∀ z ∈ D, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ D) ∧
  DifferentiableOn ℂ H D ∧
  (∀ z ∈ D, ∀ k : Fin n → ℤ, H (z.1 + (fun i => (k i : ℂ)), z.2) = H z) ∧
  (∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ D →
    (H ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0) ∧
  (∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ H z‖ ≤ M ∧
    ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ M ∧
    ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ M ∧ ‖iteratedFDeriv ℂ 2 H z‖ ≤ M)

/-- The bound `Δ` for the change of the averaged bordered torsion. -/
@[expose] def extShift (n : ℕ) (σK σB μ L₁ L_Y d : ℝ) : ℝ :=
  max (KAM.Sharp.torsionShift n σK σB μ L₁ d) ((σK - μ) * (σB - μ) * (L_Y * d))

/-- **One certificate covers a parameter box** (isoenergetic; see the module docstring). -/
theorem g1_box {n : ℕ} (hn : 2 ≤ n) {τ : ℝ} (hτ : (n : ℝ) - 1 ≤ τ)
    {ρ ρinf : ℝ} (hρinf : 0 < ρinf) (hρinfρ : ρinf < ρ)
    {M σK σB σT μ γbar σω ν : ℝ}
    (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB) (hσT : 0 < σT)
    (hμ : 0 < μ) (hγbar : 0 < γbar) (hσω : 1 < σω) (hν : 0 < ν)
    (ωstar : Fin n → ℝ) (hωstar : ωstar ≠ 0)
    {Λ : Type*} [PseudoMetricSpace Λ] (𝔥 : Λ → (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (l₀ : Λ)
    (S : Set Λ) (hl₀ : l₀ ∈ S) {L₀ L₁ L_E L_Y : ℝ} (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁)
    (hL_E : 0 ≤ L_E) (hL_Y : 0 ≤ L_Y) :
    ∀ (D : Set ((Fin n → ℂ) × (Fin n → ℂ)))
      (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (s γ e E₀ b₀ d : ℝ),
      (∀ l ∈ S, BoxH1 M D (𝔥 l)) →
      (∀ l ∈ S, ∀ z ∈ D, ‖hamiltonianVectorFieldℂ (𝔥 l) z - hamiltonianVectorFieldℂ (𝔥 l₀) z‖ ≤
        L₀ * dist l l₀) →
      (∀ l ∈ S, ∀ z ∈ D, ‖fderiv ℂ (hamiltonianVectorFieldℂ (𝔥 l)) z -
        fderiv ℂ (hamiltonianVectorFieldℂ (𝔥 l₀)) z‖ ≤ L₁ * dist l l₀) →
      (∀ l ∈ S, ∀ z ∈ D, ‖𝔥 l z - 𝔥 l₀ z‖ ≤ L_E * dist l l₀) →
      (∀ l ∈ S, ∀ z ∈ D, ‖fderiv ℂ (𝔥 l) z - fderiv ℂ (𝔥 l₀) z‖ ≤ L_Y * dist l l₀) →
      DifferentiableOn ℂ K (complexStrip n ρ) → IsPrimaryOnStrip K ρ → IsRealOnReals K →
      (∀ θ ∈ complexStrip n ρ, Metric.ball (K θ) μ ⊆ D) →
      (∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ K θ‖ ≤ σK - μ) →
      (∀ θ ∈ complexStrip n ρ, IsUnit (gramMatrix K θ).det ∧
        ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ σB - μ) →
      IsUnit (KAM.Iso.extendedTorsionAverage (𝔥 l₀) K (s • ωstar)).det →
      (∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage (𝔥 l₀) K (s • ωstar))⁻¹ i j‖ ≤ b₀) →
      1 < s → s < σω → ν ≤ (s - 1) * ‖ωstar‖ → ν ≤ (σω - s) * ‖ωstar‖ →
      0 < γ → γ ≤ γbar → IsDiophantine γ τ ωstar → 0 ≤ e →
      (∀ θ ∈ complexStrip n ρ, ‖invarianceError (𝔥 l₀) K (s • ωstar) θ‖ ≤ e) →
      ‖KAM.Iso.energyAverage (𝔥 l₀) K - (E₀ : ℂ)‖ ≤ e →
      0 ≤ d →
      b₀ * extShift n σK σB μ L₁ L_Y d ≤ 1 / 2 →
      b₀ ≤ (σT - μ) * (1 - b₀ * extShift n σK σB μ L₁ L_Y d) →
      isoC1 n τ ρ ρinf M σK σB σT μ ν γbar * (e + max L₀ L_E * d) /
        (γ ^ 4 * ρ ^ (4 * τ)) < 1 →
      ∀ l ∈ S, dist l l₀ ≤ d →
        ∃ (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (sinf : ℝ),
          1 < sinf ∧ sinf < σω ∧ DifferentiableOn ℂ Kinf (complexStrip n ρinf) ∧
          IsPrimaryOnStrip Kinf ρinf ∧ IsRealOnReals Kinf ∧
          (∀ θ ∈ complexStrip n ρinf, invarianceError (𝔥 l) Kinf (sinf • ωstar) θ = 0) ∧
          (∀ θ ∈ complexStrip n ρinf, 𝔥 l (Kinf θ) = (E₀ : ℂ)) ∧
          (∀ θ ∈ complexStrip n ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ D) ∧
          (∀ θ ∈ complexStrip n ρinf, ‖fderiv ℂ Kinf θ‖ ≤ σK - μ / 2) ∧
          (∀ θ ∈ complexStrip n ρinf, ‖Kinf θ - K θ‖ ≤
            isoC2 n τ ρ ρinf M σK σB σT * (e + max L₀ L_E * dist l l₀) /
              (γ ^ 2 * ρ ^ (2 * τ))) ∧
          ‖sinf • ωstar - s • ωstar‖ ≤
            isoC2 n τ ρ ρinf M σK σB σT * (e + max L₀ L_E * dist l l₀) / (γ ^ 2 * ρ ^ (2 * τ)) := by
  intro D K s γ e E₀ b₀ d hH1 hX hDX hH hDH hK hKp hKr hball hDK hG hTu hTb hs1 hsσ hν1 hν2 hγ
    hγγbar hdio he0 hE hEn hd hb₀Δ hbT hC1 l hlS hld
  have hP : Params n τ M σK σB σT := ⟨hn, hτ, hM, hσK, hσB, hσT⟩
  have hρ0 : 0 < ρ := hρinf.trans hρinfρ
  obtain ⟨hopen, htransl, hholo, hper, hreal, hbd⟩ := hH1 l hlS
  have hdist : 0 ≤ dist l l₀ := dist_nonneg
  have hLmax : 0 ≤ max L₀ L_E := le_max_of_le_left hL₀
  have hKD : ∀ θ ∈ complexStrip n ρ, K θ ∈ D := fun θ hθ =>
    hball θ hθ (Metric.mem_ball_self hμ)
  have hS : ∀ l' ∈ S, Standing n τ M σK σB σT D (𝔥 l') ωstar γ := fun l' hl' => by
    obtain ⟨ho, ht, hh, hp, hr, hb⟩ := hH1 l' hl'
    exact
      { toParams := hP
        isOpen := ho
        transl_mem := ht
        holo := hh
        periodic := hp
        real := hr
        bounds := fun z hz => ⟨(hb z hz).2.1, (hb z hz).2.2.1, (hb z hz).2.2.2.1⟩
        gamma_pos := hγ
        dio := hdio }
  have hGu : ∀ θ ∈ complexStrip n ρ, IsUnit (gramMatrix K θ).det := fun θ hθ => (hG θ hθ).1
  have hNd := differentiableOn_normalMat hK hGu
  have hcont : ∀ l' ∈ S, Continuous (fun x : Fin n → ℝ =>
      KAM.Iso.extendedTorsion (𝔥 l') K (s • ωstar) (fun i => (x i : ℂ))) := fun l' hl' =>
    (extended_regular (hS l' hl') hρ0 hK hKD hGu (s • ωstar)).2.2
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  -- the bordered torsion average moves by at most `Δ`
  set Δ : ℝ := extShift n σK σB μ L₁ L_Y d with hΔdef
  have hpt : ∀ x : Fin n → ℝ, ‖KAM.Iso.extendedTorsion (𝔥 l) K (s • ωstar) (fun i => (x i : ℂ)) -
      KAM.Iso.extendedTorsion (𝔥 l₀) K (s • ωstar) (fun i => (x i : ℂ))‖ ≤ Δ := by
    intro x
    have hx := ofReal_mem_complexStrip (n := n) hρ0 x
    have hN : ‖normalMat K (fun i => (x i : ℂ))‖ ≤ (σK - μ) * (σB - μ) :=
      Uniq.FrameAux.norm_normalMat_le' (hDK _ hx) (norm_le_of_rowSum_le hn (hG _ hx).2)
    have hT := KAM.Sharp.norm_torsion_sub_param_le (𝔥 l₀) (𝔥 l) K (s • ωstar)
      (hNd.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hx)) (hDK _ hx)
      (norm_le_of_rowSum_le hn (hG _ hx).2) (hDX l hlS _ (hKD _ hx))
    have hY := sum_norm_energyRow_sub_param_le (𝔥 l₀) (𝔥 l) K (fun i => (x i : ℂ)) hN
      (hDH l hlS _ (hKD _ hx))
    refine (norm_extendedTorsion_sub_param_le (𝔥 l₀) (𝔥 l) K (s • ωstar) _ hT hY).trans ?_
    refine max_le_max ?_ ?_
    · have : 2 * (n : ℝ) * ((σK - μ) * (σB - μ)) ^ 2 * (L₁ * dist l l₀) ≤
          KAM.Sharp.torsionShift n σK σB μ L₁ d := by
        rw [KAM.Sharp.torsionShift]; gcongr
      exact this
    · have hab : 0 ≤ (σK - μ) * (σB - μ) := (norm_nonneg _).trans hN
      gcongr
  have hTavg : ‖KAM.Iso.extendedTorsionAverage (𝔥 l) K (s • ωstar) -
      KAM.Iso.extendedTorsionAverage (𝔥 l₀) K (s • ωstar)‖ ≤ Δ :=
    norm_extendedTorsionAverage_sub_param_le (𝔥 l₀) (𝔥 l) K (s • ωstar) (hcont l₀ hl₀)
      (hcont l hlS) hpt
  have hb₀ : 0 ≤ b₀ := (Finset.sum_nonneg fun j _ => norm_nonneg
    ((KAM.Iso.extendedTorsionAverage (𝔥 l₀) K (s • ωstar))⁻¹ (Sum.inl ⟨0, by omega⟩) j)).trans
    (hTb _)
  have hΔ0 : 0 ≤ Δ := (norm_nonneg _).trans hTavg
  obtain ⟨hTu', hTb'⟩ := KAM.Sharp.inv_rowSum_of_perturb hTu hTb hTavg hb₀Δ hbT
  -- the invariance error and the energy
  have hEl : ∀ θ ∈ complexStrip n ρ, ‖invarianceError (𝔥 l) K (s • ωstar) θ‖ ≤
      e + max L₀ L_E * dist l l₀ := by
    intro θ hθ
    have hsplit : invarianceError (𝔥 l) K (s • ωstar) θ =
        invarianceError (𝔥 l₀) K (s • ωstar) θ +
        (hamiltonianVectorFieldℂ (𝔥 l) (K θ) - hamiltonianVectorFieldℂ (𝔥 l₀) (K θ)) := by
      unfold invarianceError; abel
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add (hE θ hθ) ((hX l hlS _ (hKD θ hθ)).trans ?_))
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hdist
  have hHK : ∀ l' ∈ S, Continuous (fun x : Fin n → ℝ => 𝔥 l' (K fun j => (x j : ℂ))) :=
    fun l' hl' => Exactness.continuous_real_of_differentiableOn hρ0
      ((hH1 l' hl').2.2.1.comp hK hKD)
  have hEnl : ‖KAM.Iso.energyAverage (𝔥 l) K - (E₀ : ℂ)‖ ≤ e + max L₀ L_E * dist l l₀ := by
    have h1 := norm_energyAverage_sub_param_le (𝔥 l₀) (𝔥 l) K (hHK l₀ hl₀) (hHK l hlS)
      (A := L_E * dist l l₀) fun x => hH l hlS _ (hKD _ (ofReal_mem_complexStrip hρ0 x))
    have h2 : ‖KAM.Iso.energyAverage (𝔥 l) K - (E₀ : ℂ)‖ ≤
        ‖KAM.Iso.energyAverage (𝔥 l) K - KAM.Iso.energyAverage (𝔥 l₀) K‖ +
          ‖KAM.Iso.energyAverage (𝔥 l₀) K - (E₀ : ℂ)‖ := by
      rw [← sub_add_sub_cancel (KAM.Iso.energyAverage (𝔥 l) K) (KAM.Iso.energyAverage (𝔥 l₀) K)]
      exact norm_add_le _ _
    have h3 : L_E * dist l l₀ ≤ max L₀ L_E * dist l l₀ :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hdist
    linarith
  have he0l : 0 ≤ e + max L₀ L_E * dist l l₀ := by positivity
  have hC1l : isoC1 n τ ρ ρinf M σK σB σT μ ν γbar * (e + max L₀ L_E * dist l l₀) /
      (γ ^ 4 * ρ ^ (4 * τ)) < 1 := by
    refine lt_of_le_of_lt ?_ hC1
    have hC := (isoC1_pos (n := n) (τ := τ) (ρinf := ρinf) (M := M) (σK := σK) (σB := σB)
      (σT := σT) (μ := μ) (ν := ν) hρ0 hγbar).le
    have hden : 0 < γ ^ 4 * ρ ^ (4 * τ) := mul_pos (pow_pos hγ 4) (Real.rpow_pos_of_pos hρ0 _)
    have : max L₀ L_E * dist l l₀ ≤ max L₀ L_E * d := mul_le_mul_of_nonneg_left hld hLmax
    gcongr
  obtain ⟨-, -, -, hmain⟩ := KAM.Iso.Apost.g1_explicit hn hτ hρinf hρinfρ hM hσK hσB hσT hμ hγbar
    hσω hν ωstar hωstar
  exact hmain D (𝔥 l) K s γ (e + max L₀ L_E * dist l l₀) E₀ hopen htransl hholo hper hreal hbd hK
    hKp hKr hball hDK hG hTu' hTb' hs1 hsσ hν1 hν2 hγ hγγbar hdio he0l hEl hEnl hC1l

end KAM.Iso.Sharp

end
