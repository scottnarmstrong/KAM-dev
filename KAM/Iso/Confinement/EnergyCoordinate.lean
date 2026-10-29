/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Confinement.RealHam

/-!
# Part 5: the energy coordinate

Blueprint `bpI:p5:energy-coordinate`, steps `ec-reduce` and `ec-lip`.

* `energy_coordinate`: on the chart window `Q`, over a fixed slope `m`, the energy
  `H_ℝ(φ, Φ⁻¹(·, m))` is injective as a function of the chart energy `e = h(I)` (this is where
  the smallness `2 F₁ L_Φ ε < 1` of `Smallness` enters).

Proof. By `Ψ_right`, `h(Ψ(e, m)) = e`, hence
`H_ℝ(φ, Ψ(e, m)) = e + Re f(ι φ, ι Ψ(e, m))` (`ec-reduce`). The map
`e ↦ Re f(ι φ, ι Ψ(e, m))` has derivative of norm `≤ F₁ ε L_Φ < 1/2` on the interval
`[E_c - δ_E, E_c + δ_E]` (`realHam_fderiv_bound` and the chain rule through the `C¹` chart inverse
`Ψ`), so it is `1/2`-Lipschitz there (mean value theorem), and equal energies force equal chart
energies (`ec-lip`).
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Iso.Confinement

open KAM

section EnergyCoordinate

variable {B : Set (Fin 2 → ℝ)} {s₀ r₀ : ℝ} {h : (Fin 2 → ℂ) → ℂ}
  {f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {ε : ℝ} {η₁ : ℝ}

/-- `H_ℝ(φ, I) = Re h(ι I) + Re f(ι φ, ι I)` (`ec-reduce`, values). -/
private theorem realHamiltonian_eq_add (φ I : Fin 2 → ℝ) :
    realHamiltonian h f (φ, I) = realPart h I + (f (toC φ, toC I)).re :=
  Complex.add_re _ _

/-- The first chart coordinate of `Ψ (e, m)` is `e` on the window `Q` (`Ψ_right`). -/
private theorem realPart_Ψ (p : EnergyPatch (realPart h) B η₁) {e m : ℝ} (hv : (e, m) ∈ p.Q) :
    realPart h (p.Ψ (e, m)) = e :=
  congrArg Prod.fst (p.Ψ_right (e, m) (p.Q_subset hv))

/-- `ec-lip`, one point: `x ↦ Re f(ι φ, ι Ψ(x, m))` has a derivative of norm at most
`F₁ ε L_Φ` at every `(e, m) ∈ Q`. -/
private theorem hasDerivAt_fReal_Ψ (hb : BaseData B s₀ r₀ h) (hf : PerturbData B s₀ r₀ f ε)
    (p : EnergyPatch (realPart h) B η₁) {LΦ F₁ : ℝ} (hΦ : ∀ v ∈ p.Q, ‖fderiv ℝ p.Ψ v‖ ≤ LΦ)
    (hD : ∀ z ∈ fractD B s₀ r₀, ‖fderiv ℂ f z‖ ≤ F₁ * ε) (φ : Fin 2 → ℝ) {e m : ℝ}
    (hv : (e, m) ∈ p.Q) :
    ∃ d : ℝ, HasDerivAt (fun x : ℝ => (f (toC φ, toC (p.Ψ (x, m)))).re) d e ∧
      ‖d‖ ≤ F₁ * ε * LΦ := by
  have hvV : (e, m) ∈ (fun I => (realPart h I, p.m I)) '' p.W := p.Q_subset hv
  have hΨd : HasFDerivAt p.Ψ (fderiv ℝ p.Ψ (e, m)) (e, m) :=
    ((p.Ψ_contDiffOn.contDiffAt (p.isOpen_V.mem_nhds hvV)).differentiableAt
      (by simp)).hasFDerivAt
  have hγ : HasDerivAt (fun x : ℝ => (x, m)) ((1 : ℝ), (0 : ℝ)) e :=
    (hasDerivAt_id e).prodMk (hasDerivAt_const e m)
  have hΨγ : HasDerivAt (fun x : ℝ => p.Ψ (x, m)) (fderiv ℝ p.Ψ (e, m) (1, 0)) e :=
    hΨd.comp_hasDerivAt e hγ
  have hIB : p.Ψ (e, m) ∈ B := p.W_subset_B (p.Ψ_mem _ hvV)
  obtain ⟨hdiff, hbd⟩ := realHam_fderiv_bound hb hf hD φ hIB
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt e hΨγ
  refine ⟨_, hcomp, ?_⟩
  have h10 : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  calc ‖fderiv ℝ (fun x : Fin 2 → ℝ => (f (toC φ, toC x)).re) (p.Ψ (e, m))
        (fderiv ℝ p.Ψ (e, m) (1, 0))‖
      ≤ ‖fderiv ℝ (fun x : Fin 2 → ℝ => (f (toC φ, toC x)).re) (p.Ψ (e, m))‖ *
        ‖fderiv ℝ p.Ψ (e, m) (1, 0)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (F₁ * ε) * (LΦ * 1) := by
        refine mul_le_mul hbd ?_ (norm_nonneg _) ((norm_nonneg _).trans hbd)
        calc ‖fderiv ℝ p.Ψ (e, m) (1, 0)‖ ≤ ‖fderiv ℝ p.Ψ (e, m)‖ * ‖((1 : ℝ), (0 : ℝ))‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ LΦ * 1 := by
              rw [h10]
              exact mul_le_mul_of_nonneg_right (hΦ _ hv) zero_le_one
    _ = F₁ * ε * LΦ := by ring

/-- `bpI:p5:energy-coordinate`: on `Q`, over a fixed slope `m`, `H_ℝ(φ, Φ⁻¹(·, m))` is injective
(`ε ≤ min {1, 1/(2 F₁ L_Φ)}`, here through `Smallness`). -/
theorem energy_coordinate (hb : BaseData B s₀ r₀ h) (hf : PerturbData B s₀ r₀ f ε)
    (p : EnergyPatch (realPart h) B η₁) {r Lm LΦ κ F₁ C_K : ℝ} (pc : PatchConst p r Lm LΦ κ)
    (hsm : Smallness p r Lm LΦ κ F₁ C_K (rhoInf s₀) ε)
    (hD : ∀ z ∈ fractD B s₀ r₀, ‖fderiv ℂ f z‖ ≤ F₁ * ε) (φ : Fin 2 → ℝ) {e₁ e₂ m : ℝ}
    (h₁ : (e₁, m) ∈ p.Q) (h₂ : (e₂, m) ∈ p.Q)
    (heq : realHamiltonian h f (φ, p.Ψ (e₁, m)) = realHamiltonian h f (φ, p.Ψ (e₂, m))) :
    p.Ψ (e₁, m) = p.Ψ (e₂, m) := by
  -- `ec-lip`: mean value theorem for `g x = Re f(ι φ, ι Ψ(x, m))` on the energy interval
  set S : Set ℝ := Icc (realPart h p.c - p.δE) (realPart h p.c + p.δE)
  have hQ : ∀ e ∈ S, (e, m) ∈ p.Q := fun e he => ⟨he, h₁.2⟩
  choose! d hd hdb using fun e (he : e ∈ S) =>
    hasDerivAt_fReal_Ψ hb hf p pc.LΦ_bound hD φ (hQ e he)
  have hmvt := (convex_Icc (realPart h p.c - p.δE) (realPart h p.c + p.δE)
    ).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hd x hx).hasDerivWithinAt) hdb h₂.1 h₁.1
  -- `ec-reduce`: `H_ℝ(φ, Ψ(e, m)) = e + g e`
  rw [realHamiltonian_eq_add, realHamiltonian_eq_add, realPart_Ψ p h₁, realPart_Ψ p h₂] at heq
  have hC : F₁ * ε * LΦ < 1 / 2 := by
    have := hsm.lt_Phi
    linarith
  have habs : |e₁ - e₂| ≤ F₁ * ε * LΦ * |e₁ - e₂| := by
    have hdiff : |e₁ - e₂| = |(f (toC φ, toC (p.Ψ (e₁, m)))).re -
        (f (toC φ, toC (p.Ψ (e₂, m)))).re| := by
      rw [← abs_neg]
      congr 1
      linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
    exact hdiff.le.trans hmvt
  have h0 : |e₁ - e₂| = 0 := by
    have hnn := mul_nonneg (sub_nonneg.2 hC.le) (abs_nonneg (e₁ - e₂))
    have := abs_nonneg (e₁ - e₂)
    nlinarith
  have he : e₁ = e₂ := sub_eq_zero.1 (abs_eq_zero.1 h0)
  rw [he]

end EnergyCoordinate

end KAM.Iso.Confinement
