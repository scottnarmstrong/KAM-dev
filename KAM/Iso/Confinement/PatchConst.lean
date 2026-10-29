/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Confinement.Setting

/-!
# Part 5: the patch sets, the patch constants and the threshold `ε₀`

Blueprint nodes `bpI:p5:sec-patch`, `bpI:p5:patch-const`, `bpI:p5:eps0`.

* `EnergyPatch.K_eq_image`, `EnergyPatch.isCompact_K`: `𝒦 = Φ⁻¹(Q) = Ψ(Q)` is compact.
* `EnergyPatch.isOpen_Omega`, `EnergyPatch.Omega_subset_K`: `Ω = Φ⁻¹(O)` is open and `Ω ⊆ 𝒦`.
* `patchConst_exists`: the patch constants `r, L_m, L_Φ, κ` of `bpI:p5:patch-const` exist.
* `exists_eps0`: the threshold `ε₀` of `bpI:p5:eps0`, as an existence statement over the finite
  family of patches.
-/

public section

open Set Metric

namespace KAM.Iso.Confinement

open KAM

variable {hR : (Fin 2 → ℝ) → ℝ} {B : Set (Fin 2 → ℝ)} {η₁ : ℝ}

/-! ## The sets `𝒦` and `Ω` -/

/-- `Φ⁻¹(Q)` is the image `Ψ(Q)`. -/
theorem EnergyPatch.K_eq_image (p : EnergyPatch hR B η₁) : p.K = p.Ψ '' p.Q := by
  ext I
  constructor
  · rintro ⟨hIW, hIQ⟩
    exact ⟨_, hIQ, p.Ψ_left I hIW⟩
  · rintro ⟨v, hvQ, rfl⟩
    have hv : v ∈ (fun I => (hR I, p.m I)) '' p.W := p.Q_subset hvQ
    exact ⟨p.Ψ_mem v hv, by rw [p.Ψ_right v hv]; exact hvQ⟩

/-- `Φ⁻¹(Q)` is compact. -/
theorem EnergyPatch.isCompact_K (p : EnergyPatch hR B η₁) : IsCompact p.K := by
  rw [p.K_eq_image]
  have hQ : IsCompact p.Q := isCompact_Icc.prod isCompact_Icc
  exact hQ.image_of_continuousOn (p.Ψ_contDiffOn.continuousOn.mono p.Q_subset)

theorem EnergyPatch.isOpen_Omega (p : EnergyPatch hR B η₁) : IsOpen p.Omega := by
  have hcont : ContinuousOn (fun I => (hR I, p.m I)) p.W :=
    p.hR_contDiffOn.continuousOn.prodMk p.m_contDiffOn.continuousOn
  exact hcont.isOpen_inter_preimage p.isOpen_W (isOpen_Ioo.prod isOpen_Ioo)

theorem EnergyPatch.Omega_subset_K (p : EnergyPatch hR B η₁) : p.Omega ⊆ p.K := by
  rintro I ⟨hIW, hIO⟩
  exact ⟨hIW, Ioo_subset_Icc_self hIO.1, Ioo_subset_Icc_self hIO.2⟩

/-! ## The patch constants -/

/-- `bpI:p5:patch-const`: the constants exist (compactness of `𝒦`, `𝒩`). -/
theorem patchConst_exists (p : EnergyPatch hR B η₁) : ∃ r Lm LΦ κ : ℝ, PatchConst p r Lm LΦ κ := by
  obtain ⟨δ, hδ, hsub⟩ :=
    p.isCompact_K.exists_cthickening_subset_open p.isOpen_W (fun I hI => hI.1)
  have hr_pos : 0 < min δ 1 := lt_min hδ one_pos
  have hthick : cthickening (min δ 1) p.K ⊆ p.W :=
    (cthickening_mono (min_le_left _ _) _).trans hsub
  have hcompN : IsCompact (cthickening (min δ 1) p.K) := p.isCompact_K.cthickening
  have hmcont : ContinuousOn (fderiv ℝ p.m) (cthickening (min δ 1) p.K) :=
    (p.m_contDiffOn.continuousOn_fderiv_of_isOpen p.isOpen_W le_rfl).mono hthick
  obtain ⟨C₁, hC₁⟩ := hcompN.exists_bound_of_continuousOn hmcont
  have hQ : IsCompact p.Q := isCompact_Icc.prod isCompact_Icc
  have hΨcont : ContinuousOn (fderiv ℝ p.Ψ) p.Q :=
    (p.Ψ_contDiffOn.continuousOn_fderiv_of_isOpen p.isOpen_V le_rfl).mono p.Q_subset
  obtain ⟨C₂, hC₂⟩ := hQ.exists_bound_of_continuousOn hΨcont
  have hδm := p.δm_pos
  have hplus := p.mPlus_mem
  have hminus := p.mMinus_mem
  refine ⟨min δ 1, max 1 C₁, max 1 C₂,
    min (p.δm / 4) (min (p.δm - p.mPlus) (p.δm + p.mMinus)), ?_⟩
  exact
    { r_pos := hr_pos
      r_le_one := min_le_right _ _
      thick_subset := hthick
      Lm_ge := le_max_left _ _
      Lm_bound := fun I hI => (hC₁ I hI).trans (le_max_right _ _)
      LΦ_ge := le_max_left _ _
      LΦ_bound := fun v hv => (hC₂ v hv).trans (le_max_right _ _)
      κ_pos := lt_min (by linarith) (lt_min (by linarith [hplus.2]) (by linarith [hminus.1]))
      κ_le_quarter := min_le_left _ _
      κ_le_plus := (min_le_right _ _).trans (min_le_left _ _)
      κ_le_minus := (min_le_right _ _).trans (min_le_right _ _) }

/-! ## The threshold `ε₀` -/

/-- A positive function on a finite set has a positive common lower bound, also below `c`. -/
private theorem exists_pos_le_finite {α : Type*} {S : Set α} (hS : S.Finite) (b : α → ℝ)
    (hb : ∀ a, 0 < b a) {c : ℝ} (hc : 0 < c) :
    ∃ e : ℝ, 0 < e ∧ e ≤ c ∧ ∀ a ∈ S, e ≤ b a := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨c, hc, le_rfl, by simp⟩
  | @insert a s _ _ ih =>
    obtain ⟨e, he, hec, hall⟩ := ih
    refine ⟨min e (b a), lt_min he (hb a), (min_le_left _ _).trans hec, ?_⟩
    intro x hx
    rcases hx with rfl | hx
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hall x hx)

/-- `bpI:p5:eps0`: `ε₀ := min {ε₁, δE/4, ρinf/(8 C_K), r/C_K, κ/(L_m C_K), 1/(2 F₁ L_Φ)}` over the
finitely many patches, as an existence statement (only positivity and the bounds are used). -/
theorem exists_eps0 {patches : Set (EnergyPatch hR B η₁)} (hfin : patches.Finite)
    {ε₁ C_K F₁ ρinf : ℝ} (h₁ : 0 < ε₁) (h₁' : ε₁ ≤ 1) (hC : 0 < C_K) (hF : 0 < F₁) (hρ : 0 < ρinf) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ ε₁ ∧ ∀ p ∈ patches, ∃ r Lm LΦ κ : ℝ, PatchConst p r Lm LΦ κ ∧
      ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ → Smallness p r Lm LΦ κ F₁ C_K ρinf ε := by
  choose r Lm LΦ κ hpc using fun p : EnergyPatch hR B η₁ => patchConst_exists p
  let b : EnergyPatch hR B η₁ → ℝ := fun p =>
    min (p.δE / 4) (min (ρinf / (8 * C_K)) (min (r p / C_K)
      (min (κ p / (Lm p * C_K)) (1 / (2 * F₁ * LΦ p)))))
  have hb : ∀ p, 0 < b p := by
    intro p
    have hL : 0 < Lm p := lt_of_lt_of_le one_pos (hpc p).Lm_ge
    have hΦ : 0 < LΦ p := lt_of_lt_of_le one_pos (hpc p).LΦ_ge
    exact lt_min (by linarith [p.δE_pos]) (lt_min (by positivity) (lt_min
      (div_pos (hpc p).r_pos hC) (lt_min (div_pos (hpc p).κ_pos (by positivity))
        (by positivity))))
  obtain ⟨e, he, hec, hall⟩ := exists_pos_le_finite hfin b hb h₁
  refine ⟨e, he, hec, fun p hp => ⟨r p, Lm p, LΦ p, κ p, hpc p, ?_⟩⟩
  intro ε hε0 hεe
  have hL : 0 < Lm p := lt_of_lt_of_le one_pos (hpc p).Lm_ge
  have hΦ : 0 < LΦ p := lt_of_lt_of_le one_pos (hpc p).LΦ_ge
  have hεb : ε < b p := lt_of_lt_of_le hεe (hall p hp)
  simp only [b, lt_min_iff] at hεb
  obtain ⟨h1, h2, h3, h4, h5⟩ := hεb
  refine ⟨hε0, ?_, by linarith, ?_, ?_, ?_, ?_⟩
  · linarith
  · have := (lt_div_iff₀ (by positivity)).1 h2
    linarith
  · have := (lt_div_iff₀ hC).1 h3
    linarith
  · have := (lt_div_iff₀ (by positivity)).1 h4
    linarith
  · have := (lt_div_iff₀ (by positivity)).1 h5
    linarith

end KAM.Iso.Confinement
