/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Defs

/-!
# Soundness of the static sub-check

`checkStatic_sound` reads the `ω`-free static facts (`StaticFacts`) off `checkStatic`;
`checkStatic_freq` gives `ω* ≠ 0` and the two ray margins for every `ω*` in the frequency box,
from the lower bound `freqNormLo box ≤ ‖ω*‖` (`freqNormLo_le_norm`). The structural facts of the
embedding (`TorusCertificate.emb_structural`) are law-free.
-/

public section

namespace KAM.Certificate

open KAM KAM.Torus CertArith

variable {n : ℕ} {α : Type} [CertArith α]

/-- The `ω`-free static facts. -/
structure StaticFacts (c : TorusCertificate n α) : Prop where
  hn : 2 ≤ n
  hτ : (n : ℝ) - 1 ≤ (c.params.tau : ℝ)
  hρinf : (0 : ℝ) < c.params.rhoInf
  hρinfρ : (c.params.rhoInf : ℝ) < c.params.rho
  hM : (0 : ℝ) < c.params.M
  hσK : (0 : ℝ) < c.params.σK
  hσB : (0 : ℝ) < c.params.σB
  hσT : (0 : ℝ) < c.params.σT
  hμ : (0 : ℝ) < c.params.μ
  hγbar : (0 : ℝ) < c.params.γbar
  hσω : (1 : ℝ) < c.params.σω
  hν : (0 : ℝ) < c.params.nuRay
  hs1 : (1 : ℝ) < c.params.s
  hsσ : (c.params.s : ℝ) < c.params.σω
  hγ : (0 : ℝ) < c.params.γ
  hγγbar : (c.params.γ : ℝ) ≤ c.params.γbar
  he0 : (0 : ℝ) ≤ c.params.err
  hrho : c.weight.rho = c.params.rho
  hW : checkWeight c.weight c.expHalvings c.expOrder = true
  hWH : checkWeight c.weightH c.expHalvings c.expOrder = true
  hpe : checkPiEnclosure c.piEnc = true

/-- `freqNormLo` is below any `x ≥ 0` dominating every `|c_i| - r_i`. -/
theorem freqNormLo_le_of_forall (box : FreqBox) {x : ℚ} (h0 : 0 ≤ x)
    (h : ∀ i (hi : i < box.length), |box[i].1| - box[i].2 ≤ x) : freqNormLo box ≤ x := by
  induction box with
  | nil => simpa [freqNormLo] using h0
  | cons b bs ih =>
    have hb := h 0 (by simp)
    have hbs : freqNormLo bs ≤ x :=
      ih fun i hi => by
        have := h (i + 1) (by simp; omega)
        simpa only [List.getElem_cons_succ] using this
    simp only [freqNormLo, List.foldr_cons] at hbs ⊢
    exact max_le (by simpa using hb) hbs

/-- The box's lower bound of the max norm. -/
theorem freqNormLo_le_norm {box : FreqBox} (hlen : box.length = n) {ω : Fin n → ℝ}
    (hω : FreqEncloses n box ω) : (freqNormLo box : ℝ) ≤ ‖ω‖ := by
  rcases le_or_gt (freqNormLo box) 0 with h | h
  · exact (by exact_mod_cast h : (freqNormLo box : ℝ) ≤ 0).trans (norm_nonneg _)
  · -- the maximum is attained or dominated coordinatewise; argue in `ℝ` via a real bound
    have key : ∀ i (hi : i < box.length),
        ((|box[i].1| - box[i].2 : ℚ) : ℝ) ≤ ‖ω‖ := by
      intro i hi
      have hb := hω ⟨i, hlen ▸ hi⟩
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
        Option.getD_some] at hb
      have h1 : |ω ⟨i, hlen ▸ hi⟩| ≤ ‖ω‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm ω ⟨i, hlen ▸ hi⟩
      have h2 := abs_sub_abs_le_abs_sub ((box[i].1 : ℚ) : ℝ) (ω ⟨i, hlen ▸ hi⟩)
      rw [abs_sub_comm] at h2
      have h3 : ((|box[i].1| : ℚ) : ℝ) = |((box[i].1 : ℚ) : ℝ)| := Rat.cast_abs _
      push_cast
      linarith
    -- transfer through a rational approximation from below is unnecessary: compare in `ℝ`
    by_contra hlt
    push Not at hlt
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have hq0 : (0 : ℚ) ≤ q := by
      have : (0 : ℝ) ≤ q := (norm_nonneg ω).trans hq1.le
      exact_mod_cast this
    have : freqNormLo box ≤ q := freqNormLo_le_of_forall box hq0 fun i hi => by
      have := (key i hi).trans hq1.le
      exact_mod_cast this
    have : (freqNormLo box : ℝ) ≤ q := by exact_mod_cast this
    linarith

variable [LawfulCertArith α]

theorem checkStatic_sound {c : TorusCertificate n α} (h : checkStatic c = true) :
    StaticFacts c := by
  simp only [checkStatic, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] at h
  obtain ⟨_, _, _, hn, hτ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    hW, hWH, hpe, _⟩ := h
  exact
    { hn := hn
      hτ := by
        have : ((n : ℕ) : ℝ) ≤ (c.params.tau : ℝ) + 1 := by exact_mod_cast hτ
        linarith
      hρinf := by exact_mod_cast h1
      hρinfρ := by exact_mod_cast h2
      hM := by exact_mod_cast h3
      hσK := by exact_mod_cast h4
      hσB := by exact_mod_cast h5
      hσT := by exact_mod_cast h6
      hμ := by exact_mod_cast h7
      hγbar := by exact_mod_cast h8
      hσω := by exact_mod_cast h9
      hν := by exact_mod_cast h10
      hs1 := by exact_mod_cast h11
      hsσ := by exact_mod_cast h12
      hγ := by exact_mod_cast h13
      hγγbar := by exact_mod_cast h14
      he0 := by exact_mod_cast h15
      hrho := h16
      hW := hW
      hWH := hWH
      hpe := hpe }

/-- The `ω`-dependent static facts, for every `ω` in the box. -/
theorem checkStatic_freq {c : TorusCertificate n α} (h : checkStatic c = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar) :
    ωstar ≠ 0 ∧ (c.params.nuRay : ℝ) ≤ ((c.params.s : ℝ) - 1) * ‖ωstar‖ ∧
      (c.params.nuRay : ℝ) ≤ ((c.params.σω : ℝ) - c.params.s) * ‖ωstar‖ := by
  have hs := checkStatic_sound h
  simp only [checkStatic, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] at h
  obtain ⟨hlen, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hL, hm1,
    hm2⟩ := h
  have hle := freqNormLo_le_norm hlen hω
  have hL' : (0 : ℝ) < freqNormLo c.freqBox := by exact_mod_cast hL
  have hm1' : (c.params.nuRay : ℝ) ≤ ((c.params.s : ℝ) - 1) * freqNormLo c.freqBox := by
    exact_mod_cast hm1
  have hm2' : (c.params.nuRay : ℝ) ≤ ((c.params.σω : ℝ) - c.params.s) * freqNormLo c.freqBox := by
    exact_mod_cast hm2
  have hsa : (0 : ℝ) ≤ (c.params.s : ℝ) - 1 := by linarith [hs.hs1]
  have hsb : (0 : ℝ) ≤ (c.params.σω : ℝ) - c.params.s := by linarith [hs.hsσ]
  refine ⟨fun h0 => ?_, hm1'.trans (mul_le_mul_of_nonneg_left hle hsa),
    hm2'.trans (mul_le_mul_of_nonneg_left hle hsb)⟩
  rw [h0, norm_zero] at hle
  linarith

/-- Structural facts of `K` (law-free). -/
theorem TorusCertificate.emb_structural (c : TorusCertificate n α) :
    DifferentiableOn ℂ c.K (complexStrip n c.params.rho) ∧ IsPrimaryOnStrip c.K c.params.rho ∧
      IsRealOnReals c.K :=
  ⟨(CertEmbedding.differentiable_eval n c.emb).differentiableOn,
    CertEmbedding.isPrimaryOnStrip n c.emb _, CertEmbedding.isRealOnReals n c.emb⟩

end KAM.Certificate
