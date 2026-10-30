/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp.Constants
public import KAM.Sharp.ConstantsArith
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Arithmetic of the constants of the sharp isoenergetic theorem

* `iso_consts_pos`: positivity of the isoenergetic constants;
* `iso_step_small` (`stepI:p2s:st-small`): the smallness conditions of an isoenergetic step from
  `𝔠_step X ≤ 1`; the same as `KAM.Sharp.step_small` with the isoenergetic constants (the twist
  constant is `iCDTb`, the bordered one).
-/

public noncomputable section

namespace KAM.Iso.Sharp

open KAM.Sharp

variable {n : ℕ} {κ cR M σK σB σT γb μ ν : ℝ}

/-- Positivity of the isoenergetic constants (`bpI:p2s:constants`). -/
theorem iso_consts_pos (hn : 1 ≤ n) (hcR : 0 < cR) (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB)
    (hσT : 0 < σT) (hγb : 0 < γb) (_hμ : 0 < μ) (_hν : 0 < ν) :
    0 < iCDK n cR M σK σB σT γb ∧ 0 < iCDw n cR M σK σB σT γb ∧ 0 < iCE n cR M σK σB σT γb ∧
      0 < iCDTb n cR M σK σB σT γb ∧ 0 < iCStep n κ cR M σK σB σT γb ∧
      0 < iCSum n cR M σK σB σT γb ∧ 0 < iCStar n κ cR M σK σB σT γb μ ν := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have p1 : 0 < cOm n cR σK := by unfold cOm; positivity
  have p2 : 0 < cSym n cR σK σB := by unfold cSym; positivity
  have p3 : 0 < cT0 n M σK σB := by unfold cT0; positivity
  have p4 : 0 < cT1 n σK σB := by unfold cT1; positivity
  have p5 : 0 < wT n M σK := by unfold wT; positivity
  have p6 : 0 < cT2 n κ cR M σK σB := by unfold cT2; positivity
  have p7 : 0 < hT n M σK σB := by unfold hT; positivity
  have p8 : 0 < cRed n σK σB := by unfold cRed; positivity
  have p9 : 0 < cGram n σK := by unfold cGram vth; positivity
  have p10 : 0 < cB n σK σB := by unfold cB vthh; positivity
  have p11 : 0 < cDab n M σK σB := by unfold cDab vthh; positivity
  have p12 : 0 < cDc n M σK σB := by unfold cDc vthh; positivity
  have o1 : 0 < thetaS n M σK σB := by unfold thetaS; positivity
  have o2 : 0 < iCS n cR M σK σB σT γb := by unfold iCS; positivity
  have o3 : 0 < iCXiN n cR M σK σB σT γb := by unfold iCXiN; positivity
  have o4 : 0 < iCG n cR M σK σB σT γb := by unfold iCG; positivity
  have o5 : 0 < iCDXi n cR M σK σB σT γb := by unfold iCDXi; positivity
  have o6 : 0 < iCXi n cR M σK σB σT γb := by unfold iCXi; positivity
  have o7 : 0 < iCDK n cR M σK σB σT γb := by unfold iCDK; positivity
  have o8 : 0 < iCDw n cR M σK σB σT γb := by unfold iCDw; positivity
  have o9 : 0 < iCP n M σK σB := by unfold iCP; positivity
  have o10 : 0 < iCdK n cR M σK σB σT γb := by unfold iCdK; positivity
  have o11 : 0 < iCLin n cR M σK σB σT γb := by unfold iCLin; positivity
  have o12 : 0 < iCE1 n cR M σK σB σT γb := by unfold iCE1; positivity
  have o13 : 0 < iCE2 n cR M σK σB σT γb := by unfold iCE2; positivity
  have o14 : 0 < iCE n cR M σK σB σT γb := by unfold iCE; positivity
  have o15 : 0 < iCDT n cR M σK σB σT γb := by unfold iCDT vthh; positivity
  have o16 : 0 < iCDTb n cR M σK σB σT γb := by unfold iCDTb vthh; positivity
  have o17 : 0 < iRateD n cR M σK σB σT γb := by unfold iRateD; positivity
  have o18 : 0 < iRateB n cR M σK σB σT γb := by unfold iRateB; positivity
  have o19 : 0 < iRateT n cR M σK σB σT γb := by unfold iRateT vthh; positivity
  have o20 : 0 < iCStep n κ cR M σK σB σT γb := by unfold iCStep; positivity
  have o21 : 0 < iCSum n cR M σK σB σT γb := by unfold iCSum; positivity
  have o22 : 0 < iCStar n κ cR M σK σB σT γb μ ν := by unfold iCStar; positivity
  exact ⟨o7, o8, o14, o16, o20, o21, o22⟩

/-- Nonnegativity of the constants used by `iso_step_small` (no `1 ≤ n` needed). -/
private theorem iso_consts_nonneg (hcR : 0 < cR) (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB)
    (hσT : 0 < σT) (hγb : 0 < γb) :
    0 ≤ cT1 n σK σB ∧ 0 ≤ cT2 n κ cR M σK σB ∧ 0 ≤ cSym n cR σK σB ∧ 0 ≤ cGram n σK ∧
      0 ≤ iCDK n cR M σK σB σT γb ∧ 0 ≤ iCDTb n cR M σK σB σT γb ∧ 0 ≤ iCE n cR M σK σB σT γb ∧
      0 ≤ iRateD n cR M σK σB σT γb := by
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have p1 : 0 ≤ cOm n cR σK := by unfold cOm; positivity
  have p2 : 0 ≤ cSym n cR σK σB := by unfold cSym; positivity
  have p3 : 0 ≤ cT0 n M σK σB := by unfold cT0; positivity
  have p4 : 0 ≤ cT1 n σK σB := by unfold cT1; positivity
  have p5 : 0 ≤ wT n M σK := by unfold wT; positivity
  have p6 : 0 ≤ cT2 n κ cR M σK σB := by unfold cT2; positivity
  have p7 : 0 ≤ hT n M σK σB := by unfold hT; positivity
  have p8 : 0 ≤ cRed n σK σB := by unfold cRed; positivity
  have p9 : 0 ≤ cGram n σK := by unfold cGram vth; positivity
  have p10 : 0 ≤ cB n σK σB := by unfold cB vthh; positivity
  have p11 : 0 ≤ cDab n M σK σB := by unfold cDab vthh; positivity
  have p12 : 0 ≤ cDc n M σK σB := by unfold cDc vthh; positivity
  have o1 : 0 ≤ thetaS n M σK σB := by unfold thetaS; positivity
  have o2 : 0 ≤ iCS n cR M σK σB σT γb := by unfold iCS; positivity
  have o3 : 0 ≤ iCXiN n cR M σK σB σT γb := by unfold iCXiN; positivity
  have o4 : 0 ≤ iCG n cR M σK σB σT γb := by unfold iCG; positivity
  have o5 : 0 ≤ iCDXi n cR M σK σB σT γb := by unfold iCDXi; positivity
  have o6 : 0 ≤ iCXi n cR M σK σB σT γb := by unfold iCXi; positivity
  have o7 : 0 ≤ iCDK n cR M σK σB σT γb := by unfold iCDK; positivity
  have o8 : 0 ≤ iCDw n cR M σK σB σT γb := by unfold iCDw; positivity
  have o9 : 0 ≤ iCP n M σK σB := by unfold iCP; positivity
  have o10 : 0 ≤ iCdK n cR M σK σB σT γb := by unfold iCdK; positivity
  have o11 : 0 ≤ iCLin n cR M σK σB σT γb := by unfold iCLin; positivity
  have o12 : 0 ≤ iCE1 n cR M σK σB σT γb := by unfold iCE1; positivity
  have o13 : 0 ≤ iCE2 n cR M σK σB σT γb := by unfold iCE2; positivity
  have o14 : 0 ≤ iCE n cR M σK σB σT γb := by unfold iCE; positivity
  have o15 : 0 ≤ iCDT n cR M σK σB σT γb := by unfold iCDT vthh; positivity
  have o16 : 0 ≤ iCDTb n cR M σK σB σT γb := by unfold iCDTb vthh; positivity
  have o17 : 0 ≤ iRateD n cR M σK σB σT γb := by unfold iRateD; positivity
  have o18 : 0 ≤ iRateB n cR M σK σB σT γb := by unfold iRateB; positivity
  have o19 : 0 ≤ iRateT n cR M σK σB σT γb := by unfold iRateT vthh; positivity
  have o20 : 0 ≤ iCStep n κ cR M σK σB σT γb := by unfold iCStep; positivity
  have o21 : 0 ≤ iCSum n cR M σK σB σT γb := by unfold iCSum; positivity
  exact ⟨p4, p6, p2, p9, o7, o16, o14, o17⟩

/-- Step `step:p2s:st-small`: the smallness conditions (S1)–(S7) from `𝔠_step X ≤ 1`. -/
theorem iso_step_small {γ δ ε : ℝ} (hκ : 1 ≤ κ) (hcR : 0 < cR) (hM : 0 < M) (hσK : 0 < σK)
    (hσB : 0 < σB) (hσT : 0 < σT) (hγ : 0 < γ) (hγb : γ ≤ γb) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 ≤ ε) (hX : iCStep n κ cR M σK σB σT γb * ε / (γ ^ 4 * δ ^ (2 * (2 * κ))) ≤ 1) :
    ε ≤ δ ∧ cT1 n σK σB * ε / δ + cT2 n κ cR M σK σB * ε / (γ * δ ^ (κ + 1)) ≤ 1 ∧
    cSym n cR σK σB * ε / (γ * δ ^ (κ + 1)) ≤ 1 / 2 ∧
    n * (iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) / δ ≤ vth * σK ∧
    σB * cGram n σK * (iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) / δ ≤ vth ∧
    σT * (iCDTb n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1))) ≤ vth ∧
    iCE n cR M σK σB σT γb * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ))) ≤ ε := by
  obtain ⟨hT1, hT2, hSy, hGr, hDK, hDT, hE, hrD⟩ := iso_consts_nonneg (κ := κ) (n := n) hcR hM hσK
    hσB hσT (hγ.trans_le hγb)
  obtain ⟨-, ⟨-, -, a2c, -⟩, ⟨a3a, a3b, a3c, -⟩, -⟩ := Sharp.absorb hκ hγ hγb hδ hδ1 hε
  have hγb0 : 0 < γb := hγ.trans_le hγb
  have hv : vth = 1 / 8 := rfl
  -- `X = ε/(γ⁴ δ^{2a})`
  have hD : 0 < γ ^ 4 * δ ^ (2 * (2 * κ)) := by positivity
  generalize hXd : ε / (γ ^ 4 * δ ^ (2 * (2 * κ))) = X at a3a a3b a3c
  have hX0 : 0 ≤ X := by rw [← hXd]; positivity
  have hCX : iCStep n κ cR M σK σB σT γb * X ≤ 1 := by
    rw [← hXd]; rwa [mul_div_assoc] at hX
  have b1 : γb ^ 4 * (1 + cT1 n σK σB) + γb ^ 3 * cT2 n κ cR M σK σB ≤
      iCStep n κ cR M σK σB σT γb := le_max_left _ _
  have b2 : 2 * γb ^ 3 * cSym n cR σK σB ≤ iCStep n κ cR M σK σB σT γb :=
    (le_max_left _ _).trans (le_max_right _ _)
  have b3 : γb ^ 2 * iRateD n cR M σK σB σT γb / (vth * σK) ≤ iCStep n κ cR M σK σB σT γb :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have b4 : γb ^ 2 * σB * cGram n σK * iCDK n cR M σK σB σT γb / vth ≤
      iCStep n κ cR M σK σB σT γb :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have b5 : γb ^ 2 * σT * iCDTb n cR M σK σB σT γb / vth ≤ iCStep n κ cR M σK σB σT γb :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))))
  have b6 : iCE n cR M σK σB σT γb ≤ iCStep n κ cR M σK σB σT γb :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))))
  have hr : iRateD n cR M σK σB σT γb = n * iCDK n cR M σK σB σT γb := rfl
  clear hX
  generalize iCStep n κ cR M σK σB σT γb = C at *
  generalize cT1 n σK σB = c1 at *
  generalize cT2 n κ cR M σK σB = c2 at *
  generalize cSym n cR σK σB = c3 at *
  generalize cGram n σK = c4 at *
  generalize iCDK n cR M σK σB σT γb = c5 at *
  generalize iCDTb n cR M σK σB σT γb = c6 at *
  generalize iCE n cR M σK σB σT γb = c7 at *
  generalize iRateD n cR M σK σB σT γb = c8 at *
  have hmul : ∀ {c : ℝ}, c ≤ C → c * X ≤ 1 := fun h =>
    (mul_le_mul_of_nonneg_right h hX0).trans hCX
  have hδ' : δ ^ (2 * κ + 1) = δ ^ (2 * κ) * δ := by rw [Real.rpow_add hδ, Real.rpow_one]
  have hpow2 : 0 < δ ^ (2 * κ) := by positivity
  have hY : ∀ c : ℝ, c * ε / (γ ^ 2 * δ ^ (2 * κ)) / δ = c * (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) := by
    intro c; rw [hδ']; field_simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := hmul b1
    have k1 := mul_nonneg (pow_nonneg hγb0.le 4) (mul_nonneg hT1 hX0)
    have k2 := mul_nonneg (pow_nonneg hγb0.le 3) (mul_nonneg hT2 hX0)
    have : ε / δ ≤ 1 := a3a.trans (by linarith only [h1, k1, k2])
    rwa [div_le_one hδ] at this
  · have h1 := hmul b1
    have e1 : c1 * ε / δ = c1 * (ε / δ) := mul_div_assoc _ _ _
    have e2 : c2 * ε / (γ * δ ^ (κ + 1)) = c2 * (ε / (γ * δ ^ (κ + 1))) := mul_div_assoc _ _ _
    rw [e1, e2]
    have m1 := mul_le_mul_of_nonneg_left a3a hT1
    have m2 := mul_le_mul_of_nonneg_left a3b hT2
    have k0 := mul_nonneg (pow_nonneg hγb0.le 4) hX0
    linarith only [h1, m1, m2, k0]
  · have h1 := hmul b2
    rw [mul_div_assoc]
    have m1 := mul_le_mul_of_nonneg_left a3b hSy
    linarith only [h1, m1]
  · have hs : 0 < vth * σK := by rw [hv]; positivity
    have b3' := (div_le_iff₀ hs).1 b3
    rw [hr] at b3'
    have e : (n : ℝ) * (c5 * ε / (γ ^ 2 * δ ^ (2 * κ))) / δ =
        n * (c5 * (ε / (γ ^ 2 * δ ^ (2 * κ + 1)))) := by
      rw [hδ']; field_simp
    rw [e]
    have s1 : (n : ℝ) * (c5 * (ε / (γ ^ 2 * δ ^ (2 * κ + 1)))) ≤
        (n * c5) * (γb ^ 2 * X) := by
      calc _ = (n * c5) * (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left a3c (by positivity)
    calc _ ≤ _ := s1
      _ = (γb ^ 2 * (n * c5)) * X := by ring
      _ ≤ (C * (vth * σK)) * X :=
        mul_le_mul_of_nonneg_right b3' hX0
      _ = (vth * σK) * (C * X) := by ring
      _ ≤ (vth * σK) * 1 := mul_le_mul_of_nonneg_left hCX hs.le
      _ = vth * σK := mul_one _
  · have hv0 : 0 < vth := by rw [hv]; norm_num
    have b4' := (div_le_iff₀ hv0).1 b4
    have e : σB * c4 * (c5 * ε / (γ ^ 2 * δ ^ (2 * κ))) / δ =
        (σB * c4 * c5) * (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) := by
      rw [hδ']; field_simp
    rw [e]
    have hc : 0 ≤ σB * c4 * c5 := by positivity
    calc _ ≤ (σB * c4 * c5) * (γb ^ 2 * X) :=
          mul_le_mul_of_nonneg_left a3c hc
      _ = (γb ^ 2 * σB * c4 * c5) * X := by ring
      _ ≤ (C * vth) * X := mul_le_mul_of_nonneg_right b4' hX0
      _ = vth * (C * X) := by ring
      _ ≤ vth * 1 := mul_le_mul_of_nonneg_left hCX hv0.le
      _ = vth := mul_one _
  · have hv0 : 0 < vth := by rw [hv]; norm_num
    have b5' := (div_le_iff₀ hv0).1 b5
    rw [mul_div_assoc]
    calc σT * (c6 * (ε / (γ ^ 2 * δ ^ (2 * κ + 1)))) ≤
          σT * (c6 * (γb ^ 2 * X)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left a3c hDT) hσT.le
      _ = (γb ^ 2 * σT * c6) * X := by ring
      _ ≤ (C * vth) * X := mul_le_mul_of_nonneg_right b5' hX0
      _ = vth * (C * X) := by ring
      _ ≤ vth * 1 := mul_le_mul_of_nonneg_left hCX hv0.le
      _ = vth := mul_one _
  · have e : c7 * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ))) =
        ε * (c7 * X) := by
      rw [← hXd]
      exact (fun c D : ℝ => by ring : ∀ c D : ℝ, c * ε ^ 2 / D = ε * (c * (ε / D))) _ _
    rw [e]
    calc ε * (c7 * X) ≤ ε * 1 :=
          mul_le_mul_of_nonneg_left (((mul_le_mul_of_nonneg_right b6 hX0).trans hCX)) hε
      _ = ε := mul_one _

end KAM.Iso.Sharp

end
