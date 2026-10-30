/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.Constants
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Arithmetic of the constants of the sharp fixed-frequency theorem

* `consts_pos`: positivity of the constants (`bp:p2s:constants`);
* `absorb` (`bp:p2s:absorb`): the absorption of the Diophantine constant through `γ ≤ γ̄`;
* `step_small` (`step:p2s:st-small`): the smallness conditions (S1)–(S7) of a Newton step from the
  single condition `𝔠_step X ≤ 1`, `X = ε/(γ⁴ δ^{2a})`, `a = 2κ`.
-/

public noncomputable section

namespace KAM.Sharp

variable {n : ℕ} {κ cR M σK σB σT γb μ : ℝ}

/-- Positivity of the constants (`bp:p2s:constants`). -/
theorem consts_pos (hn : 1 ≤ n) (hcR : 0 < cR) (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB)
    (hσT : 0 < σT) (hγb : 0 < γb) (_hμ : 0 < μ) :
    0 < cDK n cR M σK σB σT γb ∧ 0 < cE n cR M σK σB σT γb ∧ 0 < cB n σK σB ∧
      0 < cDT n cR M σK σB σT γb ∧ 0 < cStep n κ cR M σK σB σT γb ∧
      0 < cSum n cR M σK σB σT γb ∧ 0 < cStar n κ cR M σK σB σT γb μ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : 0 < cOm n cR σK := by unfold cOm; positivity
  have h2 : 0 < cSym n cR σK σB := by unfold cSym; positivity
  have h4 : 0 < cT0 n M σK σB := by unfold cT0; positivity
  have h5 : 0 < cT1 n σK σB := by unfold cT1; positivity
  have h6 : 0 < wT n M σK := by unfold wT; positivity
  have h7 : 0 < cT2 n κ cR M σK σB := by unfold cT2; positivity
  have h8 : 0 < hT n M σK σB := by unfold hT; positivity
  have h9 : 0 < cXi0 n cR M σK σB σT γb := by unfold cXi0; positivity
  have h10 : 0 < cXiN n cR M σK σB σT γb := by unfold cXiN; positivity
  have h11 : 0 < cG n cR M σK σB σT γb := by unfold cG; positivity
  have h12 : 0 < cDXi n cR M σK σB σT γb := by unfold cDXi; positivity
  have h13 : 0 < cXi n cR M σK σB σT γb := by unfold cXi; positivity
  have h14 : 0 < cDK n cR M σK σB σT γb := by unfold cDK; positivity
  have h15 : 0 < cRed n σK σB := by unfold cRed; positivity
  have h16 : 0 < cLin n cR M σK σB σT γb := by unfold cLin; positivity
  have h17 : 0 < cE n cR M σK σB σT γb := by unfold cE; positivity
  have h18 : 0 < cGram n σK := by unfold cGram vth; positivity
  have h19 : 0 < cB n σK σB := by unfold cB vthh; positivity
  have h20 : 0 < cDab n M σK σB := by unfold cDab vthh; positivity
  have h21 : 0 < cDc n M σK σB := by unfold cDc vthh; positivity
  have h22 : 0 < cDT n cR M σK σB σT γb := by unfold cDT vthh; positivity
  have h23 : 0 < rateD n cR M σK σB σT γb := by unfold rateD; positivity
  have h24 : 0 < rateB n cR M σK σB σT γb := by unfold rateB; positivity
  have h25 : 0 < rateT n cR M σK σB σT γb := by unfold rateT vthh; positivity
  have h26 : 0 < cStep n κ cR M σK σB σT γb := by unfold cStep; positivity
  have h27 : 0 < cSum n cR M σK σB σT γb := by unfold cSum; positivity
  exact ⟨h14, h17, h19, h22, h26, h27, by unfold cStar; positivity⟩

/-- Nonnegativity of the constants used by `step_small` (no `1 ≤ n` needed). -/
private theorem consts_nonneg (hcR : 0 < cR) (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB)
    (hσT : 0 < σT) (hγb : 0 < γb) :
    0 ≤ cT1 n σK σB ∧ 0 ≤ cT2 n κ cR M σK σB ∧ 0 ≤ cSym n cR σK σB ∧ 0 ≤ cGram n σK ∧
      0 ≤ cDK n cR M σK σB σT γb ∧ 0 ≤ cDT n cR M σK σB σT γb ∧ 0 ≤ cE n cR M σK σB σT γb ∧
      0 ≤ rateD n cR M σK σB σT γb := by
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : 0 ≤ cOm n cR σK := by unfold cOm; positivity
  have h2 : 0 ≤ cSym n cR σK σB := by unfold cSym; positivity
  have h4 : 0 ≤ cT0 n M σK σB := by unfold cT0; positivity
  have h5 : 0 ≤ cT1 n σK σB := by unfold cT1; positivity
  have h6 : 0 ≤ wT n M σK := by unfold wT; positivity
  have h7 : 0 ≤ cT2 n κ cR M σK σB := by unfold cT2; positivity
  have h8 : 0 ≤ hT n M σK σB := by unfold hT; positivity
  have h9 : 0 ≤ cXi0 n cR M σK σB σT γb := by unfold cXi0; positivity
  have h10 : 0 ≤ cXiN n cR M σK σB σT γb := by unfold cXiN; positivity
  have h11 : 0 ≤ cG n cR M σK σB σT γb := by unfold cG; positivity
  have h12 : 0 ≤ cDXi n cR M σK σB σT γb := by unfold cDXi; positivity
  have h13 : 0 ≤ cXi n cR M σK σB σT γb := by unfold cXi; positivity
  have h14 : 0 ≤ cDK n cR M σK σB σT γb := by unfold cDK; positivity
  have h15 : 0 ≤ cRed n σK σB := by unfold cRed; positivity
  have h16 : 0 ≤ cLin n cR M σK σB σT γb := by unfold cLin; positivity
  have h17 : 0 ≤ cE n cR M σK σB σT γb := by unfold cE; positivity
  have h18 : 0 ≤ cGram n σK := by unfold cGram vth; positivity
  have h19 : 0 ≤ cB n σK σB := by unfold cB vthh; positivity
  have h20 : 0 ≤ cDab n M σK σB := by unfold cDab vthh; positivity
  have h21 : 0 ≤ cDc n M σK σB := by unfold cDc vthh; positivity
  have h22 : 0 ≤ cDT n cR M σK σB σT γb := by unfold cDT vthh; positivity
  have h23 : 0 ≤ rateD n cR M σK σB σT γb := by unfold rateD; positivity
  have h24 : 0 ≤ rateB n cR M σK σB σT γb := by unfold rateB; positivity
  have h25 : 0 ≤ rateT n cR M σK σB σT γb := by unfold rateT vthh; positivity
  have h26 : 0 ≤ cStep n κ cR M σK σB σT γb := by unfold cStep; positivity
  have h27 : 0 ≤ cSum n cR M σK σB σT γb := by unfold cSum; positivity
  exact ⟨h5, h7, h2, h18, h14, h22, h17, h23⟩

/-- `E/D₁ ≤ c · (E/D₂)` as soon as `D₂ ≤ c D₁`. -/
private theorem div_le_mul_div {E D₁ D₂ c : ℝ} (hE : 0 ≤ E) (h₁ : 0 < D₁) (h₂ : 0 < D₂)
    (h : D₂ ≤ c * D₁) : E / D₁ ≤ c * (E / D₂) := by
  rw [← mul_div_assoc, div_le_div_iff₀ h₁ h₂]
  nlinarith [mul_le_mul_of_nonneg_left h hE]

/-- `δ^(m κ) = (δ^κ)^m`. -/
private theorem rpow_nat_mul' {δ : ℝ} (hδ : 0 < δ) (κ : ℝ) (m : ℕ) :
    δ ^ ((m : ℝ) * κ) = (δ ^ κ) ^ m := by
  rw [mul_comm, Real.rpow_mul hδ.le, Real.rpow_natCast]

/-- Blueprint `bp:p2s:absorb` (`a = 2κ`). -/
theorem absorb {γ δ ε : ℝ} (hκ : 1 ≤ κ) (hγ : 0 < γ) (hγb : γ ≤ γb) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 ≤ ε) :
    (ε ≤ γb * (ε / (γ * δ ^ κ)) ∧ ε / (γ * δ ^ κ) ≤ γb * (ε / (γ ^ 2 * δ ^ (2 * κ)))) ∧
    (ε ≤ γb ^ 2 * (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) ∧
      ε / δ ≤ γb ^ 2 * (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) ∧
      ε / (γ * δ ^ (κ + 1)) ≤ γb * (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) ∧
      ε / (γ ^ 2 * δ ^ (2 * κ)) ≤ ε / (γ ^ 2 * δ ^ (2 * κ + 1))) ∧
    (ε / δ ≤ γb ^ 4 * (ε / (γ ^ 4 * δ ^ (2 * (2 * κ)))) ∧
      ε / (γ * δ ^ (κ + 1)) ≤ γb ^ 3 * (ε / (γ ^ 4 * δ ^ (2 * (2 * κ)))) ∧
      ε / (γ ^ 2 * δ ^ (2 * κ + 1)) ≤ γb ^ 2 * (ε / (γ ^ 4 * δ ^ (2 * (2 * κ)))) ∧
      ε / (γ ^ 2 * δ ^ (2 * κ)) ≤ γb ^ 2 * (ε / (γ ^ 4 * δ ^ (2 * (2 * κ))))) ∧
    (ε ^ 2 / (γ ^ 2 * δ ^ (2 * κ + 1)) ≤ γb ^ 2 * (ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ)))) ∧
      ε ^ 2 / (γ ^ 3 * δ ^ (3 * κ)) ≤ γb * (ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ)))) ∧
      ε ^ 2 / (γ ^ 3 * δ ^ (3 * κ + 1)) ≤ γb * (ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ))))) := by
  set s := δ ^ κ with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hδ κ
  have hsδ : s ≤ δ := by
    calc s = δ ^ κ := rfl
      _ ≤ δ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hκ
      _ = δ := Real.rpow_one δ
  have hs1 : s ≤ 1 := hsδ.trans hδ1
  have e2 : δ ^ (2 * κ) = s ^ 2 := by simpa using rpow_nat_mul' hδ κ 2
  have e3 : δ ^ (3 * κ) = s ^ 3 := by simpa using rpow_nat_mul' hδ κ 3
  have e4 : δ ^ (2 * (2 * κ)) = s ^ 4 := by
    rw [← mul_assoc]; norm_num; simpa using rpow_nat_mul' hδ κ 4
  have e21 : δ ^ (2 * κ + 1) = s ^ 2 * δ := by
    rw [Real.rpow_add hδ, e2, Real.rpow_one]
  have e31 : δ ^ (3 * κ + 1) = s ^ 3 * δ := by
    rw [Real.rpow_add hδ, e3, Real.rpow_one]
  have e11 : δ ^ (κ + 1) = s * δ := by
    rw [Real.rpow_add hδ, Real.rpow_one]
  rw [e2, e3, e4, e21, e31, e11]
  have hγb0 : 0 < γb := hγ.trans_le hγb
  -- p = γ s
  set p := γ * s with hp
  have hp0 : 0 < p := mul_pos hγ hs0
  have hpb : p ≤ γb * δ := by
    calc p = γ * s := rfl
      _ ≤ γb * δ := mul_le_mul hγb hsδ hs0.le hγb0.le
  have hpb' : p ≤ γb := hpb.trans (by nlinarith)
  have hp2 : p ^ 2 ≤ γb ^ 2 * δ := by
    calc p ^ 2 = p * p := by ring
      _ ≤ (γb * δ) * γb := mul_le_mul hpb hpb' hp0.le (by positivity)
      _ = γb ^ 2 * δ := by ring
  have hp3 : p ^ 3 ≤ γb ^ 3 * δ := by
    calc p ^ 3 = p ^ 2 * p := by ring
      _ ≤ (γb ^ 2 * δ) * γb := mul_le_mul hp2 hpb' hp0.le (by positivity)
      _ = γb ^ 3 * δ := by ring
  have hp4 : p ^ 4 ≤ γb ^ 4 * δ := by
    calc p ^ 4 = p ^ 3 * p := by ring
      _ ≤ (γb ^ 3 * δ) * γb := mul_le_mul hp3 hpb' hp0.le (by positivity)
      _ = γb ^ 4 * δ := by ring
  have hε2 : 0 ≤ ε ^ 2 := sq_nonneg ε
  have q2 : γ ^ 2 * s ^ 2 = p ^ 2 := by rw [hp]; ring
  have q3 : γ ^ 3 * s ^ 3 = p ^ 3 := by rw [hp]; ring
  have q4 : γ ^ 4 * s ^ 4 = p ^ 4 := by rw [hp]; ring
  have r21 : γ ^ 2 * (s ^ 2 * δ) = p ^ 2 * δ := by rw [hp]; ring
  have r31 : γ ^ 3 * (s ^ 3 * δ) = p ^ 3 * δ := by rw [hp]; ring
  have r11 : γ * (s * δ) = p * δ := by rw [hp]; ring
  rw [q2, q3, q4, r21, r31, r11]
  have hpd : 0 < p * δ := mul_pos hp0 hδ
  have hp2d : 0 < p ^ 2 * δ := by positivity
  have hp3d : 0 < p ^ 3 * δ := by positivity
  have P : ∀ {E D₁ D₂ c : ℝ}, 0 ≤ E → 0 < D₁ → 0 < D₂ → D₂ ≤ c * D₁ → E / D₁ ≤ c * (E / D₂) :=
    fun hE h₁ h₂ h => div_le_mul_div hE h₁ h₂ h
  clear_value p s
  have hε1 : ε = ε / 1 := (div_one ε).symm
  have hq2 : p ^ 2 ≤ γb ^ 2 := hp2.trans (mul_le_of_le_one_right (by positivity) hδ1)
  have hp2n : 0 ≤ p ^ 2 := by positivity
  have hp3n : 0 ≤ p ^ 3 := by positivity
  have P : ∀ {E D₁ D₂ c : ℝ}, 0 ≤ E → 0 < D₁ → 0 < D₂ → D₂ ≤ c * D₁ → E / D₁ ≤ c * (E / D₂) :=
    fun hE h₁ h₂ h => div_le_mul_div hE h₁ h₂ h
  have c1 : p ≤ γb * 1 := by rw [mul_one]; exact hpb'
  have c2 : p ^ 2 ≤ γb * p := by rw [sq]; exact mul_le_mul_of_nonneg_right hpb' hp0.le
  have c3 : p ^ 2 * δ ≤ γb ^ 2 * 1 :=
    (mul_le_of_le_one_right hp2n hδ1).trans (by rw [mul_one]; exact hq2)
  have c4 : p ^ 2 * δ ≤ γb ^ 2 * δ := mul_le_mul_of_nonneg_right hq2 hδ.le
  have c5 : p ^ 2 * δ ≤ γb * (p * δ) :=
    calc p ^ 2 * δ = p * (p * δ) := by ring
      _ ≤ γb * (p * δ) := mul_le_mul_of_nonneg_right hpb' hpd.le
  have c6 : p ^ 2 * δ ≤ 1 * p ^ 2 := by rw [one_mul]; exact mul_le_of_le_one_right hp2n hδ1
  have c7 : p ^ 4 ≤ γb ^ 3 * (p * δ) :=
    calc p ^ 4 = p * p ^ 3 := by ring
      _ ≤ p * (γb ^ 3 * δ) := mul_le_mul_of_nonneg_left hp3 hp0.le
      _ = γb ^ 3 * (p * δ) := by ring
  have c8 : p ^ 4 ≤ γb ^ 2 * (p ^ 2 * δ) :=
    calc p ^ 4 = p ^ 2 * p ^ 2 := by ring
      _ ≤ p ^ 2 * (γb ^ 2 * δ) := mul_le_mul_of_nonneg_left hp2 hp2n
      _ = γb ^ 2 * (p ^ 2 * δ) := by ring
  have c9 : p ^ 4 ≤ γb ^ 2 * p ^ 2 :=
    calc p ^ 4 = p ^ 2 * p ^ 2 := by ring
      _ ≤ γb ^ 2 * p ^ 2 := mul_le_mul_of_nonneg_right hq2 hp2n
  have c10 : p ^ 4 ≤ γb * p ^ 3 :=
    calc p ^ 4 = p * p ^ 3 := by ring
      _ ≤ γb * p ^ 3 := mul_le_mul_of_nonneg_right hpb' hp3n
  have c11 : p ^ 4 ≤ γb * (p ^ 3 * δ) :=
    calc p ^ 4 = p * p ^ 3 := by ring
      _ ≤ (γb * δ) * p ^ 3 := mul_le_mul_of_nonneg_right hpb hp3n
      _ = γb * (p ^ 3 * δ) := by ring
  have hp4' : p ^ 4 ≤ γb ^ 4 * δ := hp4
  have a1 := P (c := γb) hε zero_lt_one hp0 c1
  rw [← hε1] at a1
  have a2 := P (c := γb ^ 2) hε zero_lt_one hp2d c3
  rw [← hε1] at a2
  exact ⟨⟨a1, P hε hp0 (by positivity) c2⟩,
    ⟨a2, P hε hδ hp2d c4, P hε hpd hp2d c5, by simpa using P hε (by positivity) hp2d c6⟩,
    ⟨P hε hδ (by positivity) hp4', P hε hpd (by positivity) c7, P hε hp2d (by positivity) c8,
      P hε (by positivity) (by positivity) c9⟩,
    ⟨P hε2 hp2d (by positivity) c8, P hε2 (by positivity) (by positivity) c10,
      P hε2 hp3d (by positivity) c11⟩⟩

/-- Step `step:p2s:st-small`: the smallness conditions (S1)–(S7) from `𝔠_step X ≤ 1`. -/
theorem step_small {γ δ ε : ℝ} (hκ : 1 ≤ κ) (hcR : 0 < cR) (hM : 0 < M) (hσK : 0 < σK)
    (hσB : 0 < σB) (hσT : 0 < σT) (hγ : 0 < γ) (hγb : γ ≤ γb) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 ≤ ε) (hX : cStep n κ cR M σK σB σT γb * ε / (γ ^ 4 * δ ^ (2 * (2 * κ))) ≤ 1) :
    ε ≤ δ ∧ cT1 n σK σB * ε / δ + cT2 n κ cR M σK σB * ε / (γ * δ ^ (κ + 1)) ≤ 1 ∧
    cSym n cR σK σB * ε / (γ * δ ^ (κ + 1)) ≤ 1 / 2 ∧
    n * (cDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) / δ ≤ vth * σK ∧
    σB * cGram n σK * (cDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) / δ ≤ vth ∧
    σT * (cDT n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ + 1))) ≤ vth ∧
    cE n cR M σK σB σT γb * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ))) ≤ ε := by
  obtain ⟨hT1, hT2, hSy, hGr, hDK, hDT, hE, hrD⟩ := consts_nonneg (κ := κ) (n := n) hcR hM hσK
    hσB hσT (hγ.trans_le hγb)
  obtain ⟨-, ⟨-, -, a2c, -⟩, ⟨a3a, a3b, a3c, -⟩, -⟩ := absorb hκ hγ hγb hδ hδ1 hε
  have hγb0 : 0 < γb := hγ.trans_le hγb
  have hv : vth = 1 / 8 := rfl
  -- `X = ε/(γ⁴ δ^{2a})`
  have hD : 0 < γ ^ 4 * δ ^ (2 * (2 * κ)) := by positivity
  generalize hXd : ε / (γ ^ 4 * δ ^ (2 * (2 * κ))) = X at a3a a3b a3c
  have hX0 : 0 ≤ X := by rw [← hXd]; positivity
  have hCX : cStep n κ cR M σK σB σT γb * X ≤ 1 := by
    rw [← hXd]; rwa [mul_div_assoc] at hX
  have b1 : γb ^ 4 * (1 + cT1 n σK σB) + γb ^ 3 * cT2 n κ cR M σK σB ≤
      cStep n κ cR M σK σB σT γb := le_max_left _ _
  have b2 : 2 * γb ^ 3 * cSym n cR σK σB ≤ cStep n κ cR M σK σB σT γb :=
    (le_max_left _ _).trans (le_max_right _ _)
  have b3 : γb ^ 2 * rateD n cR M σK σB σT γb / (vth * σK) ≤ cStep n κ cR M σK σB σT γb :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have b4 : γb ^ 2 * σB * cGram n σK * cDK n cR M σK σB σT γb / vth ≤
      cStep n κ cR M σK σB σT γb :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have b5 : γb ^ 2 * σT * cDT n cR M σK σB σT γb / vth ≤ cStep n κ cR M σK σB σT γb :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))))
  have b6 : cE n cR M σK σB σT γb ≤ cStep n κ cR M σK σB σT γb :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))))
  have hr : rateD n cR M σK σB σT γb = n * cDK n cR M σK σB σT γb := rfl
  clear hX
  generalize cStep n κ cR M σK σB σT γb = C at *
  generalize cT1 n σK σB = c1 at *
  generalize cT2 n κ cR M σK σB = c2 at *
  generalize cSym n cR σK σB = c3 at *
  generalize cGram n σK = c4 at *
  generalize cDK n cR M σK σB σT γb = c5 at *
  generalize cDT n cR M σK σB σT γb = c6 at *
  generalize cE n cR M σK σB σT γb = c7 at *
  generalize rateD n cR M σK σB σT γb = c8 at *
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

end KAM.Sharp

end
