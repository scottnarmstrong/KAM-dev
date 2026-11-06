/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Ecc.Center
public import KAM.EffectiveStability.Tube.Ecc.Gamma

/-!
# Soundness of the eccentricity checker (T2-CONF, N6)

* `leafOK_sound`: a passing leaf certifies its box (`BoxGood`): at every chart point of the box and
  every `I` within `r` of the centre there, `Glo_j ≤ |z_j|² ≤ Ghi_j`.
* `checkTree_sound`: a passing tree certifies its box.
* `eccGamma_bounds_of_check`: **the generic enclosure.** If `globalOK d` holds and the four chart
  trees pass, then for every `φ` and every `I` with `|I_k - B_k(φ)| ≤ r`,
  `Glo_j ≤ Γ_j(I, φ) ≤ Ghi_j`.
-/

@[expose] public section

open Complex

namespace KAM.EffectiveStability.Tube

/-- The chart point `± wt t`. -/
noncomputable def chartPt (s : Bool) (t : ℝ) : ℂ := ((sgnQ s : ℚ) : ℂ) * wt t

theorem norm_sgnQ (s : Bool) : ‖((sgnQ s : ℚ) : ℂ)‖ = 1 := by
  rw [show (((sgnQ s : ℚ) : ℂ)) = (((sgnQ s : ℚ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
    Real.norm_eq_abs, abs_sgnQ]

theorem norm_chartPt (s : Bool) (t : ℝ) : ‖chartPt s t‖ = 1 := by
  rw [chartPt, norm_mul, norm_sgnQ, norm_wt, one_mul]

theorem norm_toC_circPt (s : Bool) (t : ℚ) : ‖GQ.toC (circPt s t)‖ = 1 := by
  rw [toC_circPt, norm_mul, norm_sgnQ, norm_wt, one_mul]

/-- What a box certifies: at every chart point of the box and every `I` within `r` of the centre
there, `Glo_j ≤ |z_j|² ≤ Ghi_j`. -/
def BoxGood (d : EccData) (b : EBox) : Prop :=
  ∀ t₁ t₂ : ℝ, (b.lo₁ : ℝ) ≤ t₁ → t₁ ≤ b.hi₁ → (b.lo₂ : ℝ) ≤ t₂ → t₂ ≤ b.hi₂ →
    ∀ I : Fin 3 → ℝ,
      (∀ k, |I k - tubeCenterW d.modes d.Ibar k (chartPt b.s₁ t₁) (chartPt b.s₂ t₂)| ≤ d.r) →
      ∀ j, (d.Glo j : ℝ) ≤
          Complex.normSq (zW d.V (fun k => Real.sqrt (I k)) (chartPt b.s₁ t₁) (chartPt b.s₂ t₂) j) ∧
        Complex.normSq (zW d.V (fun k => Real.sqrt (I k)) (chartPt b.s₁ t₁) (chartPt b.s₂ t₂) j) ≤
          d.Ghi j

/-! ### The cell geometry -/

/-- On a parameter interval: `|t - t_c| ≤ h`, the chart remainder is at most `cellRho` and the
chord at most `cellEps`. -/
theorem cell_geom (s : Bool) (lo hi : ℚ) (t : ℝ) (hl : (lo : ℝ) ≤ t) (hh : t ≤ hi) :
    |t - (cellT lo hi : ℝ)| ≤ (cellH lo hi : ℝ) ∧
      ‖chartPt s t - GQ.toC (circPt s (cellT lo hi)) -
          ((t - (cellT lo hi : ℝ) : ℝ) : ℂ) * GQ.toC (circDer s (cellT lo hi))‖ ≤
        (cellRho lo hi : ℝ) ∧
      ‖chartPt s t - GQ.toC (circPt s (cellT lo hi))‖ ≤ (cellEps lo hi : ℝ) := by
  have ht : |t - (cellT lo hi : ℝ)| ≤ (cellH lo hi : ℝ) := by
    simp only [cellT, cellH]; push_cast
    rw [abs_le]; constructor <;> linarith
  have hc : 0 < 1 + ((cellT lo hi : ℚ) : ℝ) ^ 2 := by positivity
  refine ⟨ht, ?_, ?_⟩
  · refine (norm_circ_remainder s (cellT lo hi) t).trans ?_
    have hsq : (t - (cellT lo hi : ℝ)) ^ 2 ≤ (cellH lo hi : ℝ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ht 2
    have e : ((cellRho lo hi : ℚ) : ℝ) =
        2 * (cellH lo hi : ℝ) ^ 2 / (1 + ((cellT lo hi : ℚ) : ℝ) ^ 2) := by
      simp only [cellRho]; push_cast; ring
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) hc.le
  · refine (norm_circ_sub s (cellT lo hi) t _ ht).trans (le_of_eq ?_)
    simp only [cellEps]; push_cast; ring

/-! ### The square-root step -/

theorem sqrt_bounds_of_sqrtOK {d : EccData} {k : Fin 3} {Bc ε₁ ε₂ sl sh : ℚ}
    (h : sqrtOK d k Bc ε₁ ε₂ sl sh = true) {x : ℝ}
    (hx : |x - Bc| ≤ ((ε₁ * d.L₁ k + ε₂ * d.L₂ k + d.tau k : ℚ) : ℝ) + d.r) :
    0 ≤ (sl : ℝ) ∧ (sl : ℝ) ≤ Real.sqrt x ∧ Real.sqrt x ≤ sh := by
  simp only [sqrtOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have h1' : (0 : ℝ) ≤ sl := by exact_mod_cast h1
  have h3' : (0 : ℝ) ≤ sh := by exact_mod_cast h3
  have h2' : ((sl * sl : ℚ) : ℝ) ≤
      ((Bc - (ε₁ * d.L₁ k + ε₂ * d.L₂ k + d.tau k) - d.r : ℚ) : ℝ) := by
    exact_mod_cast h2
  have h4' : ((Bc + (ε₁ * d.L₁ k + ε₂ * d.L₂ k + d.tau k) + d.r : ℚ) : ℝ) ≤
      ((sh * sh : ℚ) : ℝ) := by
    exact_mod_cast h4
  push_cast at h2' h4' hx
  rw [abs_le] at hx
  refine ⟨h1', Real.le_sqrt_of_sq_le (by nlinarith), ?_⟩
  rw [show (sh : ℝ) = Real.sqrt ((sh : ℝ) ^ 2) from (Real.sqrt_sq h3').symm]
  exact Real.sqrt_le_sqrt (by nlinarith)

/-! ### The centre on a cell -/

/-- At a chart point of the box, the exact centre is within `ε₁ L₁ + ε₂ L₂ + τ` of the computed
cell centre. -/
theorem cellCenter_close {d : EccData} (hg : globalOK d = true) (b : EBox) {t₁ t₂ : ℝ}
    (ht₁l : (b.lo₁ : ℝ) ≤ t₁) (ht₁h : t₁ ≤ b.hi₁) (ht₂l : (b.lo₂ : ℝ) ≤ t₂) (ht₂h : t₂ ≤ b.hi₂)
    (k : Fin 3) :
    |tubeCenterW d.modes d.Ibar k (chartPt b.s₁ t₁) (chartPt b.s₂ t₂) - (cellCenter d b k : ℝ)| ≤
      ((cellEps b.lo₁ b.hi₁ * d.L₁ k + cellEps b.lo₂ b.hi₂ * d.L₂ k + d.tau k : ℚ) : ℝ) := by
  obtain ⟨hfix, hM, hLk⟩ := globalOK_spec hg
  obtain ⟨hL₁, hL₂, hτ⟩ := hLk k
  obtain ⟨-, -, hε₁⟩ := cell_geom b.s₁ b.lo₁ b.hi₁ t₁ ht₁l ht₁h
  obtain ⟨-, -, hε₂⟩ := cell_geom b.s₂ b.lo₂ b.hi₂ t₂ ht₂l ht₂h
  have hc : (cellCenter d b k : ℝ) = fixCenterW d.K d.fix d.Ibar k
      (GQ.toC (circPt b.s₁ (cellT b.lo₁ b.hi₁))) (GQ.toC (circPt b.s₂ (cellT b.lo₂ b.hi₂))) :=
    bSumZ_div_eq d.K d.M d.fix d.Ibar k hM b.s₁ b.s₂ _ _
  rw [hc]
  have hlip := abs_tubeCenterW_sub_le d.modes d.Ibar k (norm_chartPt b.s₁ t₁) (norm_chartPt b.s₂ t₂)
    (norm_toC_circPt b.s₁ _) (norm_toC_circPt b.s₂ _) hε₁ hε₂
  have hrnd := abs_tubeCenterW_sub_fix_le d.K d.modes d.Ibar k
    (norm_toC_circPt b.s₁ (cellT b.lo₁ b.hi₁))
    (norm_toC_circPt b.s₂ (cellT b.lo₂ b.hi₂))
  rw [← hfix] at hrnd
  have e0₁ : (0 : ℝ) ≤ (cellEps b.lo₁ b.hi₁ : ℝ) := le_trans (norm_nonneg _) hε₁
  have e0₂ : (0 : ℝ) ≤ (cellEps b.lo₂ b.hi₂ : ℝ) := le_trans (norm_nonneg _) hε₂
  have hL₁' : (lipSum₁ d.modes k : ℝ) ≤ d.L₁ k := by exact_mod_cast hL₁
  have hL₂' : (lipSum₂ d.modes k : ℝ) ≤ d.L₂ k := by exact_mod_cast hL₂
  have hτ' : (errSum d.K d.modes k : ℝ) ≤ d.tau k := by exact_mod_cast hτ
  push_cast
  calc _ ≤ |tubeCenterW d.modes d.Ibar k (chartPt b.s₁ t₁) (chartPt b.s₂ t₂) -
          tubeCenterW d.modes d.Ibar k (GQ.toC (circPt b.s₁ (cellT b.lo₁ b.hi₁)))
            (GQ.toC (circPt b.s₂ (cellT b.lo₂ b.hi₂)))| +
        |tubeCenterW d.modes d.Ibar k (GQ.toC (circPt b.s₁ (cellT b.lo₁ b.hi₁)))
            (GQ.toC (circPt b.s₂ (cellT b.lo₂ b.hi₂))) -
          fixCenterW d.K d.fix d.Ibar k (GQ.toC (circPt b.s₁ (cellT b.lo₁ b.hi₁)))
            (GQ.toC (circPt b.s₂ (cellT b.lo₂ b.hi₂)))| := abs_sub_le _ _ _
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hL₁' e0₁
        have := mul_le_mul_of_nonneg_left hL₂' e0₂
        linarith

/-! ### The `Γ` check on a cell -/

theorem rdot_toC (a b : GQ) : rdot (GQ.toC a) (GQ.toC b) = ((a.reDot b : ℚ) : ℝ) := by
  simp [rdot, GQ.reDot, GQ.toC]

theorem rdot_toC_one (a : GQ) : rdot (GQ.toC a) 1 = ((a.re : ℚ) : ℝ) := by
  simp [rdot, GQ.toC]

/-- A passing cell `Γ_j` check bounds `|z_j|²` at every chart point of the box, for every
`s ∈ [sl, sh]`. -/
theorem cellZOK_sound {d : EccData} {b : EBox} {sl sh : Fin 3 → ℚ} {Zj : ℚ} {j : Fin 3}
    (h : cellZOK d b sl sh Zj j = true) {t₁ t₂ : ℝ} (ht₁l : (b.lo₁ : ℝ) ≤ t₁) (ht₁h : t₁ ≤ b.hi₁)
    (ht₂l : (b.lo₂ : ℝ) ≤ t₂) (ht₂h : t₂ ≤ b.hi₂) {s : Fin 3 → ℝ}
    (hs : ∀ k, 0 ≤ (sl k : ℝ) ∧ (sl k : ℝ) ≤ s k ∧ s k ≤ sh k) :
    (d.Glo j : ℝ) ≤ Complex.normSq (zW d.V s (chartPt b.s₁ t₁) (chartPt b.s₂ t₂) j) ∧
      Complex.normSq (zW d.V s (chartPt b.s₁ t₁) (chartPt b.s₂ t₂) j) ≤ d.Ghi j := by
  set c₁ := cellT b.lo₁ b.hi₁
  set c₂ := cellT b.lo₂ b.hi₂
  set P₁ := circPt b.s₁ c₁
  set P₂ := circPt b.s₂ c₂
  set D₁ := circDer b.s₁ c₁
  set D₂ := circDer b.s₂ c₂
  set zcQ := zCen d.V j P₁ P₂ ![(sl 0 + sh 0) / 2, (sl 1 + sh 1) / 2, (sl 2 + sh 2) / 2] with hzcQ
  set dsQ : Fin 3 → ℚ := ![(sh 0 - sl 0) / 2, (sh 1 - sl 1) / 2, (sh 2 - sl 2) / 2] with hdsQ
  have hG := GQ.nsq_eq zcQ
  have hzc : GQ.toC zcQ = ((d.V j 0 : ℚ) : ℝ) * ((((sl 0 : ℝ) + sh 0) / 2 : ℝ) : ℂ) * GQ.toC P₁ +
      ((d.V j 1 : ℚ) : ℝ) * ((((sl 1 : ℝ) + sh 1) / 2 : ℝ) : ℂ) * GQ.toC P₂ +
      ((d.V j 2 : ℚ) : ℝ) * ((((sl 2 : ℝ) + sh 2) / 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hzcQ, zCen, GQ.toC]
  unfold cellZOK zOK gammaOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hZ, hGZ⟩, hup⟩, hG0⟩, hEG⟩, hlo⟩ := h
  obtain ⟨hx₁, hρ₁, hε₁⟩ := cell_geom b.s₁ b.lo₁ b.hi₁ t₁ ht₁l ht₁h
  obtain ⟨hx₂, hρ₂, hε₂⟩ := cell_geom b.s₂ b.lo₂ b.hi₂ t₂ ht₂l ht₂h
  have hZ' : (0 : ℝ) ≤ Zj := by exact_mod_cast hZ
  have hGZ' : Complex.normSq (GQ.toC zcQ) ≤ (Zj : ℝ) * Zj := by
    rw [← hG]; exact_mod_cast hGZ
  obtain ⟨hU, hL⟩ := normSq_bounds_of_cell (V₀ := ((d.V j 0 : ℚ) : ℝ)) (V₁ := ((d.V j 1 : ℚ) : ℝ))
    (V₂ := ((d.V j 2 : ℚ) : ℝ)) (sl := fun k => (sl k : ℝ)) (sh := fun k => (sh k : ℝ)) (s := s)
    (fun k => (hs k).1) (fun k => (hs k).2) (norm_toC_circPt _ _) (norm_toC_circPt _ _)
    hx₁ hx₂ hρ₁ hρ₂ hε₁ hε₂ hZ' (GQ.toC zcQ) hzc hGZ'
  simp only [rdot_toC, rdot_toC_one] at hU hL
  have hz : zW d.V s (chartPt b.s₁ t₁) (chartPt b.s₂ t₂) j =
      (((d.V j 0 : ℚ) : ℝ) : ℂ) * (s 0 : ℂ) * chartPt b.s₁ t₁ +
        (((d.V j 1 : ℚ) : ℝ) : ℂ) * (s 1 : ℂ) * chartPt b.s₂ t₂ +
        (((d.V j 2 : ℚ) : ℝ) : ℂ) * (s 2 : ℂ) :=
    rfl
  rw [hz]
  have hup' : ((zcQ.nsq + 2 * zErr d.V j zcQ P₁ P₂ D₁ D₂ (cellH b.lo₁ b.hi₁) (cellH b.lo₂ b.hi₂)
      (cellRho b.lo₁ b.hi₁) (cellRho b.lo₂ b.hi₂) sh dsQ Zj +
      zRad d.V j (cellEps b.lo₁ b.hi₁) (cellEps b.lo₂ b.hi₂) sh dsQ *
        zRad d.V j (cellEps b.lo₁ b.hi₁) (cellEps b.lo₂ b.hi₂) sh dsQ : ℚ) : ℝ) ≤
      (d.Ghi j : ℝ) := by
    exact_mod_cast hup
  have hlo' : ((d.Glo j * zcQ.nsq : ℚ) : ℝ) ≤ (((zcQ.nsq - zErr d.V j zcQ P₁ P₂ D₁ D₂
      (cellH b.lo₁ b.hi₁) (cellH b.lo₂ b.hi₂) (cellRho b.lo₁ b.hi₁) (cellRho b.lo₂ b.hi₂) sh dsQ
        Zj) *
      (zcQ.nsq - zErr d.V j zcQ P₁ P₂ D₁ D₂ (cellH b.lo₁ b.hi₁) (cellH b.lo₂ b.hi₂)
        (cellRho b.lo₁ b.hi₁) (cellRho b.lo₂ b.hi₂) sh dsQ Zj) : ℚ) : ℝ) := by
    exact_mod_cast hlo
  have hEG' : ((zErr d.V j zcQ P₁ P₂ D₁ D₂ (cellH b.lo₁ b.hi₁) (cellH b.lo₂ b.hi₂)
      (cellRho b.lo₁ b.hi₁) (cellRho b.lo₂ b.hi₂) sh dsQ Zj : ℚ) : ℝ) ≤ (zcQ.nsq : ℝ) := by
    exact_mod_cast hEG
  have hG0' : (0 : ℝ) < (zcQ.nsq : ℝ) := by exact_mod_cast hG0
  simp only [zErr, zRad, hdsQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hup' hlo' hEG'
  push_cast at hup' hlo' hEG'
  rw [hG] at hup' hlo' hEG' hG0'
  constructor
  · have h3 := hL hG0' hEG'
    have h4 : ((d.Glo j : ℚ) : ℝ) * Complex.normSq (GQ.toC zcQ) ≤
        Complex.normSq ((((d.V j 0 : ℚ) : ℝ) : ℂ) * (s 0 : ℂ) * chartPt b.s₁ t₁ +
          (((d.V j 1 : ℚ) : ℝ) : ℂ) * (s 1 : ℂ) * chartPt b.s₂ t₂ +
          (((d.V j 2 : ℚ) : ℝ) : ℂ) * (s 2 : ℂ)) * Complex.normSq (GQ.toC zcQ) :=
      hlo'.trans h3
    exact le_of_mul_le_mul_right h4 hG0'
  · exact hU.trans hup'

/-! ### Leaves and trees -/

theorem leafOK_sound {d : EccData} (hg : globalOK d = true) {b : EBox} {sl sh Z : Fin 3 → ℚ}
    (h : leafOK d b sl sh Z = true) : BoxGood d b := by
  intro t₁ t₂ ht₁l ht₁h ht₂l ht₂h I hI j
  simp only [leafOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hs0, hs1⟩, hs2⟩, hz0⟩, hz1⟩, hz2⟩ := h
  have hsq : ∀ k, cellSqrtOK d b (sl k) (sh k) k = true := by
    intro k; fin_cases k
    · exact hs0
    · exact hs1
    · exact hs2
  have hzk : cellZOK d b sl sh (Z j) j = true := by
    fin_cases j
    · exact hz0
    · exact hz1
    · exact hz2
  have hs : ∀ k, 0 ≤ (sl k : ℝ) ∧ (sl k : ℝ) ≤ Real.sqrt (I k) ∧ Real.sqrt (I k) ≤ sh k := by
    intro k
    apply sqrt_bounds_of_sqrtOK (hsq k)
    have h1 := hI k
    have h2 := cellCenter_close hg b ht₁l ht₁h ht₂l ht₂h k
    calc |I k - (cellCenter d b k : ℝ)|
        ≤ |I k - tubeCenterW d.modes d.Ibar k (chartPt b.s₁ t₁) (chartPt b.s₂ t₂)| +
          |tubeCenterW d.modes d.Ibar k (chartPt b.s₁ t₁) (chartPt b.s₂ t₂) -
            (cellCenter d b k : ℝ)| :=
          abs_sub_le _ _ _
      _ ≤ _ := by linarith
  exact cellZOK_sound hzk ht₁l ht₁h ht₂l ht₂h hs

theorem checkTree_sound {d : EccData} (hg : globalOK d = true) :
    ∀ (t : ETree) (b : EBox), checkTree d b t = true → BoxGood d b
  | .leaf l₀ l₁ l₂ u₀ u₁ u₂ z₀ z₁ z₂, b, h => leafOK_sound hg h
  | .split ax t₁ t₂, b, h => by
    simp only [checkTree, Bool.and_eq_true] at h
    have hl := checkTree_sound hg t₁ _ h.1
    have hr := checkTree_sound hg t₂ _ h.2
    intro x₁ x₂ hx₁l hx₁h hx₂l hx₂h
    cases ax with
    | false =>
      by_cases hm : x₁ ≤ (((b.lo₁ + b.hi₁) / 2 : ℚ) : ℝ)
      · exact hl x₁ x₂ hx₁l hm hx₂l hx₂h
      · exact hr x₁ x₂ (le_of_lt (not_le.mp hm)) hx₁h hx₂l hx₂h
    | true =>
      by_cases hm : x₂ ≤ (((b.lo₂ + b.hi₂) / 2 : ℚ) : ℝ)
      · exact hl x₁ x₂ hx₁l hx₁h hx₂l hm
      · exact hr x₁ x₂ hx₁l hx₁h (le_of_lt (not_le.mp hm)) hx₂h

/-! ### The generic enclosure -/

theorem eccGamma_eq_normSq (V : Fin 3 → Fin 3 → ℚ) (I : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (j : Fin 3) :
    eccGamma V I φ j = Complex.normSq (zW V (fun k => Real.sqrt (I k))
      (Complex.exp (φ 0 * Complex.I)) (Complex.exp (φ 1 * Complex.I)) j) := by
  rw [Complex.normSq_apply]
  simp only [eccGamma, zW, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Real.cos_zero, Real.sin_zero,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

/-- Common-phase invariance: with absolute angles `θ`, `|Σ_k V_jk √I_k e^{iθ_k}|²` is
`eccGamma` at the reduced angles `φ = (θ₀ - θ₂, θ₁ - θ₂)`. -/
theorem eccGamma_phase (V : Fin 3 → Fin 3 → ℚ) (I : Fin 3 → ℝ) (θ : Fin 3 → ℝ) (j : Fin 3) :
    (∑ k, (V j k : ℝ) * Real.sqrt (I k) * Real.cos (θ k)) ^ 2 +
        (∑ k, (V j k : ℝ) * Real.sqrt (I k) * Real.sin (θ k)) ^ 2 =
      eccGamma V I ![θ 0 - θ 2, θ 1 - θ 2] j := by
  obtain ⟨a₀, h₀⟩ : ∃ a, θ 0 = a + θ 2 := ⟨θ 0 - θ 2, by ring⟩
  obtain ⟨a₁, h₁⟩ : ∃ a, θ 1 = a + θ 2 := ⟨θ 1 - θ 2, by ring⟩
  simp only [eccGamma, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, h₀, h₁, add_sub_cancel_right,
    Real.cos_zero, Real.sin_zero, Real.cos_add, Real.sin_add]
  have hcs := Real.sin_sq_add_cos_sq (θ 2)
  linear_combination ((((V j 0 : ℝ) * Real.sqrt (I 0) * Real.cos a₀ +
    (V j 1 : ℝ) * Real.sqrt (I 1) * Real.cos a₁ + (V j 2 : ℝ) * Real.sqrt (I 2)) ^ 2 +
    ((V j 0 : ℝ) * Real.sqrt (I 0) * Real.sin a₀ +
      (V j 1 : ℝ) * Real.sqrt (I 1) * Real.sin a₁) ^ 2)) * hcs

/-- **The generic eccentricity enclosure.** If the global check and the four chart trees pass,
then for every `φ` and every `I` with `|I_k - B_k(φ)| ≤ r`, `Glo_j ≤ Γ_j(I, φ) ≤ Ghi_j`. -/
theorem eccGamma_bounds_of_check {d : EccData} (hg : globalOK d = true) (T : Bool → Bool → ETree)
    (hT : ∀ s₁ s₂, checkTree d (rootBox s₁ s₂) (T s₁ s₂) = true) (φ : Fin 2 → ℝ) (I : Fin 3 → ℝ)
    (hI : ∀ k, |I k - tubeCenter d.modes d.Ibar k φ| ≤ d.r) (j : Fin 3) :
    (d.Glo j : ℝ) ≤ eccGamma d.V I φ j ∧ eccGamma d.V I φ j ≤ d.Ghi j := by
  obtain ⟨s₁, t₁, h₁l, h₁h, h₁⟩ := exists_circ (φ 0)
  obtain ⟨s₂, t₂, h₂l, h₂h, h₂⟩ := exists_circ (φ 1)
  have hbox := checkTree_sound hg (T s₁ s₂) (rootBox s₁ s₂) (hT s₁ s₂)
  rw [eccGamma_eq_normSq, h₁, h₂]
  have hI' : ∀ k, |I k - tubeCenterW d.modes d.Ibar k (chartPt s₁ t₁) (chartPt s₂ t₂)| ≤ d.r := by
    intro k
    have := hI k
    rwa [tubeCenter_eq_W, h₁, h₂] at this
  exact hbox t₁ t₂ (by simpa [rootBox] using h₁l) (by simpa [rootBox] using h₁h)
    (by simpa [rootBox] using h₂l) (by simpa [rootBox] using h₂h) I hI' j

end KAM.EffectiveStability.Tube

end
