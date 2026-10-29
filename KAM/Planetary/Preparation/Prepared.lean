/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PreparedSmall
public import KAM.Planetary.Preparation.PreparedChoice
public import KAM.Planetary.Preparation.PreparedClose
public import KAM.Planetary.Preparation.PreparedM

/-!
# The prepared datum (P11A-P8e, `bpP:p11:prepared`)

The signed `prepared`: for small `eps` the data `p11PrepQ D nu eps` (the core construction of
`PreparedBasic` with the frequency datum `p11PrepChk`) satisfies `P11PreparedFullSpec`.
Assembly of `p11_prepared_basic_dom` (pr-basic, pr-a), `p11_pr_b`, `p11_pr_c`, `p11_pr_d`,
the identification `p11_prep_chk_eq` and the relation `p11_prep_freqR_eq`.
-/

@[expose] public noncomputable section
open Set
namespace KAM.Planetary

theorem prepared {n : ℕ} (D : P11Physical n) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∃ eps3 c3 : ℝ, 0 < eps3 ∧ eps3 < 1 ∧ 1 ≤ c3 ∧
    ∀ eps, 0 < eps → eps ≤ eps3 →
      5*eps ≤ p11s2 (p11SecularData D) nu eps ∧
      c3*eps*Real.log (1/eps)^(5*(p11SecularData D).tau+2+
        ((p11SecularData D).tau+1)*((p11PatchData D).mu+1)) ≤ 1 ∧
      ∃ Q, P11PreparedFullSpec D nu eps c3 Q := by
  have hCF : P11SecularFullSpec D (p11SecularData D) := (holo_chart D).choose_spec
  have hC := hCF.1
  have hn : 1 ≤ n := by have := D.n_ge; omega
  obtain ⟨e0, he0, he01, hsmall⟩ := p11_prep_small D hnu
  obtain ⟨eb, hebpos, hbasic⟩ := p11_prepared_basic_dom D hnu
  obtain ⟨Kb, hKb, hb⟩ := p11_pr_b hC hnu
  obtain ⟨Kc, hKc, hc⟩ := p11_pr_c hC hnu hn
  obtain ⟨Kd, hKd, hd⟩ := p11_pr_d hCF hnu
  obtain ⟨-, hτ0, -, -, -, -, -, -, -, -⟩ := fast_consts hC
  have hc21 : 1 ≤ p11SlowConstant D nu := (hsmall e0 he0 le_rfl).2.2.2.2.2
  set c2 := p11SlowConstant D nu with hc2
  set c3 : ℝ := max (max 1 c2) (Kc * (1 + c2)) with hc3
  have hc3a : 1 ≤ c3 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hc3b : c2 ≤ c3 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hc3c : Kc * (1 + c2) ≤ c3 := le_max_right _ _
  set Qe : ℝ := 5 * (p11SecularData D).tau + 2 +
    ((p11SecularData D).tau + 1) * (((p11PatchData D).mu : ℝ) + 1) with hQe
  have hQe0 : 0 ≤ Qe := by
    have : (0 : ℝ) ≤ (p11PatchData D).mu := Nat.cast_nonneg _
    rw [hQe]; positivity
  set M : ℝ := (Kb + Kd) * (1 + c2) + c3 with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  obtain ⟨e1, he1, hX⟩ := p11_prep_eventually_le hM0 hQe0
  refine ⟨min e0 (min eb e1), c3, lt_min he0 (lt_min hebpos he1),
    lt_of_le_of_lt (min_le_left _ _) he01, hc3a, fun eps heps hle => ?_⟩
  have hle0 := hle.trans (min_le_left _ _)
  have hleb := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hle1 := hle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hεM, hzs, h5, hF, hS, -⟩ := hsmall eps heps hle0
  have hX' := hX eps heps hle1
  have hl : 1 ≤ Real.log (1 / eps) := slow_log_ge_one hC heps hεM
  have hXn : 0 ≤ eps * Real.log (1 / eps) ^ Qe :=
    mul_nonneg heps.le (Real.rpow_nonneg (by linarith) _)
  have hθb : Kb * (1 + c2) * eps * Real.log (1 / eps) ^ Qe ≤ 1 := by
    have h1 : Kb * (1 + c2) ≤ M := by rw [hM]; nlinarith
    calc Kb * (1 + c2) * eps * Real.log (1 / eps) ^ Qe
        = (Kb * (1 + c2)) * (eps * Real.log (1 / eps) ^ Qe) := by ring
      _ ≤ M * (eps * Real.log (1 / eps) ^ Qe) := mul_le_mul_of_nonneg_right h1 hXn
      _ ≤ 1 := hX'
  have hθd : Kd * (1 + c2) * eps * Real.log (1 / eps) ^ Qe ≤ 1 := by
    have h1 : Kd * (1 + c2) ≤ M := by rw [hM]; nlinarith
    calc Kd * (1 + c2) * eps * Real.log (1 / eps) ^ Qe
        = (Kd * (1 + c2)) * (eps * Real.log (1 / eps) ^ Qe) := by ring
      _ ≤ M * (eps * Real.log (1 / eps) ^ Qe) := mul_le_mul_of_nonneg_right h1 hXn
      _ ≤ 1 := hX'
  have hθ3 : c3 * eps * Real.log (1 / eps) ^ Qe ≤ 1 := by
    have h1 : c3 ≤ M := by rw [hM]; nlinarith
    calc c3 * eps * Real.log (1 / eps) ^ Qe
        = c3 * (eps * Real.log (1 / eps) ^ Qe) := by ring
      _ ≤ M * (eps * Real.log (1 / eps) ^ Qe) := mul_le_mul_of_nonneg_right h1 hXn
      _ ≤ 1 := hX'
  refine ⟨h5, hθ3, p11PrepQ D nu eps, ?_⟩
  have hbasic' := (hbasic eps heps hleb c3 hc3b (p11PrepChk D nu eps)).1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hbasic'
  have hs2 := (slow_pos hC hnu heps hεM).2.2.le
  have hN := p11PrepQ_N_formula D nu eps
  have hbb := hb (Fast := p11FastData D eps) (A := p11SlowData D nu eps)
    (Q := p11PrepQ D nu eps) heps hεM (by linarith) hθb hzs h5 hF hS hN
  have hdd := hd (Fast := p11FastData D eps) (A := p11SlowData D nu eps)
    (Q := p11PrepQ D nu eps) heps hεM (by linarith) hθd hzs h5 hF hS hN
  have hcc := hc (Fast := p11FastData D eps) (A := p11SlowData D nu eps) (c := c2) (cc := c3)
    (p11PrepQ D nu eps) heps hεM (by linarith) hc3c hzs h5 hF hS
    (fun ρ _ J _ => p11_prep_chk_eq D nu heps.ne' J ρ)
  have hfr := p11_prep_freqR_eq heps h5 hs2 hS
  exact ⟨⟨b1, b2, b3, b4, b5, b6, b7, b8, hbb.1, hbb.2.1, hfr, fun ρ hρ => hcc ρ hρ, hdd.1, b9⟩,
    fun ρ _ J _ => p11_prep_chk_eq D nu heps.ne' J ρ, fun ρ hρ => hcc ρ hρ, hdd.2.1, hdd.2.2⟩

end KAM.Planetary

end
