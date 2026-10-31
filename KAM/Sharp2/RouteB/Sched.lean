/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteB.Data
public import KAM.Sharp2.SmallDiv.Scale
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Route B: the schedule, the stage inputs and the stage certificates

For well-formed numbers (`NumB.Wf`, `ρ ≤ 1`):

* the schedule: `δ_s = δ₀/a^s` is positive, strictly decreasing, `δ₀ = (ρ - ρ∞)(a-1)/(3a) < 1`
  (no clipping), `r_s = ρ∞ + 3a/(a-1) δ_s`, `r_s - 3δ_s = r_{s+1}`, `δ_s ≤ min (r_s) 1 ≤ r_s`, and
  the full-bite ratio `δ_s/min (r_s) 1` is nonincreasing (`SDConst`'s `fullBite_ratio_mono`);
* the split `s_τ = τ/(τ+1)`: `1/(s_τ^τ (1 - s_τ)) = (τ+1)^{τ+1}/τ^τ`;
* the stage inputs: `(N.inp s).Ok`, `N.inp s = N.inp kp` for `s ≥ kp`;
* `NumB.Cert.at`: the three certificates the step needs at stage `s` (actual bite, split bite,
  full bite), in the prefix and in the tail.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2.RouteB

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2

variable {n : ℕ} {N : NumB n}

namespace NumB.Wf

variable (hN : N.Wf)
include hN

theorem a_pos : 0 < N.a := by linarith [hN.a_gt]

theorem ρ_pos : 0 < N.ρ := hN.ρinf_pos.trans hN.ρinf_lt

theorem τ_pos : 0 < N.τ := by linarith [hN.τ_ge]

/-- No clipping: `δ₀ = (ρ - ρ∞)(a-1)/(3a)`, since `ρ ≤ 1`. -/
theorem δ0_eq : N.δ0 = (N.ρ - N.ρinf) * (N.a - 1) / (3 * N.a) := by
  have ha := hN.a_pos
  have h1 : (N.ρ - N.ρinf) * (N.a - 1) / (3 * N.a) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith [hN.ρinf_pos, hN.ρinf_lt, hN.ρ_le, hN.a_gt]
  exact min_eq_right h1.le

theorem δ0_pos : 0 < N.δ0 := bite0R_pos hN.a_gt hN.ρinf_lt

omit hN in
theorem δ0_le_one : N.δ0 ≤ 1 := min_le_left _ _

theorem δ_pos (s : ℕ) : 0 < N.δ s := biteSR_pos hN.a_gt hN.ρinf_lt s

theorem δ_le (s : ℕ) : N.δ s ≤ N.δ0 := biteSR_le hN.a_gt hN.ρinf_lt s

theorem δ_le_one (s : ℕ) : N.δ s ≤ 1 := (hN.δ_le s).trans (NumB.Wf.δ0_le_one (N := N))

omit hN in
theorem δ_zero : N.δ 0 = N.δ0 := by simp [NumB.δ, NumB.δ0, biteSR]

theorem δ_succ (s : ℕ) : N.δ (s + 1) = N.δ s / N.a := by
  have := hN.a_pos.ne'
  simp only [NumB.δ, biteSR, pow_succ]
  field_simp

theorem δ_lt_succ (s : ℕ) : N.δ (s + 1) < N.δ s := by
  rw [hN.δ_succ, div_lt_iff₀ hN.a_pos]
  nlinarith [hN.δ_pos s, hN.a_gt]

theorem δ_anti {s t : ℕ} (h : s ≤ t) : N.δ t ≤ N.δ s := by
  induction t, h using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => exact (hN.δ_lt_succ t).le.trans ih

theorem δ_strict {s t : ℕ} (h : s < t) : N.δ t < N.δ s :=
  (hN.δ_anti (Nat.succ_le_of_lt h)).trans_lt (hN.δ_lt_succ s)

theorem δ_inj {s t : ℕ} (h : N.δ s = N.δ t) : s = t := by
  rcases lt_trichotomy s t with hst | hst | hst
  · exact absurd h (hN.δ_strict hst).ne'
  · exact hst
  · exact absurd h (hN.δ_strict hst).ne

theorem r_zero : N.r 0 = N.ρ := stripSR_zero hN.a_gt

theorem r_succ (s : ℕ) : N.r s - 3 * N.δ s = N.r (s + 1) := stripSR_succ hN.a_gt s

theorem r_gt (s : ℕ) : N.ρinf < N.r s := stripSR_gt hN.a_gt hN.ρinf_lt s

theorem three_δ_lt (s : ℕ) : 3 * N.δ s < N.r s := by
  have := hN.r_succ s
  have := hN.r_gt (s + 1)
  linarith [hN.ρinf_pos]

/-- `r_s = ρ∞ + 3a/(a-1) δ_s`. -/
theorem r_eq (s : ℕ) : N.r s = N.ρinf + 3 * N.a / (N.a - 1) * N.δ s := by
  have h := stripSR_eq hN.a_gt (ρ := N.ρ) (ρinf := N.ρinf) s
  have h0 := hN.δ0_eq
  have ha1 : N.a - 1 ≠ 0 := by linarith [hN.a_gt]
  have ha : N.a ≠ 0 := hN.a_pos.ne'
  have e : 3 * bite0R N.a N.ρ N.ρinf * N.a / (N.a - 1) = N.ρ - N.ρinf := by
    change 3 * N.δ0 * N.a / (N.a - 1) = _
    rw [h0]; field_simp
  change N.r s = _ at h
  rw [h, e]
  change N.ρ - (N.ρ - N.ρinf) + 3 * N.δ s * N.a / (N.a - 1) = _
  ring

theorem r_le (s : ℕ) : N.r s ≤ N.ρ := by
  have h0 := hN.r_eq 0
  rw [hN.r_zero] at h0
  rw [hN.r_eq s, h0]
  have hc : 0 ≤ 3 * N.a / (N.a - 1) := by
    have := hN.a_gt; have : 0 < N.a - 1 := by linarith
    positivity
  linarith [mul_le_mul_of_nonneg_left (hN.δ_anti (Nat.zero_le s)) hc]

theorem bfull_pos (s : ℕ) : 0 < N.bfull s :=
  lt_min (hN.ρinf_pos.trans (hN.r_gt s)) one_pos

omit hN in
theorem bfull_le (s : ℕ) : N.bfull s ≤ N.r s := min_le_left _ _

theorem δ_le_bfull (s : ℕ) : N.δ s ≤ N.bfull s :=
  le_min (by linarith [hN.three_δ_lt s, hN.δ_pos s]) (hN.δ_le_one s)

/-- The full-bite ratio `δ_s/min (r_s) 1` is nonincreasing in `s`. -/
theorem ratio_anti {s t : ℕ} (h : s ≤ t) : N.δ t / N.bfull t ≤ N.δ s / N.bfull s := by
  have hc : 0 < 3 * N.a / (N.a - 1) := by
    have := hN.a_pos; have : 0 < N.a - 1 := by linarith [hN.a_gt]
    positivity
  have key := fullBite_ratio_mono hN.ρinf_pos hc (hN.δ_pos t) (hN.δ_anti h)
  simpa only [NumB.bfull, hN.r_eq] using key

/-! ### The split -/

theorem split_pos : 0 < N.split := div_pos hN.τ_pos (by linarith [hN.τ_pos])

theorem split_lt_one : N.split < 1 := by
  rw [NumB.split, div_lt_one (by linarith [hN.τ_pos])]; linarith

/-- `1/(s_τ^τ (1 - s_τ)) = (τ+1)^{τ+1}/τ^τ`. -/
theorem split_factor : 1 / (N.split ^ N.τ * (1 - N.split)) = N.rcf := by
  have hτ := hN.τ_pos
  have h1 : 0 < N.τ + 1 := by linarith
  have e1 : 1 - N.split = 1 / (N.τ + 1) := by rw [NumB.split]; field_simp; ring
  have e2 : N.split ^ N.τ = N.τ ^ N.τ / (N.τ + 1) ^ N.τ := Real.div_rpow hτ.le h1.le _
  have e3 : (N.τ + 1) ^ (N.τ + 1) = (N.τ + 1) ^ N.τ * (N.τ + 1) := Real.rpow_add_one h1.ne' _
  have h2 : 0 < N.τ ^ N.τ := Real.rpow_pos_of_pos hτ _
  have h3 : 0 < (N.τ + 1) ^ N.τ := Real.rpow_pos_of_pos h1 _
  rw [e1, e2, NumB.rcf, e3]
  field_simp

/-! ### The stage inputs -/

/-- The tail record: `N.inp s = N.inp kp` for `s ≥ kp`. -/
theorem inp_tail {s : ℕ} (hs : N.kp ≤ s) : N.inp s = N.inp N.kp := by
  have hk := hN.kp_pos
  have hs0 : s ≠ 0 := by omega
  have hk0 : N.kp ≠ 0 := by omega
  simp only [NumB.inp, not_lt.2 hs, lt_irrefl, ↓reduceIte, hs0, hk0, min_eq_right hs,
    min_self]

omit hN in
theorem inp_n (s : ℕ) : (N.inp s).n = n := rfl

omit hN in
theorem inp_iso (s : ℕ) : (N.inp s).iso = N.iso := rfl

omit hN in
theorem inp_δ (s : ℕ) : (N.inp s).δ = N.δ (min s N.kp) := rfl

theorem δ_le_inp (s : ℕ) : N.δ s ≤ (N.inp s).δ := hN.δ_anti (min_le_left _ _)

theorem inp_lam_pos (s : ℕ) : 0 < (N.inp s).lam ∧ (N.inp s).lam ≤ 1 := by
  show 0 < (if s = 0 then N.lam0 else 1) ∧ (if s = 0 then N.lam0 else 1) ≤ 1
  split_ifs
  · exact ⟨hN.lam.1, hN.lam.2.1⟩
  · exact ⟨one_pos, le_rfl⟩

theorem inp_c_pos (s : ℕ) : 0 < (N.inp s).c := by
  show 0 < (if s < N.kp then N.c s else N.ctail)
  split_ifs
  · exact hN.sd.1 s
  · exact hN.sd.2.2.2.1

theorem rcf_pos : 0 < N.rcf := by
  rw [← hN.split_factor]
  have := hN.split_pos
  have := hN.split_lt_one
  have : 0 < N.split ^ N.τ := Real.rpow_pos_of_pos hN.split_pos _
  have : 0 < 1 - N.split := by linarith
  positivity

theorem inp_c1_pos (s : ℕ) : 0 < (N.inp s).c1 := by
  show 0 < (if s < N.kp then N.c' s else N.ctail) * N.rcf
  refine mul_pos ?_ hN.rcf_pos
  split_ifs
  · exact hN.sd.2.1 s
  · exact hN.sd.2.2.2.1

theorem inp_cavg_nonneg (s : ℕ) : 0 ≤ (N.inp s).cavg := by
  show 0 ≤ (if s < N.kp then N.cbar s * (N.δ s / N.bfull s) ^ N.τ
    else N.cbtail * (N.δ N.kp / N.bfull N.kp) ^ N.τ)
  split_ifs
  · exact mul_nonneg (hN.sd.2.2.1 s).le
      (Real.rpow_nonneg (div_nonneg (hN.δ_pos s).le (hN.bfull_pos s).le) _)
  · exact mul_nonneg hN.sd.2.2.2.2.le
      (Real.rpow_nonneg (div_nonneg (hN.δ_pos _).le (hN.bfull_pos _).le) _)

/-- Every stage input is admissible (`bp:p2s2:data-ok`). -/
theorem inp_ok (s : ℕ) : (N.inp s).Ok where
  one_le_n := by have := hN.two_le; show 1 ≤ n; omega
  one_le_κ := hN.τ_ge
  nonneg := hN.nonneg
  caps := hN.caps
  budgets := hN.budgets
  sd := ⟨hN.inp_c_pos s, hN.inp_c1_pos s, hN.inp_cavg_nonneg s⟩
  ratios := hN.ratios
  a_gt := hN.a_gt
  lam := by
    refine ⟨(hN.inp_lam_pos s).1, (hN.inp_lam_pos s).2, ?_, ?_⟩
    · show 0 < (if s = 0 then N.lamW0 else 1)
      split_ifs
      · exact hN.lam.2.2.1
      · exact one_pos
    · show (if s = 0 then N.lamW0 else 1) ≤ 1
      split_ifs
      · exact hN.lam.2.2.2
      · exact le_rfl
  γb_pos := hN.γb
  δ_pos := hN.δ_pos _
  δ_le := hN.δ_le_one _

end NumB.Wf

/-- The certificates of stage `s` (`bp:p2s2:standing` (R4)): at the actual bite `δ_s`, at the split
bite `s_τ δ_s` (with `c'/(s_τ^τ(1 - s_τ)) ≤ c₁`), and at the full bite `min (r_s) 1`. -/
theorem NumB.Cert.at {γ : ℝ} {Ω : Set (Fin n → ℝ)} (hN : N.Wf) (hC : N.Cert γ Ω) (s : ℕ) :
    SDConst n N.τ γ (N.δ s) (N.inp s).c Ω ∧
      (∃ c', SDConst n N.τ γ (N.split * N.δ s) c' Ω ∧
        c' / (N.split ^ N.τ * (1 - N.split)) ≤ (N.inp s).c1) ∧
      ∃ cb, SDConst n N.τ γ (N.bfull s) cb Ω ∧ cb * (N.δ s / N.bfull s) ^ N.τ ≤ (N.inp s).cavg := by
  have hsp := hN.split_factor
  have hsδ : N.split * N.δ s ≤ N.δ s :=
    mul_le_of_le_one_left (hN.δ_pos s).le hN.split_lt_one.le
  have hc1 : ∀ c' : ℝ, c' / (N.split ^ N.τ * (1 - N.split)) = c' * N.rcf := fun c' => by
    rw [← hsp, div_eq_mul_one_div]
  by_cases hs : s < N.kp
  · refine ⟨?_, ⟨N.c' s, hC.split s hs, ?_⟩, N.cbar s, hC.bar s hs, ?_⟩
    · show SDConst n N.τ γ (N.δ s) (if s < N.kp then N.c s else N.ctail) Ω
      simp only [hs, ↓reduceIte]; exact hC.stage s hs
    · rw [hc1]
      show N.c' s * N.rcf ≤ (if s < N.kp then N.c' s else N.ctail) * N.rcf
      simp only [hs, ↓reduceIte, le_refl]
    · show _ ≤ (if s < N.kp then N.cbar s * (N.δ s / N.bfull s) ^ N.τ
        else N.cbtail * (N.δ N.kp / N.bfull N.kp) ^ N.τ)
      simp only [hs, ↓reduceIte, le_refl]
  · have hs' : N.kp ≤ s := not_lt.1 hs
    have hδk : N.δ s ≤ N.δ N.kp := hN.δ_anti hs'
    refine ⟨?_, ⟨N.ctail, hC.tail _ (mul_pos hN.split_pos (hN.δ_pos s)) (hsδ.trans hδk), ?_⟩,
      N.cbtail, hC.tailbar s hs', ?_⟩
    · show SDConst n N.τ γ (N.δ s) (if s < N.kp then N.c s else N.ctail) Ω
      simp only [hs, ↓reduceIte]; exact hC.tail _ (hN.δ_pos s) hδk
    · rw [hc1]
      show N.ctail * N.rcf ≤ (if s < N.kp then N.c' s else N.ctail) * N.rcf
      simp only [hs, ↓reduceIte, le_refl]
    · show _ ≤ (if s < N.kp then N.cbar s * (N.δ s / N.bfull s) ^ N.τ
        else N.cbtail * (N.δ N.kp / N.bfull N.kp) ^ N.τ)
      simp only [hs, ↓reduceIte]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
        (div_nonneg (hN.δ_pos s).le (hN.bfull_pos s).le) (hN.ratio_anti hs') hN.τ_pos.le)
        hN.sd.2.2.2.2.le

end KAM.Sharp2.RouteB

end
