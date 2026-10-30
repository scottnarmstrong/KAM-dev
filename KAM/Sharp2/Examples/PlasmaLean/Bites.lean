/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.Examples.PlasmaLean.Balanced
public import KAM.Sharp2.Examples.PlasmaLean.Frequency
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Certified small-divisor constants at PlasmaLean's frequency

With `ρ = 1/50`, `ρ∞ = ρ/1000`, the schedule is `δ_s = 2^{-s} 333/100000`,
`r_s = ρ - 6δ₀(1 - 2^{-s})`. For each of the bites `δ₀, δ₁, δ₂, r₀, r₁, r₂` of the prefix, two
kernel `decide`s certify a rational bound `B` of the whole sum `S(ω*, b)`, finite part and tail, by
`smallDivisorSum_le_bal` at the cut-off `2^l`; then `sdConst_bite` gives
`SDConst 2 1 γ* b c {ω*}`.

Each `decide` is a single bite. The heaviest is `δ₂`, with `2 · 2¹¹` modes `k'` of `ι`.
-/

@[expose] public section

namespace KAM.Sharp2.Examples

open KAM KAM.Certificate KAM.CertificateSharp

/-- The checker's data of the bite `b`: `S(ω, b) = smallDivisorSum ω (2b)`. -/
def biteData (b E1 : ℚ) (l : ℕ) : SdsData :=
  { box := iotaBox, γ := gammaStar, δ := 2 * b, N := 2 ^ l, J := 8, E1 := E1 }

/-- The two checks and the rational test give a small-divisor constant at the bite `b`. -/
theorem sdConst_bite {b E1 c B : ℚ} {l : ℕ} (hchk : balCheck (biteData b E1 l) l = true)
    (hB : balBound (biteData b E1 l) l ≤ B) (hb : 0 < b) (hc : 0 < c)
    (hnum : B * (gammaStar * b) ^ 2 ≤ (31415 / 10000 * c) ^ 2) :
    SDConst 2 1 (gammaStar : ℝ) (b : ℝ) (c : ℝ) {omegaStar} := by
  have hγ : (0 : ℝ) < gammaStar := by norm_num [gammaStar]
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hdio := isDiophantine_omegaStar
  have h1 := smallDivisorSum_le_bal (biteData b E1 l) rfl hchk hB (ω' := ![iota]) iota_mem_box
    (by rw [snoc_iota]; exact hdio)
  rw [snoc_iota] at h1
  have h2 : sdSum omegaStar (b : ℝ) ≤ (B : ℝ) := by
    rw [sdSum_eq_smallDivisorSum]
    have e : (((biteData b E1 l).δ : ℚ) : ℝ) = 2 * (b : ℝ) := by
      simp [biteData]
    rwa [e] at h1
  refine sdConst_two_of_sdSum hγ hb' hc' hdio h2 ?_
  have : ((B * (gammaStar * b) ^ 2 : ℚ) : ℝ) ≤ (((31415 / 10000 * c) ^ 2 : ℚ) : ℝ) :=
    Rat.cast_le.mpr hnum
  push_cast at this
  exact this

theorem bite_d0_check :
    balCheck (biteData (333 / 100000) (959039 / 1000000) 9) 9 = true := by decide +kernel
theorem bite_d0_bound :
    balBound (biteData (333 / 100000) (959039 / 1000000) 9) 9 ≤ 10938 := by decide +kernel

theorem bite_d1_check :
    balCheck (biteData (333 / 200000) (489653 / 500000) 10) 10 = true := by decide +kernel
theorem bite_d1_bound :
    balBound (biteData (333 / 200000) (489653 / 500000) 10) 10 ≤ 43107 := by decide +kernel

theorem bite_d2_check :
    balCheck (biteData (333 / 400000) (1237 / 1250) 11) 11 = true := by decide +kernel
theorem bite_d2_bound :
    balBound (biteData (333 / 400000) (1237 / 1250) 11) 11 ≤ 171512 := by decide +kernel

theorem bite_r0_check :
    balCheck (biteData (1 / 50) (194467 / 250000) 6) 6 = true := by decide +kernel
theorem bite_r0_bound :
    balBound (biteData (1 / 50) (194467 / 250000) 6) 6 ≤ 20651 / 50 := by decide +kernel

theorem bite_r1_check :
    balCheck (biteData (1001 / 100000) (440929 / 500000) 7) 7 = true := by decide +kernel
theorem bite_r1_bound :
    balBound (biteData (1001 / 100000) (440929 / 500000) 7) 7 ≤ 13553 / 10 := by decide +kernel

theorem bite_r2_check :
    balCheck (biteData (1003 / 200000) (234739 / 250000) 8) 8 = true := by decide +kernel
theorem bite_r2_bound :
    balBound (biteData (1003 / 200000) (234739 / 250000) 8) 8 ≤ 4928 := by decide +kernel

theorem sdConst_d0 : SDConst 2 1 (gammaStar : ℝ) ((333 / 100000 : ℚ) : ℝ)
    ((1524 / 100000 : ℚ) : ℝ) {omegaStar} :=
  sdConst_bite bite_d0_check bite_d0_bound (by norm_num) (by norm_num)
    (by norm_num [gammaStar])

theorem sdConst_d1 : SDConst 2 1 (gammaStar : ℝ) ((333 / 200000 : ℚ) : ℝ)
    ((1512 / 100000 : ℚ) : ℝ) {omegaStar} :=
  sdConst_bite bite_d1_check bite_d1_bound (by norm_num) (by norm_num)
    (by norm_num [gammaStar])

theorem sdConst_d2 : SDConst 2 1 (gammaStar : ℝ) ((333 / 400000 : ℚ) : ℝ)
    ((1508 / 100000 : ℚ) : ℝ) {omegaStar} :=
  sdConst_bite bite_d2_check bite_d2_bound (by norm_num) (by norm_num)
    (by norm_num [gammaStar])

theorem sdConst_r0 : SDConst 2 1 (gammaStar : ℝ) ((1 / 50 : ℚ) : ℝ)
    ((1778 / 100000 : ℚ) : ℝ) {omegaStar} :=
  sdConst_bite bite_r0_check bite_r0_bound (by norm_num) (by norm_num)
    (by norm_num [gammaStar])

theorem sdConst_r1 : SDConst 2 1 (gammaStar : ℝ) ((1001 / 100000 : ℚ) : ℝ)
    ((1612 / 100000 : ℚ) : ℝ) {omegaStar} :=
  sdConst_bite bite_r1_check bite_r1_bound (by norm_num) (by norm_num)
    (by norm_num [gammaStar])

theorem sdConst_r2 : SDConst 2 1 (gammaStar : ℝ) ((1003 / 200000 : ℚ) : ℝ)
    ((1540 / 100000 : ℚ) : ℝ) {omegaStar} :=
  sdConst_bite bite_r2_check bite_r2_bound (by norm_num) (by norm_num)
    (by norm_num [gammaStar])

end KAM.Sharp2.Examples

end
