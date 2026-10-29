/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.AsymptoticEntries.Calculus

/-!
# Planar quartic torsion: the polynomial bookkeeping of `beta_def` (P11C, package T18)

Blueprint P, Part 11b (`bpP:p11b:asymptotics`, step `stepP:p11b:as-ent`): abstract bounds for the
three entries of `beta_def c P` in terms of the six coefficient sizes `c₁ = O(α)`, `c₂ = O(α²)`,
`c₃ = O(α ^ (3/2))`, `c₄ = O(α ^ (7/2))`, `c₅ = O(α ^ (9/4))`, `c₆ = O(α ^ (11/4))` and the
projector sizes `π₂₂ = O(α ^ (5/2))`, `π₁₂ = O(α ^ (5/4))` (with `π₁₁ = 1 - π₂₂`).  The functions
are abstract, so the lemmas are pure big-O statements.
-/

@[expose] public noncomputable section
open Set Filter Asymptotics Real
open scoped Topology
namespace KAM.Planetary

/-- Monomial bound: `c v ^ i w ^ j` with `c = O(a ^ e)`, `v = O(a ^ (5/2))`, `w = O(a ^ (5/4))`. -/
theorem p11cAe_mono3 {c v w : ℝ → ℝ} {e : ℝ} (hc : c =O[𝓝[>] 0] fun a : ℝ => a ^ e)
    (hv : v =O[𝓝[>] 0] fun a : ℝ => a ^ (5 / 2 : ℝ))
    (hw : w =O[𝓝[>] 0] fun a : ℝ => a ^ (5 / 4 : ℝ)) (i j : ℕ) {t : ℝ}
    (ht : t ≤ e + i * (5 / 2) + j * (5 / 4)) :
    (fun a => c a * v a ^ i * w a ^ j) =O[𝓝[>] 0] fun a : ℝ => a ^ t := by
  have hvi : (fun a => v a ^ i) =O[𝓝[>] 0] fun a : ℝ => a ^ ((i : ℝ) * (5 / 2)) :=
    (hv.pow i).congr' EventuallyEq.rfl (p11cAe_pos.mono fun a ha => by
      show (a ^ (5 / 2 : ℝ)) ^ i = a ^ ((i : ℝ) * (5 / 2))
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le, mul_comm])
  have hwj : (fun a => w a ^ j) =O[𝓝[>] 0] fun a : ℝ => a ^ ((j : ℝ) * (5 / 4)) :=
    (hw.pow j).congr' EventuallyEq.rfl (p11cAe_pos.mono fun a ha => by
      show (a ^ (5 / 4 : ℝ)) ^ j = a ^ ((j : ℝ) * (5 / 4))
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le, mul_comm])
  exact ((p11cAe_mul (p11cAe_mul hc hvi) hwj).trans
    (p11cAe_rpow_isBigO (by linarith))).congr_left fun a => by rfl

section Entries

variable {c0 c1 c2 c3 c4 c5 v w : ℝ → ℝ}
  (h0 : c0 =O[𝓝[>] 0] fun a : ℝ => a ^ (1 : ℝ))
  (h1 : c1 =O[𝓝[>] 0] fun a : ℝ => a ^ (2 : ℝ))
  (h2 : c2 =O[𝓝[>] 0] fun a : ℝ => a ^ (3 / 2 : ℝ))
  (h3 : c3 =O[𝓝[>] 0] fun a : ℝ => a ^ (7 / 2 : ℝ))
  (h4 : c4 =O[𝓝[>] 0] fun a : ℝ => a ^ (9 / 4 : ℝ))
  (h5 : c5 =O[𝓝[>] 0] fun a : ℝ => a ^ (11 / 4 : ℝ))
  (hv : v =O[𝓝[>] 0] fun a : ℝ => a ^ (5 / 2 : ℝ))
  (hw : w =O[𝓝[>] 0] fun a : ℝ => a ^ (5 / 4 : ℝ))

include h0 h1 h2 h3 h4 h5 hv hw

/-- The `(1,1)` entry of `beta_def` is `8 c₁ + O(α ^ (7/2))`. -/
theorem p11cAe_entA :
    (fun a => c0 a * (1 - v a) ^ 2 + c1 a * v a ^ 2 + (c2 a + c3 a) * ((1 - v a) * v a) +
      (c4 a * (1 - v a) + c5 a * v a) * w a - c0 a) =O[𝓝[>] 0]
      fun a : ℝ => a ^ (7 / 2 : ℝ) := by
  have t1 := p11cAe_mono3 h0 hv hw 1 0 (t := 7 / 2) (by norm_num)
  have t2 := p11cAe_mono3 h0 hv hw 2 0 (t := 7 / 2) (by norm_num)
  have t3 := p11cAe_mono3 h1 hv hw 2 0 (t := 7 / 2) (by norm_num)
  have t4 := p11cAe_mono3 h2 hv hw 1 0 (t := 7 / 2) (by norm_num)
  have t5 := p11cAe_mono3 h2 hv hw 2 0 (t := 7 / 2) (by norm_num)
  have t6 := p11cAe_mono3 h3 hv hw 1 0 (t := 7 / 2) (by norm_num)
  have t7 := p11cAe_mono3 h3 hv hw 2 0 (t := 7 / 2) (by norm_num)
  have t8 := p11cAe_mono3 h4 hv hw 0 1 (t := 7 / 2) (by norm_num)
  have t9 := p11cAe_mono3 h4 hv hw 1 1 (t := 7 / 2) (by norm_num)
  have t10 := p11cAe_mono3 h5 hv hw 1 1 (t := 7 / 2) (by norm_num)
  have s1 := (t1.const_mul_left (-2))
  have s2 := s1.add t2
  have s3 := s2.add t3
  have s4 := s3.add t4
  have s5 := s4.add (t5.const_mul_left (-1))
  have s6 := s5.add t6
  have s7 := s6.add (t7.const_mul_left (-1))
  have s8 := s7.add t8
  have s9 := s8.add (t9.const_mul_left (-1))
  have s10 := s9.add t10
  exact s10.congr_left fun a => by ring

/-- The `(2,2)` entry of `beta_def` is `8 c₂ + O(α ^ 4)`. -/
theorem p11cAe_entE :
    (fun a => c0 a * v a ^ 2 + c1 a * (1 - v a) ^ 2 + (c2 a + c3 a) * ((1 - v a) * v a) -
      (c4 a * v a + c5 a * (1 - v a)) * w a - c1 a) =O[𝓝[>] 0]
      fun a : ℝ => a ^ (4 : ℝ) := by
  have t1 := p11cAe_mono3 h0 hv hw 2 0 (t := 4) (by norm_num)
  have t2 := p11cAe_mono3 h1 hv hw 1 0 (t := 4) (by norm_num)
  have t3 := p11cAe_mono3 h1 hv hw 2 0 (t := 4) (by norm_num)
  have t4 := p11cAe_mono3 h2 hv hw 1 0 (t := 4) (by norm_num)
  have t5 := p11cAe_mono3 h2 hv hw 2 0 (t := 4) (by norm_num)
  have t6 := p11cAe_mono3 h3 hv hw 1 0 (t := 4) (by norm_num)
  have t7 := p11cAe_mono3 h3 hv hw 2 0 (t := 4) (by norm_num)
  have t8 := p11cAe_mono3 h4 hv hw 1 1 (t := 4) (by norm_num)
  have t9 := p11cAe_mono3 h5 hv hw 0 1 (t := 4) (by norm_num)
  have t10 := p11cAe_mono3 h5 hv hw 1 1 (t := 4) (by norm_num)
  have s1 := t1
  have s2 := s1.add (t2.const_mul_left (-2))
  have s3 := s2.add t3
  have s4 := s3.add t4
  have s5 := s4.add (t5.const_mul_left (-1))
  have s6 := s5.add t6
  have s7 := s6.add (t7.const_mul_left (-1))
  have s8 := s7.add (t8.const_mul_left (-1))
  have s9 := s8.add (t9.const_mul_left (-1))
  have s10 := s9.add t10
  exact s10.congr_left fun a => by ring

/-- The off-diagonal entry of `beta_def` is `4 c₃ + O(α ^ (7/2))`. -/
theorem p11cAe_entB :
    (fun a => 4 * (c0 a + c1 a) * ((1 - v a) * v a) + c2 a * (1 - 2 * v a) ^ 2 +
      c3 a * ((1 - 2 * v a) ^ 2 / 2 - 2 * ((1 - v a) * v a)) +
      2 * (c5 a - c4 a) * w a * (1 - 2 * v a) - c2 a) =O[𝓝[>] 0]
      fun a : ℝ => a ^ (7 / 2 : ℝ) := by
  have t1 := p11cAe_mono3 h0 hv hw 1 0 (t := 7 / 2) (by norm_num)
  have t2 := p11cAe_mono3 h0 hv hw 2 0 (t := 7 / 2) (by norm_num)
  have t3 := p11cAe_mono3 h1 hv hw 1 0 (t := 7 / 2) (by norm_num)
  have t4 := p11cAe_mono3 h1 hv hw 2 0 (t := 7 / 2) (by norm_num)
  have t5 := p11cAe_mono3 h2 hv hw 1 0 (t := 7 / 2) (by norm_num)
  have t6 := p11cAe_mono3 h2 hv hw 2 0 (t := 7 / 2) (by norm_num)
  have t7 := p11cAe_mono3 h3 hv hw 0 0 (t := 7 / 2) (by norm_num)
  have t8 := p11cAe_mono3 h3 hv hw 1 0 (t := 7 / 2) (by norm_num)
  have t9 := p11cAe_mono3 h3 hv hw 2 0 (t := 7 / 2) (by norm_num)
  have t10 := p11cAe_mono3 h5 hv hw 0 1 (t := 7 / 2) (by norm_num)
  have t11 := p11cAe_mono3 h5 hv hw 1 1 (t := 7 / 2) (by norm_num)
  have t12 := p11cAe_mono3 h4 hv hw 0 1 (t := 7 / 2) (by norm_num)
  have t13 := p11cAe_mono3 h4 hv hw 1 1 (t := 7 / 2) (by norm_num)
  have s1 := (t1.const_mul_left (4))
  have s2 := s1.add (t2.const_mul_left (-4))
  have s3 := s2.add (t3.const_mul_left (4))
  have s4 := s3.add (t4.const_mul_left (-4))
  have s5 := s4.add (t5.const_mul_left (-4))
  have s6 := s5.add (t6.const_mul_left (4))
  have s7 := s6.add (t7.const_mul_left (1 / 2))
  have s8 := s7.add (t8.const_mul_left (-4))
  have s9 := s8.add (t9.const_mul_left (4))
  have s10 := s9.add (t10.const_mul_left (2))
  have s11 := s10.add (t11.const_mul_left (-4))
  have s12 := s11.add (t12.const_mul_left (-2))
  have s13 := s12.add (t13.const_mul_left (4))
  exact s13.congr_left fun a => by ring

end Entries

end KAM.Planetary

end
