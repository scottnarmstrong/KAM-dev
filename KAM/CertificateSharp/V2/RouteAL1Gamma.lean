/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.SmallDivQ
public import KAM.Strip.CohomologicalL1Cert
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `Γ_∞` from a clock box (package C6L1)

The ℓ¹ entry needs `Γ_∞(sω*, δ) = sup_{k≠0} e^{-2πδ|k|₁}/(2π|k·sω*|)` at `δ = δ₀` and `δ = ρ'`,
for every `ω*` of the certificate's box. For a clock box `[(c₀, r₀), (κ, 0)]` (C2's `clockOk`),
`ω* = κ (ω', 1)` with `|ω' - c₀/κ| ≤ r₀/κ`, and `sω* = (sκ)(ω', 1)`:

* `fibCheck`, `fibCheck_sound`: SHARP-L9's fibered certificate `KAM.smallDivisorSup_snoc_le` on an
  interval of `ω'`, one entry per `0 < |k'| ≤ N` (package B10C's `GInfData` with the interval as
  data): the nearest integer `p(k')` of `-k'c`, the lower bound `|k'c + p| - |k'| r`, and
  `E₁ ≥ e^{-2πδ}` by a degree-four Taylor test with `2π ≥ 6.283`;
* `smallDivisorSup_smul_le`: `Γ_∞(tω, δ) ≤ Γ_∞(ω, δ)/t` for `t > 0`;
* `gamOk`, `gamOk_sound`: the test at a clock box and its soundness.

The box version of C5CORE (`KAM.CertificateSharp.SupData`) costs `≈ 2N²` modes; this one `2N`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.L1

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- The witness of a fibered `Γ_∞` claim: the cut-off, `E₁ ≥ e^{-2πδ}` and the claimed bound of
`Γ_∞((ω', 1), δ)`. -/
structure FibWit where
  N : ℕ
  E1 : ℚ
  claim : ℚ

/-- The Taylor polynomial `1 + y + y²/2 + y³/6 + y⁴/24` at `y = 6.283 δ`. -/
def fexpLow (δ : ℚ) : ℚ :=
  1 + 6283 / 1000 * δ + (6283 / 1000 * δ) ^ 2 / 2 + (6283 / 1000 * δ) ^ 3 / 6 +
    (6283 / 1000 * δ) ^ 4 / 24

/-- The nearest integer of `-z c`. -/
def fpk (c : ℚ) (z : ℤ) : ℤ := ⌊-((z : ℚ) * c) + 1 / 2⌋

/-- `|z c + p(z)|`. -/
def fdist (c : ℚ) (z : ℤ) : ℚ := |(z : ℚ) * c + (fpk c z : ℚ)|

/-- The lower bound of `|z ω' + p(z)|` for `|ω' - c| ≤ r`. -/
def flb (c r : ℚ) (z : ℤ) : ℚ := fdist c z - |(z : ℚ)| * r

/-- The test of the fiber `k' = z`. -/
def fiberOkL (c r : ℚ) (w : FibWit) (z : ℤ) : Bool :=
  decide (fdist c z + |(z : ℚ)| * r ≤ 1 / 2) && decide (0 < flb c r z) &&
    decide (w.E1 ^ (z.natAbs + (fpk c z).natAbs) ≤ w.claim * (628 / 100 * flb c r z)) &&
    decide (w.E1 ^ z.natAbs ≤ w.claim * (314 / 100))

/-- The rational test of `Γ_∞((ω', 1), δ) ≤ claim` for `|ω' - c| ≤ r` and `(ω', 1)`
`(g, 1)`-Diophantine. -/
def fibCheck (c r g δ : ℚ) (w : FibWit) : Bool :=
  decide (0 < δ) && decide (0 < g) && decide (1 ≤ 628 / 100 * δ * (w.N + 1)) &&
    decide (1 ≤ w.E1 * fexpLow δ) &&
    decide (((w.N : ℚ) + 1) * w.E1 ^ (w.N + 1) ≤ w.claim * (628 / 100 * g)) &&
    decide (w.E1 ≤ w.claim * (628 / 100)) &&
    (List.range w.N).all fun j => fiberOkL c r w ((j : ℤ) + 1) && fiberOkL c r w (-((j : ℤ) + 1))

theorem fdot_one (ι : ℝ) (k : Fin 1 → ℤ) :
    Diophantine.frequencyDot ![ι] k = (k 0 : ℝ) * ι := by
  simp [Diophantine.frequencyDot]

theorem fabs_dot_bounds {c r : ℚ} {ι : ℝ} (hι : |ι - c| ≤ r) (z : ℤ) :
    |(z : ℝ) * ι + (fpk c z : ℝ)| ≤ (fdist c z : ℝ) + |(z : ℝ)| * r ∧
      (flb c r z : ℝ) ≤ |(z : ℝ) * ι + (fpk c z : ℝ)| := by
  have hd : |(z : ℝ) * ι - (z : ℝ) * c| ≤ |(z : ℝ)| * r := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hι (abs_nonneg _)
  have hdist : ((fdist c z : ℚ) : ℝ) = |(z : ℝ) * c + (fpk c z : ℝ)| := by
    simp [fdist]
  have e : (z : ℝ) * ι + (fpk c z : ℝ) =
      ((z : ℝ) * c + (fpk c z : ℝ)) + ((z : ℝ) * ι - (z : ℝ) * c) := by ring
  constructor
  · rw [e, hdist]
    exact (abs_add_le _ _).trans (add_le_add le_rfl hd)
  · have hlb : ((flb c r z : ℚ) : ℝ) = (fdist c z : ℝ) - |(z : ℝ)| * r := by
      simp [flb]
    rw [hlb, hdist, e]
    have := abs_sub_abs_le_abs_sub ((z : ℝ) * c + (fpk c z : ℝ))
      (-((z : ℝ) * ι - (z : ℝ) * c))
    rw [abs_neg, sub_neg_eq_add] at this
    linarith

theorem fmodeNat_one (k : Fin 1 → ℤ) : modeNat k = (k 0).natAbs := by
  simp [modeNat]

theorem fiberOkL_of {c r : ℚ} {w : FibWit} (h : (List.range w.N).all
      (fun j => fiberOkL c r w ((j : ℤ) + 1) && fiberOkL c r w (-((j : ℤ) + 1))) = true)
    {k : Fin 1 → ℤ} (hk : k ∈ modeBox 1 w.N) : fiberOkL c r w (k 0) = true := by
  rw [List.all_eq_true] at h
  obtain ⟨hk0, hkN⟩ := mem_modeBox.mp hk
  rw [fmodeNat_one] at hkN
  have hz : k 0 ≠ 0 := fun h0 => hk0 (funext fun i => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simpa using h0)
  have hpos : 0 < (k 0).natAbs := Int.natAbs_pos.mpr hz
  have hj := h ((k 0).natAbs - 1) (List.mem_range.mpr (by omega))
  rw [Bool.and_eq_true] at hj
  have e : (((k 0).natAbs - 1 : ℕ) : ℤ) + 1 = ((k 0).natAbs : ℤ) := by omega
  rw [e] at hj
  rcases Int.natAbs_eq (k 0) with h1 | h1
  · rw [h1]; exact hj.1
  · rw [h1]; exact hj.2

/-- The exponential test gives `e^{-2πδ} ≤ E₁`. -/
theorem fexp_neg_le {δ E1 : ℚ} (hδ : 0 < (δ : ℝ)) (h : 1 ≤ E1 * fexpLow δ) :
    Real.exp (-(2 * Real.pi * δ)) ≤ (E1 : ℝ) := by
  have hpi := Real.pi_gt_d4
  set y : ℝ := 6283 / 1000 * δ with hy
  have hy0 : 0 ≤ y := by positivity
  have hyb : y ≤ 2 * Real.pi * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
  have hP : 1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 ≤ Real.exp (2 * Real.pi * δ) := by
    set x : ℝ := 2 * Real.pi * δ with hx
    have h1 := Real.sum_le_exp_of_nonneg (hy0.trans hyb) 5
    have e1 : ∑ i ∈ Finset.range 5, x ^ i / (i.factorial : ℝ) =
        1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [e1] at h1
    have hmono : 1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 ≤
        1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 := by
      gcongr
    exact hmono.trans h1
  have hcast : ((fexpLow δ : ℚ) : ℝ) = 1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 := by
    simp only [fexpLow, hy]
    push_cast
    ring
  have h' : (1 : ℝ) ≤ E1 * (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24) := by
    have := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at this
    rwa [← hcast]
  have hP0 : 0 < 1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 := by positivity
  have hinv : (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24)⁻¹ ≤ (E1 : ℝ) := by
    rw [inv_eq_one_div, div_le_iff₀ hP0]
    exact h'
  calc Real.exp (-(2 * Real.pi * δ)) = (Real.exp (2 * Real.pi * δ))⁻¹ := Real.exp_neg _
    _ ≤ (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24)⁻¹ := inv_anti₀ hP0 hP
    _ ≤ (E1 : ℝ) := hinv

/-- **Soundness of the fibered test** on an interval of `ω'`. -/
theorem fibCheck_sound {c r g δ : ℚ} {w : FibWit} (h : fibCheck c r g δ w = true) {ι : ℝ}
    (hι : |ι - c| ≤ r) (hdio : IsDiophantine (g : ℝ) 1 (Fin.snoc ![ι] 1 : Fin 2 → ℝ)) :
    smallDivisorSup (Fin.snoc ![ι] 1 : Fin 2 → ℝ) (δ : ℝ) ≤ (w.claim : ℝ) := by
  simp only [fibCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hδ, hg⟩, hN⟩, hE1⟩, htail⟩, hB1⟩, hlist⟩ := h
  have hbox : ∀ k ∈ modeBox 1 w.N, fdist c (k 0) + |((k 0 : ℤ) : ℚ)| * r ≤ 1 / 2 ∧
      0 < flb c r (k 0) ∧
      w.E1 ^ (modeNat k + (fpk c (k 0)).natAbs) ≤ w.claim * (628 / 100 * flb c r (k 0)) ∧
      w.E1 ^ modeNat k ≤ w.claim * (314 / 100) := fun k hk => by
    have h1 := fiberOkL_of hlist hk
    simp only [fiberOkL, Bool.and_eq_true, decide_eq_true_eq] at h1
    rw [fmodeNat_one]
    exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2, h1.2⟩
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hpi := Real.pi_gt_d2
  have hE : Real.exp (-(2 * Real.pi * δ)) ≤ (w.E1 : ℝ) := fexp_neg_le hδ' hE1
  have hEj : ∀ j : ℕ, Real.exp (-(2 * Real.pi * δ) * j) ≤ (w.E1 : ℝ) ^ j := fun j => by
    calc Real.exp (-(2 * Real.pi * δ) * j) = Real.exp (-(2 * Real.pi * δ)) ^ j := by
          rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ (w.E1 : ℝ) ^ j := pow_le_pow_left₀ (Real.exp_pos _).le hE j
  have hN' : (1 : ℝ) ≤ 2 * Real.pi * δ * (w.N + 1) := by
    have : (1 : ℝ) ≤ 628 / 100 * δ * (w.N + 1) := by
      have h := (Rat.cast_le (K := ℝ)).mpr hN
      push_cast at h
      exact h
    have hN0 : (0 : ℝ) ≤ (w.N : ℝ) + 1 := by positivity
    nlinarith
  have hc0 : (0 : ℝ) ≤ w.claim := by
    have h := (Rat.cast_le (K := ℝ)).mpr hB1
    push_cast at h
    have : (0 : ℝ) ≤ w.E1 := (Real.exp_pos _).le.trans hE
    nlinarith
  have key := smallDivisorSup_snoc_le (m := 1) (ω' := ![ι]) hdio hg' zero_le_one hδ' hN'
    (fun k => fpk c (k 0)) (fun k => (flb c r (k 0) : ℝ))
    (fun k hk => by
      rw [fdot_one]
      have h1 := (fabs_dot_bounds hι (k 0)).1
      have h2 := (Rat.cast_le (K := ℝ)).mpr (hbox k hk).1
      push_cast at h2
      linarith)
    (fun k hk => by
      rw [fdot_one]
      exact ⟨by exact_mod_cast (hbox k hk).2.1, (fabs_dot_bounds hι (k 0)).2⟩)
    (fun j => (w.E1 : ℝ) ^ j) hEj (B := (w.claim : ℝ))
    (by
      rw [pow_one, div_le_iff₀ (by positivity)]
      have h := (Rat.cast_le (K := ℝ)).mpr hB1
      push_cast at h
      nlinarith)
    (fun k hk => by
      obtain ⟨-, hL, hEk, hEk'⟩ := hbox k hk
      have hL' : (0 : ℝ) < flb c r (k 0) := by exact_mod_cast hL
      have hEk2 : (w.E1 : ℝ) ^ (modeNat k + (fpk c (k 0)).natAbs) ≤
          w.claim * (628 / 100 * flb c r (k 0)) := by
        have h := (Rat.cast_le (K := ℝ)).mpr hEk
        push_cast at h
        exact h
      have hEk3 : (w.E1 : ℝ) ^ modeNat k ≤ w.claim * (314 / 100) := by
        have h := (Rat.cast_le (K := ℝ)).mpr hEk'
        push_cast at h
        exact h
      refine ⟨?_, ?_⟩
      · rw [div_le_iff₀ (by positivity)]
        have h2 : (628 / 100 : ℝ) * flb c r (k 0) ≤ 2 * Real.pi * flb c r (k 0) :=
          mul_le_mul_of_nonneg_right (by linarith) hL'.le
        nlinarith
      · rw [div_le_iff₀ Real.pi_pos]
        nlinarith)
  refine key.trans (max_le le_rfl ?_)
  have htail' : ((w.N : ℝ) + 1) * (w.E1 : ℝ) ^ (w.N + 1) ≤ w.claim * (628 / 100 * g) := by
    have h := (Rat.cast_le (K := ℝ)).mpr htail
    push_cast at h
    exact h
  have hexp : Real.exp (-(2 * Real.pi * δ) * ((w.N : ℝ) + 1)) ≤ (w.E1 : ℝ) ^ (w.N + 1) := by
    have := hEj (w.N + 1)
    push_cast at this
    exact this
  unfold sdSupTail
  rw [Real.rpow_one, div_le_iff₀ (by positivity)]
  have hN0 : (0 : ℝ) ≤ (w.N : ℝ) + 1 := by positivity
  calc ((w.N : ℝ) + 1) * Real.exp (-(2 * Real.pi * δ) * ((w.N : ℝ) + 1))
      ≤ ((w.N : ℝ) + 1) * (w.E1 : ℝ) ^ (w.N + 1) := mul_le_mul_of_nonneg_left hexp hN0
    _ ≤ w.claim * (628 / 100 * g) := htail'
    _ ≤ w.claim * (2 * Real.pi * g) := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        nlinarith

/-- `Γ_∞(tω, δ) ≤ Γ_∞(ω, δ)/t` for `t > 0`. -/
theorem smallDivisorSup_smul_le {m : ℕ} {ω : Fin m → ℝ} {γ τ δ t : ℝ}
    (hω : Diophantine.Condition ω γ τ) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (ht : 0 < t) :
    smallDivisorSup (t • ω) δ ≤ smallDivisorSup ω δ / t := by
  refine smallDivisorSup_le_of_forall (div_nonneg (smallDivisorSup_nonneg _ _) ht.le)
    fun k hk => ?_
  have hdot : Diophantine.frequencyDot (t • ω) k = t * Diophantine.frequencyDot ω k := by
    simp only [Diophantine.frequencyDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hterm := smallDivisorSupTerm_le_smallDivisorSup hω hγ hτ hδ k
  rw [smallDivisorSupTerm_of_ne hk] at hterm
  rw [hdot, abs_mul, abs_of_pos ht]
  have e : Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) /
      (2 * Real.pi * (t * |Diophantine.frequencyDot ω k|)) =
      Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) /
        (2 * Real.pi * |Diophantine.frequencyDot ω k|) / t := by
    rw [div_div]; ring_nf
  rw [e]
  exact div_le_div_of_nonneg_right hterm ht.le

/-- The test of `Γ_∞(sω*, δ) ≤ G` at a clock box `[(c₀, r₀), (κ, 0)]`. -/
def gamOk (box : FreqBox) (κ γ s δ G : ℚ) (w : FibWit) : Bool :=
  clockOk box κ && decide (0 < s) &&
    fibCheck ((box.getD 0 (0, 0)).1 / κ) ((box.getD 0 (0, 0)).2 / κ) (γ / κ) δ w &&
    decide (w.claim ≤ G * (s * κ))

/-- **Soundness of the test at a clock box.** -/
theorem gamOk_sound {box : FreqBox} {κ γ s δ G : ℚ} {w : FibWit}
    (h : gamOk box κ γ s δ G w = true) {ωstar : Fin 2 → ℝ} (hω : FreqEncloses 2 box ωstar)
    (hdio : IsDiophantine (γ : ℝ) 1 ωstar) :
    smallDivisorSup ((s : ℝ) • ωstar) (δ : ℝ) ≤ (G : ℝ) := by
  simp only [gamOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hκ, hs⟩, hfib⟩, hG⟩ := h
  have hκ1 := hκ
  simp only [clockOk, Bool.and_eq_true, decide_eq_true_eq] at hκ1
  obtain ⟨hκ0, hbx⟩ := hκ1
  have hκ' : (0 : ℝ) < κ := by exact_mod_cast hκ0
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hδ : (0 : ℚ) < δ := by
    simp only [fibCheck, Bool.and_eq_true, decide_eq_true_eq] at hfib
    exact hfib.1.1.1.1.1.1
  have hg : (0 : ℚ) < γ / κ := by
    simp only [fibCheck, Bool.and_eq_true, decide_eq_true_eq] at hfib
    exact hfib.1.1.1.1.1.2
  have h1 : ωstar 1 = κ := by
    have := hω 1
    simp only [Fin.val_one, hbx] at this
    push_cast at this
    have h0 : |ωstar 1 - κ| = 0 := le_antisymm this (abs_nonneg _)
    exact sub_eq_zero.1 (abs_eq_zero.1 h0)
  set ι : ℝ := ωstar 0 / κ with hιd
  have hsn : (Fin.snoc ![ι] 1 : Fin 2 → ℝ) = (κ : ℝ)⁻¹ • ωstar := by
    funext i
    fin_cases i
    · simp [hιd, Fin.snoc, div_eq_inv_mul]
    · have : (κ : ℝ)⁻¹ * ωstar 1 = 1 := by rw [h1]; exact inv_mul_cancel₀ hκ'.ne'
      simpa [Fin.snoc] using this.symm
  have hsω : (s : ℝ) • ωstar = ((s : ℝ) * κ) • (Fin.snoc ![ι] 1 : Fin 2 → ℝ) := by
    rw [hsn, smul_smul, mul_assoc, mul_inv_cancel₀ hκ'.ne', mul_one]
  have hι : |ι - (((box.getD 0 (0, 0)).1 / κ : ℚ) : ℝ)| ≤
      (((box.getD 0 (0, 0)).2 / κ : ℚ) : ℝ) := by
    have h0 := hω 0
    simp only [Fin.val_zero] at h0
    push_cast
    rw [hιd, ← sub_div, abs_div, abs_of_pos hκ']
    exact div_le_div_of_nonneg_right h0 hκ'.le
  have hdio' : IsDiophantine (((γ / κ : ℚ)) : ℝ) 1 (Fin.snoc ![ι] 1 : Fin 2 → ℝ) := by
    have h2 := KAM.CertificateSharp.isDiophantine_smul hdio ((κ : ℝ)⁻¹)
    have e1 : (γ : ℝ) * |(κ : ℝ)⁻¹| = ((γ / κ : ℚ) : ℝ) := by
      rw [abs_of_pos (inv_pos.2 hκ')]; push_cast; rw [div_eq_mul_inv]
    have e2 : (fun i => (κ : ℝ)⁻¹ * ωstar i) = (Fin.snoc ![ι] 1 : Fin 2 → ℝ) := by
      rw [hsn]; rfl
    rwa [e1, e2] at h2
  have hF := fibCheck_sound hfib hι hdio'
  have hg' : (0 : ℝ) < ((γ / κ : ℚ) : ℝ) := by exact_mod_cast hg
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hsc := smallDivisorSup_smul_le (t := (s : ℝ) * κ) hdio'.condition hg' zero_le_one hδ'
    (mul_pos hs' hκ')
  rw [hsω]
  refine hsc.trans ?_
  rw [div_le_iff₀ (mul_pos hs' hκ')]
  have hG' : (w.claim : ℝ) ≤ G * (s * κ) := by exact_mod_cast hG
  exact hF.trans hG'

end KAM.CertificateSharp.V2.L1

end
