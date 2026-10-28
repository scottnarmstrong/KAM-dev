/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGMeasure.Setting
public import KAM.Planetary.PGMeasure.LatticeTail
public import KAM.Planetary.PGMeasure.ResonanceSlow
public import KAM.Planetary.PGMeasure.ResonanceFast
public import KAM.Planetary.PGMeasure.ResonanceLarge
public import KAM.Planetary.Hamiltonian.Diophantine

/-!
# P Part 4: the two-scale Diophantine measure bound (`bpP:p4:two-scale-diophantine-measure`)

The explicit constants `measure_c1`, `measure_c2`, the identification `resonanceBad_eq` of the
resonance union with the complement of the two-scale set `𝒟_{α₁,α₂,τ}`, and the measure estimate
`two_scale_diophantine_measure`, assembled from the slow (`stepP:p4:dm-slow`, P4-R0), fast
(`stepP:p4:dm-y`, `stepP:p4:dm-A`, P4-RA) and large (`stepP:p4:dm-Bstruct`, `stepP:p4:dm-B`, P4-RB)
resonance helpers (`stepP:p4:dm-sum`). Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`,
package P4-M.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b n : ℕ}

def measure_c1 (d : MeasureData a b) : ℝ :=
  d.Lg^(a+b)/(volume d.core).toReal * max (4*(2*d.Ry)^(a-1)*latticeS (a+b) d.tau)
    (4*b^2*d.LB*(2*d.Ry)^a * (2*3^(a+b-1)/(d.tau+1-(a+b:ℕ))) *
      (4*d.LN*d.Lg)^(d.tau+1-(a+b:ℕ)))

def measure_c2 (d : MeasureData a b) : ℝ := b*d.LB*latticeS b (d.tau+1)

theorem resonanceBad_eq (F : (Fin (a+b) → ℝ) → Fin (a+b) → ℝ)
    (D : Set (Fin (a+b) → ℝ)) (alpha1 alpha2 tau : ℝ) :
    resonanceBad F D alpha1 alpha2 tau =
      {J ∈ D | F J ∉ twoScaleDiophantine a b alpha1 alpha2 tau} := by
  ext J
  constructor
  · rintro ⟨hJ, k, hk, h⟩
    refine ⟨hJ, fun hdio => ?_⟩
    refine absurd h (not_lt.mpr ?_)
    by_cases h0 : (blockFast k : Fin a → ℤ) = 0
    · simp only [h0, ↓reduceIte]
      exact hdio.2 k hk h0
    · simp only [h0, ↓reduceIte]
      exact hdio.1 k h0
  · rintro ⟨hJ, hnot⟩
    refine ⟨hJ, ?_⟩
    by_contra hcon
    push Not at hcon
    refine hnot ⟨fun k h0 => ?_, fun k hk h0 => ?_⟩
    · have hk : k ≠ 0 := fun h => h0 (by rw [h]; rfl)
      have h0' : ¬ ((blockFast k : Fin a → ℤ) = 0) := h0
      have := hcon k hk
      simpa only [h0', ↓reduceIte] using this
    · have h0' : (blockFast k : Fin a → ℤ) = 0 := h0
      have := hcon k hk
      simpa only [h0', ↓reduceIte] using this

theorem latticeS_nonneg {m : ℕ} {tau : ℝ} (h : (m : ℝ) < tau) : 0 ≤ latticeS m tau := by
  unfold latticeS
  have h1 : 0 < tau + 1 - m := by linarith
  have h2 : 0 < tau - m := by linarith
  positivity

/-- `stepP:p4:dm-slow`, `dm-y`, `dm-A`, `dm-B`: every resonant action is a slow resonance, or the
`pullMap` image of a fast-dominant or large-mode frequency-coordinate resonance. -/
theorem resonanceBad_subset_union (d : MeasureData a b) (mu alpha1 alpha2 : ℝ)
    (Q : Set (Fin b → ℝ)) :
    resonanceBad (freq d.H0 d.P0 d.Omega d.beta mu) (joinedActions d.core Q) alpha1 alpha2 d.tau ⊆
      ({J : Fin (a+b) → ℝ | J ∈ joinedActions d.core Q ∧
        ∃ k : Fin (a+b) → ℤ, k ≠ 0 ∧ blockFast k = 0 ∧
          |∑ i, (k i : ℝ) * freq d.H0 d.P0 d.Omega d.beta mu J i| <
            alpha2 / (∑ i, |(k i : ℝ)|) ^ d.tau} ∪
      pullMap d '' (⋃ k ∈ fastModes a b mu d.LN d.Lg,
        resonanceSet d mu Q k (alpha1 / l1 k ^ d.tau))) ∪
      pullMap d '' (⋃ k ∈ largeModes a b mu d.LN d.Lg,
        resonanceSet d mu Q k (alpha1 / l1 k ^ d.tau)) := by
  rintro J ⟨hJ, k, hk, h⟩
  by_cases h0 : (blockFast k : Fin a → ℤ) = 0
  · refine Or.inl (Or.inl ⟨hJ, k, hk, h0, ?_⟩)
    simpa [h0] using h
  · have h' : |∑ i, (k i : ℝ) * freq d.H0 d.P0 d.Omega d.beta mu J i| < alpha1 / l1 k ^ d.tau := by
      simpa [h0, l1] using h
    obtain ⟨z, hz, rfl⟩ := mem_pullMap_image_of_resonant d mu hJ h'
    by_cases hl : ‖kFast k‖ / 2 < mu * d.LN * d.Lg * l1 k
    · exact Or.inr ⟨z, mem_biUnion (x := k) ⟨h0, hl⟩ hz, rfl⟩
    · exact Or.inl (Or.inr ⟨z, mem_biUnion (x := k) ⟨h0, not_lt.mp hl⟩ hz, rfl⟩)

theorem two_scale_diophantine_measure (d : MeasureData a b)
    (lambda mu alpha1 alpha2 : ℝ) (hl : 0 < lambda) (hl0 : lambda ≤ d.lambda0)
    (hmu : mu ∈ Ioc 0 d.mu1) (ha1 : 0 < alpha1) (ha2 : 0 < alpha2)
    (Q : Set (Fin b → ℝ)) (hQ : MeasurableSet Q) (hQsub : Q ⊆ actionShell b (-lambda) lambda) :
    volume (resonanceBad (freq d.H0 d.P0 d.Omega d.beta mu)
      (joinedActions d.core Q) alpha1 alpha2 d.tau) ≤
      ENNReal.ofReal (measure_c1 d*alpha1*(1+mu^(d.tau-(a+b:ℕ))/lambda)+
        measure_c2 d*(alpha2/mu)/lambda) *
        volume d.core * ENNReal.ofReal ((2*lambda)^b) := by
  have hmu0 := hmu.1
  have hLN0 : 0 < d.LN := by linarith [d.hLN]
  have hLg0 : 0 < d.Lg := by linarith [d.hLg]
  have hLB0 : 0 < d.LB := by linarith [d.hLB]
  have hRy0 := d.hRy
  have hvcfin : volume d.core ≠ ⊤ := d.hcore.measure_lt_top.ne
  set vcr : ℝ := (volume d.core).toReal with hvcr
  have hvcpos : 0 < vcr := ENNReal.toReal_pos d.hvol.ne' hvcfin
  have hvc : volume d.core = ENNReal.ofReal vcr := (ENNReal.ofReal_toReal hvcfin).symm
  have hW0 : 0 ≤ (2 * lambda) ^ b := by positivity
  have hS0 := slow_resonance_measure_le d hl hl0 hmu ha2 hQ hQsub
  have hA := fast_modes_measure_le d hmu hl hl0 hQ hQsub ha1
  have hB := large_modes_measure_le d hmu hl hl0 hQ hQsub ha1
  have hUA : ∀ z ∈ (⋃ k ∈ fastModes a b mu d.LN d.Lg,
      resonanceSet d mu Q k (alpha1 / l1 k ^ d.tau)), blockFast z ∈ freqCore d := by
    intro z hz
    simp only [mem_iUnion] at hz
    obtain ⟨k, -, hz⟩ := hz
    exact hz.1
  have hUB : ∀ z ∈ (⋃ k ∈ largeModes a b mu d.LN d.Lg,
      resonanceSet d mu Q k (alpha1 / l1 k ^ d.tau)), blockFast z ∈ freqCore d := by
    intro z hz
    simp only [mem_iUnion] at hz
    obtain ⟨k, -, hz⟩ := hz
    exact hz.1
  have hA' := (volume_pullMap_image_le d hUA).trans (mul_le_mul_right hA _)
  have hB' := (volume_pullMap_image_le d hUB).trans (mul_le_mul_right hB _)
  refine (measure_mono (resonanceBad_subset_union d mu alpha1 alpha2 Q)).trans
    ((measure_union_le _ _).trans ((add_le_add_left (measure_union_le _ _) _).trans ?_))
  refine (add_le_add (add_le_add hS0 hA') hB').trans ?_
  have hnτ : ((a + b : ℕ) : ℝ) < d.tau := d.htau
  have hbτ : (b : ℝ) < d.tau + 1 := by
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    push_cast at hnτ
    linarith
  have hden : 0 < d.tau + 1 - ((a + b : ℕ) : ℝ) := by linarith
  have hS1 := latticeS_nonneg hnτ
  have hS2 := latticeS_nonneg hbτ
  have hM0 : 0 ≤ mu ^ (d.tau - ((a + b : ℕ) : ℝ)) := Real.rpow_nonneg hmu0.le _
  have hP0 : 0 ≤ (4 * d.LN * d.Lg) ^ (d.tau + 1 - ((a + b : ℕ) : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hC0 : 0 ≤ 2 * (3 : ℝ) ^ (a + b - 1) / (d.tau + 1 - ((a + b : ℕ) : ℝ)) :=
    div_nonneg (by positivity) hden.le
  have hG0 : 0 ≤ d.Lg ^ (a + b) := by positivity
  unfold measure_c1 measure_c2
  set B' : ℝ := 4 * b ^ 2 * d.LB * (2 * d.Ry) ^ a *
    (2 * 3 ^ (a + b - 1) / (d.tau + 1 - ((a + b : ℕ) : ℝ))) *
    (4 * d.LN * d.Lg) ^ (d.tau + 1 - ((a + b : ℕ) : ℝ)) with hB'def
  have hB'0 : 0 ≤ B' := by positivity
  set A : ℝ := 4 * (2 * d.Ry) ^ (a - 1) * latticeS (a + b) d.tau with hAdef
  have hA0 : 0 ≤ A := by positivity
  set M : ℝ := mu ^ (d.tau - ((a + b : ℕ) : ℝ)) with hMdef
  set W : ℝ := (2 * lambda) ^ b with hWdef
  set G : ℝ := d.Lg ^ (a + b) with hGdef
  set x0 : ℝ := b * d.LB * latticeS b (d.tau + 1) * (alpha2 / mu) / lambda with hx0def
  have hx0 : 0 ≤ x0 := by positivity
  set m : ℝ := max A B' with hmdef
  have hm0 : 0 ≤ m := hB'0.trans (le_max_right _ _)
  have hXc : 0 ≤ G / vcr * m * alpha1 * (1 + M / lambda) + x0 := by positivity
  have hreal : x0 * vcr * W + G * (A * alpha1 * W) + G * (B' * alpha1 * M / lambda * W) ≤
      (G / vcr * m * alpha1 * (1 + M / lambda) + x0) * vcr * W := by
    have e : (G / vcr * m * alpha1 * (1 + M / lambda) + x0) * vcr * W =
        G * m * alpha1 * W + G * m * alpha1 * W * (M / lambda) + x0 * vcr * W := by
      field_simp
    rw [e]
    have h1 : G * (A * alpha1 * W) ≤ G * m * alpha1 * W := by
      have := mul_le_mul_of_nonneg_left (le_max_left A B') (by positivity : 0 ≤ G * alpha1 * W)
      nlinarith
    have h2 : G * (B' * alpha1 * M / lambda * W) ≤ G * m * alpha1 * W * (M / lambda) := by
      have := mul_le_mul_of_nonneg_left (le_max_right A B')
        (by positivity : 0 ≤ G * alpha1 * W * (M / lambda))
      have e2 : G * (B' * alpha1 * M / lambda * W) = G * alpha1 * W * (M / lambda) * B' := by
        ring
      rw [e2]
      nlinarith
    linarith
  rw [← hvcr, hvc]
  have hxx : ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal y * ENNReal.ofReal vcr * ENNReal.ofReal W =
      ENNReal.ofReal (y * vcr * W) := fun y hy => by
    rw [← ENNReal.ofReal_mul hy, ← ENNReal.ofReal_mul (mul_nonneg hy hvcpos.le)]
  rw [hxx x0 hx0, ← ENNReal.ofReal_mul hG0, ← ENNReal.ofReal_mul hG0,
    hxx _ hXc, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

end KAM.Planetary

end
