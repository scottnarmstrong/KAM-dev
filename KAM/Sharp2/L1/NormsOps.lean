/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.L1.Norms
public import KAM.Strip.FourierBasic

/-!
# Operations on the weighted-ℓ¹ bounds (package B10c)

Small closure properties of `L1Vec` and `L1Mat` used by the entry step: differences, monotonicity
of `L1Mat` in the strip, congruence on the real torus (`L1Vec` only sees the values at real points)
and the zero bound.
-/

@[expose] public noncomputable section

namespace KAM.Sharp2.L1

open KAM KAM.Torus

variable {n : ℕ}

/-- `‖a - b‖_s ≤ ‖a‖_s + ‖b‖_s`. -/
theorem summableWeighted_sub {s : ℝ} {a b : (Fin n → ℤ) → ℂ}
    (ha : Fourier.SummableWeighted s a) (hb : Fourier.SummableWeighted s b) :
    Fourier.SummableWeighted s (fun k => a k - b k) ∧
      Fourier.weightedNorm s (fun k => a k - b k) ≤
        Fourier.weightedNorm s a + Fourier.weightedNorm s b := by
  have hb' : Fourier.SummableWeighted s (fun k => -b k) := by
    simpa [Fourier.SummableWeighted, norm_neg] using hb
  have hw : Fourier.weightedNorm s (fun k => -b k) = Fourier.weightedNorm s b := by
    simp [Fourier.weightedNorm, norm_neg]
  have h := summableWeighted_add ha hb'
  simp only [← sub_eq_add_neg, hw] at h
  exact h

/-- Differences: `‖f - g‖_{1,r} ≤ ‖f‖_{1,r} + ‖g‖_{1,r}`. -/
theorem L1Vec.sub {ι : Type*} {r A B : ℝ} {f g : (Fin n → ℂ) → ι → ℂ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (complexStrip n r)) (hg : DifferentiableOn ℂ g (complexStrip n r))
    (hfA : L1Vec r f A) (hgB : L1Vec r g B) : L1Vec r (f - g) (A + B) := by
  refine ⟨add_nonneg hfA.1 hgB.1, fun i => ?_⟩
  have hc : coeffR (f - g) i = fun k => coeffR f i k - coeffR g i k := funext fun k =>
    torusCoeff_sub (continuous_restrict hr (differentiableOn_pi.mp hf i))
      (continuous_restrict hr (differentiableOn_pi.mp hg i)) k
  rw [hc]
  obtain ⟨h1, h2⟩ := summableWeighted_sub (hfA.2 i).1 (hgB.2 i).1
  exact ⟨h1, h2.trans (add_le_add (hfA.2 i).2 (hgB.2 i).2)⟩

/-- `L1Mat` on a narrower strip. -/
theorem L1Mat.mono {ι κ : Type*} [Fintype κ] {r r' A : ℝ} {M : (Fin n → ℂ) → Matrix ι κ ℂ}
    (hrr : r' ≤ r) (h : L1Mat r M A) : L1Mat r' M A := by
  have hss : 2 * Real.pi * r' ≤ 2 * Real.pi * r :=
    mul_le_mul_of_nonneg_left hrr (by positivity)
  refine ⟨h.1, fun i j => (summableWeighted_mono hss (h.2.1 i j)).1, fun i => ?_⟩
  exact (Finset.sum_le_sum fun j _ => (summableWeighted_mono hss (h.2.1 i j)).2).trans (h.2.2 i)

/-- `L1Vec` depends only on the values at real points. -/
theorem L1Vec.congr_real {ι : Type*} {r A : ℝ} {f g : (Fin n → ℂ) → ι → ℂ}
    (hfg : ∀ x : Fin n → ℝ, f (fun j => (x j : ℂ)) = g (fun j => (x j : ℂ))) (h : L1Vec r f A) :
    L1Vec r g A := by
  have hc : ∀ i, coeffR g i = coeffR f i := fun i => by
    simp only [coeffR, hfg]
  exact ⟨h.1, fun i => by rw [hc i]; exact h.2 i⟩

/-- A larger bound. -/
theorem L1Vec.le {ι : Type*} {r A B : ℝ} {f : (Fin n → ℂ) → ι → ℂ} (h : L1Vec r f A)
    (hAB : A ≤ B) : L1Vec r f B :=
  ⟨h.1.trans hAB, fun i => ⟨(h.2 i).1, (h.2 i).2.trans hAB⟩⟩

/-- A larger bound. -/
theorem L1Mat.le {ι κ : Type*} [Fintype κ] {r A B : ℝ} {M : (Fin n → ℂ) → Matrix ι κ ℂ}
    (h : L1Mat r M A) (hAB : A ≤ B) : L1Mat r M B :=
  ⟨h.1.trans hAB, h.2.1, fun i => (h.2.2 i).trans hAB⟩

end KAM.Sharp2.L1

end
