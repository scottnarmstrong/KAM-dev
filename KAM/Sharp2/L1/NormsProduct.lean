/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.L1.Norms
public import KAM.Fourier.Convolution
public import KAM.Strip.FourierDerivative
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Wiener products in the weighted-ℓ¹ norm (package B10a)

Blueprint `bp:p2s2l1:toolkit`(b) of `blueprint/parts/p2s2-l1hybrid.tex`.

* The bridge `torusCoeff_mul_eq_convolution`: for maps holomorphic and `1`-periodic on `T_r` with
  coefficients summable at the coefficient radius `2πr`, the coefficients of the product are the
      convolution of
  the coefficients. On the strip both maps are their Fourier series
      (`KAM.eq_fourierSum_of_summableWeighted`),
  the product of the two absolutely convergent series is the Cauchy product, and a summable series
      has its
  coefficients as Fourier coefficients (`KAM.torusCoeff_fourierSum`). This is the strip analogue of
      the
  fixed-action argument of `KAM.Weighted.coeff_mul`.
* `L1Mat.mulVec`: `‖M v‖_{1,r} ≤ ‖M‖_{1,r} ‖v‖_{1,r}` (row sums times the max over components), from
  `KAM.Fourier.weightedNorm_convolution_le`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.Sharp2.L1

open KAM KAM.Torus

variable {n : ℕ}

/-! ### The Cauchy product of two Fourier series -/

/-- `(k, l) ↦ (l, k - l)`: output mode and summation index to the two input modes. -/
def cauchyEquiv : ((Fin n → ℤ) × (Fin n → ℤ)) ≃ ((Fin n → ℤ) × (Fin n → ℤ)) where
  toFun p := (p.2, p.1 - p.2)
  invFun p := (p.1 + p.2, p.1)
  left_inv p := by ext j <;> simp
  right_inv p := by ext j <;> simp

/-- The Cauchy product `(∑ aₗ χₗ)(∑ bₗ χₗ) = ∑ₖ (∑ₗ a_{k-l} b_l) χₖ` on the strip. -/
theorem fourierSum_mul_fourierSum {s : ℝ} {a b : (Fin n → ℤ) → ℂ}
    (ha : Fourier.SummableWeighted (2 * Real.pi * s) a)
    (hb : Fourier.SummableWeighted (2 * Real.pi * s) b) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n s) :
    fourierSum a θ * fourierSum b θ = fourierSum (fun k => ∑' l, a (k - l) * b l) θ := by
  set F : (Fin n → ℤ) × (Fin n → ℤ) → ℂ := fun p =>
    (a p.1 * character p.1 θ) * (b p.2 * character p.2 θ) with hF
  have hAn : Summable fun k => ‖a k * character k θ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_coeff_mul_character_le a hθ) ha
  have hBn : Summable fun k => ‖b k * character k θ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_coeff_mul_character_le b hθ) hb
  have hFn : Summable fun p => ‖F p‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      (hAn.mul_of_nonneg hBn (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
    simp only [hF, norm_mul]
    exact le_rfl
  have hFs : Summable F := hFn.of_norm
  have hprod : fourierSum a θ * fourierSum b θ = ∑' p, F p :=
    tsum_mul_tsum_of_summable_norm hAn hBn
  have hterm : ∀ q : (Fin n → ℤ) × (Fin n → ℤ), F (cauchyEquiv q) =
      (a q.2 * b (q.1 - q.2)) * character q.1 θ := by
    intro q
    simp only [hF, cauchyEquiv, Equiv.coe_fn_mk]
    have : character q.2 θ * character (q.1 - q.2) θ = character q.1 θ := by
      rw [character_mul]; simp
    rw [← this]; ring
  have hFq : Summable fun q => F (cauchyEquiv q) := cauchyEquiv.summable_iff.mpr hFs
  rw [hprod, ← cauchyEquiv.tsum_eq F, hFq.tsum_prod]
  unfold fourierSum
  refine tsum_congr fun k => ?_
  simp only [hterm]
  rw [tsum_mul_right]
  congr 1
  exact (Equiv.subLeft k).tsum_eq (fun l => a l * b (k - l)) |>.symm.trans <| by
    refine tsum_congr fun l => ?_
    simp [Equiv.subLeft_apply]

/-- The coefficient convolution in the orientation of the Cauchy product. -/
theorem convolution_eq_tsum (a b : (Fin n → ℤ) → ℂ) :
    Fourier.convolution a b = fun k => ∑' l, a (k - l) * b l := by
  funext k
  unfold Fourier.convolution
  rw [← (Equiv.subLeft k).tsum_eq (fun l => a (k - l) * b l)]
  refine tsum_congr fun l => ?_
  simp [Equiv.subLeft_apply]

/-! ### The product bridge -/

/-- **Coefficients of a product.** For `u, v` holomorphic and `1`-periodic on `T_r` with
coefficients summable at radius `2πr`, the coefficients of `u v` on `ℝⁿ` are the convolution of
those of `u` and `v`. -/
theorem torusCoeff_mul_eq_convolution {r : ℝ} (hr : 0 < r) {u v : (Fin n → ℂ) → ℂ}
    (hu : DifferentiableOn ℂ u (complexStrip n r)) (hup : IsPeriodicOn u r)
    (hv : DifferentiableOn ℂ v (complexStrip n r)) (hvp : IsPeriodicOn v r)
    (hus : Fourier.SummableWeighted (2 * Real.pi * r) (torusCoeff fun x => u fun j => (x j : ℂ)))
    (hvs : Fourier.SummableWeighted (2 * Real.pi * r) (torusCoeff fun x => v fun j => (x j : ℂ))) :
    (torusCoeff fun x => u (fun j => (x j : ℂ)) * v (fun j => (x j : ℂ))) =
      Fourier.convolution (torusCoeff fun x => u fun j => (x j : ℂ))
        (torusCoeff fun x => v fun j => (x j : ℂ)) := by
  have hs : 0 ≤ 2 * Real.pi * r := by positivity
  have hx : (fun x : Fin n → ℝ => u (fun j => (x j : ℂ)) * v (fun j => (x j : ℂ))) =
      fun x => fourierSum (fun k => ∑' l, (torusCoeff fun x => u fun j => (x j : ℂ)) (k - l) *
        (torusCoeff fun x => v fun j => (x j : ℂ)) l) (fun j => (x j : ℂ)) := by
    funext x
    have hθ := ofReal_mem_complexStrip hr x
    rw [eq_fourierSum_of_summableWeighted hr hu hup hus _ hθ,
      eq_fourierSum_of_summableWeighted hr hv hvp hvs _ hθ, fourierSum_mul_fourierSum hus hvs hθ]
  funext k
  rw [hx, ← convolution_eq_tsum]
  exact torusCoeff_fourierSum hr.le (hus.convolution hs hvs) k

/-- Linearity of the Fourier coefficient over finite sums of continuous functions. -/
theorem torusCoeff_finset_sum {ι : Type*} (s : Finset ι) {F : ι → (Fin n → ℝ) → ℂ}
    (hF : ∀ i, Continuous (F i)) (k : Fin n → ℤ) :
    torusCoeff (fun x => ∑ i ∈ s, F i x) k = ∑ i ∈ s, torusCoeff (F i) k := by
  simpa using torusCoeff_finset_sum_mul s hF (fun _ => 1) k

/-- The triangle inequality of the weighted sum over a finite family. -/
theorem summableWeighted_finset_sum {ι : Type*} (t : Finset ι) {s : ℝ} {c : ι → (Fin n → ℤ) → ℂ}
    (hc : ∀ i ∈ t, Fourier.SummableWeighted s (c i)) :
    Fourier.SummableWeighted s (fun k => ∑ i ∈ t, c i k) ∧
      Fourier.weightedNorm s (fun k => ∑ i ∈ t, c i k) ≤ ∑ i ∈ t, Fourier.weightedNorm s (c i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [Fourier.SummableWeighted, Fourier.weightedNorm]
  | @insert i t hi ih =>
    have hci := hc i (Finset.mem_insert_self i t)
    obtain ⟨h1, h2⟩ := ih fun j hj => hc j (Finset.mem_insert_of_mem hj)
    simp only [Finset.sum_insert hi]
    obtain ⟨h3, h4⟩ := summableWeighted_add hci h1
    exact ⟨h3, h4.trans (add_le_add le_rfl h2)⟩

/-! ### Matrix times vector (`bp:p2s2l1:toolkit`(b)) -/

/-- Blueprint `bp:p2s2l1:toolkit`(b): the Wiener product, matrix times vector. -/
theorem L1Mat.mulVec {ι κ : Type*} [Fintype ι] [Fintype κ] {r A B : ℝ}
    {M : (Fin n → ℂ) → Matrix ι κ ℂ} {v : (Fin n → ℂ) → κ → ℂ} (hr : 0 < r)
    (hM : DifferentiableOn ℂ M (complexStrip n r)) (hMp : IsPeriodicOn M r)
    (hv : DifferentiableOn ℂ v (complexStrip n r)) (hvp : IsPeriodicOn v r) (hMA : L1Mat r M A)
    (hvB : L1Vec r v B) : L1Vec r (fun θ => M θ *ᵥ v θ) (A * B) := by
  have hs : 0 ≤ 2 * Real.pi * r := by positivity
  refine ⟨mul_nonneg hMA.1 hvB.1, fun i => ?_⟩
  have hMij : ∀ j, DifferentiableOn ℂ (fun z => M z i j) (complexStrip n r) := fun j =>
    differentiableOn_entry hM i j
  have hMijp : ∀ j, IsPeriodicOn (fun z => M z i j) r := fun j l z hz => by simp only [hMp l z hz]
  have hvj : ∀ j, DifferentiableOn ℂ (fun z => v z j) (complexStrip n r) := fun j =>
    differentiableOn_pi.mp hv j
  have hvjp : ∀ j, IsPeriodicOn (fun z => v z j) r := fun j l z hz => congrFun (hvp l z hz) j
  have hc : coeffR (fun θ => M θ *ᵥ v θ) i = fun k => ∑ j,
      Fourier.convolution (torusCoeff fun x => M (fun l => (x l : ℂ)) i j) (coeffR v j) k := by
    funext k
    have h1 : coeffR (fun θ => M θ *ᵥ v θ) i =
        torusCoeff fun x => ∑ j, M (fun l => (x l : ℂ)) i j * v (fun l => (x l : ℂ)) j := by
      simp only [coeffR, Matrix.mulVec, dotProduct]
    rw [h1, torusCoeff_finset_sum (F := fun j (x : Fin n → ℝ) =>
        M (fun l => (x l : ℂ)) i j * v (fun l => (x l : ℂ)) j) _
      (fun j => (continuous_restrict hr (hMij j)).mul (continuous_restrict hr (hvj j)))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [torusCoeff_mul_eq_convolution hr (hMij j) (hMijp j) (hvj j) (hvjp j) (hMA.2.1 i j)
      (hvB.2 j).1]
  rw [hc]
  obtain ⟨h1, h2⟩ := summableWeighted_finset_sum Finset.univ
    (fun j _ => (hMA.2.1 i j).convolution hs (hvB.2 j).1)
  refine ⟨h1, h2.trans ?_⟩
  calc ∑ j, Fourier.weightedNorm (2 * Real.pi * r)
        (Fourier.convolution (torusCoeff fun x => M (fun l => (x l : ℂ)) i j) (coeffR v j))
      ≤ ∑ j, Fourier.weightedNorm (2 * Real.pi * r)
          (torusCoeff fun x => M (fun l => (x l : ℂ)) i j) * B :=
        Finset.sum_le_sum fun j _ =>
          (Fourier.weightedNorm_convolution_le hs (hMA.2.1 i j) (hvB.2 j).1).trans
            (mul_le_mul_of_nonneg_left (hvB.2 j).2 (weightedNorm_nonneg _ _))
    _ = (∑ j, Fourier.weightedNorm (2 * Real.pi * r)
          (torusCoeff fun x => M (fun l => (x l : ℂ)) i j)) * B := (Finset.sum_mul ..).symm
    _ ≤ A * B := mul_le_mul_of_nonneg_right (hMA.2.2 i) hvB.1

end KAM.Sharp2.L1

end
