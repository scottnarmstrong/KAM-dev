/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.CohomologicalL1Bound
public import KAM.Matrix.Norms
public import KAM.Matrix.Calculus
public import KAM.Torus.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Weighted-ℓ¹ norms on strips (package B10a)

Blueprint `bp:p2s2l1:norms` and `bp:p2s2l1:toolkit` (a), (b) of `blueprint/parts/p2s2-l1hybrid.tex`.

For `f : T_r → ℂ^ι` the bound `‖f‖_{1,r} ≤ A` is the predicate `L1Vec r f A`: every component has
    torus
coefficients summable with the weight `e^{2πr|k|₁}` (the repository's `KAM.Fourier.weightedNorm` at
    the
coefficient radius `2πr`) and weighted sum `≤ A`, and `0 ≤ A`. For a matrix function `L1Mat r M A`
    bounds every
row sum of the entry norms. No junk value enters a statement.

* `L1Vec.norm_le`, `L1Mat.norm_le`: the sup bound on the strip (the max norm and its operator norm,
    the maximal
  row sum), from the SHARP-L9 bridge `KAM.norm_le_of_l1`.
* `L1Vec.const`, `L1Vec.add`, `L1Vec.mono`: constants, sums and monotonicity in the strip.

The Wiener products are in `KAM.Sharp2.L1.NormsProduct`, the row-sum Cauchy estimates in
`KAM.Sharp2.L1.NormsCauchy`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.Sharp2.L1

open KAM KAM.Torus

variable {n : ℕ}

/-! ### The norms -/

/-- The Fourier coefficients on the real torus of the component `i` of `f`. -/
abbrev coeffR {ι : Type*} (f : (Fin n → ℂ) → ι → ℂ) (i : ι) : (Fin n → ℤ) → ℂ :=
  torusCoeff fun x => f (fun j => (x j : ℂ)) i

/-- Blueprint `bp:p2s2l1:norms` (vectors): `‖f‖_{1,r} ≤ A`, componentwise, with summability and `0
    ≤ A`
(the vector premise of `KAM.cohomological_l1`). -/
def L1Vec {ι : Type*} (r : ℝ) (f : (Fin n → ℂ) → ι → ℂ) (A : ℝ) : Prop :=
  0 ≤ A ∧ ∀ i, Fourier.SummableWeighted (2 * Real.pi * r) (coeffR f i) ∧
    Fourier.weightedNorm (2 * Real.pi * r) (coeffR f i) ≤ A

/-- Blueprint `bp:p2s2l1:norms` (matrices): every row sum of the entry norms is `≤ A`. -/
def L1Mat {ι κ : Type*} [Fintype κ] (r : ℝ) (M : (Fin n → ℂ) → Matrix ι κ ℂ) (A : ℝ) : Prop :=
  0 ≤ A ∧ (∀ i j, Fourier.SummableWeighted (2 * Real.pi * r)
      (torusCoeff fun x => M (fun l => (x l : ℂ)) i j)) ∧
    ∀ i, ∑ j, Fourier.weightedNorm (2 * Real.pi * r) (torusCoeff fun x => M (fun l => (x l : ℂ)) i
        j) ≤ A

/-- The Jacobian matrix `(∂_j f_i)`. -/
def jac {ι : Type*} (f : (Fin n → ℂ) → ι → ℂ) (θ : Fin n → ℂ) : Matrix ι (Fin n) ℂ :=
  Matrix.of fun i j => fderiv ℂ f θ (Pi.single j 1) i

/-! ### Weighted sums -/

theorem weightedNorm_nonneg (s : ℝ) (a : (Fin n → ℤ) → ℂ) : 0 ≤ Fourier.weightedNorm s a :=
  tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

/-- The triangle inequality of the weighted sum. -/
theorem summableWeighted_add {s : ℝ} {a b : (Fin n → ℤ) → ℂ}
    (ha : Fourier.SummableWeighted s a) (hb : Fourier.SummableWeighted s b) :
    Fourier.SummableWeighted s (fun k => a k + b k) ∧
      Fourier.weightedNorm s (fun k => a k + b k) ≤
        Fourier.weightedNorm s a + Fourier.weightedNorm s b := by
  have hle : ∀ k, ‖a k + b k‖ * Real.exp (s * Fourier.modeSize k) ≤
      ‖a k‖ * Real.exp (s * Fourier.modeSize k) + ‖b k‖ * Real.exp (s * Fourier.modeSize k) :=
    fun k => by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (Real.exp_pos _).le
  have hs : Fourier.SummableWeighted s (fun k => a k + b k) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hle (ha.add hb)
  exact ⟨hs, (Summable.tsum_le_tsum hle hs (ha.add hb)).trans_eq (Summable.tsum_add ha hb)⟩

/-- Weighted summability and the weighted sum are monotone in the radius. -/
theorem summableWeighted_mono {s s' : ℝ} {a : (Fin n → ℤ) → ℂ} (hss : s' ≤ s)
    (ha : Fourier.SummableWeighted s a) :
    Fourier.SummableWeighted s' a ∧ Fourier.weightedNorm s' a ≤ Fourier.weightedNorm s a := by
  have hle : ∀ k, ‖a k‖ * Real.exp (s' * Fourier.modeSize k) ≤
      ‖a k‖ * Real.exp (s * Fourier.modeSize k) := fun k =>
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hss (Fourier.modeSize_nonneg k))) (norm_nonneg _)
  have hs : Fourier.SummableWeighted s' a :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hle ha
  exact ⟨hs, Summable.tsum_le_tsum hle hs ha⟩

/-- Linearity of the Fourier coefficient on sums of continuous functions. -/
theorem torusCoeff_add' {f g : (Fin n → ℝ) → ℂ} (hf : Continuous f) (hg : Continuous g)
    (k : Fin n → ℤ) : torusCoeff (fun x => f x + g x) k = torusCoeff f k + torusCoeff g k := by
  have hc : Continuous fun x : Fin n → ℝ => character (-k) (fun j => (x j : ℂ)) :=
    (differentiable_character _).continuous.comp
      (continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j))
  simp only [torusCoeff, torusAverage, mul_add]
  exact MeasureTheory.integral_add (integrableOn_unitCube_of_continuous (hc.mul hf))
    (integrableOn_unitCube_of_continuous (hc.mul hg))

/-- The restriction to `ℝⁿ` of a map holomorphic on `T_r` (`r > 0`) is continuous. -/
theorem continuous_restrict {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {r : ℝ}
    {f : (Fin n → ℂ) → F} (hr : 0 < r) (hf : DifferentiableOn ℂ f (complexStrip n r)) :
    Continuous fun x : Fin n → ℝ => f fun j => (x j : ℂ) :=
  hf.continuousOn.comp_continuous
    (continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j))
    (fun x => ofReal_mem_complexStrip hr x)

/-- The entries of a holomorphic matrix function are holomorphic. -/
theorem differentiableOn_entry {ι κ : Type*} [Fintype ι] [Fintype κ] {s : Set (Fin n → ℂ)}
    {M : (Fin n → ℂ) → Matrix ι κ ℂ} (hM : DifferentiableOn ℂ M s) (i : ι) (j : κ) :
    DifferentiableOn ℂ (fun z => M z i j) s :=
  (matEntryCLM i j).differentiable.comp_differentiableOn hM

/-! ### Sup bounds (`bp:p2s2l1:toolkit`(a)) -/

/-- Blueprint `bp:p2s2l1:toolkit`(a), vectors. -/
theorem L1Vec.norm_le {ι : Type*} [Fintype ι] {r A : ℝ} {f : (Fin n → ℂ) → ι → ℂ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (complexStrip n r)) (hfp : IsPeriodicOn f r) (h : L1Vec r f A) :
    ∀ θ ∈ complexStrip n r, ‖f θ‖ ≤ A := fun θ hθ =>
  (pi_norm_le_iff_of_nonneg h.1).mpr fun i =>
    norm_le_of_l1 (g := fun z => f z i) hr (differentiableOn_pi.mp hf i)
      (fun j z hz => congrFun (hfp j z hz) i) (h.2 i).1 (h.2 i).2 θ hθ

/-- Blueprint `bp:p2s2l1:toolkit`(a), matrices (operator norm of the max norm = maximal row sum). -/
theorem L1Mat.norm_le {ι κ : Type*} [Fintype ι] [Fintype κ] {r A : ℝ} {M : (Fin n → ℂ) → Matrix ι κ
    ℂ}
    (hr : 0 < r) (hM : DifferentiableOn ℂ M (complexStrip n r)) (hMp : IsPeriodicOn M r) (h : L1Mat
        r M A) :
    ∀ θ ∈ complexStrip n r, ‖M θ‖ ≤ A := fun θ hθ =>
  (norm_le_iff_forall_rowSum h.1).2 fun i =>
    (Finset.sum_le_sum fun j _ => norm_le_of_l1 (g := fun z => M z i j) hr (differentiableOn_entry
        hM i j)
      (fun l z hz => by simp only [hMp l z hz]) (h.2.1 i j) le_rfl θ hθ).trans (h.2.2 i)

/-! ### Constants, sums and monotonicity (`bp:p2s2l1:toolkit`(b)) -/

/-- The coefficients of a constant: `ĉ_k = c` at `k = 0`, `0` otherwise. -/
theorem torusCoeff_const (c : ℂ) (k : Fin n → ℤ) :
    torusCoeff (fun _ : Fin n → ℝ => c) k = if k = 0 then c else 0 := by
  have h : torusCoeff (fun _ : Fin n → ℝ => c) k =
      torusAverage (fun x : Fin n → ℝ => character (-k) (fun j => (x j : ℂ))) * c := by
    simp only [torusCoeff, torusAverage]
    rw [MeasureTheory.integral_mul_const]
  rw [h, torusAverage_character]
  by_cases hk : k = 0
  · subst hk
    simp
  · have hk' : -k ≠ 0 := neg_ne_zero.mpr hk
    simp [hk, hk']

/-- Blueprint `bp:p2s2l1:toolkit`(b): constants, sums, strip monotonicity. -/
theorem L1Vec.const {ι : Type*} [Fintype ι] {r : ℝ} (_hr : 0 ≤ r) (c : ι → ℂ) :
    L1Vec r (fun _ : Fin n → ℂ => c) ‖c‖ := by
  refine ⟨norm_nonneg c, fun i => ?_⟩
  have hc : coeffR (fun _ : Fin n → ℂ => c) i = fun k => if k = 0 then c i else 0 :=
    funext fun k => torusCoeff_const (c i) k
  have hz : ∀ k : Fin n → ℤ, k ≠ 0 →
      ‖(if k = 0 then c i else 0)‖ * Real.exp (2 * Real.pi * r * Fourier.modeSize k) = 0 :=
    fun k hk => by simp [hk]
  have hs : Fourier.SummableWeighted (2 * Real.pi * r) (fun k => if k = 0 then c i else 0) :=
    summable_of_ne_finset_zero (s := {0}) fun k hk => hz k (by simpa using hk)
  rw [hc]
  refine ⟨hs, ?_⟩
  have hw : Fourier.weightedNorm (2 * Real.pi * r) (fun k : Fin n → ℤ => if k = 0 then c i else 0) =
      ‖c i‖ := by
    unfold Fourier.weightedNorm
    rw [tsum_eq_single 0 hz]
    simp [Fourier.modeSize]
  rw [hw]
  exact norm_le_pi_norm c i

theorem L1Vec.add {ι : Type*} [Fintype ι] {r A B : ℝ} {f g : (Fin n → ℂ) → ι → ℂ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (complexStrip n r)) (hg : DifferentiableOn ℂ g (complexStrip n r))
    (hfA : L1Vec r f A) (hgB : L1Vec r g B) : L1Vec r (f + g) (A + B) := by
  refine ⟨add_nonneg hfA.1 hgB.1, fun i => ?_⟩
  have hc : coeffR (f + g) i = fun k => coeffR f i k + coeffR g i k := funext fun k =>
    torusCoeff_add' (continuous_restrict hr (differentiableOn_pi.mp hf i))
      (continuous_restrict hr (differentiableOn_pi.mp hg i)) k
  rw [hc]
  obtain ⟨h1, h2⟩ := summableWeighted_add (hfA.2 i).1 (hgB.2 i).1
  exact ⟨h1, h2.trans (add_le_add (hfA.2 i).2 (hgB.2 i).2)⟩

theorem L1Vec.mono {ι : Type*} {r r' A : ℝ} {f : (Fin n → ℂ) → ι → ℂ} (_hr' : 0 ≤ r') (hrr : r' ≤ r)
    (h : L1Vec r f A) : L1Vec r' f A := by
  refine ⟨h.1, fun i => ?_⟩
  have hss : 2 * Real.pi * r' ≤ 2 * Real.pi * r :=
    mul_le_mul_of_nonneg_left hrr (by positivity)
  obtain ⟨h1, h2⟩ := summableWeighted_mono hss (h.2 i).1
  exact ⟨h1, h2.trans (h.2 i).2⟩

end KAM.Sharp2.L1

end
