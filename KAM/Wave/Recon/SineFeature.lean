/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import KAM.Frozen.Wave.Defs.EllWeight
public import KAM.Frozen.Wave.Defs.SineMode

/-!
# Analytic sine features (blueprint `bpW:w1:sine-feature`)

Infrastructure used by several nodes; the dependency graph is still being built.

For `a > 0`, `p ∈ ℝ`, `k ∈ ℕ` and `β : ℕ+ → ℝ` with `|β j| ≤ B j^ν`, the feature map
`Ψ(x)_j = β_j φ_j^{(k)}(x) / ω_{a,p}(j)` takes values in `ℓ²` and is analytic.

* `KAM.Wave.sineFeatureC` : `ℂ → ℓ²_ℂ` on the strip `|Im z| < a` (zero outside);
* `KAM.Wave.sineFeatureR` : `ℝ → ℓ²_ℝ`;
* `KAM.Wave.sineFeatureC_bound` : part (i);
* `KAM.Wave.sineFeatureC_differentiableOn`, `KAM.Wave.sineFeatureC_analyticAt` : holomorphy on the
  strip (part (ii));
* `KAM.Wave.sineFeatureR_analyticAt` : real analyticity (part (ii));
* `KAM.Wave.hasSum_inner_sineFeatureR`, `KAM.Wave.summable_abs_inner_sineFeatureR` : the pairing
  identity, absolutely convergent (part (iii)).

The `k`-th derivative of `sin` is written `sin (t + kπ/2)`.
-/

@[expose] public noncomputable section

open scoped ENNReal

namespace KAM.Wave

/-- `φ_j^{(k)}(x) = √(2/π) j^k sin(j x + kπ/2)`, the `k`-th derivative of the sine mode
(blueprint `bpW:w1:sine-feature`), on the real line. -/
def sineModeIter (k : ℕ) (j : ℕ+) (x : ℝ) : ℝ :=
  Real.sqrt (2 / Real.pi) * (j : ℝ) ^ k * Real.sin ((j : ℝ) * x + k * Real.pi / 2)

/-- The complex-argument version of `sineModeIter`. -/
def sineModeIterC (k : ℕ) (j : ℕ+) (z : ℂ) : ℂ :=
  (Real.sqrt (2 / Real.pi) : ℂ) * (j : ℂ) ^ k * Complex.sin ((j : ℂ) * z + k * Real.pi / 2)

/-- `|β j| ≤ B j^ν` with `B, ν ≥ 0`. -/
def PolyBounded (β : ℕ+ → ℝ) (B ν : ℝ) : Prop :=
  0 ≤ B ∧ 0 ≤ ν ∧ ∀ j : ℕ+, |β j| ≤ B * (j : ℝ) ^ ν

/-- The coordinates `β_j φ_j^{(k)}(x) / ω_{a,p}(j)` of the real feature. -/
def sineFeatCoord (a p : ℝ) (β : ℕ+ → ℝ) (k : ℕ) (x : ℝ) (j : ℕ+) : ℝ :=
  β j * sineModeIter k j x / ellWeight a p j

/-- The coordinates `β_j φ_j^{(k)}(z) / ω_{a,p}(j)` of the complex feature. -/
def sineFeatCoordC (a p : ℝ) (β : ℕ+ → ℝ) (k : ℕ) (z : ℂ) (j : ℕ+) : ℂ :=
  (β j : ℂ) * sineModeIterC k j z / (ellWeight a p j : ℂ)

lemma sineModeIter_zero (j : ℕ+) (x : ℝ) : sineModeIter 0 j x = sineMode j x := by
  simp [sineModeIter, sineMode]

lemma sineModeIterC_ofReal (k : ℕ) (j : ℕ+) (x : ℝ) :
    sineModeIterC k j (x : ℂ) = (sineModeIter k j x : ℝ) := by
  simp [sineModeIterC, sineModeIter, Complex.ofReal_sin]

lemma sineFeatCoordC_ofReal (a p : ℝ) (β : ℕ+ → ℝ) (k : ℕ) (x : ℝ) (j : ℕ+) :
    sineFeatCoordC a p β k (x : ℂ) j = (sineFeatCoord a p β k x j : ℝ) := by
  simp [sineFeatCoordC, sineFeatCoord, sineModeIterC_ofReal]

private lemma ellWeight_pos (a p : ℝ) (j : ℕ+) : 0 < ellWeight a p j := by
  unfold ellWeight
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

lemma norm_complex_sin_le (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-z * Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]; simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.neg_im,
      Complex.I_im]; exact Real.exp_le_exp.2 (by simpa using le_abs_self z.im)
  have h2 : ‖Complex.exp (z * Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]; simp only [Complex.mul_re, Complex.I_re, Complex.I_im]
    exact Real.exp_le_exp.2 (by simpa using neg_le_abs z.im)
  calc ‖(Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * Complex.I / 2‖
      ≤ (‖Complex.exp (-z * Complex.I)‖ + ‖Complex.exp (z * Complex.I)‖) / 2 := by
        simp only [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
        gcongr
        exact norm_sub_le _ _
    _ ≤ Real.exp |z.im| := by linarith

lemma summable_rpow_mul_exp_neg (r δ : ℝ) (hδ : 0 < δ) :
    Summable fun j : ℕ+ => (j : ℝ) ^ r * Real.exp (-δ * j) := by
  have hs : Summable fun n : ℕ => (n : ℝ) ^ ⌈r⌉₊ * Real.exp (-δ * n) :=
    Real.summable_pow_mul_exp_neg_nat_mul ⌈r⌉₊ hδ
  have hs' : Summable fun j : ℕ+ => (j : ℝ) ^ ⌈r⌉₊ * Real.exp (-δ * j) :=
    hs.comp_injective PNat.coe_injective
  refine hs'.of_nonneg_of_le (fun j => by positivity) fun j => ?_
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
  gcongr
  calc (j : ℝ) ^ r ≤ (j : ℝ) ^ (⌈r⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hj (Nat.le_ceil r)
    _ = (j : ℝ) ^ ⌈r⌉₊ := Real.rpow_natCast _ _

/-- The summable majorant `b_j = √(2/π) B j^{ν+k-p} e^{-δ j}` of `bpW:w1:sine-feature` (i). -/
def sineFeatMajorant (B ν p : ℝ) (k : ℕ) (δ : ℝ) (j : ℕ+) : ℝ :=
  Real.sqrt (2 / Real.pi) * B * (j : ℝ) ^ (ν + k - p) * Real.exp (-δ * j)

lemma summable_sineFeatMajorant (B ν p : ℝ) (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Summable (sineFeatMajorant B ν p k δ) := by
  have := (summable_rpow_mul_exp_neg (ν + k - p) δ hδ).mul_left (Real.sqrt (2 / Real.pi) * B)
  refine this.congr fun j => ?_
  simp [sineFeatMajorant, mul_assoc]

/-- `bpW:w1:sine-feature` (i), coordinatewise: `|Ψ(z)_j| ≤ b_j` whenever `|Im z| ≤ a'`
(`δ = a - a'`). -/
lemma sineFeatCoordC_norm_le {a p : ℝ} {β : ℕ+ → ℝ} {B ν : ℝ} (hβ : PolyBounded β B ν) (k : ℕ)
    {a' : ℝ} {z : ℂ} (hz : |z.im| ≤ a') (j : ℕ+) :
    ‖sineFeatCoordC a p β k z j‖ ≤ sineFeatMajorant B ν p k (a - a') j := by
  obtain ⟨hB, hν, hβj⟩ := hβ
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
  have hjpos : (0 : ℝ) < j := by positivity
  have hs : ‖Complex.sin ((j : ℂ) * z + k * Real.pi / 2)‖ ≤ Real.exp (j * a') := by
    refine (norm_complex_sin_le _).trans (Real.exp_le_exp.2 ?_)
    have : ((j : ℂ) * z + k * Real.pi / 2).im = j * z.im := by simp
    rw [this, abs_mul, abs_of_pos hjpos]
    exact mul_le_mul_of_nonneg_left hz hjpos.le
  have hw : ‖(ellWeight a p j : ℂ)‖ = (j : ℝ) ^ p * Real.exp (a * j) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (ellWeight_pos a p j).le]; rfl
  have hwpos : 0 < (j : ℝ) ^ p * Real.exp (a * j) := ellWeight_pos a p j
  unfold sineFeatCoordC sineModeIterC sineFeatMajorant
  rw [norm_div, hw, div_le_iff₀ hwpos]
  simp only [norm_mul, Complex.norm_real, norm_pow, Complex.norm_natCast, Real.norm_eq_abs]
  have hsq : |Real.sqrt (2 / Real.pi)| = Real.sqrt (2 / Real.pi) :=
    abs_of_nonneg (Real.sqrt_nonneg _)
  rw [hsq]
  have hcalc : (j : ℝ) ^ (ν + k - p) = (j : ℝ) ^ ν * (j : ℝ) ^ k / (j : ℝ) ^ p := by
    rw [Real.rpow_sub hjpos, Real.rpow_add hjpos, Real.rpow_natCast]
  have hjp : (0 : ℝ) < (j : ℝ) ^ p := Real.rpow_pos_of_pos hjpos _
  have hexp : Real.exp (-(a - a') * j) * Real.exp (a * j) = Real.exp (j * a') := by
    rw [← Real.exp_add]; congr 1; ring
  have hR : Real.sqrt (2 / Real.pi) * B * (j : ℝ) ^ (ν + k - p) * Real.exp (-(a - a') * j) *
      ((j : ℝ) ^ p * Real.exp (a * j)) =
      (B * (j : ℝ) ^ ν) * (Real.sqrt (2 / Real.pi) * (j : ℝ) ^ k * Real.exp (j * a')) := by
    rw [hcalc, ← hexp]; field_simp
  rw [hR]
  have h0 : 0 ≤ Real.sqrt (2 / Real.pi) * (j : ℝ) ^ k := by positivity
  gcongr
  · exact hβj j

lemma memℓp_two_of_norm_le {E : Type*} [NormedAddCommGroup E] {c : ℕ+ → E} {b : ℕ+ → ℝ}
    (hb : Summable b) (hc : ∀ j, ‖c j‖ ≤ b j) : Memℓp c 2 := by
  have h1 : Memℓp c 1 := by
    refine memℓp_gen ?_
    simpa using Summable.of_nonneg_of_le (fun j => norm_nonneg _) hc hb
  exact h1.of_exponent_ge (by norm_num)

section Feature

variable (a p : ℝ) (β : ℕ+ → ℝ) {B ν : ℝ}

lemma sineFeatCoord_norm_le (hβ : PolyBounded β B ν) (k : ℕ) (x : ℝ) (j : ℕ+) :
    ‖sineFeatCoord a p β k x j‖ ≤ sineFeatMajorant B ν p k a j := by
  have := sineFeatCoordC_norm_le (a := a) (p := p) hβ k (a' := 0) (z := (x : ℂ)) (by simp) j
  rw [sineFeatCoordC_ofReal, Complex.norm_real, sub_zero] at this
  exact this

lemma memℓp_sineFeatCoord (ha : 0 < a) (hβ : PolyBounded β B ν) (k : ℕ) (x : ℝ) :
    Memℓp (sineFeatCoord a p β k x) 2 :=
  memℓp_two_of_norm_le (summable_sineFeatMajorant B ν p k ha) (sineFeatCoord_norm_le a p β hβ k x)

lemma memℓp_sineFeatCoordC (hβ : PolyBounded β B ν) (k : ℕ) {z : ℂ} (hz : |z.im| < a) :
    Memℓp (sineFeatCoordC a p β k z) 2 :=
  memℓp_two_of_norm_le
    (summable_sineFeatMajorant B ν p k (δ := a - |z.im|) (by linarith))
    fun j => sineFeatCoordC_norm_le hβ k (a' := |z.im|) le_rfl j

/-- The real analytic sine feature `Ψ_ℝ^k(x) ∈ ℓ²_ℝ`, `Ψ(x)_j = β_j φ_j^{(k)}(x) / ω_{a,p}(j)`
(blueprint `bpW:w1:sine-feature`). -/
def sineFeatureR (ha : 0 < a) (hβ : PolyBounded β B ν) (k : ℕ) (x : ℝ) :
    lp (fun _ : ℕ+ => ℝ) 2 :=
  ⟨sineFeatCoord a p β k x, memℓp_sineFeatCoord a p β ha hβ k x⟩

/-- The complex sine feature `Ψ^k(z) ∈ ℓ²_ℂ` on the strip `|Im z| < a` (zero outside; blueprint
`bpW:w1:sine-feature`). -/
def sineFeatureC (hβ : PolyBounded β B ν) (k : ℕ) (z : ℂ) : lp (fun _ : ℕ+ => ℂ) 2 :=
  if h : |z.im| < a then ⟨sineFeatCoordC a p β k z, memℓp_sineFeatCoordC a p β hβ k h⟩ else 0

lemma sineFeatureR_apply (ha : 0 < a) (hβ : PolyBounded β B ν) (k : ℕ) (x : ℝ) (j : ℕ+) :
    sineFeatureR a p β ha hβ k x j = sineFeatCoord a p β k x j := rfl

lemma sineFeatureC_apply (hβ : PolyBounded β B ν) (k : ℕ) {z : ℂ} (hz : |z.im| < a) (j : ℕ+) :
    sineFeatureC a p β hβ k z j = sineFeatCoordC a p β k z j := by
  simp [sineFeatureC, hz]

lemma sineFeatCoordC_differentiable (k : ℕ) (j : ℕ+) :
    Differentiable ℂ fun z => sineFeatCoordC a p β k z j := by
  unfold sineFeatCoordC sineModeIterC
  fun_prop

/-- Blueprint `bpW:w1:sine-feature` (i) in norm form: `‖Ψ(z)_j‖ ≤ b_j` for `|Im z| ≤ a'`. -/
lemma sineFeatureC_bound (hβ : PolyBounded β B ν) (k : ℕ) {a' : ℝ} (ha' : a' < a) {z : ℂ}
    (hz : |z.im| ≤ a') (j : ℕ+) :
    ‖sineFeatureC a p β hβ k z j‖ ≤ sineFeatMajorant B ν p k (a - a') j := by
  rw [sineFeatureC_apply a p β hβ k (lt_of_le_of_lt hz ha')]
  exact sineFeatCoordC_norm_le hβ k hz j

/-- Blueprint `bpW:w1:sine-feature` (ii): `Ψ` is holomorphic on every strip `|Im z| < a' < a`. -/
theorem sineFeatureC_differentiableOn (hβ : PolyBounded β B ν) (k : ℕ) {a' : ℝ} (ha' : a' < a) :
    DifferentiableOn ℂ (sineFeatureC a p β hβ k) {z : ℂ | |z.im| < a'} := by
  let F : ℕ+ → ℂ → lp (fun _ : ℕ+ => ℂ) 2 := fun j z => lp.single 2 j (sineFeatCoordC a p β k z j)
  have hF : ∀ j, Differentiable ℂ (F j) := fun j =>
    (lp.singleContinuousLinearMap (𝕜 := ℂ) (E := fun _ : ℕ+ => ℂ) (p := 2) j).differentiable.comp
      (sineFeatCoordC_differentiable a p β k j)
  have hopen : IsOpen {z : ℂ | |z.im| < a'} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hsum : DifferentiableOn ℂ (fun w => ∑' j, F j w) {z : ℂ | |z.im| < a'} :=
    Complex.differentiableOn_tsum_of_summable_norm (u := sineFeatMajorant B ν p k (a - a'))
      (summable_sineFeatMajorant B ν p k (by linarith)) (fun j => (hF j).differentiableOn) hopen
      (fun j w hw => by
        simp only [F, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
        exact sineFeatCoordC_norm_le hβ k (le_of_lt hw) j)
  refine hsum.congr fun z hz => ?_
  have hz' : |z.im| < a := lt_trans hz ha'
  have h := lp.hasSum_single (p := 2) (by simp) (sineFeatureC a p β hβ k z)
  rw [← h.tsum_eq]
  refine tsum_congr fun j => ?_
  simp only [F, sineFeatureC_apply a p β hβ k hz']

theorem sineFeatureC_analyticAt (hβ : PolyBounded β B ν) (k : ℕ) {z : ℂ} (hz : |z.im| < a) :
    AnalyticAt ℂ (sineFeatureC a p β hβ k) z := by
  have hlt : (|z.im| + a) / 2 < a := by linarith
  refine (sineFeatureC_differentiableOn a p β hβ k hlt).analyticAt ?_
  exact (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const).mem_nhds
    (by show |z.im| < (|z.im| + a) / 2; linarith)

end Feature

lemma memℓp_re (z : lp (fun _ : ℕ+ => ℂ) 2) : Memℓp (fun j => (z j).re) 2 := by
  refine memℓp_gen ?_
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    ((lp.memℓp z).summable (by simp))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  calc ‖(z j).re‖ ^ 2 = |(z j).re| ^ 2 := by rw [Real.norm_eq_abs]
    _ ≤ ‖z j‖ ^ 2 := by gcongr; exact Complex.abs_re_le_norm _

/-- The real part, coordinatewise, as an element of `ℓ²_ℝ`. -/
def lpRe (z : lp (fun _ : ℕ+ => ℂ) 2) : lp (fun _ : ℕ+ => ℝ) 2 := ⟨fun j => (z j).re, memℓp_re z⟩

lemma lpRe_apply (z : lp (fun _ : ℕ+ => ℂ) 2) (j : ℕ+) : lpRe z j = (z j).re := rfl

lemma norm_lpRe_le (z : lp (fun _ : ℕ+ => ℂ) 2) : ‖lpRe z‖ ≤ ‖z‖ := by
  refine lp.norm_le_of_tsum_le (by simp) (norm_nonneg _) ?_
  rw [lp.norm_rpow_eq_tsum (by simp) z]
  refine Summable.tsum_le_tsum (fun j => ?_) ((lp.memℓp (lpRe z)).summable (by simp))
    ((lp.memℓp z).summable (by simp))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, lpRe_apply]
  calc ‖(z j).re‖ ^ 2 = |(z j).re| ^ 2 := by rw [Real.norm_eq_abs]
    _ ≤ ‖z j‖ ^ 2 := by gcongr; exact Complex.abs_re_le_norm _

/-- The real part, coordinatewise, as a continuous `ℝ`-linear map `ℓ²_ℂ → ℓ²_ℝ`. -/
def lpReCLM : lp (fun _ : ℕ+ => ℂ) 2 →L[ℝ] lp (fun _ : ℕ+ => ℝ) 2 :=
  LinearMap.mkContinuous
    { toFun := lpRe
      map_add' := fun z w => by ext j; simp [lpRe_apply]
      map_smul' := fun c z => by ext j; simp [lpRe_apply] }
    1 (fun z => by simpa using norm_lpRe_le z)

lemma lpReCLM_apply (z : lp (fun _ : ℕ+ => ℂ) 2) (j : ℕ+) : lpReCLM z j = (z j).re := rfl

section FeatureReal

variable (a p : ℝ) (β : ℕ+ → ℝ) {B ν : ℝ}

lemma sineFeatureR_eq_re (ha : 0 < a) (hβ : PolyBounded β B ν) (k : ℕ) (x : ℝ) :
    sineFeatureR a p β ha hβ k x = lpReCLM (sineFeatureC a p β hβ k (x : ℂ)) := by
  ext j
  rw [lpReCLM_apply, sineFeatureC_apply a p β hβ k (by simpa using ha), sineFeatureR_apply,
    sineFeatCoordC_ofReal, Complex.ofReal_re]

/-- Blueprint `bpW:w1:sine-feature` (ii): `Ψ_ℝ` is real analytic. -/
theorem sineFeatureR_analyticAt (ha : 0 < a) (hβ : PolyBounded β B ν) (k : ℕ) (x : ℝ) :
    AnalyticAt ℝ (sineFeatureR a p β ha hβ k) x := by
  have hC := (sineFeatureC_analyticAt a p β hβ k (z := (x : ℂ)) (by simpa using ha)).restrictScalars
    (𝕜 := ℝ)
  have hfun : sineFeatureR a p β ha hβ k =
      lpReCLM ∘ (sineFeatureC a p β hβ k) ∘ (Complex.ofRealCLM : ℝ → ℂ) :=
    funext fun x => sineFeatureR_eq_re a p β ha hβ k x
  rw [hfun]
  exact (lpReCLM.analyticAt _).comp (hC.comp (Complex.ofRealCLM.analyticAt x))

/-- Blueprint `bpW:w1:sine-feature` (iii): `⟨Ψ_ℝ(x), y⟩ = Σ_j β_j (y_j/ω_{a,p}(j)) φ_j^{(k)}(x)`,
absolutely convergent. -/
theorem hasSum_inner_sineFeatureR (ha : 0 < a) (hβ : PolyBounded β B ν) (k : ℕ) (x : ℝ)
    (y : lp (fun _ : ℕ+ => ℝ) 2) :
    HasSum (fun j : ℕ+ => β j * (y j / ellWeight a p j) * sineModeIter k j x)
      (inner ℝ (sineFeatureR a p β ha hβ k x) y) := by
  convert lp.hasSum_inner (sineFeatureR a p β ha hβ k x) y using 1
  funext j
  simp only [sineFeatureR_apply, sineFeatCoord, RCLike.inner_apply,
    conj_trivial]
  field_simp

theorem summable_abs_inner_sineFeatureR (ha : 0 < a) (hβ : PolyBounded β B ν) (k : ℕ) (x : ℝ)
    (y : lp (fun _ : ℕ+ => ℝ) 2) :
    Summable fun j : ℕ+ => |β j * (y j / ellWeight a p j) * sineModeIter k j x| :=
  (hasSum_inner_sineFeatureR a p β ha hβ k x y).summable.abs

end FeatureReal

end KAM.Wave

end
