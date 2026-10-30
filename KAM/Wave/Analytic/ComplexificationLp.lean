/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Analytic.Complexification
public import KAM.Frozen.Wave.Defs.WaveSpace

/-!
# Complexification of `ℓ²`

Blueprint-W `bpW:w1:complexification` and `bpW:w1:complexification-lemma` (i) (package W1-ANALYTIC).
This is source-faithful infrastructure used by several nodes; the dependency graph is still being
built.

`ι : ℓ²_ℝ → ℓ²_ℂ`, `re : ℓ²_ℂ → ℓ²_ℝ` and the conjugation of `ℓ²_ℂ` are built coordinatewise
(`KAM.Wave.lpPointwise`); `ℓ²` is `lp (fun _ : ℕ+ => ℝ) 2` as in the frozen `KAM.Wave.WaveSpace`,
and `E^ℂ_{1,1}` is `WaveSpaceC`, the product of two copies of `ℓ²_ℂ`.
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Wave

/-- Pointwise application of a norm-nonincreasing real-linear map to `ℓ²`-sequences. -/
def lpPointwise {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (φ : E →L[ℝ] E') (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) :
    lp (fun _ : ℕ+ => E) 2 →L[ℝ] lp (fun _ : ℕ+ => E') 2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun j => φ (x j), (lp.memℓp x).norm.mono fun j => hφ (x j)⟩
      map_add' := fun x y => by ext j; simp; rfl
      map_smul' := fun c x => by ext j; simp } 1 fun x => by
    rw [one_mul]
    exact lp.norm_mono (by norm_num) fun j => hφ (x j)

@[simp] theorem lpPointwise_apply {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (φ : E →L[ℝ] E') (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖)
    (x : lp (fun _ : ℕ+ => E) 2) (j : ℕ+) : lpPointwise φ hφ x j = φ (x j) := rfl


theorem norm_ofRealCLM_le (x : ℝ) : ‖Complex.ofRealCLM x‖ ≤ ‖x‖ := by simp

theorem norm_reCLM_le (z : ℂ) : ‖Complex.reCLM z‖ ≤ ‖z‖ := by
  simpa using Complex.abs_re_le_norm z

theorem norm_conjCLE_le (z : ℂ) : ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ) z‖ ≤ ‖z‖ := by simp

/-- Blueprint `bpW:w1:complexification`: the inclusion `ι : ℓ²_ℝ → ℓ²_ℂ`. -/
def complexifyLp : lp (fun _ : ℕ+ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ+ => ℂ) 2 :=
  lpPointwise Complex.ofRealCLM norm_ofRealCLM_le

/-- Blueprint `bpW:w1:complexification`: the real part `re : ℓ²_ℂ → ℓ²_ℝ`. -/
def reLp : lp (fun _ : ℕ+ => ℂ) 2 →L[ℝ] lp (fun _ : ℕ+ => ℝ) 2 :=
  lpPointwise Complex.reCLM norm_reCLM_le

/-- Blueprint `bpW:w1:complexification`: coordinatewise conjugation of `ℓ²_ℂ` (`ℝ`-linear). -/
def conjLp : lp (fun _ : ℕ+ => ℂ) 2 →L[ℝ] lp (fun _ : ℕ+ => ℂ) 2 :=
  lpPointwise (Complex.conjCLE : ℂ →L[ℝ] ℂ) norm_conjCLE_le

@[simp] theorem complexifyLp_apply (y : lp (fun _ : ℕ+ => ℝ) 2) (j : ℕ+) :
    complexifyLp y j = (y j : ℂ) := rfl

@[simp] theorem reLp_apply (z : lp (fun _ : ℕ+ => ℂ) 2) (j : ℕ+) :
    reLp z j = (z j).re := rfl

@[simp] theorem conjLp_apply (z : lp (fun _ : ℕ+ => ℂ) 2) (j : ℕ+) :
    conjLp z j = starRingEnd ℂ (z j) := rfl

/-- Blueprint `bpW:w1:complexification-lemma` (i): `‖ι y‖ = ‖y‖`. -/
theorem norm_complexifyLp (y : lp (fun _ : ℕ+ => ℝ) 2) : ‖complexifyLp y‖ = ‖y‖ :=
  le_antisymm (lp.norm_mono (by norm_num) fun j => by simp)
    (lp.norm_mono (by norm_num) fun j => by simp)

/-- Blueprint `bpW:w1:complexification-lemma` (i): `‖re z‖ ≤ ‖z‖`. -/
theorem norm_reLp_le (z : lp (fun _ : ℕ+ => ℂ) 2) : ‖reLp z‖ ≤ ‖z‖ :=
  lp.norm_mono (by norm_num) fun j => by simpa using Complex.abs_re_le_norm (z j)

/-- Blueprint `bpW:w1:complexification-lemma` (i): `re ∘ ι = id`. -/
@[simp] theorem reLp_complexifyLp (y : lp (fun _ : ℕ+ => ℝ) 2) : reLp (complexifyLp y) = y := by
  ext j; simp

/-- Blueprint `bpW:w1:complexification-lemma` (i): conjugation is an isometry. -/
theorem norm_conjLp (z : lp (fun _ : ℕ+ => ℂ) 2) : ‖conjLp z‖ = ‖z‖ :=
  le_antisymm (lp.norm_mono (by norm_num) fun j => by simp)
    (lp.norm_mono (by norm_num) fun j => by simp)

/-- Blueprint `bpW:w1:complexification-lemma` (i): conjugation is conjugate-linear. -/
theorem conjLp_smul (c : ℂ) (z : lp (fun _ : ℕ+ => ℂ) 2) :
    conjLp (c • z) = starRingEnd ℂ c • conjLp z := by
  ext j; simp

@[simp] theorem conjLp_conjLp (z : lp (fun _ : ℕ+ => ℂ) 2) : conjLp (conjLp z) = z := by
  ext j; simp

/-- Blueprint `bpW:w1:complexification-lemma` (i): `‖ι y + i ι y'‖² = ‖y‖² + ‖y'‖²`. -/
theorem norm_sq_complexify_add_I_smul (y y' : lp (fun _ : ℕ+ => ℝ) 2) :
    ‖complexifyLp y + Complex.I • complexifyLp y'‖ ^ 2 = ‖y‖ ^ 2 + ‖y'‖ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have key : ∀ f : lp (fun _ : ℕ+ => ℝ) 2, ‖f‖ ^ 2 = ∑' j, ‖f j‖ ^ 2 := fun f => by
    have := lp.norm_rpow_eq_tsum hp f
    simpa using this
  have hs : ∀ f : lp (fun _ : ℕ+ => ℝ) 2, Summable fun j => ‖f j‖ ^ 2 := fun f => by
    simpa using (lp.memℓp f).summable hp
  have hz : ∀ j, ‖(complexifyLp y + Complex.I • complexifyLp y') j‖ ^ 2 =
      ‖y j‖ ^ 2 + ‖y' j‖ ^ 2 := fun j => by
    simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, complexifyLp_apply,
      smul_eq_mul, Real.norm_eq_abs, sq_abs]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hzs : ‖complexifyLp y + Complex.I • complexifyLp y'‖ ^ 2 =
      ∑' j, ‖(complexifyLp y + Complex.I • complexifyLp y') j‖ ^ 2 := by
    have := lp.norm_rpow_eq_tsum hp (complexifyLp y + Complex.I • complexifyLp y')
    simpa using this
  rw [hzs, key y, key y', ← (hs y).tsum_add (hs y')]
  exact tsum_congr hz

end KAM.Wave
