/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import KAM.Frozen.Wave.Defs.ReconU
public import KAM.Frozen.Wave.Defs.ReconV
public import KAM.Wave.Recon.SineFeature

/-!
# Analytic reconstruction (blueprint `bpW:w1:recon-analytic`)

Infrastructure used by several nodes; the dependency graph is still being built.

With `a = p = 1` and `β_j = λ_j^{-1/2}` (respectively `λ_j^{1/2}`) the real sine features of
`KAM.Wave.sineFeatureR` give the derived reconstructions
`U^{(k)}_y(x) = ⟨Ψ^{U,k}(x), y⟩`, `V^{(k)}_y(x) = ⟨Ψ^{V,k}(x), y⟩` (`KAM.Wave.reconUIter`,
`KAM.Wave.reconVIter`), continuous linear functionals of `y ∈ ℓ²_ℝ`.

* (i) `KAM.Wave.reconUIter_zero`, `KAM.Wave.reconVIter_zero`, with the series forms
  `KAM.Wave.hasSum_reconUIter`, `KAM.Wave.hasSum_reconVIter`;
* (ii) `KAM.Wave.hasDerivAt_reconUIter`, `KAM.Wave.iteratedDeriv_reconU`,
  `KAM.Wave.derivWithin_reconU_Icc` (and the `V` versions);
* (iii) `KAM.Wave.analyticAt_reconUIter`, `KAM.Wave.analyticAt_iteratedDeriv_reconU` for any real
  normed parameter space `S` (and the `V` versions).

The polynomial bound used is `|β_j| ≤ (1 + m) j` (`B = 1 + m`, `ν = 1`), which suffices for the
feature lemma, whose hypothesis only asks for some `B, ν ≥ 0`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-! ### Derivatives of the sine modes and features -/

lemma hasDerivAt_sineModeIter (k : ℕ) (j : ℕ+) (x : ℝ) :
    HasDerivAt (sineModeIter k j) (sineModeIter (k + 1) j x) x := by
  unfold sineModeIter
  have h1 : HasDerivAt (fun x : ℝ => (j : ℝ) * x + k * Real.pi / 2) (j : ℝ) x := by
    simpa using ((hasDerivAt_id x).const_mul (j : ℝ)).add_const ((k : ℝ) * Real.pi / 2)
  have h2 := (h1.sin).const_mul (Real.sqrt (2 / Real.pi) * (j : ℝ) ^ k)
  convert h2 using 1
  have : (j : ℝ) * x + ((k + 1 : ℕ) : ℝ) * Real.pi / 2 =
      ((j : ℝ) * x + k * Real.pi / 2) + Real.pi / 2 := by push_cast; ring
  rw [this, Real.sin_add_pi_div_two]
  ring

section Feature

variable (a p : ℝ) (β : ℕ+ → ℝ) {B ν : ℝ}

lemma hasDerivAt_sineFeatCoord (k : ℕ) (x : ℝ) (j : ℕ+) :
    HasDerivAt (fun x => sineFeatCoord a p β k x j) (sineFeatCoord a p β (k + 1) x j) x := by
  unfold sineFeatCoord
  exact ((hasDerivAt_sineModeIter k j x).const_mul (β j)).div_const _

/-- `(Ψ^k)' = Ψ^{k+1}` for the real sine features (blueprint `bpW:w1:recon-analytic`,
step `stepW:w1:recder`). -/
theorem hasDerivAt_sineFeatureR (ha : 0 < a) (hβ : PolyBounded β B ν) (k : ℕ) (x : ℝ) :
    HasDerivAt (sineFeatureR a p β ha hβ k) (sineFeatureR a p β ha hβ (k + 1) x) x := by
  have hd := (sineFeatureR_analyticAt a p β ha hβ k x).differentiableAt.hasDerivAt
  convert hd using 1
  ext j
  have h1 : HasDerivAt (fun x => sineFeatureR a p β ha hβ k x j)
      (deriv (sineFeatureR a p β ha hβ k) x j) x :=
    (lp.evalCLM ℝ 2 (E := fun _ : ℕ+ => ℝ) j).hasFDerivAt.comp_hasDerivAt x hd
  have h2 := hasDerivAt_sineFeatCoord a p β k x j
  exact (h2.unique h1)

end Feature

/-! ### The polynomial bounds for `β = λ^{∓1/2}` -/

section Weights

variable (m : ℝ) (hm : 0 < m)

/-- `β_j = λ_j^{-1/2}` of the displacement reconstruction. -/
def betaU (j : ℕ+) : ℝ := (Real.sqrt (lam m hm j))⁻¹

/-- `β_j = λ_j^{1/2}` of the velocity reconstruction. -/
def betaV (j : ℕ+) : ℝ := Real.sqrt (lam m hm j)

lemma one_le_lam (j : ℕ+) : 1 ≤ lam m hm j := by
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
  unfold lam
  rw [Real.one_le_sqrt]
  nlinarith

lemma lam_le (j : ℕ+) : lam m hm j ≤ (1 + m) * j := by
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
  unfold lam
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hj2 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hj2 hm.le,
    mul_nonneg (mul_nonneg hm.le hm.le) (sq_nonneg (j : ℝ))]

lemma polyBounded_betaU : PolyBounded (betaU m hm) (1 + m) 1 := by
  refine ⟨by linarith, zero_le_one, fun j => ?_⟩
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
  have h1 : 1 ≤ Real.sqrt (lam m hm j) := Real.one_le_sqrt.2 (one_le_lam m hm j)
  rw [Real.rpow_one, betaU, abs_of_nonneg (by positivity)]
  calc (Real.sqrt (lam m hm j))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    _ ≤ (1 + m) * j := by nlinarith

lemma polyBounded_betaV : PolyBounded (betaV m hm) (1 + m) 1 := by
  refine ⟨by linarith, zero_le_one, fun j => ?_⟩
  have hl := one_le_lam m hm j
  have hsq : Real.sqrt (lam m hm j) ≤ lam m hm j := by
    calc Real.sqrt (lam m hm j) ≤ Real.sqrt (lam m hm j ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = lam m hm j := Real.sqrt_sq (by linarith)
  rw [Real.rpow_one, betaV, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact hsq.trans (lam_le m hm j)

/-- The real feature `Ψ^{U,k}_ℝ` (`a = p = 1`, `β = λ^{-1/2}`). -/
def reconFeatureU (k : ℕ) (x : ℝ) : lp (fun _ : ℕ+ => ℝ) 2 :=
  sineFeatureR 1 1 (betaU m hm) one_pos (polyBounded_betaU m hm) k x

/-- The real feature `Ψ^{V,k}_ℝ` (`a = p = 1`, `β = λ^{1/2}`). -/
def reconFeatureV (k : ℕ) (x : ℝ) : lp (fun _ : ℕ+ => ℝ) 2 :=
  sineFeatureR 1 1 (betaV m hm) one_pos (polyBounded_betaV m hm) k x

/-- The derived reconstruction `U^{(k)}_y(x) = ⟨Ψ^{U,k}_ℝ(x), y⟩` (blueprint
`bpW:w1:recon-analytic`). -/
def reconUIter (k : ℕ) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) : ℝ :=
  inner ℝ (reconFeatureU m hm k x) y

/-- The derived reconstruction `V^{(k)}_y(x) = ⟨Ψ^{V,k}_ℝ(x), y⟩` (blueprint
`bpW:w1:recon-analytic`). -/
def reconVIter (k : ℕ) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) : ℝ :=
  inner ℝ (reconFeatureV m hm k x) y

/-- `y ↦ U^{(k)}_y(x)` as a continuous linear functional (blueprint `bpW:w1:recon-analytic`). -/
def reconUIterCLM (k : ℕ) (x : ℝ) : lp (fun _ : ℕ+ => ℝ) 2 →L[ℝ] ℝ :=
  innerSL ℝ (reconFeatureU m hm k x)

/-- `y ↦ V^{(k)}_y(x)` as a continuous linear functional (blueprint `bpW:w1:recon-analytic`). -/
def reconVIterCLM (k : ℕ) (x : ℝ) : lp (fun _ : ℕ+ => ℝ) 2 →L[ℝ] ℝ :=
  innerSL ℝ (reconFeatureV m hm k x)

lemma reconUIterCLM_apply (k : ℕ) (x : ℝ) (y : lp (fun _ : ℕ+ => ℝ) 2) :
    reconUIterCLM m hm k x y = reconUIter m hm k y x := innerSL_apply_apply ℝ _ _

lemma reconVIterCLM_apply (k : ℕ) (x : ℝ) (y : lp (fun _ : ℕ+ => ℝ) 2) :
    reconVIterCLM m hm k x y = reconVIter m hm k y x := innerSL_apply_apply ℝ _ _

/-- The series form of `U^{(k)}_y(x)`, absolutely convergent (blueprint `bpW:w1:recon-analytic`,
step `stepW:w1:bil`). -/
theorem hasSum_reconUIter (k : ℕ) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    HasSum (fun j : ℕ+ => coeff y j / Real.sqrt (lam m hm j) * sineModeIter k j x)
      (reconUIter m hm k y x) := by
  have h := hasSum_inner_sineFeatureR 1 1 (betaU m hm) one_pos (polyBounded_betaU m hm) k x y
  have e : (fun j : ℕ+ => coeff y j / Real.sqrt (lam m hm j) * sineModeIter k j x) =
      fun j : ℕ+ => betaU m hm j * (y j / ellWeight 1 1 j) * sineModeIter k j x := by
    funext j
    simp only [coeff, betaU]
    ring
  rw [e]
  exact h

theorem hasSum_reconVIter (k : ℕ) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    HasSum (fun j : ℕ+ => Real.sqrt (lam m hm j) * coeff y j * sineModeIter k j x)
      (reconVIter m hm k y x) := by
  have h := hasSum_inner_sineFeatureR 1 1 (betaV m hm) one_pos (polyBounded_betaV m hm) k x y
  have e : (fun j : ℕ+ => Real.sqrt (lam m hm j) * coeff y j * sineModeIter k j x) =
      fun j : ℕ+ => betaV m hm j * (y j / ellWeight 1 1 j) * sineModeIter k j x := by
    funext j
    simp only [coeff, betaV]
  rw [e]
  exact h

theorem summable_abs_reconUIter (k : ℕ) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    Summable fun j : ℕ+ => |coeff y j / Real.sqrt (lam m hm j) * sineModeIter k j x| :=
  (hasSum_reconUIter m hm k y x).summable.abs

theorem summable_abs_reconVIter (k : ℕ) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    Summable fun j : ℕ+ => |Real.sqrt (lam m hm j) * coeff y j * sineModeIter k j x| :=
  (hasSum_reconVIter m hm k y x).summable.abs

/-- Blueprint `bpW:w1:recon-analytic` (i): `U^{(0)}_y = reconU`. -/
theorem reconUIter_zero (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    reconUIter m hm 0 y x = reconU m hm y x := by
  refine (hasSum_reconUIter m hm 0 y x).unique ?_
  unfold reconU
  simp only [sineModeIter_zero]
  exact ((hasSum_reconUIter m hm 0 y x).summable.congr
    fun j => by rw [sineModeIter_zero]).hasSum

/-- Blueprint `bpW:w1:recon-analytic` (i): `V^{(0)}_y = reconV`. -/
theorem reconVIter_zero (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    reconVIter m hm 0 y x = reconV m hm y x := by
  refine (hasSum_reconVIter m hm 0 y x).unique ?_
  unfold reconV
  simp only [sineModeIter_zero]
  exact ((hasSum_reconVIter m hm 0 y x).summable.congr
    fun j => by rw [sineModeIter_zero]).hasSum

/-! ### Derivatives -/

/-- Blueprint `bpW:w1:recon-analytic` (ii): `U^{(k)}_y' = U^{(k+1)}_y`. -/
theorem hasDerivAt_reconUIter (k : ℕ) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    HasDerivAt (reconUIter m hm k y) (reconUIter m hm (k + 1) y x) x := by
  have h := (hasDerivAt_sineFeatureR 1 1 (betaU m hm) one_pos (polyBounded_betaU m hm) k x).inner
    ℝ (hasDerivAt_const x y)
  convert h using 1
  · rfl
  · simp [reconUIter, reconFeatureU]

/-- Blueprint `bpW:w1:recon-analytic` (ii): `V^{(k)}_y' = V^{(k+1)}_y`. -/
theorem hasDerivAt_reconVIter (k : ℕ) (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    HasDerivAt (reconVIter m hm k y) (reconVIter m hm (k + 1) y x) x := by
  have h := (hasDerivAt_sineFeatureR 1 1 (betaV m hm) one_pos (polyBounded_betaV m hm) k x).inner
    ℝ (hasDerivAt_const x y)
  convert h using 1
  · rfl
  · simp [reconVIter, reconFeatureV]

/-- Blueprint `bpW:w1:recon-analytic` (ii): `U^{(k)}_y` is the `k`-th derivative of `reconU`. -/
theorem iteratedDeriv_reconU (k : ℕ) (y : lp (fun _ : ℕ+ => ℝ) 2) :
    iteratedDeriv k (reconU m hm y) = reconUIter m hm k y := by
  induction k with
  | zero =>
    funext x
    rw [iteratedDeriv_zero, reconUIter_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (hasDerivAt_reconUIter m hm k y x).deriv

/-- Blueprint `bpW:w1:recon-analytic` (ii): `V^{(k)}_y` is the `k`-th derivative of `reconV`. -/
theorem iteratedDeriv_reconV (k : ℕ) (y : lp (fun _ : ℕ+ => ℝ) 2) :
    iteratedDeriv k (reconV m hm y) = reconVIter m hm k y := by
  induction k with
  | zero =>
    funext x
    rw [iteratedDeriv_zero, reconVIter_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (hasDerivAt_reconVIter m hm k y x).deriv

theorem hasDerivAt_reconU (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    HasDerivAt (reconU m hm y) (reconUIter m hm 1 y x) x := by
  have := hasDerivAt_reconUIter m hm 0 y x
  have h0 : reconUIter m hm 0 y = reconU m hm y := funext (reconUIter_zero m hm y)
  rwa [h0] at this

theorem hasDerivAt_reconV (y : lp (fun _ : ℕ+ => ℝ) 2) (x : ℝ) :
    HasDerivAt (reconV m hm y) (reconVIter m hm 1 y x) x := by
  have := hasDerivAt_reconVIter m hm 0 y x
  have h0 : reconVIter m hm 0 y = reconV m hm y := funext (reconVIter_zero m hm y)
  rwa [h0] at this

/-- Blueprint `bpW:w1:recon-analytic` (ii): `∂ₓ reconU = U^{(1)}` within `[0, π]`. -/
theorem derivWithin_reconU_Icc (y : lp (fun _ : ℕ+ => ℝ) 2) {x : ℝ}
    (hx : x ∈ Set.Icc 0 Real.pi) :
    derivWithin (reconU m hm y) (Set.Icc 0 Real.pi) x = reconUIter m hm 1 y x :=
  (hasDerivAt_reconU m hm y x).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc Real.pi_pos x hx)

/-- Blueprint `bpW:w1:recon-analytic` (ii): `∂ₓ reconV = V^{(1)}` within `[0, π]`. -/
theorem derivWithin_reconV_Icc (y : lp (fun _ : ℕ+ => ℝ) 2) {x : ℝ}
    (hx : x ∈ Set.Icc 0 Real.pi) :
    derivWithin (reconV m hm y) (Set.Icc 0 Real.pi) x = reconVIter m hm 1 y x :=
  (hasDerivAt_reconV m hm y x).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc Real.pi_pos x hx)

/-! ### Joint analyticity -/

/-- The sine features are analytic in `x`, as a map from the product `S × ℝ`. -/
lemma analyticAt_reconFeatureU (k : ℕ) {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (q : S × ℝ) :
    AnalyticAt ℝ (fun q : S × ℝ => reconFeatureU m hm k q.2) q :=
  (sineFeatureR_analyticAt 1 1 (betaU m hm) one_pos (polyBounded_betaU m hm) k q.2).comp
    analyticAt_snd

lemma analyticAt_reconFeatureV (k : ℕ) {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (q : S × ℝ) :
    AnalyticAt ℝ (fun q : S × ℝ => reconFeatureV m hm k q.2) q :=
  (sineFeatureR_analyticAt 1 1 (betaV m hm) one_pos (polyBounded_betaV m hm) k q.2).comp
    analyticAt_snd

/-- Blueprint `bpW:w1:recon-analytic` (iii): for `Y : S → ℓ²_ℝ` analytic at `s₀`,
`(s, x) ↦ U^{(k)}_{Y s}(x)` is real analytic at `(s₀, x₀)`, for every `x₀`. -/
theorem analyticAt_reconUIter (k : ℕ) {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    {Y : S → lp (fun _ : ℕ+ => ℝ) 2} {s₀ : S} (hY : AnalyticAt ℝ Y s₀) (x₀ : ℝ) :
    AnalyticAt ℝ (fun q : S × ℝ => reconUIter m hm k (Y q.1) q.2) (s₀, x₀) := by
  have hY' : AnalyticAt ℝ (fun q : S × ℝ => Y q.1) (s₀, x₀) :=
    hY.comp analyticAt_fst
  have hB := (innerSL ℝ : lp (fun _ : ℕ+ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ+ => ℝ) 2 →L[ℝ] ℝ)
    |>.analyticAt_bilinear (reconFeatureU m hm k x₀, Y s₀)
  exact hB.comp_of_eq ((analyticAt_reconFeatureU m hm k (s₀, x₀)).prod hY') rfl

theorem analyticAt_reconVIter (k : ℕ) {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    {Y : S → lp (fun _ : ℕ+ => ℝ) 2} {s₀ : S} (hY : AnalyticAt ℝ Y s₀) (x₀ : ℝ) :
    AnalyticAt ℝ (fun q : S × ℝ => reconVIter m hm k (Y q.1) q.2) (s₀, x₀) := by
  have hY' : AnalyticAt ℝ (fun q : S × ℝ => Y q.1) (s₀, x₀) :=
    hY.comp analyticAt_fst
  have hB := (innerSL ℝ : lp (fun _ : ℕ+ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ+ => ℝ) 2 →L[ℝ] ℝ)
    |>.analyticAt_bilinear (reconFeatureV m hm k x₀, Y s₀)
  exact hB.comp_of_eq ((analyticAt_reconFeatureV m hm k (s₀, x₀)).prod hY') rfl

/-- The `S = ℝⁿ` form of `bpW:w1:recon-analytic` (iii): the iterated `x`-derivatives of
`reconU (Y s)` are jointly real analytic. -/
theorem analyticAt_iteratedDeriv_reconU (k : ℕ) {S : Type*} [NormedAddCommGroup S]
    [NormedSpace ℝ S] {Y : S → lp (fun _ : ℕ+ => ℝ) 2} {s₀ : S} (hY : AnalyticAt ℝ Y s₀)
    (x₀ : ℝ) :
    AnalyticAt ℝ (fun q : S × ℝ => iteratedDeriv k (reconU m hm (Y q.1)) q.2) (s₀, x₀) := by
  simp_rw [iteratedDeriv_reconU]
  exact analyticAt_reconUIter m hm k hY x₀

theorem analyticAt_iteratedDeriv_reconV (k : ℕ) {S : Type*} [NormedAddCommGroup S]
    [NormedSpace ℝ S] {Y : S → lp (fun _ : ℕ+ => ℝ) 2} {s₀ : S} (hY : AnalyticAt ℝ Y s₀)
    (x₀ : ℝ) :
    AnalyticAt ℝ (fun q : S × ℝ => iteratedDeriv k (reconV m hm (Y q.1)) q.2) (s₀, x₀) := by
  simp_rw [iteratedDeriv_reconV]
  exact analyticAt_reconVIter m hm k hY x₀

end Weights

end KAM.Wave

end
