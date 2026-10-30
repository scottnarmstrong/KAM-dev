/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Seq.Transport

/-!
# Diagonal multipliers on `ℓ²` (blueprint-W `bpW:w1:multiplier`)

Off-frontier, source-faithful infrastructure; the dependency graph is still being built.

* `weightedDiagCLM μ hM`: the operator `D_μ y = (μ_j y_j)` on `lp (fun _ : ℕ+ => 𝕜) 2` for `‖μ_j‖ ≤ M`, with
  `‖D_μ‖ ≤ M` (`norm_diagCLM_le`) and `‖μ_j‖ ≤ ‖D_μ‖` (`norm_le_norm_of_apply_eq`).
* `not_exists_diag_of_unbounded`: a diagonal map with unbounded `μ` is not a bounded operator.
* `diag_representative`: the representative of `w ↦ (m_j w_j)` between weights is `D_μ`,
  `μ_j = m_j ω_{a',p'}(j) / ω_{a,p}(j)`.
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Wave

variable {K : Type*} [RCLike K]

/-- The diagonal sequence `μ y` is square summable for bounded `μ`. -/
theorem memℓp_diag {μ : ℕ+ → K} {M : ℝ} (hM : ∀ j, ‖μ j‖ ≤ M) (y : lp (fun _ : ℕ+ => K) 2) :
    Memℓp (fun j => μ j * y j) 2 := by
  refine memℓp_gen ?_
  have hs : Summable fun j => M ^ 2 * ‖y j‖ ^ 2 := (lp_two_hasSum_sq y).summable.mul_left _
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hs
  have h0 : 0 ≤ ‖μ j‖ := norm_nonneg _
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul]
  rw [mul_pow]
  gcongr
  exact hM j

/-- **Diagonal multiplier** `D_μ` (blueprint `bpW:w1:multiplier`): the bounded operator
`y ↦ (μ_j y_j)` on `ℓ²` for `‖μ_j‖ ≤ M`. -/
def weightedDiagCLM (μ : ℕ+ → K) {M : ℝ} (hM : ∀ j, ‖μ j‖ ≤ M) :
    lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2 :=
  LinearMap.mkContinuous
    { toFun := fun y => ⟨fun j => μ j * y j, memℓp_diag hM y⟩
      map_add' := fun y y' => by ext j; simp [mul_add]; rfl
      map_smul' := fun c y => by ext j; simp [mul_left_comm] }
    M
    (fun y => by
      have h0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
      have hsq : ‖(⟨fun j => μ j * y j, memℓp_diag hM y⟩ : lp (fun _ : ℕ+ => K) 2)‖ ^ 2 ≤
          (M * ‖y‖) ^ 2 := by
        have := hasSum_le (fun j => ?_) (lp_two_hasSum_sq
          (⟨fun j => μ j * y j, memℓp_diag hM y⟩ : lp (fun _ : ℕ+ => K) 2))
          ((lp_two_hasSum_sq y).mul_left (M ^ 2))
        · simpa [mul_pow] using this
        · simp only [norm_mul]
          rw [mul_pow]
          gcongr
          exact hM j
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg h0 (norm_nonneg _))
        two_ne_zero).1 hsq)

@[simp] theorem weightedDiagCLM_apply (μ : ℕ+ → K) {M : ℝ} (hM : ∀ j, ‖μ j‖ ≤ M)
    (y : lp (fun _ : ℕ+ => K) 2) (j : ℕ+) : weightedDiagCLM μ hM y j = μ j * y j := rfl

/-- `bpW:w1:multiplier`: `‖D_μ‖ ≤ M`. -/
theorem norm_diagCLM_le (μ : ℕ+ → K) {M : ℝ} (hM : ∀ j, ‖μ j‖ ≤ M) : ‖weightedDiagCLM μ hM‖ ≤ M := by
  have h0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  exact LinearMap.mkContinuous_norm_le _ h0 _

/-- `weightedDiagCLM` does not depend on the proof of the bound. -/
theorem weightedDiagCLM_eq (μ : ℕ+ → K) {M M' : ℝ} (hM : ∀ j, ‖μ j‖ ≤ M) (hM' : ∀ j, ‖μ j‖ ≤ M') :
    weightedDiagCLM μ hM = weightedDiagCLM μ hM' := rfl

/-- `bpW:w1:multiplier`: `‖D_μ‖ ≤ M'` for any bound `M'` of `‖μ_j‖`. -/
theorem norm_diagCLM_le' (μ : ℕ+ → K) {M M' : ℝ} (hM : ∀ j, ‖μ j‖ ≤ M) (hM' : ∀ j, ‖μ j‖ ≤ M') :
    ‖weightedDiagCLM μ hM‖ ≤ M' := by
  rw [weightedDiagCLM_eq μ hM hM']; exact norm_diagCLM_le μ hM'

/-- A diagonal operator with `‖μ_j‖ = 1` is an isometry. -/
theorem norm_diagCLM_apply_of_norm_eq_one (μ : ℕ+ → K) {M : ℝ} (hM : ∀ j, ‖μ j‖ ≤ M)
    (h1 : ∀ j, ‖μ j‖ = 1) (y : lp (fun _ : ℕ+ => K) 2) : ‖weightedDiagCLM μ hM y‖ = ‖y‖ := by
  have := (lp_two_hasSum_sq (weightedDiagCLM μ hM y)).unique
    (by simpa [norm_mul, h1] using lp_two_hasSum_sq y)
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

/-- `bpW:w1:multiplier`: any bounded operator acting diagonally with multiplier `μ` has
`‖μ_j‖ ≤ ‖T‖` (test on `e_j`). -/
theorem norm_le_norm_of_apply_eq {μ : ℕ+ → K}
    (T : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2)
    (hT : ∀ y j, T y j = μ j * y j) (j : ℕ+) : ‖μ j‖ ≤ ‖T‖ := by
  have h1 : T (lp.single 2 j (1 : K)) = lp.single 2 j (μ j) := by
    ext i
    rw [hT]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have h2 := T.le_opNorm (lp.single 2 j (1 : K))
  rw [h1, lp.norm_single (by norm_num), lp.norm_single (by norm_num), norm_one, mul_one] at h2
  exact h2

/-- `bpW:w1:multiplier`: `‖μ_j‖ ≤ ‖D_μ‖`. -/
theorem norm_le_norm_diagCLM (μ : ℕ+ → K) {M : ℝ} (hM : ∀ j, ‖μ j‖ ≤ M) (j : ℕ+) :
    ‖μ j‖ ≤ ‖weightedDiagCLM μ hM‖ :=
  norm_le_norm_of_apply_eq _ (fun _ _ => rfl) j

/-- `bpW:w1:multiplier`: a diagonal map with unbounded multiplier is not a bounded operator. -/
theorem not_exists_diag_of_unbounded {μ : ℕ+ → K} (hμ : ∀ B : ℝ, ∃ j, B < ‖μ j‖) :
    ¬ ∃ T : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2, ∀ y j, T y j = μ j * y j := by
  rintro ⟨T, hT⟩
  obtain ⟨j, hj⟩ := hμ ‖T‖
  exact absurd (norm_le_norm_of_apply_eq T hT j) (not_le.2 hj)

/-- `bpW:w1:multiplier`: the representative `τ_{a',p'} ∘ (w ↦ m w) ∘ κ_{a,p}` of a diagonal map is
`D_μ` with `μ_j = m_j ω_{a',p'}(j) / ω_{a,p}(j)`. -/
theorem diag_representative (a p a' p' : ℝ) (m : ℕ+ → K) (y : lp (fun _ : ℕ+ => K) 2) (j : ℕ+) :
    (ellWeight a' p' j : K) * (m j * coeffW a p y j) =
      (m j * ((ellWeight a' p' j : K) / (ellWeight a p j : K))) * y j := by
  have := ellWeight_cast_ne_zero (K := K) a p j
  simp only [coeffW_apply]
  field_simp

/-- The ratio `ω_{a',p'}(j) / ω_{a,p}(j)` (the embedding multiplier of `bpW:w1:embed`). -/
def embedRatio (a p a' p' : ℝ) (j : ℕ+) : ℝ := ellWeight a' p' j / ellWeight a p j

theorem embedRatio_pos (a p a' p' : ℝ) (j : ℕ+) : 0 < embedRatio a p a' p' j :=
  div_pos (ellWeight_pos _ _ _) (ellWeight_pos _ _ _)

theorem embedRatio_eq (a p a' p' : ℝ) (j : ℕ+) :
    embedRatio a p a' p' j = (j : ℝ) ^ (p' - p) * Real.exp ((a' - a) * j) := by
  have hj : (0 : ℝ) < j := by exact_mod_cast j.pos
  unfold embedRatio ellWeight
  rw [Real.rpow_sub hj, sub_mul, Real.exp_sub]
  have := (Real.rpow_pos_of_pos hj p).ne'
  field_simp

/-- `bpW:w1:embed` (i): for `a' ≤ a`, `p' ≤ p` the ratio lies in `(0, 1]`. -/
theorem embedRatio_le_one {a a' p p' : ℝ} (ha : a' ≤ a) (hp : p' ≤ p) (j : ℕ+) :
    embedRatio a p a' p' j ≤ 1 := by
  rw [embedRatio_eq]
  have hj : (1 : ℝ) ≤ j := Nat.one_le_cast.2 j.pos
  have h1 : (j : ℝ) ^ (p' - p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hj (by linarith)
  have h2 : Real.exp ((a' - a) * j) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
    _ = 1 := one_mul 1

/-- `bpW:w1:embed` (ii): for `a > a'`, `σ = p' - p > 0`, the ratio is at most
`(σ / (e (a - a')))^σ`. -/
theorem embedRatio_le_of_lt {a a' p p' : ℝ} (ha : a' < a) (hp : p < p') (j : ℕ+) :
    embedRatio a p a' p' j ≤ ((p' - p) / (Real.exp 1 * (a - a'))) ^ (p' - p) := by
  rw [embedRatio_eq]
  set σ := p' - p with hσ
  set c := a - a' with hc
  have hσ0 : 0 < σ := by linarith
  have hc0 : 0 < c := by linarith
  have hj : (0 : ℝ) < j := by exact_mod_cast j.pos
  set u := c * j / σ with hu
  have hu0 : 0 < u := by positivity
  have h1 : u ≤ Real.exp (u - 1) := by linarith [Real.add_one_le_exp (u - 1)]
  have h2 : u ^ σ ≤ Real.exp (c * j - σ) := by
    calc u ^ σ ≤ (Real.exp (u - 1)) ^ σ := Real.rpow_le_rpow hu0.le h1 hσ0.le
      _ = Real.exp ((u - 1) * σ) := (Real.exp_mul _ _).symm
      _ = Real.exp (c * j - σ) := by congr 1; rw [hu]; field_simp
  have h3 : (j : ℝ) ^ σ = (σ / c) ^ σ * u ^ σ := by
    rw [← Real.mul_rpow (by positivity) hu0.le, hu]; congr 1; field_simp
  have h4 : ((σ / (Real.exp 1 * c)) ^ σ) = (σ / c) ^ σ * Real.exp (-σ) := by
    have : σ / (Real.exp 1 * c) = σ / c * (Real.exp 1)⁻¹ := by field_simp
    rw [this, Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (Real.exp_pos 1).le,
      Real.exp_one_rpow, ← Real.exp_neg]
  rw [h4, h3, show (a' - a) * (j : ℝ) = -(c * j) by rw [hc]; ring]
  calc (σ / c) ^ σ * u ^ σ * Real.exp (-(c * j))
      ≤ (σ / c) ^ σ * Real.exp (c * j - σ) * Real.exp (-(c * j)) := by gcongr
    _ = (σ / c) ^ σ * Real.exp (-σ) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- A coefficient sequence `κ_{a,p} y` lies in `ℓ^{a',p'}` whenever the weight ratio is bounded;
this
is `bpW:w1:embed` (i), (ii) for the bound `M`, with the bound
`‖κ_{a,p} y‖_{a',p'} ≤ M ‖y‖` (`‖y‖ = ‖κ_{a,p} y‖_{a,p}`). -/
theorem isEll_coeffW_of_ratio_le {a p a' p' M : ℝ} (hM : ∀ j, embedRatio a p a' p' j ≤ M)
    (y : lp (fun _ : ℕ+ => K) 2) :
    IsEll a' p' (coeffW a p y) ∧ ellNorm a' p' (coeffW a p y) ≤ M * ellNorm a p (coeffW a p y) := by
  have hM' : ∀ j, ‖((embedRatio a p a' p' j : ℝ) : K)‖ ≤ M := fun j => by
    rw [RCLike.norm_ofReal, abs_of_pos (embedRatio_pos _ _ _ _ _)]; exact hM j
  have heq : ∀ j, (ellWeight a' p' j : K) * coeffW a p y j =
      ((embedRatio a p a' p' j : ℝ) : K) * y j := by
    intro j
    have := diag_representative a p a' p' (fun _ => (1 : K)) y j
    simpa [embedRatio] using this
  have hIs : IsEll a' p' (coeffW a p y) := by
    unfold IsEll
    have := memℓp_diag hM' y
    simpa only [heq] using this
  refine ⟨hIs, ?_⟩
  have h0 : 0 ≤ M := (embedRatio_pos a p a' p' 1).le.trans (hM 1)
  have hnorm : ellNorm a' p' (coeffW a p y) = ‖tauLp a' p' _ hIs‖ := by
    rw [ellNorm, ← norm_tauLp_sq a' p' _ hIs, Real.sqrt_sq (norm_nonneg _)]
  have : tauLp a' p' _ hIs = weightedDiagCLM _ hM' y := by ext j; rw [tauLp_apply, heq]; rfl
  rw [hnorm, this, ellNorm_coeffW]
  exact (weightedDiagCLM _ hM').le_opNorm y |>.trans (by gcongr; exact norm_diagCLM_le _ hM')

end KAM.Wave

end
