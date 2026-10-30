/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Seq.Multiplier

/-!
# Embeddings between weighted spaces (blueprint-W `bpW:w1:embed`)

Off-frontier, source-faithful infrastructure; the dependency graph is still being built.

* (i) `embedCLM`: the representative `D_μ`, `μ_j = ω_{a',p'}(j)/ω_{a,p}(j) ∈ (0,1]`, of the
  inclusion
  `ℓ^{a,p} ⊂ ℓ^{a',p'}` for `a' ≤ a`, `p' ≤ p`; `norm_embedCLM_le`, `ellTsumNorm_coeffW_le_of_le`.
* (ii) `ellTsumNorm_coeffW_le_of_lt`: the constant `(σ/(e(a-a')))^σ`.
* (iii) `coeffW_embedCLM`, `embedCLM_injective`, `embedCLM_comp`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {K : Type*} [RCLike K]

theorem norm_embedRatio_cast_le_one {a a' p p' : ℝ} (ha : a' ≤ a) (hp : p' ≤ p) (j : ℕ+) :
    ‖((embedRatio a p a' p' j : ℝ) : K)‖ ≤ 1 := by
  rw [RCLike.norm_ofReal, abs_of_pos (embedRatio_pos _ _ _ _ _)]
  exact embedRatio_le_one ha hp j

/-- **Embedding** (blueprint `bpW:w1:embed` (i)): the representative of the inclusion
`ℓ^{a,p} ⊂ ℓ^{a',p'}`, `a' ≤ a`, `p' ≤ p`. -/
def embedCLM (a p a' p' : ℝ) (ha : a' ≤ a) (hp : p' ≤ p) :
    lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2 :=
  weightedDiagCLM (fun j => ((embedRatio a p a' p' j : ℝ) : K)) (norm_embedRatio_cast_le_one ha hp)

@[simp] theorem embedCLM_apply (a p a' p' : ℝ) (ha : a' ≤ a) (hp : p' ≤ p)
    (y : lp (fun _ : ℕ+ => K) 2) (j : ℕ+) :
    embedCLM a p a' p' ha hp y j = ((embedRatio a p a' p' j : ℝ) : K) * y j := rfl

/-- `bpW:w1:embed` (i): `‖ι‖ ≤ 1`. -/
theorem norm_embedCLM_le (a p a' p' : ℝ) (ha : a' ≤ a) (hp : p' ≤ p) :
    ‖(embedCLM a p a' p' ha hp : lp (fun _ : ℕ+ => K) 2 →L[K] _)‖ ≤ 1 :=
  norm_diagCLM_le _ _

/-- `bpW:w1:embed` (i): `ℓ^{a,p} ⊂ ℓ^{a',p'}` with `‖w‖_{a',p'} ≤ ‖w‖_{a,p}`. -/
theorem ellTsumNorm_coeffW_le_of_le {a a' p p' : ℝ} (ha : a' ≤ a) (hp : p' ≤ p)
    (y : lp (fun _ : ℕ+ => K) 2) :
    IsEll a' p' (coeffW a p y) ∧
      ellTsumNorm a' p' (coeffW a p y) ≤ ellTsumNorm a p (coeffW a p y) := by
  have := isEll_coeffW_of_ratio_le (M := 1) (fun j => embedRatio_le_one ha hp j) y
  simpa using this

/-- `bpW:w1:embed` (ii): for `a > a'` and `σ = p' - p > 0`,
`‖w‖_{a',p'} ≤ (σ/(e(a-a')))^σ ‖w‖_{a,p}`. -/
theorem ellTsumNorm_coeffW_le_of_lt {a a' p p' : ℝ} (ha : a' < a) (hp : p < p')
    (y : lp (fun _ : ℕ+ => K) 2) :
    IsEll a' p' (coeffW a p y) ∧
      ellTsumNorm a' p' (coeffW a p y) ≤
        ((p' - p) / (Real.exp 1 * (a - a'))) ^ (p' - p) * ellTsumNorm a p (coeffW a p y) :=
  isEll_coeffW_of_ratio_le (fun j => embedRatio_le_of_lt ha hp j) y

/-- `bpW:w1:embed` (i), source-facing: `‖w‖_{a',p'} ≤ ‖w‖_{a,p}` for `w = κ_{a,p} y`. -/
theorem ellNorm_coeffW_le_of_le {a a' p p' : ℝ} (ha : a' ≤ a) (hp : p' ≤ p)
    (y : lp (fun _ : ℕ+ => K) 2) :
    ellNorm a' p' (coeffW a p y) (ellTsumNorm_coeffW_le_of_le ha hp y).1 ≤
      ellNorm a p (coeffW a p y) (isEll_coeffW a p y) := by
  rw [ellNorm_eq_ellTsumNorm, ellNorm_eq_ellTsumNorm]
  exact (ellTsumNorm_coeffW_le_of_le ha hp y).2

/-- `bpW:w1:embed` (ii), source-facing. -/
theorem ellNorm_coeffW_le_of_lt {a a' p p' : ℝ} (ha : a' < a) (hp : p < p')
    (y : lp (fun _ : ℕ+ => K) 2) :
    ellNorm a' p' (coeffW a p y) (ellTsumNorm_coeffW_le_of_lt ha hp y).1 ≤
      ((p' - p) / (Real.exp 1 * (a - a'))) ^ (p' - p) *
        ellNorm a p (coeffW a p y) (isEll_coeffW a p y) := by
  rw [ellNorm_eq_ellTsumNorm, ellNorm_eq_ellTsumNorm]
  exact (ellTsumNorm_coeffW_le_of_lt ha hp y).2

/-- `bpW:w1:embed` (iii): the inclusions do not change coefficients: `κ_{a',p'} D_μ = κ_{a,p}`. -/
theorem coeffW_embedCLM (a p a' p' : ℝ) (ha : a' ≤ a) (hp : p' ≤ p) (y : lp (fun _ : ℕ+ => K) 2) :
    coeffW a' p' (embedCLM a p a' p' ha hp y) = coeffW a p y := by
  funext j
  have h1 := ellWeight_cast_ne_zero (K := K) a' p' j
  have h2 := ellWeight_cast_ne_zero (K := K) a p j
  simp only [coeffW_apply, embedCLM_apply, embedRatio, RCLike.ofReal_div]
  field_simp

/-- `bpW:w1:embed` (iii): the inclusion is injective. -/
theorem embedCLM_injective (a p a' p' : ℝ) (ha : a' ≤ a) (hp : p' ≤ p) :
    Function.Injective (embedCLM (K := K) a p a' p' ha hp) := fun y y' h =>
  coeffW_injective a p (by rw [← coeffW_embedCLM a p a' p' ha hp y, h,
    coeffW_embedCLM a p a' p' ha hp y'])

/-- `bpW:w1:embed` (iii): the inclusions compose. -/
theorem embedCLM_comp (a p a' p' a'' p'' : ℝ) (ha : a' ≤ a) (hp : p' ≤ p)
    (ha' : a'' ≤ a') (hp' : p'' ≤ p') (y : lp (fun _ : ℕ+ => K) 2) :
    embedCLM a' p' a'' p'' ha' hp' (embedCLM a p a' p' ha hp y) =
      embedCLM a p a'' p'' (ha'.trans ha) (hp'.trans hp) y := by
  ext j
  simp only [embedCLM_apply, embedRatio, ← mul_assoc, ← RCLike.ofReal_mul]
  congr 2
  have := (ellWeight_pos a' p' j).ne'
  field_simp

end KAM.Wave

end
