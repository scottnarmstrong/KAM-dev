/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Cubic.TriML
public import KAM.Wave.Cubic.GradLp

/-!
# The unweighted pairing and the quartic form `𝒬` (blueprint `bpW:w1:gradient-identity` (i))

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is
still being built.

`KAM.Wave.wavePair a p u y = Σ_l (κ_{a,p+1} u)_l (κ_{a,p} y)_l` is the unweighted pairing
`⟨κ_{a,p+1}u, κ_{a,p}y⟩₀`, a continuous bilinear form on `ℓ²_𝕜` of norm `≤ 1`
(`KAM.Wave.wavePairCLM`). `KAM.Wave.waveQuartForm` is the continuous 4-linear form
`𝒬(y₁,y₂,y₃,y₄) = ⟨T(κy₁,κy₂,κy₃), κy₄⟩₀` (`ContinuousMultilinearMap` on `Fin 4`), with
`‖𝒬‖ ≤ C_*` (`waveQuartForm_norm_le`, `norm_waveQuartForm_le`) and the defining identity
`waveQuartForm_apply`. Full symmetry is in `KAM/Wave/Cubic/QSymm.lean`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {K : Type*} [RCLike K] {a p : ℝ}

lemma norm_coeffW_le_norm {a' p' : ℝ} (ha : 0 ≤ a') (hp : 0 ≤ p') (u : lp (fun _ : ℕ+ => K) 2)
    (l : ℕ+) : ‖coeffW a' p' u l‖ ≤ ‖u l‖ := by
  rw [coeffW_apply, norm_div, norm_ellWeight_cast]
  exact div_le_self (norm_nonneg _) (one_le_ellWeight ha hp l)

section Pair

variable (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

include ha hp in
lemma wavePair_summable (u y : lp (fun _ : ℕ+ => K) 2) :
    Summable fun l : ℕ+ => ‖coeffW a (p + 1) u l * coeffW a p y l‖ := by
  have hp0 : 0 ≤ p := by linarith
  have h := waveCauchySchwarz_tsum (f := fun l => ‖u l‖) (g := fun l => ‖y l‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (lp_two_hasSum_sq u).summable
    (lp_two_hasSum_sq y).summable
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_) h.1
  rw [norm_mul]
  exact mul_le_mul (norm_coeffW_le_norm ha (by linarith) u l) (norm_coeffW_le_norm ha hp0 y l)
    (norm_nonneg _) (norm_nonneg _)

/-- The unweighted pairing `⟨κ_{a,p+1} u, κ_{a,p} y⟩₀`. -/
def wavePair (a p : ℝ) (u y : lp (fun _ : ℕ+ => K) 2) : K :=
  ∑' l : ℕ+, coeffW a (p + 1) u l * coeffW a p y l

include ha hp in
lemma wavePair_norm_le (u y : lp (fun _ : ℕ+ => K) 2) : ‖wavePair a p u y‖ ≤ ‖u‖ * ‖y‖ := by
  have hp0 : 0 ≤ p := by linarith
  have h := waveCauchySchwarz_tsum (f := fun l => ‖u l‖) (g := fun l => ‖y l‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (lp_two_hasSum_sq u).summable
    (lp_two_hasSum_sq y).summable
  have e1 : Real.sqrt (∑' l, ‖u l‖ ^ 2) = ‖u‖ := by
    rw [(lp_two_hasSum_sq u).tsum_eq, Real.sqrt_sq (norm_nonneg _)]
  have e2 : Real.sqrt (∑' l, ‖y l‖ ^ 2) = ‖y‖ := by
    rw [(lp_two_hasSum_sq y).tsum_eq, Real.sqrt_sq (norm_nonneg _)]
  calc ‖wavePair a p u y‖ ≤ ∑' l : ℕ+, ‖coeffW a (p + 1) u l * coeffW a p y l‖ :=
        norm_tsum_le_tsum_norm (wavePair_summable ha hp u y)
    _ ≤ ∑' l, ‖u l‖ * ‖y l‖ := by
        refine Summable.tsum_le_tsum (fun l => ?_) (wavePair_summable ha hp u y) h.1
        rw [norm_mul]
        exact mul_le_mul (norm_coeffW_le_norm ha (by linarith) u l)
          (norm_coeffW_le_norm ha hp0 y l) (norm_nonneg _) (norm_nonneg _)
    _ ≤ _ := by rw [← e1, ← e2]; exact h.2

include ha hp in
lemma wavePair_add_left (u u' y : lp (fun _ : ℕ+ => K) 2) :
    wavePair a p (u + u') y = wavePair a p u y + wavePair a p u' y := by
  unfold wavePair
  rw [← Summable.tsum_add (wavePair_summable ha hp u y).of_norm
    (wavePair_summable ha hp u' y).of_norm]
  exact tsum_congr fun l => by simp only [coeffW_apply, lp.coeFn_add, Pi.add_apply]; ring

include ha hp in
lemma wavePair_add_right (u y y' : lp (fun _ : ℕ+ => K) 2) :
    wavePair a p u (y + y') = wavePair a p u y + wavePair a p u y' := by
  unfold wavePair
  rw [← Summable.tsum_add (wavePair_summable ha hp u y).of_norm
    (wavePair_summable ha hp u y').of_norm]
  exact tsum_congr fun l => by simp only [coeffW_apply, lp.coeFn_add, Pi.add_apply]; ring

lemma wavePair_smul_left (r : K) (u y : lp (fun _ : ℕ+ => K) 2) :
    wavePair a p (r • u) y = r * wavePair a p u y := by
  unfold wavePair
  rw [← tsum_mul_left]
  exact tsum_congr fun l => by
    simp only [coeffW_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; ring

lemma wavePair_smul_right (r : K) (u y : lp (fun _ : ℕ+ => K) 2) :
    wavePair a p u (r • y) = r * wavePair a p u y := by
  unfold wavePair
  rw [← tsum_mul_left]
  exact tsum_congr fun l => by
    simp only [coeffW_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; ring

/-- The pairing as a continuous bilinear form on `ℓ²_𝕜`. -/
def wavePairCLM : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2 →L[K] K :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ K (wavePair a p) (wavePair_add_left ha hp)
      (fun r u y => by simpa [smul_eq_mul] using wavePair_smul_left r u y)
      (wavePair_add_right ha hp)
      (fun r u y => by simpa [smul_eq_mul] using wavePair_smul_right r u y))
    1 (fun u y => by
      simpa using wavePair_norm_le ha hp u y)

lemma wavePairCLM_apply (u y : lp (fun _ : ℕ+ => K) 2) :
    wavePairCLM (K := K) (a := a) (p := p) ha hp u y = wavePair a p u y := rfl

include ha hp in
lemma norm_wavePairCLM_le : ‖wavePairCLM (K := K) (a := a) (p := p) ha hp‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

end Pair

section Quart

variable (m : ℝ) (hm : 0 < m) (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

/-- The continuous 4-linear form `𝒬(y₁,y₂,y₃,y₄) = ⟨T(κy₁,κy₂,κy₃), κy₄⟩₀`. -/
def waveQuartForm :
    ContinuousMultilinearMap K (fun _ : Fin 4 => lp (fun _ : ℕ+ => K) 2) K :=
  ContinuousMultilinearMap.uncurryRight
    ((wavePairCLM (K := K) (a := a) (p := p) ha hp).compContinuousMultilinearMap
      (waveTriML (K := K) m hm ha hp))

lemma waveQuartForm_apply_vec (v : Fin 4 → lp (fun _ : ℕ+ => K) 2) :
    waveQuartForm (K := K) m hm ha hp v =
      wavePair a p (waveTriML (K := K) m hm ha hp ![v 0, v 1, v 2]) (v 3) := by
  unfold waveQuartForm
  rw [ContinuousMultilinearMap.uncurryRight_apply]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  rfl

/-- Defining identity: `𝒬(y₁,y₂,y₃,y₄) = ⟨T(κy₁,κy₂,κy₃), κy₄⟩₀`. -/
theorem waveQuartForm_apply (y₁ y₂ y₃ y₄ : lp (fun _ : ℕ+ => K) 2) :
    waveQuartForm (K := K) m hm ha hp ![y₁, y₂, y₃, y₄] =
      ∑' l : ℕ+, waveTriSeq m hm (coeffW a p y₁) (coeffW a p y₂) (coeffW a p y₃) l *
        coeffW a p y₄ l := by
  rw [waveQuartForm_apply_vec]
  simp only [wavePair, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, coeffW_waveTriML m hm ha hp]
  rfl

/-- `‖𝒬‖ ≤ C_*`. -/
theorem waveQuartForm_norm_le : ‖waveQuartForm (K := K) m hm ha hp‖ ≤ waveCubicConst p := by
  unfold waveQuartForm
  rw [ContinuousMultilinearMap.uncurryRight_norm]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  calc _ ≤ 1 * ‖waveTriML (K := K) m hm ha hp‖ := by
        gcongr; exact norm_wavePairCLM_le ha hp
    _ ≤ _ := by rw [one_mul]; exact waveTriML_norm_le m hm ha hp

/-- `|𝒬(y₁,y₂,y₃,y₄)| ≤ C_* ∏ ‖y_i‖`. -/
theorem norm_waveQuartForm_le (v : Fin 4 → lp (fun _ : ℕ+ => K) 2) :
    ‖waveQuartForm (K := K) m hm ha hp v‖ ≤ waveCubicConst p * ∏ i, ‖v i‖ :=
  ((waveQuartForm (K := K) m hm ha hp).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (waveQuartForm_norm_le m hm ha hp)
      (Finset.prod_nonneg fun _ _ => norm_nonneg _))

end Quart

end KAM.Wave

end
