/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Cubic.FrozenForm
public import KAM.Wave.Seq.Embed
public import KAM.Wave.Analytic.ComplexificationLp

/-!
# The Hamiltonian field (blueprint `bpW:w1:hamfield` (i)–(iii))

In the weighted coordinates at weight `(a,p)` (phase space `ℓ² × ℓ²`, max norm):

* (i) `KAM.Wave.waveXLam z = (D z.2, -D z.1)`, `D = lamMul 1`, represents the linear field
  `X_Λ(q,p) = (λ p, -λ q) : E_{a,p} → E_{a,p-1}` (`coeffW_waveXLam_fst`, `_snd`), `‖X_Λ‖ ≤ √(1+m)`
  (`norm_waveXLam_le`), and is not bounded into `E_{a,p}` (`not_exists_bounded_waveXLam`);
* (ii) `KAM.Wave.waveXG z = (0, -𝒩(z.1))` represents `X_G(q,p) = (0, -𝒢(q))` into `E_{a,p+1}`;
  `𝕜`-analytic on all of `ℓ²_𝕜 × ℓ²_𝕜` for `𝕜 ∈ {ℝ, ℂ}` (`waveXG_analyticOnNhd`), with
  `‖X_G z‖ ≤ C_* ‖z.1‖³`, Lipschitz bound (`waveXG_sub_le`), and complex extension compatible
  with the real one (`waveXG_complexify`);
* (iii) `KAM.Wave.waveXH = X_Λ + ι̂ X_G` represents `X_H : E_{a,p} → E_{a,p-1}` and is analytic
  (`waveXH_analyticOnNhd`), with coordinates `(λ_j p_j, -λ_j q_j - 𝒢(q)_j)`
  (`coeffW_waveXH_fst`, `coeffW_waveXH_snd`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {K : Type*} [RCLike K] (m : ℝ) (hm : 0 < m)

/-- The phase space `ℓ²_𝕜 × ℓ²_𝕜` in weighted coordinates. -/
abbrev WaveSpaceK (K : Type*) [RCLike K] : Type _ :=
  lp (fun _ : ℕ+ => K) 2 × lp (fun _ : ℕ+ => K) 2

/-- (i) The linear field `X_Λ` in weighted coordinates: `(y, y') ↦ (D y', -D y)`, `D = λ/j`. -/
def waveXLam : WaveSpaceK K →L[K] WaveSpaceK K :=
  ((lamMul (K := K) m hm 1).comp (ContinuousLinearMap.snd K (lp (fun _ : ℕ+ => K) 2)
      (lp (fun _ : ℕ+ => K) 2))).prod
    (-((lamMul (K := K) m hm 1).comp (ContinuousLinearMap.fst K (lp (fun _ : ℕ+ => K) 2)
      (lp (fun _ : ℕ+ => K) 2))))

@[simp] lemma waveXLam_apply (z : WaveSpaceK K) :
    waveXLam m hm z = (lamMul (K := K) m hm 1 z.2, -lamMul (K := K) m hm 1 z.1) := rfl

/-- (i) `X_Λ` represents `(q, p) ↦ (λ p, -λ q) : E_{a,p} → E_{a,p-1}`: first component. -/
theorem coeffW_waveXLam_fst (a p : ℝ) (z : WaveSpaceK K) (j : ℕ+) :
    coeffW a (p - 1) (waveXLam m hm z).1 j = (lam m hm j : K) * coeffW a p z.2 j := by
  have h := lamMul_represents hm a (p - 1) 1 z.2 j
  rw [sub_add_cancel] at h
  rw [waveXLam_apply, coeffW_apply, ← h]
  have := ellWeight_cast_ne_zero (K := K) a (p - 1) j
  simp only [Real.rpow_one]
  field_simp

/-- (i), second component. -/
theorem coeffW_waveXLam_snd (a p : ℝ) (z : WaveSpaceK K) (j : ℕ+) :
    coeffW a (p - 1) (waveXLam m hm z).2 j = -((lam m hm j : K) * coeffW a p z.1 j) := by
  have h := lamMul_represents hm a (p - 1) 1 z.1 j
  rw [sub_add_cancel] at h
  rw [waveXLam_apply, coeffW_apply, lp.coeFn_neg, Pi.neg_apply, ← h]
  have := ellWeight_cast_ne_zero (K := K) a (p - 1) j
  simp only [Real.rpow_one]
  field_simp

/-- (i) `‖X_Λ‖ ≤ √(1+m)`. -/
theorem norm_waveXLam_le : ‖(waveXLam (K := K) m hm)‖ ≤ Real.sqrt (1 + m) := by
  have h1 := norm_lamMul_le_of_nonneg (K := K) hm (r := 1) zero_le_one
  have e : (1 + m) ^ ((1 : ℝ) / 2) = Real.sqrt (1 + m) := by
    rw [Real.sqrt_eq_rpow]
  rw [e] at h1
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun z => ?_
  simp only [waveXLam_apply, Prod.norm_def]
  refine max_le ?_ ?_
  · calc ‖lamMul (K := K) m hm 1 z.2‖ ≤ ‖(lamMul (K := K) m hm 1 :
          lp (fun _ : ℕ+ => K) 2 →L[K] _)‖ * ‖z.2‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ Real.sqrt (1 + m) * ‖z.2‖ := by gcongr
      _ ≤ _ := by
          gcongr
          exact le_max_right _ _
  · calc ‖-lamMul (K := K) m hm 1 z.1‖ = ‖lamMul (K := K) m hm 1 z.1‖ := norm_neg _
      _ ≤ ‖(lamMul (K := K) m hm 1 : lp (fun _ : ℕ+ => K) 2 →L[K] _)‖ * ‖z.1‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ Real.sqrt (1 + m) * ‖z.1‖ := by gcongr
      _ ≤ _ := by
          gcongr
          exact le_max_left _ _

/-- (i) `X_Λ` is not bounded `E_{a,p} → E_{a,p}`: no continuous linear map of the phase space has
the coordinates `(λ_j z₂_j, -λ_j z₁_j)` at the same weight. -/
theorem not_exists_bounded_waveXLam :
    ¬ ∃ T : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2,
      ∀ y j, T y j = ((lam m hm j ^ (1 : ℝ) : ℝ) : K) * y j :=
  not_exists_bounded_lam_pow hm one_pos

/-- (ii) The nonlinear field `X_G(q,p) = (0, -𝒢(q))` in weighted coordinates:
`(y, y') ↦ (0, -𝒩(y))`. -/
def waveXG {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (z : WaveSpaceK K) : WaveSpaceK K :=
  (0, -waveCubicNL (K := K) m hm ha hp z.1)

/-- (ii) `X_G` is `𝕜`-analytic on all of `ℓ²_𝕜 × ℓ²_𝕜`. -/
theorem waveXG_analyticOnNhd {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) :
    AnalyticOnNhd K (waveXG (K := K) m hm ha hp) Set.univ := by
  intro z _
  have hfst : AnalyticAt K (fun z : WaveSpaceK K => z.1) z :=
    (ContinuousLinearMap.fst K (lp (fun _ : ℕ+ => K) 2) (lp (fun _ : ℕ+ => K) 2)).analyticAt z
  have hN : AnalyticAt K (fun z : WaveSpaceK K => waveCubicNL (K := K) m hm ha hp z.1) z :=
    (waveCubicNL_analyticOnNhd m hm ha hp z.1 trivial).comp hfst
  exact AnalyticAt.prod analyticAt_const hN.neg

/-- (ii) `‖X_G(z)‖ ≤ C_* ‖z.1‖³`. -/
theorem waveXG_norm_le {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (z : WaveSpaceK K) :
    ‖waveXG (K := K) m hm ha hp z‖ ≤ waveCubicConst p * ‖z.1‖ ^ 3 := by
  simp only [waveXG, Prod.norm_def, norm_zero, norm_neg]
  exact max_le (by have := waveCubicConst_nonneg p; positivity) (waveCubicNL_norm_le m hm ha hp z.1)

/-- (ii) Lipschitz bound: `‖X_G z - X_G z'‖ ≤ 3 C_* ‖z.1 - z'.1‖ max(‖z.1‖,‖z'.1‖)²`. -/
theorem waveXG_sub_le {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (z z' : WaveSpaceK K) :
    ‖waveXG (K := K) m hm ha hp z - waveXG (K := K) m hm ha hp z'‖ ≤
      3 * waveCubicConst p * ‖z.1 - z'.1‖ * (max ‖z.1‖ ‖z'.1‖) ^ 2 := by
  have h := waveCubicNL_sub_le m hm ha hp z.1 z'.1
  have e : waveXG (K := K) m hm ha hp z - waveXG (K := K) m hm ha hp z' =
      (0, -(waveCubicNL (K := K) m hm ha hp z.1 - waveCubicNL (K := K) m hm ha hp z'.1)) := by
    refine Prod.ext (by simp [waveXG]) ?_
    simp only [waveXG, Prod.snd_sub]
    abel
  rw [e]
  simp only [Prod.norm_def, norm_zero, norm_neg]
  refine max_le ?_ h
  have := waveCubicConst_nonneg p
  positivity

/-- (ii) The complex extension of `X_G` is compatible with the real one. -/
theorem waveXG_complexify {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (z : WaveSpaceK ℝ) :
    waveXG (K := ℂ) m hm ha hp (complexifyLp z.1, complexifyLp z.2) =
      (complexifyLp (waveXG (K := ℝ) m hm ha hp z).1,
        complexifyLp (waveXG (K := ℝ) m hm ha hp z).2) := by
  simp only [waveXG, waveCubicNL_eq]
  rw [Prod.ext_iff]
  refine ⟨by simp, ?_⟩
  simp only [map_neg]
  rw [waveTriML_complexify]

/-- (iii) The Hamiltonian field `X_H = X_Λ + ι̂ X_G : E_{a,p} → E_{a,p-1}` in weighted coordinates
(`ι̂` the representative of `E_{a,p+1} ⊂ E_{a,p-1}`). -/
def waveXH {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (z : WaveSpaceK K) : WaveSpaceK K :=
  waveXLam m hm z +
    ((embedCLM (K := K) a (p + 1) a (p - 1) le_rfl (by linarith)) (waveXG m hm ha hp z).1,
      (embedCLM (K := K) a (p + 1) a (p - 1) le_rfl (by linarith)) (waveXG m hm ha hp z).2)

/-- (iii) `X_H` is `𝕜`-analytic on all of `ℓ²_𝕜 × ℓ²_𝕜`. -/
theorem waveXH_analyticOnNhd {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) :
    AnalyticOnNhd K (waveXH (K := K) m hm ha hp) Set.univ := by
  intro z _
  have hG := waveXG_analyticOnNhd (K := K) m hm ha hp z trivial
  have hι : AnalyticAt K (fun w : WaveSpaceK K =>
      ((embedCLM (K := K) a (p + 1) a (p - 1) le_rfl (by linarith) :
          lp (fun _ : ℕ+ => K) 2 →L[K] _) w.1,
        (embedCLM (K := K) a (p + 1) a (p - 1) le_rfl (by linarith) :
          lp (fun _ : ℕ+ => K) 2 →L[K] _) w.2))
      (waveXG m hm ha hp z) :=
    by exact ((embedCLM (K := K) a (p + 1) a (p - 1) le_rfl (by linarith)).prodMap
      (embedCLM (K := K) a (p + 1) a (p - 1) le_rfl (by linarith))).analyticAt (waveXG m hm ha hp z)
  have h2 := hι.comp hG
  have h1 : AnalyticAt K (waveXLam (K := K) m hm) z := (waveXLam (K := K) m hm).analyticAt z
  exact h1.add h2

/-- (iii) First coordinate sequence of `X_H`: `κ_{a,p-1} (X_H z).1 = λ · κ_{a,p} z.2`. -/
theorem coeffW_waveXH_fst {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (z : WaveSpaceK K) (j : ℕ+) :
    coeffW a (p - 1) (waveXH m hm ha hp z).1 j = (lam m hm j : K) * coeffW a p z.2 j := by
  have e : (waveXH m hm ha hp z).1 = (waveXLam m hm z).1 +
      (embedCLM (K := K) a (p + 1) a (p - 1) le_rfl (by linarith))
        (0 : lp (fun _ : ℕ+ => K) 2) := rfl
  rw [e, map_zero, add_zero]
  exact coeffW_waveXLam_fst m hm a p z j

/-- (iii) Second coordinate sequence of `X_H`:
`κ_{a,p-1} (X_H z).2 = -λ · κ_{a,p} z.1 - κ_{a,p+1} 𝒩(z.1)` (the latter is `𝒢(κ_{a,p} z.1)`). -/
theorem coeffW_waveXH_snd {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) (z : WaveSpaceK K) (j : ℕ+) :
    coeffW a (p - 1) (waveXH m hm ha hp z).2 j =
      -((lam m hm j : K) * coeffW a p z.1 j) -
        coeffW a (p + 1) (waveCubicNL (K := K) m hm ha hp z.1) j := by
  have e : (waveXH m hm ha hp z).2 = (waveXLam m hm z).2 +
      (embedCLM (K := K) a (p + 1) a (p - 1) le_rfl (by linarith))
        (-waveCubicNL (K := K) m hm ha hp z.1) :=
    rfl
  rw [e, map_neg, ← sub_eq_add_neg, coeffW_sub, Pi.sub_apply, coeffW_embedCLM,
    coeffW_waveXLam_snd]

end KAM.Wave

end
