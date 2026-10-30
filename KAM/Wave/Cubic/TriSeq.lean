/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Cubic.SelectionOneSided

/-!
# The cubic coefficients and the trilinear sums over `𝕜 ∈ {ℝ, ℂ}`
(blueprint `bpW:w1:trilinear`, step `stepW:w1:tricoord`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is
still being built.

`KAM.Wave.waveTriCoef` is `c_{ijkl} = g_{ijkl} (λ_i λ_j λ_k λ_l)^{-1/2}` (real); it satisfies the
hypothesis of `bpW:w1:selection` (a) with `M = 1/(2π)` (`KAM.Wave.waveTriCoef_bound`).
`KAM.Wave.waveTriSeq` is the trilinear sum over any `RCLike` field, and
`KAM.Wave.waveTri_oneSided` is the exact bound `‖T(q,q',q'')‖_{a,p+1} ≤ C_* ∏‖·‖_{a,p}` with
`C_* = K_{p+1/2}²/π` (`KAM.Wave.waveCubicConst`), for `a ≥ 0`, `p ≥ 1/2`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {K : Type*} [RCLike K] (m : ℝ) (hm : 0 < m)

/-- The real coefficients `c_{ijkl} = g_{ijkl} (λ_i λ_j λ_k λ_l)^{-1/2}`. -/
def waveTriCoef (i j k l : ℕ+) : ℝ :=
  waveQuartic i j k l / (Real.sqrt (lam m hm i) * Real.sqrt (lam m hm j) *
    Real.sqrt (lam m hm k) * Real.sqrt (lam m hm l))

lemma wave_sqrt_pnat_le_sqrt_lam (n : ℕ+) : Real.sqrt (n : ℝ) ≤ Real.sqrt (lam m hm n) :=
  Real.sqrt_le_sqrt (wave_pnat_le_lam m hm n)

/-- The selection-rule bound for `c_{ijkl}` with `M = 1/(2π)` (`stepW:w1:tricoord`). -/
theorem waveTriCoef_bound (i j k l : ℕ+) :
    ‖(waveTriCoef m hm i j k l : K)‖ ≤
      (1 / (2 * Real.pi)) * (((i : ℝ) * j * k * l) ^ (-(1 / 2 : ℝ))) * waveSelCount l (i, j, k) := by
  rw [RCLike.norm_ofReal, wave_rpow_neg_half_prod]
  unfold waveTriCoef
  have hpos : ∀ n : ℕ+, 0 < Real.sqrt (n : ℝ) := fun n => Real.sqrt_pos.2 (by positivity)
  have hD0 : 0 < Real.sqrt (i : ℝ) * Real.sqrt j * Real.sqrt k * Real.sqrt l :=
    by have := hpos i; have := hpos j; have := hpos k; have := hpos l; positivity
  have hDle : Real.sqrt (i : ℝ) * Real.sqrt j * Real.sqrt k * Real.sqrt l ≤
      Real.sqrt (lam m hm i) * Real.sqrt (lam m hm j) * Real.sqrt (lam m hm k) *
        Real.sqrt (lam m hm l) := by
    have := wave_sqrt_pnat_le_sqrt_lam m hm i
    have := wave_sqrt_pnat_le_sqrt_lam m hm j
    have := wave_sqrt_pnat_le_sqrt_lam m hm k
    have := wave_sqrt_pnat_le_sqrt_lam m hm l
    gcongr
  rw [abs_div, abs_of_pos (lt_of_lt_of_le hD0 hDle)]
  have hQ := abs_waveQuartic_le_signs i j k l
  calc |waveQuartic i j k l| / (Real.sqrt (lam m hm i) * Real.sqrt (lam m hm j) *
        Real.sqrt (lam m hm k) * Real.sqrt (lam m hm l))
      ≤ |waveQuartic i j k l| / (Real.sqrt (i : ℝ) * Real.sqrt j * Real.sqrt k * Real.sqrt l) :=
        div_le_div_of_nonneg_left (abs_nonneg _) hD0 hDle
    _ ≤ ((1 / (2 * Real.pi)) * waveSelCount l (i, j, k)) /
          (Real.sqrt (i : ℝ) * Real.sqrt j * Real.sqrt k * Real.sqrt l) :=
        div_le_div_of_nonneg_right hQ hD0.le
    _ = _ := by
        unfold waveSelCount
        field_simp

/-- The trilinear sums `T(q,q',q'')_l = Σ_{ijk} c_{ijkl} q_i q'_j q''_k` (blueprint
`bpW:w0n:cubic-bound`, over `𝕜`). -/
def waveTriSeq (q q' q'' : ℕ+ → K) : ℕ+ → K :=
  waveSelSum (fun i j k l => (waveTriCoef m hm i j k l : K)) q q' q''

/-- `bpW:w1:trilinear` (i), sequence form: absolute convergence, `T(q,q',q'') ∈ ℓ^{a,p+1}` and
`‖T(q,q',q'')‖_{a,p+1} ≤ C_* ‖q‖_{a,p}‖q'‖_{a,p}‖q''‖_{a,p}`, `C_* = K_{p+1/2}²/π`. -/
theorem waveTri_oneSided {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) {q q' q'' : ℕ+ → K}
    (hq : IsEll a p q) (hq' : IsEll a p q') (hq'' : IsEll a p q'') :
    (∀ l : ℕ+, Summable fun t : ℕ+ × ℕ+ × ℕ+ =>
        ‖(waveTriCoef m hm t.1 t.2.1 t.2.2 l : K) * (q t.1 * (q' t.2.1 * q'' t.2.2))‖) ∧
      IsEll a (p + 1) (waveTriSeq m hm q q' q'') ∧
      ellTsumNorm a (p + 1) (waveTriSeq m hm q q' q'') ≤
        waveCubicConst p * (ellTsumNorm a p q * ellTsumNorm a p q' * ellTsumNorm a p q'') := by
  have h := waveSel_oneSided (K := K) ha hp (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
    (c := fun i j k l => (waveTriCoef m hm i j k l : K)) (fun i j k l => waveTriCoef_bound m hm i j k l)
    hq hq' hq''
  refine ⟨h.1, h.2.1, ?_⟩
  have hc : 2 * (1 / (2 * Real.pi)) * waveAlgConst (p + 1 / 2) ^ 2 = waveCubicConst p := by
    unfold waveCubicConst
    field_simp
  have := h.2.2
  rw [hc] at this
  exact this

end KAM.Wave

end
