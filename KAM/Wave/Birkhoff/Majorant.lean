/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.Reindex
public import KAM.Wave.Cubic.TriSeq

/-!
# Majorant for the cubic sums (blueprint-W `bpW:w3:majorant`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-SETTING, blueprint label `bpW:w3:majorant`.

For nonnegative `u, u', u'' ∈ ℓ^{a,p}`,
`𝓜(u,u',u'')_l = λ_l^{-1/2} Σ_{i,j,k ≥ 1} |g_{ijkl}| u_i u'_j u''_k / √(λ_i λ_j λ_k)`
(`birkMajorant`; `birkMajorant_eq` is the displayed formula). The sums converge absolutely and
`‖𝓜(u,u',u'')‖_{a,p+1} ≤ C_* ‖u‖ ‖u'‖ ‖u''‖` with `C_* = waveCubicConst p = K_{p+1/2}²/π`
(`birkMajorant_bound`). Also the passage from sums over `(ℤ ∖ {0})³` to the sign-folded sequences
`u_i = |w_i| + |w_{-i}|` (`birk_three_sum`, `birkFold`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m)

/-- (`bpW:w3:majorant`) `𝓜(u,u',u'')_l = Σ_{ijk} |c_{ijkl}| u_i u'_j u''_k`,
`c_{ijkl} = g_{ijkl}(λ_iλ_jλ_kλ_l)^{-1/2}`. -/
def birkMajorant (u u' u'' : ℕ+ → ℝ) (l : ℕ+) : ℝ :=
  waveSelSum (K := ℝ) (fun i j k l => |waveTriCoef m hm i j k l|) u u' u'' l

/-- (`bpW:w3:majorant`) the displayed formula
`λ_l^{-1/2} Σ |g_{ijkl}| u_i u'_j u''_k/√(λ_iλ_jλ_k)`. -/
theorem birkMajorant_eq (u u' u'' : ℕ+ → ℝ) (l : ℕ+) :
    birkMajorant m hm u u' u'' l =
      (lam m hm l) ^ (-(1 / 2 : ℝ)) * ∑' t : ℕ+ × ℕ+ × ℕ+,
        |waveQuartic t.1 t.2.1 t.2.2 l| * (u t.1 * (u' t.2.1 * u'' t.2.2)) /
          Real.sqrt (lam m hm t.1 * lam m hm t.2.1 * lam m hm t.2.2) := by
  unfold birkMajorant waveSelSum
  rw [← tsum_mul_left]
  refine tsum_congr fun t => ?_
  obtain ⟨i, j, k⟩ := t
  simp only [waveTriCoef, abs_div]
  have hi := wave_lam_pos m hm i
  have hj := wave_lam_pos m hm j
  have hk := wave_lam_pos m hm k
  have hl := wave_lam_pos m hm l
  rw [abs_of_pos (by positivity : 0 < Real.sqrt (lam m hm i) * Real.sqrt (lam m hm j) *
      Real.sqrt (lam m hm k) * Real.sqrt (lam m hm l)),
    Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.rpow_neg hl.le,
    ← Real.sqrt_eq_rpow]
  have := Real.sqrt_pos.2 hi
  have := Real.sqrt_pos.2 hj
  have := Real.sqrt_pos.2 hk
  have := Real.sqrt_pos.2 hl
  field_simp

/-- (`bpW:w3:majorant`) The sums converge absolutely and
`‖𝓜(u,u',u'')‖_{a,p+1} ≤ C_* ‖u‖_{a,p}‖u'‖_{a,p}‖u''‖_{a,p}`, `C_* = K_{p+1/2}²/π`
(`waveCubicConst p`). -/
theorem birkMajorant_bound {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) {u u' u'' : ℕ+ → ℝ}
    (hu : IsEll a p u) (hu' : IsEll a p u') (hu'' : IsEll a p u'') :
    (∀ l : ℕ+, Summable fun t : ℕ+ × ℕ+ × ℕ+ =>
        ‖|waveTriCoef m hm t.1 t.2.1 t.2.2 l| * (u t.1 * (u' t.2.1 * u'' t.2.2))‖) ∧
      IsEll a (p + 1) (birkMajorant m hm u u' u'') ∧
      ellTsumNorm a (p + 1) (birkMajorant m hm u u' u'') ≤
        waveCubicConst p * (ellTsumNorm a p u * ellTsumNorm a p u' * ellTsumNorm a p u'') := by
  have h := waveSel_oneSided (K := ℝ) ha hp (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
    (c := fun i j k l => |waveTriCoef m hm i j k l|)
    (fun i j k l => by
      have := waveTriCoef_bound (K := ℝ) m hm i j k l
      simpa using this) hu hu' hu''
  refine ⟨h.1, h.2.1, ?_⟩
  have hc : 2 * (1 / (2 * Real.pi)) * waveAlgConst (p + 1 / 2) ^ 2 = waveCubicConst p := by
    unfold waveCubicConst
    field_simp
  have := h.2.2
  rw [hc] at this
  exact this

/-! ### Folding the signs -/

/-- The sign-folded sequence `u_i = |w_i| + |w_{-i}|` of a two-sided sequence `W ≥ 0`. -/
def birkFold (W : BirkIdx → ℝ) (i : ℕ+) : ℝ := W (true, i) + W (false, i)

/-- (`bpW:w3:quartic`, Step Majorize) A sum over `(ℤ ∖ {0})³` of a sign-independent weight `G`
against a product of nonnegative two-sided sequences is the corresponding sum over `ℕ+³` of
the sign-folded sequences. -/
theorem birk_three_sum {G : ℕ+ → ℕ+ → ℕ+ → ℝ} (hG : ∀ i j k, 0 ≤ G i j k)
    (W : Fin 3 → BirkIdx → ℝ) (hW : ∀ t l, 0 ≤ W t l)
    (hsum : Summable fun τ : ℕ+ × ℕ+ × ℕ+ =>
      G τ.1 τ.2.1 τ.2.2 * (birkFold (W 0) τ.1 * (birkFold (W 1) τ.2.1 * birkFold (W 2) τ.2.2))) :
    Summable (fun y : Fin 3 → BirkIdx => G (y 0).2 (y 1).2 (y 2).2 * ∏ t, W t (y t)) ∧
      ∑' y : Fin 3 → BirkIdx, G (y 0).2 (y 1).2 (y 2).2 * ∏ t, W t (y t) =
        ∑' τ : ℕ+ × ℕ+ × ℕ+, G τ.1 τ.2.1 τ.2.2 *
          (birkFold (W 0) τ.1 * (birkFold (W 1) τ.2.1 * birkFold (W 2) τ.2.2)) := by
  set H : (Fin 3 → ℕ+) → ℝ := fun mm => G (mm 0) (mm 1) (mm 2) *
    ∏ t, birkFold (W t) (mm t) with hH
  have hHs : Summable H := by
    have := birkTriEquiv.summable_iff.2 hsum
    refine this.congr fun mm => ?_
    simp [hH, birkTriEquiv_apply, Fin.prod_univ_three, mul_assoc]
  have hF0 : ∀ y : Fin 3 → BirkIdx, 0 ≤ G (y 0).2 (y 1).2 (y 2).2 * ∏ t, W t (y t) := fun y =>
    mul_nonneg (hG _ _ _) (Finset.prod_nonneg fun t _ => hW _ _)
  have hle : ∀ (s : Fin 3 → Bool) (mm : Fin 3 → ℕ+),
      G (mm 0) (mm 1) (mm 2) * ∏ t, W t (s t, mm t) ≤ H mm := fun s mm => by
    refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun t _ => hW _ _) fun t _ => ?_) (hG _ _ _)
    cases hs : s t <;> simp [birkFold, hW]
  have hsumm : Summable (fun y : Fin 3 → BirkIdx => G (y 0).2 (y 1).2 (y 2).2 * ∏ t, W t (y t)) := by
    refine birk_summable_pi hF0 fun s => ?_
    exact Summable.of_nonneg_of_le (fun mm => hF0 (fun t => (s t, mm t))) (fun mm => hle s mm) hHs
  refine ⟨hsumm, ?_⟩
  rw [birk_tsum_pi hsumm]
  have hs : ∀ s ∈ (Finset.univ : Finset (Fin 3 → Bool)), Summable fun mm : Fin 3 → ℕ+ =>
      G (mm 0) (mm 1) (mm 2) * ∏ t, W t (s t, mm t) :=
    fun s _ => Summable.of_nonneg_of_le (fun mm => hF0 (fun t => (s t, mm t))) (fun mm => hle s mm) hHs
  have e1 : ∑ s : Fin 3 → Bool, ∑' mm : Fin 3 → ℕ+, G (mm 0) (mm 1) (mm 2) * ∏ t, W t (s t, mm t) =
      ∑' mm : Fin 3 → ℕ+, ∑ s : Fin 3 → Bool, G (mm 0) (mm 1) (mm 2) * ∏ t, W t (s t, mm t) :=
    (Summable.tsum_finsetSum hs).symm
  simp only [birkPiEquiv_apply] at e1 ⊢
  rw [e1]
  have e2 : ∀ mm : Fin 3 → ℕ+, ∑ s : Fin 3 → Bool, G (mm 0) (mm 1) (mm 2) * ∏ t, W t (s t, mm t) =
      H mm := fun mm => by
    rw [← Finset.mul_sum, hH]
    congr 1
    exact birk_sign_sum_prod (fun t b => W t (b, mm t))
  rw [tsum_congr e2, ← birkTriEquiv.tsum_eq]
  refine tsum_congr fun mm => ?_
  simp [hH, birkTriEquiv_apply, Fin.prod_univ_three, mul_assoc]

end KAM.Wave

end
