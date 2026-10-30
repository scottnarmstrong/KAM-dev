/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Algebra.TwoSided
public import KAM.Frozen.Wave.Defs.EllWeight
public import KAM.Frozen.Wave.Defs.Lam

/-!
# Passage between one- and two-sided sequences (blueprint `bpW:w1:twosided`)

Infrastructure used by several nodes; the dependency graph is still being built.

One-sided sequences are `q : ℕ+ → ℂ` with `WaveOneMem a p q`
(`∑ (ω_{a,p}(j) |q_j|)² < ∞`, `ellWeight`);
two-sided ones are `ℤ → ℂ` with `WaveTwoMem`.

* `KAM.Wave.waveExt` : the even/odd extensions `E^±`; `wave_ext_mem` is part (i);
  `waveEvenMaj`, `wave_evenMaj_norm_sq` the even sequence with `‖x‖² = 2‖q‖²`;
* `KAM.Wave.waveRestr`, `wave_restr_mem` : restriction with gain, part (ii);
* `KAM.Wave.waveJ`, `wave_J_norm_sq`, `wave_J_surj` : the pairing, part (iii).
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- Membership in the one-sided space `ℓ^{a,p}_ℂ` (blueprint `bpW:w0:ellap`). -/
def WaveOneMem (a p : ℝ) (q : ℕ+ → ℂ) : Prop :=
  Summable fun j : ℕ+ => (ellWeight a p j * ‖q j‖) ^ 2

/-- The norm of `ℓ^{a,p}_ℂ`. -/
def waveOneNorm (a p : ℝ) (q : ℕ+ → ℂ) : ℝ :=
  √(∑' j : ℕ+, (ellWeight a p j * ‖q j‖) ^ 2)

theorem waveOneNorm_nonneg (a p : ℝ) (q : ℕ+ → ℂ) : 0 ≤ waveOneNorm a p q := Real.sqrt_nonneg _

/-- The positive integer `|l|` of a nonzero `l ∈ ℤ`. -/
def wavePosOf (l : ℤ) (h : l ≠ 0) : ℕ+ := ⟨l.natAbs, Int.natAbs_pos.mpr h⟩

theorem wavePosOf_pos (j : ℕ+) : wavePosOf ((j : ℕ) : ℤ) (by simp) = j := by
  apply PNat.eq; simp [wavePosOf]

theorem wavePosOf_neg (j : ℕ+) : wavePosOf (-((j : ℕ) : ℤ)) (by simp) = j := by
  apply PNat.eq; simp [wavePosOf]

/-- Folding a two-sided sum with `f 0` in the middle and prescribed positive and negative halves. -/
theorem wave_hasSum_fold2 {f : ℤ → ℝ} {g₁ g₂ : ℕ+ → ℝ} {S₁ S₂ : ℝ}
    (hpos : ∀ n : ℕ+, f (((n : ℕ) : ℤ)) = g₁ n) (hneg : ∀ n : ℕ+, f (-((n : ℕ) : ℤ)) = g₂ n)
    (h₁ : HasSum g₁ S₁) (h₂ : HasSum g₂ S₂) : HasSum f (f 0 + S₁ + S₂) := by
  have hgN₁ : HasSum (fun n : ℕ => g₁ n.succPNat) S₁ :=
    (Equiv.hasSum_iff (Equiv.pnatEquivNat.symm) (f := g₁)).mpr h₁
  have hgN₂ : HasSum (fun n : ℕ => g₂ n.succPNat) S₂ :=
    (Equiv.hasSum_iff (Equiv.pnatEquivNat.symm) (f := g₂)).mpr h₂
  have h1 : HasSum (fun n : ℕ => f ((n : ℕ) : ℤ)) (f 0 + S₁) := by
    have e : (fun n : ℕ => f (((n + 1 : ℕ) : ℕ) : ℤ)) = fun n : ℕ => g₁ n.succPNat :=
      funext fun n => hpos n.succPNat
    refine (hasSum_nat_add_iff' (f := fun n : ℕ => f ((n : ℕ) : ℤ)) (g := f 0 + S₁) 1).mp ?_
    simp only [Finset.sum_range_one, Nat.cast_zero, add_sub_cancel_left]
    rw [e]; exact hgN₁
  have h2 : HasSum (fun n : ℕ => f (-((n : ℤ) + 1))) S₂ := by
    have : (fun n : ℕ => f (-((n : ℤ) + 1))) = fun n : ℕ => g₂ n.succPNat :=
      funext fun n => by
        have := hneg n.succPNat
        simpa using this
    rw [this]; exact hgN₂
  have := HasSum.of_nat_of_neg_add_one (f := f) h1 h2
  simpa [add_assoc] using this

/-- Folding a symmetric two-sided sum: `∑_ℤ f = f 0 + 2 ∑_{j ≥ 1} g`. -/
theorem wave_hasSum_fold {f : ℤ → ℝ} {g : ℕ+ → ℝ} {S : ℝ}
    (hpos : ∀ n : ℕ+, f (((n : ℕ) : ℤ)) = g n) (hneg : ∀ n : ℕ+, f (-((n : ℕ) : ℤ)) = g n)
    (hg : HasSum g S) : HasSum f (f 0 + 2 * S) := by
  have := wave_hasSum_fold2 hpos hneg hg hg
  rwa [show f 0 + S + S = f 0 + 2 * S by ring] at this

theorem waveJap_pnat (j : ℕ+) : waveJap ((j : ℕ) : ℤ) = (j : ℝ) := by
  have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast j.pos
  simp only [waveJap, Int.cast_natCast]
  rw [abs_of_nonneg (by linarith), max_eq_right this]

/-- On `l = j ≥ 1` the two-sided weight is the one-sided weight. -/
theorem waveTwoWeight_pnat (a s : ℝ) (j : ℕ+) :
    waveTwoWeight a s ((j : ℕ) : ℤ) = ellWeight a s j := by
  have : (0 : ℝ) ≤ (j : ℝ) := by positivity
  simp [waveTwoWeight, waveJap_pnat, ellWeight, abs_of_nonneg this]

/-- On `l = -j`, `j ≥ 1`, the two-sided weight is the one-sided weight. -/
theorem waveTwoWeight_neg_pnat (a s : ℝ) (j : ℕ+) :
    waveTwoWeight a s (-((j : ℕ) : ℤ)) = ellWeight a s j := by
  have h := waveTwoWeight_pnat a s j
  simp only [waveTwoWeight, waveJap_neg] at h ⊢
  simpa using h

/-- `ω_{a,p+1/2}(j)² = ω_{a,p}(j)² · j`. -/
theorem wave_ellWeight_sq_succ (a p : ℝ) (j : ℕ+) :
    ellWeight a (p + 1 / 2) j ^ 2 = ellWeight a p j ^ 2 * (j : ℝ) := by
  have hj : (0 : ℝ) < (j : ℝ) := by positivity
  simp only [ellWeight]
  rw [mul_pow, mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast ((j : ℝ) ^ p),
    ← Real.rpow_mul hj.le, ← Real.rpow_mul hj.le,
    show (p + 1 / 2) * ((2 : ℕ) : ℝ) = p * ((2 : ℕ) : ℝ) + 1 by push_cast; ring,
    Real.rpow_add hj, Real.rpow_one]
  ring

theorem wave_le_lam (m : ℝ) (hm : 0 < m) (j : ℕ+) : (j : ℝ) ≤ lam m hm j := by
  have : (j : ℝ) ^ 2 ≤ (j : ℝ) ^ 2 + m := by linarith
  have h := Real.abs_le_sqrt this
  rwa [abs_of_nonneg (by positivity)] at h

theorem wave_lam_pos (m : ℝ) (hm : 0 < m) (j : ℕ+) : 0 < lam m hm j :=
  lt_of_lt_of_le (by positivity) (wave_le_lam m hm j)

/-- The even (`σ = 1`) and odd (`σ = -1`) extensions
`(E^σ q)_l = σ^{[l<0]} q_{|l|} / √λ_{|l|}`, `(E^σ q)_0 = 0` (blueprint `bpW:w1:twosided` (i)). -/
def waveExt (m : ℝ) (hm : 0 < m) (σ : ℂ) (q : ℕ+ → ℂ) (l : ℤ) : ℂ :=
  if h : l = 0 then 0
  else (if l < 0 then σ else 1) * q (wavePosOf l h) / (Real.sqrt (lam m hm (wavePosOf l h)) : ℂ)

theorem waveExt_zero (m : ℝ) (hm : 0 < m) (σ : ℂ) (q : ℕ+ → ℂ) : waveExt m hm σ q 0 = 0 := by
  simp [waveExt]

theorem waveExt_pos (m : ℝ) (hm : 0 < m) (σ : ℂ) (q : ℕ+ → ℂ) (j : ℕ+) :
    waveExt m hm σ q ((j : ℕ) : ℤ) = q j / (Real.sqrt (lam m hm j) : ℂ) := by
  have h : ((j : ℕ) : ℤ) ≠ 0 := by simp
  have h2 : ¬ (((j : ℕ) : ℤ) < 0) := by simp
  simp only [waveExt, h, h2, ↓reduceDIte, ↓reduceIte, wavePosOf_pos, one_mul]

theorem waveExt_neg (m : ℝ) (hm : 0 < m) (σ : ℂ) (q : ℕ+ → ℂ) (j : ℕ+) :
    waveExt m hm σ q (-((j : ℕ) : ℤ)) = σ * q j / (Real.sqrt (lam m hm j) : ℂ) := by
  have h : (-((j : ℕ) : ℤ)) ≠ 0 := by simp
  have h2 : (-((j : ℕ) : ℤ)) < 0 := by simp
  simp only [waveExt, h, h2, ↓reduceDIte, ↓reduceIte, wavePosOf_neg]

theorem waveExt_add (m : ℝ) (hm : 0 < m) (σ : ℂ) (q q' : ℕ+ → ℂ) :
    waveExt m hm σ (q + q') = waveExt m hm σ q + waveExt m hm σ q' := by
  funext l
  by_cases h : l = 0
  · simp [waveExt, h]
  · simp only [waveExt, h, ↓reduceDIte, Pi.add_apply]; ring

theorem waveExt_smul (m : ℝ) (hm : 0 < m) (σ : ℂ) (r : ℂ) (q : ℕ+ → ℂ) :
    waveExt m hm σ (r • q) = r • waveExt m hm σ q := by
  funext l
  by_cases h : l = 0
  · simp [waveExt, h]
  · simp only [waveExt, h, ↓reduceDIte, Pi.smul_apply, smul_eq_mul]; ring

theorem waveExt_norm_pos (m : ℝ) (hm : 0 < m) {σ : ℂ} (q : ℕ+ → ℂ) (j : ℕ+) :
    ‖waveExt m hm σ q ((j : ℕ) : ℤ)‖ = ‖q j‖ / √(lam m hm j) := by
  rw [waveExt_pos, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

theorem waveExt_norm_neg (m : ℝ) (hm : 0 < m) {σ : ℂ} (hσ : ‖σ‖ = 1) (q : ℕ+ → ℂ) (j : ℕ+) :
    ‖waveExt m hm σ q (-((j : ℕ) : ℤ))‖ = ‖q j‖ / √(lam m hm j) := by
  rw [waveExt_neg, norm_div, norm_mul, hσ, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

/-- Even and odd extensions (blueprint `bpW:w1:twosided` (i)): `E^± : ℓ^{a,p}_ℂ → ℓ^{a,p+1/2}_b`
with `‖E^± q‖_{a,p+1/2} ≤ √2 ‖q‖_{a,p}`. Here `σ = ±1` (any `‖σ‖ = 1`). -/
theorem wave_ext_mem (m : ℝ) (hm : 0 < m) {a p : ℝ} {σ : ℂ} (hσ : ‖σ‖ = 1) {q : ℕ+ → ℂ}
    (hq : WaveOneMem a p q) :
    WaveTwoMem a (p + 1 / 2) (waveExt m hm σ q) ∧
    waveTwoNorm a (p + 1 / 2) (waveExt m hm σ q) ≤ √2 * waveOneNorm a p q := by
  set F : ℕ+ → ℝ := fun j => (ellWeight a (p + 1 / 2) j * (‖q j‖ / √(lam m hm j))) ^ 2 with hF
  have hF_le : ∀ j, F j ≤ (ellWeight a p j * ‖q j‖) ^ 2 := fun j => by
    have hl := wave_lam_pos m hm j
    have e : F j = ellWeight a p j ^ 2 * (j : ℝ) * ‖q j‖ ^ 2 / lam m hm j := by
      simp only [hF]
      rw [mul_pow, div_pow, Real.sq_sqrt hl.le, wave_ellWeight_sq_succ]; ring
    rw [e, div_le_iff₀ hl]
    have := mul_le_mul_of_nonneg_left (wave_le_lam m hm j)
      (mul_nonneg (sq_nonneg (ellWeight a p j)) (sq_nonneg ‖q j‖))
    nlinarith
  have hFs : Summable F :=
    Summable.of_nonneg_of_le (fun j => sq_nonneg _) hF_le hq
  have hfold := wave_hasSum_fold
    (f := fun l => (waveTwoWeight a (p + 1 / 2) l * ‖waveExt m hm σ q l‖) ^ 2) (g := F)
    (fun j => by simp only [hF, waveTwoWeight_pnat, waveExt_norm_pos m hm])
    (fun j => by simp only [hF, waveTwoWeight_neg_pnat, waveExt_norm_neg m hm hσ]) hFs.hasSum
  simp only [waveExt_zero, norm_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_add] at hfold
  refine ⟨hfold.summable, ?_⟩
  unfold waveTwoNorm waveOneNorm
  rw [hfold.tsum_eq]
  calc √(2 * ∑' j, F j) ≤ √(2 * ∑' j : ℕ+, (ellWeight a p j * ‖q j‖) ^ 2) :=
        Real.sqrt_le_sqrt
          (mul_le_mul_of_nonneg_left (hFs.tsum_le_tsum hF_le hq) (by norm_num : (0 : ℝ) ≤ 2))
    _ = _ := Real.sqrt_mul (by norm_num) _

/-- The even majorant sequence `x_l = |q_{|l|}| / √|l|` (`l ≠ 0`), `x_0 = 0`
(blueprint `bpW:w1:twosided` (i)). -/
def waveEvenMaj (q : ℕ+ → ℂ) (l : ℤ) : ℂ :=
  if h : l = 0 then 0 else ((‖q (wavePosOf l h)‖ / √((wavePosOf l h : ℕ+) : ℝ) : ℝ) : ℂ)

theorem waveEvenMaj_zero (q : ℕ+ → ℂ) : waveEvenMaj q 0 = 0 := by simp [waveEvenMaj]

theorem waveEvenMaj_norm_pos (q : ℕ+ → ℂ) (j : ℕ+) :
    ‖waveEvenMaj q ((j : ℕ) : ℤ)‖ = ‖q j‖ / √(j : ℝ) := by
  have h : ((j : ℕ) : ℤ) ≠ 0 := by simp
  simp only [waveEvenMaj, h, ↓reduceDIte, wavePosOf_pos, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (by positivity)

theorem waveEvenMaj_norm_neg (q : ℕ+ → ℂ) (j : ℕ+) :
    ‖waveEvenMaj q (-((j : ℕ) : ℤ))‖ = ‖q j‖ / √(j : ℝ) := by
  have h : (-((j : ℕ) : ℤ)) ≠ 0 := by simp
  simp only [waveEvenMaj, h, ↓reduceDIte, wavePosOf_neg, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (by positivity)

/-- The even sequence `x_l = |q_{|l|}|/√|l|` satisfies `‖x‖²_{a,p+1/2} = 2 ‖q‖²_{a,p}`
(blueprint `bpW:w1:twosided` (i)). -/
theorem wave_evenMaj_norm_sq {a p : ℝ} {q : ℕ+ → ℂ} (hq : WaveOneMem a p q) :
    WaveTwoMem a (p + 1 / 2) (waveEvenMaj q) ∧
    waveTwoNorm a (p + 1 / 2) (waveEvenMaj q) ^ 2 = 2 * waveOneNorm a p q ^ 2 := by
  set F : ℕ+ → ℝ := fun j => (ellWeight a (p + 1 / 2) j * (‖q j‖ / √(j : ℝ))) ^ 2 with hF
  have hFG : ∀ j, F j = (ellWeight a p j * ‖q j‖) ^ 2 := fun j => by
    have hj : (0 : ℝ) < (j : ℝ) := by positivity
    simp only [hF]
    rw [mul_pow, div_pow, Real.sq_sqrt hj.le, wave_ellWeight_sq_succ]
    field_simp
  have hFs : Summable F := hq.congr fun j => (hFG j).symm
  have hfold := wave_hasSum_fold
    (f := fun l => (waveTwoWeight a (p + 1 / 2) l * ‖waveEvenMaj q l‖) ^ 2) (g := F)
    (fun j => by simp only [hF, waveTwoWeight_pnat, waveEvenMaj_norm_pos])
    (fun j => by simp only [hF, waveTwoWeight_neg_pnat, waveEvenMaj_norm_neg]) hFs.hasSum
  simp only [waveEvenMaj_zero, norm_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_add] at hfold
  refine ⟨hfold.summable, ?_⟩
  unfold waveTwoNorm waveOneNorm
  rw [hfold.tsum_eq, Real.sq_sqrt (by positivity), Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _)]
  rw [tsum_congr hFG]

/-- Restriction with gain: `(X_l / √λ_l)_{l ≥ 1}` (blueprint `bpW:w1:twosided` (ii)). -/
def waveRestr (m : ℝ) (hm : 0 < m) (X : ℤ → ℂ) (j : ℕ+) : ℂ :=
  X ((j : ℕ) : ℤ) / (Real.sqrt (lam m hm j) : ℂ)

/-- Restriction with gain (blueprint `bpW:w1:twosided` (ii)): for `X ∈ ℓ^{a,p+1/2}_b` the sequence
`(X_l/√λ_l)_{l ≥ 1}` lies in `ℓ^{a,p+1}_ℂ` with norm at most
`(∑_{l ≥ 1} l^{2p+1} e^{2al} |X_l|²)^{1/2} ≤ ‖X‖_{a,p+1/2}`; and at most `‖X‖_{a,p+1/2}/√2`
if `|X|` is even. -/
theorem wavePnatCast_injective : Function.Injective (fun j : ℕ+ => ((j : ℕ) : ℤ)) :=
  fun _ _ h => PNat.coe_injective (Nat.cast_injective h)

theorem wave_restr_mem (m : ℝ) (hm : 0 < m) {a p : ℝ} {X : ℤ → ℂ}
    (hX : WaveTwoMem a (p + 1 / 2) X) :
    WaveOneMem a (p + 1) (waveRestr m hm X) ∧
    waveOneNorm a (p + 1) (waveRestr m hm X) ≤
      √(∑' j : ℕ+, (ellWeight a (p + 1 / 2) j * ‖X ((j : ℕ) : ℤ)‖) ^ 2) ∧
    √(∑' j : ℕ+, (ellWeight a (p + 1 / 2) j * ‖X ((j : ℕ) : ℤ)‖) ^ 2) ≤
      waveTwoNorm a (p + 1 / 2) X ∧
    ((∀ l : ℤ, ‖X (-l)‖ = ‖X l‖) →
      √2 * √(∑' j : ℕ+, (ellWeight a (p + 1 / 2) j * ‖X ((j : ℕ) : ℤ)‖) ^ 2) ≤
        waveTwoNorm a (p + 1 / 2) X) := by
  set H : ℕ+ → ℝ := fun j => (ellWeight a (p + 1 / 2) j * ‖X ((j : ℕ) : ℤ)‖) ^ 2 with hH
  have hHs : Summable H := by
    have := hX.comp_injective (i := fun j : ℕ+ => ((j : ℕ) : ℤ))
      wavePnatCast_injective
    refine this.congr fun j => ?_
    simp [hH, waveTwoWeight_pnat]
  have hR : ∀ j, (ellWeight a (p + 1) j * ‖waveRestr m hm X j‖) ^ 2 ≤ H j := fun j => by
    have hl := wave_lam_pos m hm j
    have hj : (0 : ℝ) < (j : ℝ) := by positivity
    have e : (ellWeight a (p + 1) j * ‖waveRestr m hm X j‖) ^ 2 =
        ellWeight a (p + 1 / 2) j ^ 2 * (j : ℝ) * ‖X ((j : ℕ) : ℤ)‖ ^ 2 / lam m hm j := by
      have e1 : ellWeight a (p + 1) j ^ 2 = ellWeight a (p + 1 / 2) j ^ 2 * (j : ℝ) := by
        have := wave_ellWeight_sq_succ a (p + 1 / 2) j
        rw [show p + 1 / 2 + 1 / 2 = p + 1 by ring] at this
        exact this
      simp only [waveRestr]
      rw [mul_pow, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt hl.le, e1]
      ring
    rw [e, div_le_iff₀ hl]
    simp only [hH]
    have := mul_le_mul_of_nonneg_left (wave_le_lam m hm j)
      (mul_nonneg (sq_nonneg (ellWeight a (p + 1 / 2) j)) (sq_nonneg ‖X ((j : ℕ) : ℤ)‖))
    nlinarith
  have hRs : WaveOneMem a (p + 1) (waveRestr m hm X) :=
    Summable.of_nonneg_of_le (fun j => sq_nonneg _) hR hHs
  have hle : ∑' j, H j ≤ ∑' l : ℤ, (waveTwoWeight a (p + 1 / 2) l * ‖X l‖) ^ 2 := by
    have := tsum_comp_le_tsum_of_inj hX (fun _ => sq_nonneg _) wavePnatCast_injective
    refine le_trans (le_of_eq ?_) this
    exact tsum_congr fun j => by simp [hH, waveTwoWeight_pnat]
  refine ⟨hRs, Real.sqrt_le_sqrt (hRs.tsum_le_tsum hR hHs), Real.sqrt_le_sqrt hle, fun hev => ?_⟩
  have hfold := wave_hasSum_fold
    (f := fun l => (waveTwoWeight a (p + 1 / 2) l * ‖X l‖) ^ 2) (g := H)
    (fun j => by simp [hH, waveTwoWeight_pnat])
    (fun j => by simp only [hH, waveTwoWeight_neg_pnat, hev]) hHs.hasSum
  unfold waveTwoNorm
  rw [← Real.sqrt_mul (by norm_num), hfold.tsum_eq]
  refine Real.sqrt_le_sqrt ?_
  have : 0 ≤ (waveTwoWeight a (p + 1 / 2) 0 * ‖X 0‖) ^ 2 := sq_nonneg _
  linarith

/-- The pairing `J(z, z̄)_j = z_j`, `J(z, z̄)_{-j} = z̄_j` (`j ≥ 1`), `J(z, z̄)_0 = 0`
(blueprint `bpW:w1:twosided` (iii)); `z̄` is an independent variable. -/
def waveJ (z zb : ℕ+ → ℂ) (l : ℤ) : ℂ :=
  if h : l = 0 then 0 else if 0 < l then z (wavePosOf l h) else zb (wavePosOf l h)

theorem waveJ_zero (z zb : ℕ+ → ℂ) : waveJ z zb 0 = 0 := by simp [waveJ]

theorem waveJ_pos (z zb : ℕ+ → ℂ) (j : ℕ+) : waveJ z zb ((j : ℕ) : ℤ) = z j := by
  have h : ((j : ℕ) : ℤ) ≠ 0 := by simp
  have h2 : 0 < ((j : ℕ) : ℤ) := by simp
  simp only [waveJ, h, h2, ↓reduceDIte, ↓reduceIte, wavePosOf_pos]

theorem waveJ_neg (z zb : ℕ+ → ℂ) (j : ℕ+) : waveJ z zb (-((j : ℕ) : ℤ)) = zb j := by
  have h : (-((j : ℕ) : ℤ)) ≠ 0 := by simp
  have h2 : ¬ 0 < (-((j : ℕ) : ℤ)) := by simp
  simp only [waveJ, h, h2, ↓reduceDIte, ↓reduceIte, wavePosOf_neg]

theorem waveJ_add (z zb z' zb' : ℕ+ → ℂ) :
    waveJ (z + z') (zb + zb') = waveJ z zb + waveJ z' zb' := by
  funext l
  by_cases h : l = 0
  · simp [waveJ, h]
  · by_cases h2 : 0 < l <;> simp [waveJ, h, h2]

theorem waveJ_smul (r : ℂ) (z zb : ℕ+ → ℂ) : waveJ (r • z) (r • zb) = r • waveJ z zb := by
  funext l
  by_cases h : l = 0
  · simp [waveJ, h]
  · by_cases h2 : 0 < l <;> simp [waveJ, h, h2]

/-- The pairing is an isometry for the norm `(‖z‖² + ‖z̄‖²)^{1/2}` (blueprint `bpW:w1:twosided`
(iii)). -/
theorem wave_J_norm_sq {a p : ℝ} {z zb : ℕ+ → ℂ} (hz : WaveOneMem a p z) (hzb : WaveOneMem a p zb) :
    WaveTwoMem a p (waveJ z zb) ∧
    waveTwoNorm a p (waveJ z zb) ^ 2 = waveOneNorm a p z ^ 2 + waveOneNorm a p zb ^ 2 := by
  have hfold := wave_hasSum_fold2
    (f := fun l => (waveTwoWeight a p l * ‖waveJ z zb l‖) ^ 2)
    (g₁ := fun j : ℕ+ => (ellWeight a p j * ‖z j‖) ^ 2)
    (g₂ := fun j : ℕ+ => (ellWeight a p j * ‖zb j‖) ^ 2)
    (fun j => by simp only [waveTwoWeight_pnat, waveJ_pos])
    (fun j => by simp only [waveTwoWeight_neg_pnat, waveJ_neg]) hz.hasSum hzb.hasSum
  simp only [waveJ_zero, norm_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_add] at hfold
  refine ⟨hfold.summable, ?_⟩
  unfold waveTwoNorm waveOneNorm
  rw [hfold.tsum_eq, Real.sq_sqrt (add_nonneg (tsum_nonneg fun _ => sq_nonneg _)
      (tsum_nonneg fun _ => sq_nonneg _)),
    Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _),
    Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _)]

/-- `‖J(z, z̄)‖_{a,p} ≤ √2 max(‖z‖_{a,p}, ‖z̄‖_{a,p})` (blueprint `bpW:w1:twosided` (iii)). -/
theorem wave_J_norm_le {a p : ℝ} {z zb : ℕ+ → ℂ} (hz : WaveOneMem a p z) (hzb : WaveOneMem a p zb) :
    waveTwoNorm a p (waveJ z zb) ≤ √2 * max (waveOneNorm a p z) (waveOneNorm a p zb) := by
  obtain ⟨-, h⟩ := wave_J_norm_sq hz hzb
  have h1 := le_max_left (waveOneNorm a p z) (waveOneNorm a p zb)
  have h2 := le_max_right (waveOneNorm a p z) (waveOneNorm a p zb)
  have h3 := waveOneNorm_nonneg a p z
  have h4 := waveOneNorm_nonneg a p zb
  refine (pow_le_pow_iff_left₀ (waveTwoNorm_nonneg _ _ _)
    (mul_nonneg (Real.sqrt_nonneg _) (h3.trans h1)) (two_ne_zero)).mp ?_
  rw [h, mul_pow, Real.sq_sqrt (by norm_num)]
  nlinarith [mul_self_le_mul_self h3 h1, mul_self_le_mul_self h4 h2]

/-- The pairing is onto `{w : w_0 = 0}` (blueprint `bpW:w1:twosided` (iii)). -/
theorem wave_J_surj {a p : ℝ} {w : ℤ → ℂ} (hw0 : w 0 = 0) (hw : WaveTwoMem a p w) :
    ∃ z zb : ℕ+ → ℂ, WaveOneMem a p z ∧ WaveOneMem a p zb ∧ waveJ z zb = w := by
  have hinj2 : Function.Injective (fun j : ℕ+ => -((j : ℕ) : ℤ)) :=
    fun _ _ h => wavePnatCast_injective (neg_injective h)
  refine ⟨fun j => w ((j : ℕ) : ℤ), fun j => w (-((j : ℕ) : ℤ)), ?_, ?_, ?_⟩
  · refine (hw.comp_injective wavePnatCast_injective).congr fun j => ?_
    simp [waveTwoWeight_pnat]
  · refine (hw.comp_injective hinj2).congr fun j => ?_
    simp [waveTwoWeight_neg_pnat]
  · funext l
    by_cases h : l = 0
    · simp [h, waveJ_zero, hw0]
    · by_cases h2 : 0 < l
      · have : ((wavePosOf l h : ℕ+) : ℕ) = l.natAbs := rfl
        simp only [waveJ, h, h2, ↓reduceDIte, ↓reduceIte, this, Int.natCast_natAbs,
          abs_of_pos h2]
      · have h3 : l < 0 := lt_of_le_of_ne (not_lt.mp h2) h
        have : ((wavePosOf l h : ℕ+) : ℕ) = l.natAbs := rfl
        simp only [waveJ, h, h2, ↓reduceDIte, ↓reduceIte, this, Int.natCast_natAbs,
          abs_of_neg h3, neg_neg]

end KAM.Wave

end
