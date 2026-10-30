/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Young's inequality on `ℤ` (blueprint `bpW:w1:young`)

Infrastructure used by several nodes; the dependency graph is still being built.

The convolution `(c * d)_l = ∑' i, c i * d (l - i)` of `ℤ`-indexed sequences, a Cauchy–Schwarz
lemma for `tsum`s, the `ℓ² * ℓ¹ ⊆ ℓ²` bound (part (i)) and the algebraic rules of part (iii).

* `KAM.Wave.waveConv` : the convolution (a `tsum`; callers prove summability first);
* `KAM.Wave.wave_tsum_mul_sq_le` : Cauchy–Schwarz for nonnegative square-summable families;
* `KAM.Wave.wave_young` : `‖X * Y‖_{ℓ²} ≤ ‖X‖_{ℓ²} ‖Y‖_{ℓ¹}` (blueprint `bpW:w1:young` (i));
* `KAM.Wave.wave_l2_add` : the `ℓ²` triangle inequality for nonnegative sequences.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- Cauchy–Schwarz for nonnegative square-summable families (used in blueprint `bpW:w1:young`). -/
theorem wave_tsum_mul_sq_le {ι : Type*} {u v : ι → ℝ} (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hu2 : Summable fun i => u i ^ 2) (hv2 : Summable fun i => v i ^ 2) :
    Summable (fun i => u i * v i) ∧ (∑' i, u i * v i) ^ 2 ≤ (∑' i, u i ^ 2) * ∑' i, v i ^ 2 := by
  have hpq : (2:ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hu2' : Summable fun i => u i ^ (2:ℝ) := by simpa [Real.rpow_two] using hu2
  have hv2' : Summable fun i => v i ^ (2:ℝ) := by simpa [Real.rpow_two] using hv2
  obtain ⟨hs, h⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hu hv hu2' hv2'
  refine ⟨hs, ?_⟩
  have h0 : 0 ≤ ∑' i, u i * v i := tsum_nonneg fun i => mul_nonneg (hu i) (hv i)
  simp only [Real.rpow_two] at h
  have hA : 0 ≤ ∑' i, u i ^ 2 := tsum_nonneg fun i => sq_nonneg _
  have hB : 0 ≤ ∑' i, v i ^ 2 := tsum_nonneg fun i => sq_nonneg _
  have h' : ∑' i, u i * v i ≤ √(∑' i, u i ^ 2) * √(∑' i, v i ^ 2) := by
    simpa [Real.sqrt_eq_rpow] using h
  calc _ ≤ (√(∑' i, u i ^ 2) * √(∑' i, v i ^ 2)) ^ 2 := pow_le_pow_left₀ h0 h' 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]

/-- The two-sided convolution `(c * d)_l = ∑_{i ∈ ℤ} c_i d_{l-i}`
(blueprint `bpW:w1:twosided-transport`);
a `tsum`, guarded by the summability proved before each use. -/
def waveConv {R : Type*} [NonUnitalNonAssocSemiring R] [TopologicalSpace R] (c d : ℤ → R)
    (l : ℤ) : R :=
  ∑' i, c i * d (l - i)

/-- Young for nonnegative real sequences: `ℓ² * ℓ¹ ⊆ ℓ²` (blueprint `bpW:w1:young` (i)). -/
theorem wave_young_real {X Y : ℤ → ℝ} (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i)
    (hX2 : Summable fun i => X i ^ 2) (hY1 : Summable Y) :
    (∀ l, Summable fun i => X i * Y (l - i)) ∧
    Summable (fun l => waveConv X Y l ^ 2) ∧
    ∑' l, waveConv X Y l ^ 2 ≤ (∑' i, Y i) ^ 2 * ∑' i, X i ^ 2 := by
  have hYl : ∀ l, Summable fun i => Y (l - i) := fun l =>
    hY1.comp_injective (sub_right_injective : Function.Injective fun i : ℤ => l - i)
  have hYs : ∀ l, ∑' i, Y (l - i) = ∑' i, Y i := fun l =>
    (Equiv.subLeft l).tsum_eq Y
  have hXb : ∀ i, X i ^ 2 ≤ ∑' j, X j ^ 2 := fun i =>
    hX2.le_tsum i (fun j _ => sq_nonneg _)
  have hA : ∀ l, Summable fun i => X i ^ 2 * Y (l - i) := fun l =>
    Summable.of_nonneg_of_le (fun i => mul_nonneg (sq_nonneg _) (hY _))
      (fun i => mul_le_mul_of_nonneg_right (hXb i) (hY _)) ((hYl l).mul_left _)
  have cs : ∀ l, Summable (fun i => X i * Y (l - i)) ∧
      waveConv X Y l ^ 2 ≤ (∑' i, X i ^ 2 * Y (l - i)) * ∑' i, Y i := by
    intro l
    have h := wave_tsum_mul_sq_le (u := fun i => X i * √(Y (l - i))) (v := fun i => √(Y (l - i)))
      (fun i => mul_nonneg (hX i) (Real.sqrt_nonneg _)) (fun i => Real.sqrt_nonneg _)
      (by simpa [mul_pow, Real.sq_sqrt (hY _)] using hA l)
      (by simpa [Real.sq_sqrt (hY _)] using hYl l)
    have e1 : ∀ i, X i * √(Y (l - i)) * √(Y (l - i)) = X i * Y (l - i) := fun i => by
      rw [mul_assoc, Real.mul_self_sqrt (hY _)]
    simp only [e1] at h
    refine ⟨h.1, ?_⟩
    simpa [mul_pow, Real.sq_sqrt (hY _), hYs l, waveConv] using h.2
  -- double series
  have hF : Summable (Function.uncurry fun l i : ℤ => X i ^ 2 * Y (l - i)) := by
    have : Summable (fun p : ℤ × ℤ => X p.1 ^ 2 * Y p.2) :=
      summable_mul_of_summable_norm (f := fun i => X i ^ 2) (g := Y)
        (by simpa [Real.norm_eq_abs, abs_of_nonneg, sq_nonneg] using hX2)
        (by simpa [Real.norm_eq_abs, abs_of_nonneg, hY] using hY1)
    let e : ℤ × ℤ ≃ ℤ × ℤ :=
      { toFun := fun p => (p.1 + p.2, p.1), invFun := fun q => (q.2, q.1 - q.2)
        left_inv := fun p => by simp, right_inv := fun q => by simp }
    refine (e.summable_iff (f := Function.uncurry fun l i : ℤ => X i ^ 2 * Y (l - i))).mp ?_
    simpa [Function.comp_def, e] using this
  have hsumA : Summable fun l => ∑' i, X i ^ 2 * Y (l - i) := hF.prod
  have hcomm : ∑' l, ∑' i, X i ^ 2 * Y (l - i) = (∑' i, X i ^ 2) * ∑' i, Y i := by
    rw [← hF.tsum_comm, ← tsum_mul_right]
    refine tsum_congr fun i => ?_
    rw [tsum_mul_left]
    congr 1
    exact (Equiv.subRight i).tsum_eq Y
  have hle : ∀ l, waveConv X Y l ^ 2 ≤ (∑' i, X i ^ 2 * Y (l - i)) * ∑' i, Y i :=
    fun l => (cs l).2
  have hsum : Summable (fun l => waveConv X Y l ^ 2) :=
    Summable.of_nonneg_of_le (fun l => sq_nonneg _) hle (hsumA.mul_right _)
  refine ⟨fun l => (cs l).1, hsum, ?_⟩
  calc ∑' l, waveConv X Y l ^ 2 ≤ ∑' l, (∑' i, X i ^ 2 * Y (l - i)) * ∑' i, Y i :=
        hsum.tsum_le_tsum hle (hsumA.mul_right _)
    _ = _ := by rw [tsum_mul_right, hcomm]; ring

/-- Young for complex sequences (blueprint `bpW:w1:young` (i)): for `X ∈ ℓ²(ℤ)`, `Y ∈ ℓ¹(ℤ)` each
sum `∑ᵢ |Xᵢ||Y_{l-i}|` converges and `‖X * Y‖²_{ℓ²} ≤ ‖Y‖²_{ℓ¹} ‖X‖²_{ℓ²}`. -/
theorem wave_young {X Y : ℤ → ℂ} (hX : Summable fun i => ‖X i‖ ^ 2)
    (hY : Summable fun i => ‖Y i‖) :
    (∀ l, Summable fun i => ‖X i‖ * ‖Y (l - i)‖) ∧
    Summable (fun l => ‖waveConv X Y l‖ ^ 2) ∧
    ∑' l, ‖waveConv X Y l‖ ^ 2 ≤ (∑' i, ‖Y i‖) ^ 2 * ∑' i, ‖X i‖ ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := wave_young_real (X := fun i => ‖X i‖) (Y := fun i => ‖Y i‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hX hY
  have hle : ∀ l, ‖waveConv X Y l‖ ^ 2 ≤ waveConv (fun i => ‖X i‖) (fun i => ‖Y i‖) l ^ 2 :=
    fun l => by
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      have := norm_tsum_le_tsum_norm (f := fun i => X i * Y (l - i))
        (by simpa [norm_mul] using h1 l)
      simpa [waveConv, norm_mul] using this
  have hs : Summable (fun l => ‖waveConv X Y l‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun l => sq_nonneg _) hle h2
  exact ⟨h1, hs, (hs.tsum_le_tsum hle h2).trans h3⟩

/-- Young, norm form: `‖X * Y‖_{ℓ²} ≤ ‖X‖_{ℓ²} ‖Y‖_{ℓ¹}`. -/
theorem wave_young_sqrt_le {X Y : ℤ → ℂ} (hX : Summable fun i => ‖X i‖ ^ 2)
    (hY : Summable fun i => ‖Y i‖) :
    √(∑' l, ‖waveConv X Y l‖ ^ 2) ≤ √(∑' i, ‖X i‖ ^ 2) * ∑' i, ‖Y i‖ := by
  have h := (wave_young hX hY).2.2
  have hY0 : 0 ≤ ∑' i, ‖Y i‖ := tsum_nonneg fun _ => norm_nonneg _
  calc √(∑' l, ‖waveConv X Y l‖ ^ 2) ≤ √((∑' i, ‖Y i‖) ^ 2 * ∑' i, ‖X i‖ ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hY0, mul_comm]

/-- The `ℓ²` triangle inequality for nonnegative sequences on `ℤ`. -/
theorem wave_l2_add {f g : ℤ → ℝ} (hf0 : ∀ i, 0 ≤ f i) (hg0 : ∀ i, 0 ≤ g i)
    (hf : Summable fun i => f i ^ 2) (hg : Summable fun i => g i ^ 2) :
    Summable (fun i => (f i + g i) ^ 2) ∧
    √(∑' i, (f i + g i) ^ 2) ≤ √(∑' i, f i ^ 2) + √(∑' i, g i ^ 2) := by
  obtain ⟨hfg, hcs⟩ := wave_tsum_mul_sq_le hf0 hg0 hf hg
  have hs : Summable (fun i => (f i + g i) ^ 2) := by
    have : Summable fun i => f i ^ 2 + 2 * (f i * g i) + g i ^ 2 :=
      (hf.add (hfg.mul_left 2)).add hg
    simpa [add_sq, mul_assoc] using this
  refine ⟨hs, ?_⟩
  have hA : 0 ≤ ∑' i, f i ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  have hB : 0 ≤ ∑' i, g i ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  have e : ∑' i, (f i + g i) ^ 2 =
      ∑' i, f i ^ 2 + 2 * ∑' i, f i * g i + ∑' i, g i ^ 2 := by
    have h1 : ∀ i, (f i + g i) ^ 2 = f i ^ 2 + 2 * (f i * g i) + g i ^ 2 := fun i => by ring
    simp only [h1]
    rw [(hf.add (hfg.mul_left 2)).tsum_add hg, hf.tsum_add (hfg.mul_left 2), tsum_mul_left]
  have hP : 0 ≤ ∑' i, f i * g i := tsum_nonneg fun i => mul_nonneg (hf0 i) (hg0 i)
  have hP' : ∑' i, f i * g i ≤ √(∑' i, f i ^ 2) * √(∑' i, g i ^ 2) := by
    rw [← Real.sqrt_mul hA]
    exact Real.le_sqrt_of_sq_le hcs
  rw [e]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have := Real.sq_sqrt hA
  have := Real.sq_sqrt hB
  nlinarith

/-- Commutativity of the convolution (blueprint `bpW:w1:young` (iii)): the substitution
`i ↦ l - i`. -/
theorem waveConv_comm {R : Type*} [CommSemiring R] [TopologicalSpace R] (c d : ℤ → R) (l : ℤ) :
    waveConv c d l = waveConv d c l := by
  unfold waveConv
  rw [← (Equiv.subLeft l).tsum_eq (fun i => d i * c (l - i))]
  refine tsum_congr fun i => ?_
  simp [mul_comm]

/-- Summability of the convolution terms is symmetric. -/
theorem waveConv_summable_comm {R : Type*} [CommSemiring R] [TopologicalSpace R] {c d : ℤ → R}
    {l : ℤ} (h : Summable fun i => c i * d (l - i)) : Summable fun i => d i * c (l - i) := by
  have := (Equiv.subLeft l).summable_iff.mpr h
  refine this.congr fun i => ?_
  simp [mul_comm]

/-- Monotonicity of the convolution of nonnegative sequences (blueprint `bpW:w1:young` (iii)). -/
theorem waveConv_mono {X X' Y : ℤ → ℝ} (hXX : ∀ i, X i ≤ X' i)
    (hY : ∀ i, 0 ≤ Y i) (l : ℤ) (h1 : Summable fun i => X i * Y (l - i))
    (h2 : Summable fun i => X' i * Y (l - i)) :
    waveConv X Y l ≤ waveConv X' Y l :=
  h1.tsum_le_tsum (fun i => mul_le_mul_of_nonneg_right (hXX i) (hY _)) h2

/-- `|c * d| ≤ |c| * |d|` pointwise (blueprint `bpW:w1:young` (iii)). -/
theorem norm_waveConv_le {c d : ℤ → ℂ} (l : ℤ) (h : Summable fun i => ‖c i‖ * ‖d (l - i)‖) :
    ‖waveConv c d l‖ ≤ waveConv (fun i => ‖c i‖) (fun i => ‖d i‖) l := by
  have := norm_tsum_le_tsum_norm (f := fun i => c i * d (l - i))
    (by simpa [norm_mul] using h)
  simpa [waveConv, norm_mul] using this

/-- Associativity of the convolution on `ℓ¹(ℤ; ℂ)` (blueprint `bpW:w1:young` (iii), Step
`stepW:w1:rules`): the double series converge absolutely and are rearranged (Fubini for series). -/
theorem waveConv_assoc_l1 {c d e : ℤ → ℂ} (hc : Summable fun i => ‖c i‖)
    (hd : Summable fun i => ‖d i‖) (he : Summable fun i => ‖e i‖) (l : ℤ) :
    waveConv (waveConv c d) e l = waveConv c (waveConv d e) l := by
  have hB : ∀ x, ‖e x‖ ≤ ∑' i, ‖e i‖ := fun x => he.le_tsum x (fun j _ => norm_nonneg _)
  have hcd : Summable fun p : ℤ × ℤ => ‖c p.1‖ * ‖d p.2‖ :=
    summable_mul_of_summable_norm (f := fun i => ‖c i‖) (g := fun i => ‖d i‖)
      (by simpa using hc) (by simpa using hd)
  let φ : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.1 + p.2, p.1), invFun := fun q => (q.2, q.1 - q.2)
      left_inv := fun p => by simp, right_inv := fun q => by simp }
  have hH : Summable (Function.uncurry fun i j : ℤ => c j * d (i - j) * e (l - i)) := by
    refine (φ.summable_iff (f := Function.uncurry fun i j : ℤ => c j * d (i - j) * e (l - i))).mp ?_
    refine Summable.of_norm_bounded (hcd.mul_right (∑' i, ‖e i‖)) fun p => ?_
    simp only [Function.comp_apply, Function.uncurry, φ, Equiv.coe_fn_mk, add_sub_cancel_left,
      norm_mul]
    exact mul_le_mul_of_nonneg_left (hB _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hrow : ∀ i : ℤ, Summable fun j => c j * d (i - j) * e (l - i) := fun i => hH.prod_factor i
  have hL : waveConv (waveConv c d) e l = ∑' i, ∑' j, c j * d (i - j) * e (l - i) := by
    refine tsum_congr fun i => ?_
    simp only [waveConv]
    rw [← tsum_mul_right]
  rw [hL, ← hH.tsum_comm]
  simp only [waveConv]
  refine tsum_congr fun j => ?_
  rw [← tsum_mul_left]
  rw [← (Equiv.addLeft j).tsum_eq]
  refine tsum_congr fun k => ?_
  simp only [Equiv.coe_addLeft, add_sub_cancel_left]
  have : l - j - k = l - (j + k) := by ring
  rw [this]; ring

end KAM.Wave

end
