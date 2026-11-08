/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import KAM.Frozen.Defs.IsDiophantine
public import KAM.Frozen.Wave.Defs.CubicGrad
public import KAM.Frozen.Wave.Defs.IsAnalyticTorusEmbedding
public import KAM.Frozen.Wave.Defs.IsClassicalSolution
public import KAM.Frozen.Wave.Defs.LinearTorus
public import KAM.Frozen.Wave.Defs.ReconV
public import KAM.Wave.Assembly.ShellFamily
public import KAM.Wave.Assembly.Clauses
public import KAM.Wave.Recon2.Main
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W8: the proof of W-NLW2 (blueprint `bpW:w8:nlw2-proof`)

Blueprint label `bpW:w8:nlw2-proof` (milestone W8, the root).

**`KAM.Wave.nlw2_proof`** proves the frozen statement of `KAM.Wave.nlw2`
(`KAM/Frozen/Wave/Theorems/Nlw2.lean`, Theorem `bpW:wh:nlw2`) verbatim, under a distinct name;
this module imports only frozen definitions, never the frozen theorem anchor or a provider.

Witnesses (Definitions `bpW:w8:const`, `bpW:w8:patch`, in the frozen order): `r₀ = √(2t₀)`
(`w8R0`), `C = max(1, M_m) C₃` (from W2's `reconWave_clause5`, `C₃ = 4√c_A`), `τ = 24`,
`η(r) = 2^{33/64} E₇ r^{1/32}` (`w8Eta`), `Γ = ⋃ Γ_n`, `ν`, `K` the patched family of the shell
iterations run on W5's initial perturbation (`w8GammaW`, `w8NuW`, `w8KW w8AA` at `w8HF hm`).

Steps: `stepW:w8:p-pos`, `p-etapos`, `p-etalim` (here); `p-meas`, `p-incl`, `p-nucont`
(`w8_patchCont`); `p-Kcont` (`w8_patchContK`); `p-dens` (`w8_density`); `p-dioph` (`w8_dioph`);
`p-lim` (`w8_freqLimit`); `p-emb` (`w8_patchEmb`); `p-close`, `p-size` (`w8_patchClose`,
`w8_patchSize`, from `w8_shellClose` and `w8_tn_le_two_sum`); `p-inv` (`w8_patchInv`); `p-pde`
(`reconWave_clause5`); `p-inj` (`w8_injective`).
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace KAM.Wave

variable {m : ℝ} (hm : 0 < m)

local notation "𝔱" => w8T0W m hm

/-- (`bpW:w8:nlw2-proof`, Step `stepW:w8:p-close`, Lemma `bpW:w7:shell-geom` (iii)) For
`I ∈ R_n` with positive coordinates, `t_n = 2t_{n+1} ≤ 2 max_i I_i ≤ 2(I₀ + I₁)`. -/
theorem w8_tn_le_two_sum {n : ℕ} {I : Fin 2 → ℝ} (hI : I ∈ w8Rn 𝔱 n) (hpos : ∀ i, 0 < I i) :
    w8tn 𝔱 n ≤ 2 * (I 0 + I 1) := by
  have h := shellSet_norm_ge hI
  rw [shellT_succ] at h
  have hn : ‖I‖ ≤ I 0 + I 1 := by
    refine (pi_norm_le_iff_of_nonneg (by linarith [hpos 0, hpos 1])).2 fun i => ?_
    rw [Real.norm_eq_abs, abs_of_pos (hpos i)]
    fin_cases i <;> simp <;> linarith [hpos 0, hpos 1]
  have : w8tn 𝔱 n = shellT (1 / 2) 𝔱 n := rfl
  linarith

/-- Step `stepW:w8:p-close`, arithmetic: `0 < t ≤ 2r²` gives `E t^{33/64} ≤ η(r) r`,
`η(r) = 2^{33/64} E r^{1/32}`. -/
theorem w8_close_arith {E t s : ℝ} (hE : 0 ≤ E) (ht : 0 < t) (hs : 0 < s) (hts : t ≤ 2 * s) :
    E * t ^ (33 / 64 : ℝ) ≤
      (2 : ℝ) ^ (33 / 64 : ℝ) * E * Real.sqrt s ^ (1 / 32 : ℝ) * Real.sqrt s := by
  have hr := Real.sqrt_pos.2 hs
  have h1 : t ^ (33 / 64 : ℝ) ≤ (2 * s) ^ (33 / 64 : ℝ) :=
    Real.rpow_le_rpow ht.le hts (by norm_num)
  have h2 : (2 * s) ^ (33 / 64 : ℝ) =
      (2 : ℝ) ^ (33 / 64 : ℝ) * (Real.sqrt s ^ (1 / 32 : ℝ) * Real.sqrt s) := by
    rw [Real.mul_rpow (by norm_num) hs.le]
    congr 1
    have e : s = Real.sqrt s ^ (2 : ℝ) := by
      rw [Real.rpow_two, Real.sq_sqrt hs.le]
    conv_lhs => rw [e]
    rw [← Real.rpow_mul hr.le]
    conv_rhs => rw [show Real.sqrt s ^ (1 / 32 : ℝ) * Real.sqrt s =
      Real.sqrt s ^ (1 / 32 : ℝ) * Real.sqrt s ^ (1 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hr]
    norm_num
  calc E * t ^ (33 / 64 : ℝ) ≤ E * (2 * s) ^ (33 / 64 : ℝ) := mul_le_mul_of_nonneg_left h1 hE
    _ = _ := by rw [h2]; ring

/-- Step `stepW:w8:p-size`, arithmetic: `ρ_n = √(c_A(t_n + r_n²))` with `r_n² ≤ t_n ≤ 2s` gives
`2ρ_n ≤ C₃ √s`, `C₃ = 4√c_A`. -/
theorem w8_size_arith {t r2 s : ℝ} (hr : r2 ≤ t) (hts : t ≤ 2 * s) :
    2 * Real.sqrt (w8cA * (t + r2)) ≤ w8C3 * Real.sqrt s := by
  have hcA : (0 : ℝ) ≤ w8cA := by unfold w8cA; norm_num
  have h1 : Real.sqrt (w8cA * (t + r2)) ≤ Real.sqrt (4 * w8cA * s) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have h2 : Real.sqrt (4 * w8cA * s) = 2 * Real.sqrt w8cA * Real.sqrt s := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  unfold w8C3
  rw [h2] at h1
  linarith

/-- Steps `stepW:w8:p-close`, `stepW:w8:p-size` (Lemma `bpW:w8:shell-close`): for `I ∈ Γ`,
`‖K_I(θ) - linearTorus I θ‖ ≤ η(r(I)) r(I)` and `‖K_I(θ)‖ ≤ C₃ r(I)`. -/
theorem w8_patchClose (I : Fin 2 → ℝ) (hI : ∀ i, 0 < I i) (hIΓ : I ∈ w8GammaW (w8HF hm))
    (θ : Fin 2 → ℝ) :
    ‖w8KW w8AA (w8HF hm) I θ - linearTorus I hI θ‖ ≤
        w8Eta m hm (w8Upstream m hm) (Real.sqrt (I 0 + I 1)) * Real.sqrt (I 0 + I 1) ∧
      ‖w8KW w8AA (w8HF hm) I θ‖ ≤ w8C3 * Real.sqrt (I 0 + I 1) := by
  obtain ⟨n, hn⟩ := mem_iUnion.1 hIΓ
  rw [(w8_patch_of_mem hm hn).1]
  obtain ⟨hc, hs⟩ := w8_shellClose hm n hn hI θ
  have hR : I ∈ w8Rn 𝔱 n := w8Pi_subset_Rn n (w8ShellGamma_subset_Pi (w8HW hm n) hn)
  have hts := w8_tn_le_two_sum hm hR hI
  obtain ⟨-, -, hr2, -, hαt, -, ht, -, -⟩ := w8_shell_consts hm n
  have hsum : 0 < I 0 + I 1 := by linarith [hI 0, hI 1]
  have hE7 : 0 ≤ w8E7 m hm (w8Upstream m hm) := by
    have := w8E5_pos hm (w8Upstream m hm)
    have h6 : 0 ≤ w8E6 m := by
      unfold w8E6
      exact mul_nonneg (mul_nonneg (by positivity) (w8CF_pos hm).le)
        (Real.rpow_nonneg (by unfold w8cA; norm_num) _)
    unfold w8E7; linarith
  refine ⟨hc.trans (w8_close_arith hE7 ht hsum hts), hs.trans ?_⟩
  exact w8_size_arith (by linarith) hts

/-- **Proof of W-NLW2** (blueprint `bpW:w8:nlw2-proof`): the frozen statement of
`KAM.Wave.nlw2` (Theorem `bpW:wh:nlw2`), verbatim. -/
theorem nlw2_proof {m : ℝ} (hm : 0 < m) :
    ∃ (r₀ C τ : ℝ) (η : ℝ → ℝ) (Γ : Set (Fin 2 → ℝ)) (ν : (Fin 2 → ℝ) → Fin 2 → ℝ)
      (K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → WaveSpace),
      0 < r₀ ∧ 0 < C ∧ 1 < τ ∧
      (∀ r ∈ Set.Ioo 0 r₀, 0 ≤ η r) ∧ Tendsto η (𝓝[>] 0) (𝓝 0) ∧
      MeasurableSet Γ ∧ Γ ⊆ {I | (∀ i, 0 < I i) ∧ Real.sqrt (I 0 + I 1) < r₀} ∧
      ContinuousOn ν Γ ∧ ContinuousOn (Function.uncurry K) (Γ ×ˢ Set.univ) ∧
      -- (1) density one in actions
      Tendsto (fun h : ℝ => volume (Γ ∩ Metric.ball 0 h) /
          volume ({I : Fin 2 → ℝ | ∀ i, 0 < I i} ∩ Metric.ball 0 h)) (𝓝[>] 0) (𝓝 1) ∧
      -- (2) two independent frequencies
      (∀ I ∈ Γ, ∃ γ : ℝ, 0 < γ ∧ KAM.IsDiophantine γ τ (ν I)) ∧
      Tendsto ν (𝓝[Γ] 0) (𝓝 fun i => lam m hm (i : ℕ).succPNat / (2 * Real.pi)) ∧
      -- (3) small embedded tori
      (∀ (I : Fin 2 → ℝ) (hI : ∀ i, 0 < I i), I ∈ Γ → IsAnalyticTorusEmbedding (K I) ∧
        (∀ θ, ‖K I θ - linearTorus I hI θ‖ ≤
          η (Real.sqrt (I 0 + I 1)) * Real.sqrt (I 0 + I 1)) ∧
        ∀ θ, ‖K I θ‖ ≤ C * Real.sqrt (I 0 + I 1)) ∧
      -- (4) exact invariance
      (∀ I ∈ Γ, ∀ θ : Fin 2 → ℝ, ∀ j : ℕ+,
        HasDerivAt (fun t : ℝ => coeff (K I (θ + t • ν I)).1 j)
          (lam m hm j * coeff (K I θ).2 j) 0 ∧
        HasDerivAt (fun t : ℝ => coeff (K I (θ + t • ν I)).2 j)
          (-(lam m hm j * coeff (K I θ).1 j) - cubicGrad m hm (K I θ).1 j) 0) ∧
      -- (5) PDE solutions
      (∀ I ∈ Γ, ∀ θ₀ : Fin 2 → ℝ,
        (∀ z ∈ Set.univ ×ˢ Set.Icc 0 Real.pi,
          AnalyticAt ℝ (fun z : ℝ × ℝ => reconU m hm (K I (θ₀ + z.1 • ν I)).1 z.2) z) ∧
        IsClassicalSolution m hm (fun t x => reconU m hm (K I (θ₀ + t • ν I)).1 x) ∧
        (∀ t : ℝ, ∀ x ∈ Set.Icc 0 Real.pi,
          HasDerivAt (fun s => reconU m hm (K I (θ₀ + s • ν I)).1 x)
            (reconV m hm (K I (θ₀ + t • ν I)).2 x) t) ∧
        ∀ t : ℝ, ∀ x ∈ Set.Icc 0 Real.pi,
          |reconU m hm (K I (θ₀ + t • ν I)).1 x| +
            |derivWithin (reconU m hm (K I (θ₀ + t • ν I)).1) (Set.Icc 0 Real.pi) x| +
            |reconV m hm (K I (θ₀ + t • ν I)).2 x| ≤ C * Real.sqrt (I 0 + I 1)) ∧
      -- (6) family injectivity
      ∀ I ∈ Γ, ∀ I' ∈ Γ, ∀ θ θ' : Fin 2 → ℝ, K I θ = K I' θ' →
        I = I' ∧ ∃ k : Fin 2 → ℤ, θ - θ' = fun i => (k i : ℝ) := by
  set u := w8Upstream m hm
  have hC3 : 0 < w8C3 := by unfold w8C3 w8cA; positivity
  obtain ⟨hmeas, hsub, hνc⟩ := w8_patchCont (w8HF hm)
  have hbd : ∀ I ∈ w8GammaW (w8HF hm), ∀ θ : Fin 2 → ℝ,
      ‖w8KW w8AA (w8HF hm) I θ‖ ≤ w8C3 * Real.sqrt (I 0 + I 1) := fun I hI θ =>
    (w8_patchClose hm I (hsub hI).1 hI θ).2
  obtain ⟨C, -, hCpos, -, hCbd, hpde⟩ :=
    reconWave_clause5 hm hC3 (w8_patchEmb hm) hbd (w8_patchInv hm)
  have hE7 : 0 ≤ w8E7 m hm u := by
    have := w8E5_pos hm u
    have h6 : 0 ≤ w8E6 m := by
      unfold w8E6
      exact mul_nonneg (mul_nonneg (by positivity) (w8CF_pos hm).le)
        (Real.rpow_nonneg (by unfold w8cA; norm_num) _)
    unfold w8E7; linarith
  refine ⟨w8R0 m hm u, C, w8Tau, w8Eta m hm u, w8GammaW (w8HF hm), w8NuW (w8HF hm),
    w8KW w8AA (w8HF hm), ?_, hCpos, ?_, ?_, ?_, hmeas, hsub, hνc, w8_patchContK hm,
    w8_density (w8HF hm), w8_dioph (w8HF hm), w8_freqLimit (w8HF hm), ?_, w8_patchInv hm, hpde,
    w8_injective hm⟩
  · -- Step `stepW:w8:p-pos`
    have := w8T0_pos hm u
    exact Real.sqrt_pos.2 (by positivity)
  · unfold w8Tau; norm_num
  · -- Step `stepW:w8:p-etapos`
    intro r hr
    unfold w8Eta
    exact mul_nonneg (mul_nonneg (by positivity) hE7) (Real.rpow_nonneg hr.1.le _)
  · -- Step `stepW:w8:p-etalim`
    exact w8ext_tendsto_const_mul_rpow (by norm_num : (0 : ℝ) < 1 / 32)
      ((2 : ℝ) ^ (33 / 64 : ℝ) * w8E7 m hm u)
  · -- Steps `stepW:w8:p-emb`, `stepW:w8:p-close`, `stepW:w8:p-size`
    intro I hI hIΓ
    refine ⟨w8_patchEmb hm I hIΓ, fun θ => ?_, fun θ => hCbd I hIΓ θ⟩
    exact (w8_patchClose hm I hI hIΓ θ).1

end KAM.Wave

end
