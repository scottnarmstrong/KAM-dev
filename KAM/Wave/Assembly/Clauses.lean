/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Assembly.PatchInst
public import KAM.Wave.Measure.Density
public import KAM.Wave.Measure.ShellEst
public import KAM.Wave.Measure.Dioph
public import KAM.Wave.Measure.Limit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W8: clauses (1) and (2) of W-NLW2 for the patched family (blueprint `bpW:w8:nlw2-proof`,
Steps `stepW:w8:p-dens`, `stepW:w8:p-dioph`, `stepW:w8:p-lim`)

Blueprint label `bpW:w8:nlw2-proof` (milestone W8), the steps that use only
W6–W7 (not W5's action–angle map).

For a family `H : ∀ n, W8ShellPrep m hm n (Ps n) (Xs n)` of prep-step bundles, `Γ = w8GammaW H`,
`ν = w8NuW H`:
* `w8_shell_defect` (Step `stepW:w8:p-dens`, W7 Corollary `bpW:w7:shell-est`): the relative defect
  of shell `n` is `≤ (4/3)(7 + C₇) t_n^{1/94}` (`α_n^{32/47} = t_n^{95/94}`);
* `w8_density` (Step `stepW:w8:p-dens`, W7 Theorem `bpW:w7:density`): clause (1) of `nlw2`;
* `w8_dioph` (Step `stepW:w8:p-dioph`, W7 Lemma `bpW:w7:dioph`): for `I ∈ Γ_n`,
  `KAM.IsDiophantine (α̌_n/(8π)) 24 (ν I)`;
* `w8_freqLimit` (Step `stepW:w8:p-lim`, W7 Lemma `bpW:w7:limit`): `ν → λ_J/(2π)` along
  `𝓝[Γ] 0`.
The remaining steps of `bpW:w8:nlw2-proof` (clauses (3)–(6), continuity of `K`) need the shell
tori `K^{(n)}`, i.e. W5's `bpW:w5:action-angle`.
-/

@[expose] public noncomputable section

open Set Real Filter Topology MeasureTheory
open scoped ENNReal

namespace KAM.Wave

variable {m : ℝ} {hm : 0 < m} {Ps : ℕ → (Fin 2 → ℝ) → KamPhase → ℂ}
  {Xs : ℕ → (Fin 2 → ℝ) → KamPhase → KamPhase}

local notation "𝔱" => w8T0W m hm

/-- `(7 + C₇) α_n^{32/47} / ((1 - q²) t_n) = (4/3)(7 + C₇) t_n^{1/94}` for `q = 1/2`
(W7 Remark `bpW:w7:exponents`: `(95/64)(32/47) = 95/94`). -/
theorem w8_defect_rate_eq (c : ℝ) {t : ℝ} (ht : 0 < t) :
    c * (t ^ (95 / 64 : ℝ)) ^ (32 / 47 : ℝ) / ((1 - (1 / 2 : ℝ) ^ 2) * t) =
      4 / 3 * c * t ^ (1 / 94 : ℝ) := by
  rw [← Real.rpow_mul ht.le, show (95 / 64 : ℝ) * (32 / 47) = 1 / 94 + 1 by norm_num,
    Real.rpow_add ht, Real.rpow_one]
  field_simp
  ring

/-- `t_n → 0` and `t_n^a → 0` for `a > 0`. -/
theorem w8tn_tendsto_rpow (t0 : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => w8tn t0 n ^ a) atTop (𝓝 0) := by
  have h : Tendsto (fun n => w8tn t0 n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).mul_const t0
    rw [zero_mul] at this
    exact this
  have := h.rpow_const (Or.inr ha.le)
  rwa [Real.zero_rpow ha.ne'] at this

/-- **Shell defect** (blueprint `bpW:w8:nlw2-proof`, Step `stepW:w8:p-dens`; W7 Corollary
`bpW:w7:shell-est` for the shell iteration): `Leb(R_n ∖ Γ)/Leb(R_n) ≤ (4/3)(7 + C₇) t_n^{1/94}`. -/
theorem w8_shell_defect (H : ∀ n, W8ShellPrep m hm n (Ps n) (Xs n)) (n : ℕ) :
    volume (shellSet (1 / 2) 𝔱 n \ w8GammaW H) / volume (shellSet (1 / 2) 𝔱 n) ≤
      ENNReal.ofReal (4 / 3 * (7 + measC7 m hm) * w8tn 𝔱 n ^ (1 / 94 : ℝ)) := by
  have hT := w8T0_pos hm (w8Upstream m hm)
  obtain ⟨-, -, hexcl, -⟩ := w8_w6General (H n)
  have hαt := (w8alpha_le hm (w8Upstream m hm) n).2
  have h := shell_defect_le m hm (q := 1 / 2) (by norm_num) (by norm_num) hT n (w8MeasSetup hm n)
    hαt (fun _ hξ => ⟨hξ.1, hξ.2⟩) ((w8Pi_subset_Rn n).trans (w8Rn_subset_box n))
    (w8ShellFamily (H n)) (Γ := w8GammaW H) (fun x ⟨_, hxP, hxE⟩ => by
      by_contra hxΓ
      exact hxE (hexcl ⟨hxP, fun hx => hxΓ (mem_iUnion.2 ⟨n, hx⟩)⟩))
  refine h.trans (le_of_eq ?_)
  congr 1
  exact w8_defect_rate_eq _ (w8tn_pos hT n)

/-- **Clause (1), density one** (blueprint `bpW:w8:nlw2-proof`, Step `stepW:w8:p-dens`): for the
patched set `Γ`, `Leb(Γ ∩ B_h)/Leb(P ∩ B_h) → 1` as `h → 0⁺`. -/
theorem w8_density (H : ∀ n, W8ShellPrep m hm n (Ps n) (Xs n)) :
    Tendsto (fun h : ℝ => volume (w8GammaW H ∩ Metric.ball 0 h) /
      volume ({I : Fin 2 → ℝ | ∀ i, 0 < I i} ∩ Metric.ball 0 h)) (𝓝[>] 0) (𝓝 1) := by
  have hT := w8T0_pos hm (w8Upstream m hm)
  obtain ⟨hmeas, hsub, -⟩ := w8_patchCont H
  refine density_one_of_shells (q := 1 / 2) (by norm_num) (by norm_num) hT hmeas
    (fun I hI => (hsub hI).1) ?_
  have hg : Tendsto (fun n => ENNReal.ofReal (4 / 3 * (7 + measC7 m hm) * w8tn 𝔱 n ^ (1 / 94 : ℝ)))
      atTop (𝓝 0) := by
    have := ((w8tn_tendsto_rpow 𝔱 (by norm_num : (0 : ℝ) < 1 / 94)).const_mul
      (4 / 3 * (7 + measC7 m hm)))
    rw [mul_zero] at this
    have := ENNReal.tendsto_ofReal this
    rwa [ENNReal.ofReal_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg (fun n => bot_le)
    fun n => w8_shell_defect H n

/-- For `I ∈ Γ_n`: `ν(I) = ν^{(n)}_*(I)` and `(2π) ν(I) = ω^{(n)}_*(I)`. -/
theorem w8NuW_of_mem (H : ∀ n, W8ShellPrep m hm n (Ps n) (Xs n)) {n : ℕ} {I : Fin 2 → ℝ}
    (hI : I ∈ w8Gammas H n) :
    w8NuW H I = w8ShellNu (H n) I ∧ (2 * π) • w8NuW H I = w8ShellOmega (H n) I := by
  have h : w8NuW H I = w8ShellNu (H n) I :=
    w8PatchNu_of_mem (w8Gammas_subset H) (w8T0_pos hm _) (w8Nus H) hI
  exact ⟨h, by rw [h, w8ShellNu_smul]⟩

/-- **Clause (2), Diophantine** (blueprint `bpW:w8:nlw2-proof`, Step `stepW:w8:p-dioph`): for
`I ∈ Γ_n`, `ν(I)` is Diophantine with `γ_I = α̌_n/(8π)` and `τ = 24`. -/
theorem w8_dioph (H : ∀ n, W8ShellPrep m hm n (Ps n) (Xs n)) :
    ∀ I ∈ w8GammaW H, ∃ γ : ℝ, 0 < γ ∧ KAM.IsDiophantine γ w8Tau (w8NuW H I) := by
  intro I hI
  obtain ⟨n, hn⟩ := mem_iUnion.1 hI
  have hT := w8T0_pos hm (w8Upstream m hm)
  have hc : 0 < alphaCheck (w8alpha 𝔱 n) / 2 :=
    half_pos (Real.rpow_pos_of_pos (w8alpha_pos hT n) _)
  have hlow := (w8_freqShell (H n)).2.2.1.2.2 I hn
  have hD := isDiophantine_of_lower_bound hc (ω := w8ShellOmega (H n) I) fun k hk => by
    have := hlow k hk
    rwa [← div_div] at this
  refine ⟨alphaCheck (w8alpha 𝔱 n) / 2 / (4 * π), by positivity, ?_⟩
  have e : w8NuW H I = fun i => w8ShellOmega (H n) I i / (2 * π) := by
    rw [(w8NuW_of_mem H hn).1]
    funext i
    simp only [w8ShellNu, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  exact hD

/-- **Clause (2), frequency limit** (blueprint `bpW:w8:nlw2-proof`, Step `stepW:w8:p-lim`):
`ν(I) → λ_J/(2π)` as `I → 0` in `Γ`. -/
theorem w8_freqLimit (H : ∀ n, W8ShellPrep m hm n (Ps n) (Xs n)) :
    Tendsto (w8NuW H) (𝓝[w8GammaW H] 0)
      (𝓝 fun i => lam m hm (i : ℕ).succPNat / (2 * π)) := by
  have hT := w8T0_pos hm (w8Upstream m hm)
  have hR : ∀ n, w8Gammas H n ⊆ w8Rn 𝔱 n := fun n => (w8Gammas_subset H n).trans (w8Pi_subset_Rn n)
  have hlim := tendsto_frequency_limit m hm (q := 1 / 2) (by norm_num) (by norm_num) hT
    (Γ := w8GammaW H) (fun I hI => by
      obtain ⟨n, hn⟩ := mem_iUnion.1 hI
      exact ⟨n, hR n hn⟩)
    (fun I => (2 * π) • w8NuW H I) (fun k => w8alpha 𝔱 k) (fun k I hI hIk => by
      obtain ⟨n, hn⟩ := mem_iUnion.1 hI
      have hnk : n = k := by
        by_contra hne
        exact Set.disjoint_left.1 (w8Rn_disjoint hT hne) (hR n hn) hIk
      subst hnk
      rw [(w8NuW_of_mem H hn).2]
      obtain ⟨h1, h2, -⟩ := (w8_freqShell (H n)).2.2.1
      refine (h1 I hn).trans (h2.trans ?_)
      exact (w8_etor hm n).2.2.2.2)
    (w8tn_tendsto_rpow 𝔱 (by norm_num : (0 : ℝ) < 95 / 64))
  have e : (fun I : Fin 2 → ℝ => fun i => ((2 * π) • w8NuW H I) i / (2 * π)) = w8NuW H := by
    funext I i
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  rwa [e] at hlim

end KAM.Wave

end
