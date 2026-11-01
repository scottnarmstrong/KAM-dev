/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.ComposeMaps
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: the Cauchy estimate for the compositions on the torus (blueprint `bpW:w6:convergence` (iii))

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:convergence` (steps `c-cauchy`, `c-lim`).

* `kamNorm_sub_le_of_segment`: the mean value inequality along a segment, with the norm
  `|·|_{r_0}` on the values and an arbitrary bound on the directional derivatives;
* `w6PsiC_cauchy`: `|Ψ^{ν+1}(w) - Ψ^ν(w)|_{p_+,r_0} ≤ 2 M_{F,ν}` on `D_{ν+1}` (the blueprint's
  `|Φ^{ν+1}(w) - Φ^ν(w)|_{p_+,r_0} ≤ 2·2M_{F,ν}`, with `|Ψ_{ν+1}|_{r_ν} ≤ M_{F,ν}`);
* `w6TorusPt θ = ι(θ) = (θ, 0, 0, 0)`; `w6PiStarS = Π_* = ⋂_ν Π_ν`;
* `w6PsiStar`, `w6PhiStar = ι + ι ∘ Ψ_*`: the limit on the torus;
* `w6PsiC_tail`: `|Ψ_* - Ψ^n|_{r_0} ≤ e_Φ 8^{-n}` on `T_{s_∞} × Π_*`.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Wave

open KAM

/-- **Mean value inequality on a segment** (step `c-cauchy`): if `g` is differentiable along the
segment `[w, z]` and `|Dg(x)(z - w)|_{r_0} ≤ C` there, then `|g z - g w|_{r_0} ≤ C`. -/
theorem kamNorm_sub_le_of_segment {r0 C : ℝ} (hr0 : 0 < r0) {g : KamPhase → KamPhase}
    {w z : KamPhase}
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℂ g (w + t • (z - w)))
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, kamNorm r0 (fderiv ℂ g (w + t • (z - w)) (z - w)) ≤ C) :
    kamNorm r0 (g z - g w) ≤ C := by
  have : Fact (0 < r0) := ⟨hr0⟩
  let f : ℝ → StepPhase r0 := fun t => StepPhase.ofK (g (w + t • (z - w)))
  have hpath : ∀ t : ℝ, HasDerivAt (fun t : ℝ => w + t • (z - w)) (z - w) t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const (z - w)).const_add w
  have hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f
      (StepPhase.ofK (fderiv ℂ g (w + t • (z - w)) (z - w))) (Icc 0 1) t := by
    intro t ht
    have h1 := ((stepOfKCLM r0).hasFDerivAt.comp _ (hg t ht).hasFDerivAt).restrictScalars ℝ
    exact (h1.comp_hasDerivAt t (hpath t)).hasDerivWithinAt
  have key := norm_image_sub_le_of_norm_deriv_le_segment' hf
    (fun t ht => hb t (Ico_subset_Icc_self ht)) 1 ⟨zero_le_one, le_rfl⟩
  have e1 : f 1 = StepPhase.ofK (g z) := by simp [f]
  have e0 : f 0 = StepPhase.ofK (g w) := by simp [f]
  rw [e1, e0, sub_zero, mul_one] at key
  exact key

section cauchy

variable {d : W6SeqData} {S0 : W6State}

/-- **Cauchy step** (step `c-cauchy`): for `ξ ∈ Π_μ` (`μ ≤ ν`) and `w ∈ D_{ν+1}`,
`|Ψ^{ν+1}(w) - Ψ^ν(w)|_{r_0} ≤ 2 M_{F,ν}`. -/
theorem w6PsiC_cauchy (hI : W6IterHyp d S0) {ν : ℕ} {ξ : Fin 2 → ℝ}
    (hξ : ∀ μ < ν + 1, ξ ∈ (w6Seq d S0 μ).Pi) {w : KamPhase} (hw : w ∈ d.domNu (ν + 1)) :
    kamNorm (d.rNu 0) (w6PsiC d S0 (ν + 1) ξ w - w6PsiC d S0 ν ξ w) ≤
      2 * stepMF w6CF w6T (d.alpha ν) (d.sigma ν) (d.eps ν) := by
  have hd := hI.std
  have hr0 := W6SeqData.w6r_pos hd.1 0
  have hrν := W6SeqData.w6r_pos hd.1 ν
  have h0ν := W6SeqData.rNu_le_r0 hd ν
  have hξν : ξ ∈ (w6Seq d S0 ν).Pi := hξ ν (Nat.lt_succ_self ν)
  have hξ' : ∀ μ < ν, ξ ∈ (w6Seq d S0 μ).Pi := fun μ hμ => hξ μ (Nat.lt_succ_of_lt hμ)
  obtain ⟨-, -, -, hall⟩ := w6StepK_smooth hd (hI.stage ν) hξν
  obtain ⟨-, hz, eK, hPsiK, -, -⟩ := hall w hw
  have hwν : w ∈ d.domNu ν := W6SeqData.domNu_succ_subset hd ν hw
  set z := w6PhiK d S0 ν ξ w
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, w + t • (z - w) ∈ d.domNu ν := fun t ht =>
    (kamDomain_convex _ _).add_smul_sub_mem hwν hz ht
  have hc := w6Cp_le_two ν
  have hmvt : kamNorm (d.rNu 0) (w6PsiC d S0 ν ξ z - w6PsiC d S0 ν ξ w) ≤
      stepMF w6CF w6T (d.alpha ν) (d.sigma ν) (d.eps ν) := by
    refine kamNorm_sub_le_of_segment hr0
      (fun t ht => (w6Compose_main hI ν ξ hξ' _ (hseg t ht)).2.2.2.1) fun t ht => ?_
    have h6 := (w6Compose_main hI ν ξ hξ' _ (hseg t ht)).2.2.2.2.2 (z - w)
    have ezw : z - w = w6Iota (w6PsiK d S0 ν ξ w) := by rw [eK]; abel
    have h1 : kamNorm (d.rNu ν) (z - w) ≤ stepMF w6CF w6T (d.alpha ν) (d.sigma ν) (d.eps ν) := by
      rw [ezw]; exact (kamNorm_w6Iota_le hrν _).trans hPsiK
    have h2 : 0 ≤ kamNorm (d.rNu ν) (z - w) := kamNorm_nonneg hrν.le _
    have h3 := one_le_w6Cp ν
    nlinarith
  have e : w6PsiC d S0 (ν + 1) ξ w - w6PsiC d S0 ν ξ w =
      w6PsiK d S0 ν ξ w + (w6PsiC d S0 ν ξ z - w6PsiC d S0 ν ξ w) := by
    show w6PsiK d S0 ν ξ w + w6PsiC d S0 ν ξ z - w6PsiC d S0 ν ξ w = _
    abel
  rw [e]
  have h4 := kamNorm_add_le hr0 (w6PsiK d S0 ν ξ w) (w6PsiC d S0 ν ξ z - w6PsiC d S0 ν ξ w)
  have h5 : kamNorm (d.rNu 0) (w6PsiK d S0 ν ξ w) ≤ kamNorm (d.rNu ν) (w6PsiK d S0 ν ξ w) :=
    kamNorm_anti hrν h0ν _
  linarith

/-- `ι(θ) = (θ, 0, 0, 0)`: the torus `{y = 0, z = z̄ = 0}`. -/
def w6TorusPt (θ : Fin 2 → ℂ) : KamPhase := (θ, 0, 0, 0)

/-- `Π_* = ⋂_ν Π_ν` for the iteration started at `S₀`. -/
def w6PiStarS (d : W6SeqData) (S0 : W6State) : Set (Fin 2 → ℝ) := ⋂ ν, (w6Seq d S0 ν).Pi

theorem w6TorusPt_mem {θ : Fin 2 → ℂ} (hd : W6State.Std d) (hθ : θ ∈ complexStrip 2 d.sInfty)
    (ν : ℕ) : w6TorusPt θ ∈ d.domNu ν := by
  have hr := W6SeqData.w6r_pos hd.1 ν
  refine ⟨fun i => (hθ i).trans_le (W6SeqData.sInf_le_s hd.1 ν), ?_, ?_⟩
  · simp only [w6TorusPt, norm_zero]; positivity
  · simp only [w6TorusPt, norm_zero, add_zero]; exact hr

theorem w6PiStarS_mem {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w6PiStarS d S0) (ν : ℕ) :
    ∀ μ < ν, ξ ∈ (w6Seq d S0 μ).Pi := fun μ _ => mem_iInter.1 hξ μ

/-- `Ψ^ν ∘ ι` on the torus. -/
def w6PsiT (d : W6SeqData) (S0 : W6State) (ν : ℕ) (θ : Fin 2 → ℂ) (ξ : Fin 2 → ℝ) : KamPhase :=
  w6PsiC d S0 ν ξ (w6TorusPt θ)

/-- `Ψ_*(θ, ξ) = lim_ν Ψ^ν(ι θ)`. -/
def w6PsiStar (d : W6SeqData) (S0 : W6State) (θ : Fin 2 → ℂ) (ξ : Fin 2 → ℝ) : KamPhase :=
  limUnder atTop fun ν => w6PsiT d S0 ν θ ξ

/-- `Φ_*(θ, ξ) = ι θ + ι Ψ_*(θ, ξ)`: the limit of `Φ^ν ∘ ι`. -/
def w6PhiStar (d : W6SeqData) (S0 : W6State) (θ : Fin 2 → ℂ) (ξ : Fin 2 → ℝ) : KamPhase :=
  w6TorusPt θ + w6Iota (w6PsiStar d S0 θ ξ)

/-- Tails of the Cauchy sums: `|Ψ^m(ιθ) - Ψ^n(ιθ)|_{r_0} ≤ e_Φ 8^{-n}` for `n ≤ m`. -/
theorem w6PsiT_tail (hI : W6IterHyp d S0) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 d.sInfty)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w6PiStarS d S0) (n : ℕ) :
    ∀ k, kamNorm (d.rNu 0) (w6PsiT d S0 (n + k) θ ξ - w6PsiT d S0 n θ ξ) ≤
      ∑ ν ∈ Finset.Ico n (n + k), 4 * w6CF * d.qNu ν * d.sigma ν := by
  have hd := hI.std
  have hr0 := W6SeqData.w6r_pos hd.1 0
  intro k
  induction k with
  | zero => simp [kamNorm]
  | succ k ih =>
    have h1 := w6PsiC_cauchy hI (ν := n + k) (w6PiStarS_mem hξ _) (w6TorusPt_mem hd hθ _)
    rw [W6SeqData.stepMF_eq hd.1] at h1
    have e : w6PsiT d S0 (n + (k + 1)) θ ξ - w6PsiT d S0 n θ ξ =
        (w6PsiT d S0 (n + k + 1) θ ξ - w6PsiT d S0 (n + k) θ ξ) +
          (w6PsiT d S0 (n + k) θ ξ - w6PsiT d S0 n θ ξ) := by
      rw [← add_assoc]; abel
    rw [e, ← add_assoc, Finset.sum_Ico_succ_top (by omega)]
    have h2 := kamNorm_add_le hr0 (w6PsiT d S0 (n + k + 1) θ ξ - w6PsiT d S0 (n + k) θ ξ)
      (w6PsiT d S0 (n + k) θ ξ - w6PsiT d S0 n θ ξ)
    have hq := (W6SeqData.qNu_pos hd.1 (n + k)).le
    have hσ := (W6SeqData.sigmaNu_pos hd.1 (n + k)).le
    have hc := w6CF_pos.le
    have : 0 ≤ w6CF * d.qNu (n + k) * d.sigma (n + k) := by positivity
    unfold w6PsiT at *
    linarith

theorem kamNorm_continuous (r : ℝ) : Continuous (kamNorm r) := by
  unfold kamNorm
  fun_prop

/-- **Convergence and tail bound** (steps `c-cauchy`, `c-lim`): on `T_{s_∞} × Π_*`,
`Ψ^n(ιθ) → Ψ_*(θ)` and `|Ψ_*(θ) - Ψ^n(ιθ)|_{r_0} ≤ e_Φ 8^{-n}`. -/
theorem w6PsiC_tail (hI : W6IterHyp d S0) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 d.sInfty)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w6PiStarS d S0) :
    Tendsto (fun ν => w6PsiT d S0 ν θ ξ) atTop (𝓝 (w6PsiStar d S0 θ ξ)) ∧
    ∀ n, kamNorm (d.rNu 0) (w6PsiStar d S0 θ ξ - w6PsiT d S0 n θ ξ) ≤ d.ePhi / 8 ^ n := by
  have hd := hI.std
  have hr0 := W6SeqData.w6r_pos hd.1 0
  have htail : ∀ n m, n ≤ m →
      kamNorm (d.rNu 0) (w6PsiT d S0 m θ ξ - w6PsiT d S0 n θ ξ) ≤ d.ePhi / 8 ^ n := by
    intro n m hnm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    exact (w6PsiT_tail hI hθ hξ n k).trans (W6SeqData.cauchy_tail_le hd.1 hd.2 n (n + k))
  have hC : max 1 (max (d.rNu 0 ^ 2) (d.rNu 0)) > 0 := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hcs : CauchySeq fun ν => w6PsiT d S0 ν θ ξ := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hP : 0 ≤ d.ePhi := by
      rw [W6SeqData.ePhi_eq hd.1]
      have := W6SeqData.qNu_pos hd.1 0; have := W6SeqData.sigmaNu_pos hd.1 0
      have := w6CF_pos; positivity
    obtain ⟨N, hN⟩ : ∃ N : ℕ, max 1 (max (d.rNu 0 ^ 2) (d.rNu 0)) * (d.ePhi / 8 ^ N) < ε := by
      have ht : Tendsto (fun N : ℕ => max 1 (max (d.rNu 0 ^ 2) (d.rNu 0)) * (d.ePhi / 8 ^ N))
          atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 8)
          (by norm_num : (1 : ℝ) / 8 < 1)).const_mul (max 1 (max (d.rNu 0 ^ 2) (d.rNu 0)) *
            d.ePhi)
        simpa [div_eq_mul_inv, mul_assoc, inv_pow] using this
      exact (ht.eventually (gt_mem_nhds hε)).exists
    refine ⟨N, fun m hm => ?_⟩
    rw [dist_eq_norm]
    calc ‖w6PsiT d S0 m θ ξ - w6PsiT d S0 N θ ξ‖ ≤
        max 1 (max (d.rNu 0 ^ 2) (d.rNu 0)) * kamNorm (d.rNu 0)
          (w6PsiT d S0 m θ ξ - w6PsiT d S0 N θ ξ) := norm_kamPhase_le_kamNorm hr0 _
      _ ≤ max 1 (max (d.rNu 0 ^ 2) (d.rNu 0)) * (d.ePhi / 8 ^ N) :=
          mul_le_mul_of_nonneg_left (htail N m hm) hC.le
      _ < ε := hN
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  have hlim : w6PsiStar d S0 θ ξ = L := hL.limUnder_eq
  refine ⟨hlim ▸ hL, fun n => ?_⟩
  rw [hlim]
  have hcont : Tendsto (fun m => kamNorm (d.rNu 0) (w6PsiT d S0 m θ ξ - w6PsiT d S0 n θ ξ)) atTop
      (𝓝 (kamNorm (d.rNu 0) (L - w6PsiT d S0 n θ ξ))) :=
    ((kamNorm_continuous _).tendsto _).comp (hL.sub_const _)
  exact le_of_tendsto hcont (eventually_atTop.2 ⟨n, fun m hm => htail n m hm⟩)

end cauchy

end KAM.Wave
