/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.ConvCauchy
public import KAM.Wave.Analytic.UniformLimit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: the transformations on the torus (blueprint `bpW:w6:convergence` (iii))

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:convergence` (clause (iii); steps `c-dom`, `c-lim`,
`c-cont`).

For `ξ ∈ Π_*` and `θ ∈ T_{s_∞}` (`T_{s'} = complexStrip 2 s'`): `Φ^ν(ιθ) = ιθ + ιΨ^ν(ιθ)`,
holomorphic, periodic and real in `θ`; `Φ^ν ∘ ι → Φ_*` uniformly on `T_{s_∞} × Π_*` (even in the
`p_+`-norm of the errors); `Φ_*` is holomorphic (W1's uniform-limit lemma), periodic, real, jointly
continuous, with values in `closure D(s_0 - 4σ_0, 2η_0 r_0) ⊆ D_0`, and
`Φ_*(θ) - ιθ = ι V` with `|V|_{r_0} ≤ e_Φ`; the `θ`-derivatives converge uniformly on
`T_{s_0/2} × Π_*` (Cauchy estimate on balls of radius `s_0/4`).
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Wave

open KAM

/-- Uniform convergence from a geometric bound. -/
theorem w6_tendstoUniformlyOn_geom {α E : Type*} [SeminormedAddCommGroup E] {S : Set α}
    {F : ℕ → α → E} {f : α → E} {K : ℝ} (h : ∀ n, ∀ q ∈ S, ‖f q - F n q‖ ≤ K * (1 / 8) ^ n) :
    TendstoUniformlyOn F f atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have ht : Tendsto (fun n : ℕ => K * (1 / 8 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 8)
      (by norm_num : (1 : ℝ) / 8 < 1)).const_mul K
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn q hq
  rw [dist_eq_norm]
  exact (h n q hq).trans_lt hn

/-- `ι` on the angles as a continuous linear map. -/
def w6TorusCLM : (Fin 2 → ℂ) →L[ℂ] KamPhase :=
  ContinuousLinearMap.inl ℂ (Fin 2 → ℂ) ((Fin 2 → ℂ) × HomL2 × HomL2)

theorem w6TorusCLM_apply (θ : Fin 2 → ℂ) : w6TorusCLM θ = w6TorusPt θ := rfl

theorem w6TorusPt_add_single (θ : Fin 2 → ℂ) (i : Fin 2) :
    w6TorusPt (θ + Pi.single i 1) = w6TorusPt θ + stepTau i := by
  simp [w6TorusPt, stepTau]

theorem stepReal_w6TorusPt (x : Fin 2 → ℝ) : StepReal (w6TorusPt fun i => (x i : ℂ)) := by
  refine ⟨fun i => ?_, fun i => ?_, fun j => ?_, fun j => ?_⟩ <;> simp [w6TorusPt]

theorem isClosed_stepReal : IsClosed {w : KamPhase | StepReal w} := by
  have hc1 : ∀ i : Fin 2, Continuous fun w : KamPhase => (w.1 i).im := fun i => by fun_prop
  have hc2 : ∀ i : Fin 2, Continuous fun w : KamPhase => (w.2.1 i).im := fun i => by fun_prop
  have hev : ∀ j : ℕ+, Continuous fun f : HomL2 => f j := fun j =>
    (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 j).continuous
  have hc3 : ∀ j : ℕ+, Continuous fun w : KamPhase => (w.2.2.1 j).im := fun j =>
    Complex.continuous_im.comp ((hev j).comp (continuous_fst.comp
      (continuous_snd.comp continuous_snd)))
  have hc4 : ∀ j : ℕ+, Continuous fun w : KamPhase => (w.2.2.2 j).im := fun j =>
    Complex.continuous_im.comp ((hev j).comp (continuous_snd.comp
      (continuous_snd.comp continuous_snd)))
  have e : {w : KamPhase | StepReal w} =
      (⋂ i, {w : KamPhase | (w.1 i).im = 0}) ∩ ((⋂ i, {w : KamPhase | (w.2.1 i).im = 0}) ∩
        ((⋂ j, {w : KamPhase | (w.2.2.1 j).im = 0}) ∩ ⋂ j, {w : KamPhase | (w.2.2.2 j).im = 0}))
      := by
    ext w; simp [StepReal]
  rw [e]
  exact (isClosed_iInter fun i => isClosed_eq (hc1 i) continuous_const).inter
    ((isClosed_iInter fun i => isClosed_eq (hc2 i) continuous_const).inter
      ((isClosed_iInter fun j => isClosed_eq (hc3 j) continuous_const).inter
        (isClosed_iInter fun j => isClosed_eq (hc4 j) continuous_const)))

/-- `closure D(s', r') ⊆ D(s, r)` for `s' < s`, `0 ≤ r' < r`. -/
theorem closure_kamDomain_subset {s' s r' r : ℝ} (hs : s' < s) (hr' : 0 ≤ r') (hr : r' < r) :
    closure (kamDomain s' r') ⊆ kamDomain s r := by
  let C : Set KamPhase := {z | (∀ i, |(z.1 i).im| ≤ s') ∧ ‖z.2.1‖ ≤ r' ^ 2 ∧
    ‖z.2.2.1‖ + ‖z.2.2.2‖ ≤ r'}
  have hC : IsClosed C := by
    have e : C = (⋂ i, {z : KamPhase | |(z.1 i).im| ≤ s'}) ∩ ({z : KamPhase | ‖z.2.1‖ ≤ r' ^ 2} ∩
        {z : KamPhase | ‖z.2.2.1‖ + ‖z.2.2.2‖ ≤ r'}) := by
      ext z; simp [C]
    rw [e]
    exact (isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const).inter
      ((isClosed_le (by fun_prop) continuous_const).inter
        (isClosed_le (by fun_prop) continuous_const))
  have hsub : kamDomain s' r' ⊆ C := fun z hz =>
    ⟨fun i => (hz.1 i).le, hz.2.1.le, hz.2.2.le⟩
  refine (closure_minimal hsub hC).trans fun z hz => ⟨fun i => (hz.1 i).trans_lt hs, ?_, ?_⟩
  · have : r' ^ 2 < r ^ 2 := by nlinarith
    exact hz.2.1.trans_lt this
  · exact hz.2.2.trans_lt hr

section torus

variable {d : W6SeqData} {S0 : W6State}

/-- The constant `max(1, r_0², r_0)` comparing the product norm with `|·|_{r_0}`. -/
def w6Cr (d : W6SeqData) : ℝ := max 1 (max (d.rNu 0 ^ 2) (d.rNu 0))

theorem w6Cr_pos : 0 < w6Cr d := lt_of_lt_of_le one_pos (le_max_left _ _)

theorem w6ePhi_nonneg (hd : W6State.Std d) : 0 ≤ d.ePhi := by
  rw [W6SeqData.ePhi_eq hd.1]
  have := W6SeqData.qNu_pos hd.1 0; have := W6SeqData.sigmaNu_pos hd.1 0
  have := w6CF_pos; positivity

/-- `Φ^ν(ιθ) = ιθ + ιΨ^ν(ιθ)` on `T_{s_∞} × Π_*`. -/
theorem w6PhiT_eq (hI : W6IterHyp d S0) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 d.sInfty)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w6PiStarS d S0) (ν : ℕ) :
    w6PhiC d S0 ν ξ (w6TorusPt θ) = w6TorusPt θ + w6Iota (w6PsiT d S0 ν θ ξ) :=
  (w6Compose_main hI ν ξ (w6PiStarS_mem hξ ν) _ (w6TorusPt_mem hI.std hθ ν)).1

/-- `‖Φ_*(θ) - Φ^n(ιθ)‖ ≤ C e_Φ 8^{-n}` on `T_{s_∞} × Π_*` (product norm). -/
theorem w6PhiT_sub_le (hI : W6IterHyp d S0) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 d.sInfty)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w6PiStarS d S0) (n : ℕ) :
    ‖w6PhiStar d S0 θ ξ - w6PhiC d S0 n ξ (w6TorusPt θ)‖ ≤ w6Cr d * d.ePhi * (1 / 8) ^ n := by
  have hr0 := W6SeqData.w6r_pos hI.std.1 0
  rw [w6PhiT_eq hI hθ hξ n]
  unfold w6PhiStar
  rw [add_sub_add_left_eq_sub, ← map_sub]
  calc _ ≤ w6Cr d * kamNorm (d.rNu 0) (w6Iota (w6PsiStar d S0 θ ξ - w6PsiT d S0 n θ ξ)) :=
        norm_kamPhase_le_kamNorm hr0 _
    _ ≤ w6Cr d * (d.ePhi / 8 ^ n) := mul_le_mul_of_nonneg_left
        ((kamNorm_w6Iota_le hr0 _).trans ((w6PsiC_tail hI hθ hξ).2 n)) w6Cr_pos.le
    _ = w6Cr d * d.ePhi * (1 / 8) ^ n := by rw [one_div_pow]; ring

theorem w6PhiT_tendsto (hI : W6IterHyp d S0) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 d.sInfty)
    {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w6PiStarS d S0) :
    Tendsto (fun n => w6PhiC d S0 n ξ (w6TorusPt θ)) atTop (𝓝 (w6PhiStar d S0 θ ξ)) := by
  have h := ((w6Iota.continuous.tendsto _).comp (w6PsiC_tail hI hθ hξ).1).const_add
    (w6TorusPt θ)
  refine h.congr fun n => ?_
  rw [w6PhiT_eq hI hθ hξ n]
  rfl

theorem w6PhiT_differentiableOn (hI : W6IterHyp d S0) {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ w6PiStarS d S0) (ν : ℕ) :
    DifferentiableOn ℂ (fun θ => w6PhiC d S0 ν ξ (w6TorusPt θ)) (complexStrip 2 d.sInfty) :=
  fun θ hθ => (((w6Compose_main hI ν ξ (w6PiStarS_mem hξ ν) _
    (w6TorusPt_mem hI.std hθ ν)).2.2.1).comp θ w6TorusCLM.differentiableAt).differentiableWithinAt

/-- Joint continuity of one factor `(w, ξ) ↦ Φ_{ν+1}(w, ξ)` on `D_{ν+1} × Π_ν` (step `c-cont`). -/
theorem w6PhiK_continuousOn (hI : W6IterHyp d S0) (ν : ℕ) :
    ContinuousOn (fun q : KamPhase × (Fin 2 → ℝ) => w6PhiK d S0 ν q.2 q.1)
      (d.domNu (ν + 1) ×ˢ (w6Seq d S0 ν).Pi) := by
  have hrν := W6SeqData.w6r_pos hI.std.1 ν
  rintro ⟨w0, ξ0⟩ ⟨hw0, hξ0⟩
  obtain ⟨A, hA, hlip⟩ := (w6StepK_clauses hI.std (hI.stage ν) hξ0).1
  obtain ⟨hsubU, hdK, -, -⟩ := w6StepK_smooth hI.std (hI.stage ν) hξ0
  have hc : ContinuousAt (w6PhiK d S0 ν ξ0) w0 := (hdK w0 (hsubU hw0)).continuousAt
  set C := max 1 (max (d.rNu ν ^ 2) (d.rNu ν))
  have hC : 0 < C := lt_of_lt_of_le one_pos (le_max_left _ _)
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ1, hδ1, h1⟩ := Metric.continuousAt_iff.1 hc (ε / 2) (by positivity)
  refine ⟨min δ1 (ε / (2 * (C * A + 1))), by positivity, ?_⟩
  rintro ⟨w, ξ⟩ ⟨hw, hξ⟩ hdist
  have hdw : dist w w0 < δ1 := (le_max_left _ _).trans_lt (hdist.trans_le (min_le_left _ _))
  have hdξ : dist ξ ξ0 < ε / (2 * (C * A + 1)) :=
    (le_max_right _ _).trans_lt (hdist.trans_le (min_le_right _ _))
  have e1 : ‖w6PhiK d S0 ν ξ w - w6PhiK d S0 ν ξ0 w‖ ≤ C * A * ‖ξ0 - ξ‖ := by
    rw [norm_sub_rev]
    calc _ ≤ C * kamNorm (d.rNu ν) (w6PhiK d S0 ν ξ0 w - w6PhiK d S0 ν ξ w) :=
          norm_kamPhase_le_kamNorm hrν _
      _ ≤ C * (A * ‖ξ0 - ξ‖) := mul_le_mul_of_nonneg_left (hlip ξ hξ w hw) hC.le
      _ = C * A * ‖ξ0 - ξ‖ := by ring
  have e2 : dist (w6PhiK d S0 ν ξ0 w) (w6PhiK d S0 ν ξ0 w0) < ε / 2 := h1 hdw
  have hξn : ‖ξ0 - ξ‖ = dist ξ ξ0 := by rw [dist_eq_norm, norm_sub_rev]
  have e3 : C * A * ‖ξ0 - ξ‖ < ε / 2 := by
    rw [hξn]
    have hCA : 0 ≤ C * A := by positivity
    calc C * A * dist ξ ξ0 ≤ (C * A + 1) * dist ξ ξ0 :=
          mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
      _ < (C * A + 1) * (ε / (2 * (C * A + 1))) :=
          mul_lt_mul_of_pos_left hdξ (by positivity)
      _ = ε / 2 := by field_simp
  simp only
  rw [dist_eq_norm] at e2 ⊢
  calc ‖w6PhiK d S0 ν ξ w - w6PhiK d S0 ν ξ0 w0‖ ≤
      ‖w6PhiK d S0 ν ξ w - w6PhiK d S0 ν ξ0 w‖ + ‖w6PhiK d S0 ν ξ0 w - w6PhiK d S0 ν ξ0 w0‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-- Joint continuity of `(w, ξ) ↦ Φ^ν(w, ξ)` on `D_ν × Π_*` (step `c-cont`). -/
theorem w6PhiC_continuousOn (hI : W6IterHyp d S0) (ν : ℕ) :
    ContinuousOn (fun q : KamPhase × (Fin 2 → ℝ) => w6PhiC d S0 ν q.2 q.1)
      (d.domNu ν ×ˢ w6PiStarS d S0) := by
  induction ν with
  | zero => exact continuous_fst.continuousOn
  | succ ν ih =>
    have hh : ContinuousOn (fun q : KamPhase × (Fin 2 → ℝ) => (w6PhiK d S0 ν q.2 q.1, q.2))
        (d.domNu (ν + 1) ×ˢ w6PiStarS d S0) :=
      ((w6PhiK_continuousOn hI ν).mono (prod_mono subset_rfl fun ξ hξ => mem_iInter.1 hξ ν)).prodMk
        continuous_snd.continuousOn
    refine ih.comp hh fun q hq => ⟨?_, hq.2⟩
    exact ((w6StepK_smooth hI.std (hI.stage ν) (mem_iInter.1 hq.2 ν)).2.2.2 q.1 hq.1).2.1

end torus

end KAM.Wave
