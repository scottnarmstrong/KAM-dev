/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.ConvMaps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: invariant tori in KAM coordinates (blueprint `bpW:w6:invariance`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:invariance` (steps `i-weak`, `i-torus`, `i-lim`).

Model (as in `StrongConj`): fields with values in `𝒫^{p-1}` are read in the `(p-1)`-representatives,
`X_{H_μ} = X_{N_μ} + ι X_{P_μ}` (`w6Field`), and "`X ∈ 𝒫`" means `X = ι_{p→p-1} A` with `A ∈ 𝒫`
(`ι_{p→p-1} = kamHomEmbed 1 (1 - 1) 1`).

* `w6StrongConjK`: `bpW:w6:strong` on `KamPhase` (pointwise, for a linear map `L = DΦ(w)`);
* `w6Field_torus`: `X_{H}(ιθ) = ι_{p→p-1}((ω/2π, 0, 0, 0) + ι X_P(ιθ))` at torus points;
* `w6Invariance_step` (step `i-torus`): `X_{H_0}(Φ^ν ιθ) = ι_{p→p-1}(∂_θ(Φ^ν∘ι)(θ) ω_ν/2π +
  DΦ^ν(ιθ) ι X_{P_ν}(ιθ))`;
* `w6Invariance_of_stepSmooth` (`bpW:w6:invariance`, conditional on the W5 dependency
  `W6StepSmooth`): `X_{H_0}(Φ_*(θ)) = ι_{p→p-1}(∂_θΦ_*(θ) ν_*)` for `ξ ∈ Π_*`,
  `θ ∈ T_{s_0/2}`, `ν_* = ω_*/2π`; the right side exhibits both sides as elements of `𝒫`.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Wave

open KAM

theorem w6_pred_le_one : (1 : ℝ) - 1 ≤ 1 := by norm_num

/-- `ι_{p → p-1}` for `p = 1` (in the representatives). -/
def w6IotaPred : KamPhase →L[ℂ] KamPhase := kamHomEmbed 1 (1 - 1) 1 w6_pred_le_one

theorem homEmbed_gen_comp (a q p pb : ℝ) (hqp : q ≤ p) (hpb : p ≤ pb) (x : HomL2) :
    homEmbed_gen a q p hqp (homEmbed_gen a p pb hpb x) = homEmbed_gen a q pb (hqp.trans hpb) x := by
  ext j
  simp only [homEmbed_gen, weightedDiagCLM_apply, homEmbedCoef_gen]
  have h1 : (homWt a p j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a p j).ne'
  have h2 : (homWt a pb j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a pb j).ne'
  push_cast
  field_simp

theorem w6IotaPred_w6Iota (W : KamPhase) :
    w6IotaPred (w6Iota W) = kamHomEmbed 1 (1 - 1) (3 / 2) w6_pred_le W := by
  simp only [w6IotaPred, w6Iota, kamHomEmbed_apply, homEmbed_gen_comp]

/-- **Strong conjugacy** (`bpW:w6:strong`) on `KamPhase`, pointwise: if `L` (`= DΦ(w)`) is
symplectic on `𝒫`, maps `𝒫^{p_+}` onto `𝒫^{p_+}`, the values `X_H` (`= X_H(Φ w)`) and
`X_{H_+}` (`= X_{H_+}(w)`) in `𝒫^{p-1}` satisfy `ϖ(X_H, L W) = ϖ(X_{H_+}, W)` for `W ∈ 𝒫^{p_+}`, and
`X_{H_+} = ι_{p→p-1} A` with `A ∈ 𝒫`, then `X_H = ι_{p→p-1}(L A)`. -/
theorem w6StrongConjK (L : KamPhase →L[ℂ] KamPhase)
    (hsymp : ∀ W W', w6Symp (L W) (L W') = w6Symp W W')
    (honto : ∀ W'', ∃ W', L (w6Iota W') = w6Iota W'') (XH XHp : KamPhase)
    (hweak : ∀ W' W'', L (w6Iota W') = w6Iota W'' → w6SympPred XH W'' = w6SympPred XHp W')
    (A : KamPhase) (hA : XHp = w6IotaPred A) : XH = w6IotaPred (L A) := by
  refine sub_eq_zero.1 (stepSymp_nondeg (q := 1 - 1) (q' := 3 / 2) zero_le_one w6_pred_nonneg
    fun W'' => ?_)
  obtain ⟨W', hW'⟩ := honto W''
  have h1 := hweak W' W'' hW'
  have h2 := hsymp A (w6Iota W')
  rw [hW'] at h2
  unfold w6SympPred at h1
  unfold w6Symp at h2
  rw [stepSymp_sub_left, h1, hA]
  unfold w6IotaPred w6Iota at *
  rw [stepSymp_embed_pred_eq zero_le_one w6_one_le_three_halves w6_two_nonneg w6_pred_nonneg,
    stepSymp_embed_pred_eq zero_le_one w6_one_le_three_halves w6_two_nonneg w6_pred_nonneg, h2]
  exact sub_self _

/-- `ν = ω/2π` as a complex vector. -/
def w6NuVec (ω : Fin 2 → ℝ) : Fin 2 → ℂ := fun i => ((ω i / (2 * π) : ℝ) : ℂ)

theorem w6NuVec_continuous : Continuous w6NuVec := by
  unfold w6NuVec
  fun_prop

/-- At torus points, `X_H(ιθ) = ι_{p→p-1}((ω/2π, 0, 0, 0) + ι X_P(ιθ)) ∈ 𝒫`
(step `i-torus`: `X_{N}(ιθ) = (ω/2π, 0, 0, 0)`). -/
theorem w6Field_torus {K0 : ℝ} {Ω : ℕ+ → ℝ} (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2))
    (ω : Fin 2 → ℝ) (X : KamPhase → KamPhase) (θ : Fin 2 → ℂ) :
    w6Field hΩ ω X (w6TorusPt θ) =
      w6IotaPred (w6TorusPt (w6NuVec ω) + w6Iota (X (w6TorusPt θ))) := by
  rw [map_add, w6IotaPred_w6Iota]
  unfold w6Field
  congr 1
  simp only [stepXN, w6TorusPt, w6IotaPred, kamHomEmbed_apply, map_zero, neg_zero]
  congr 1
  funext i
  simp only [w6NuVec]
  push_cast
  ring

theorem w6Field_continuousAt {K0 : ℝ} {Ω : ℕ+ → ℝ} (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2))
    (ω : Fin 2 → ℝ) {X : KamPhase → KamPhase} {w : KamPhase} (hX : ContinuousAt X w) :
    ContinuousAt (w6Field hΩ ω X) w := by
  have hN : Continuous (stepXN (a := 1) (p := 1) hΩ ω) := by
    unfold stepXN
    exact continuous_const.prodMk (continuous_const.prodMk
      (((stepXNdiag hΩ).continuous.comp (continuous_snd.comp (continuous_snd.comp
        continuous_snd))).prodMk ((stepXNdiag hΩ).continuous.comp (continuous_fst.comp
          (continuous_snd.comp continuous_snd))).neg))
  exact hN.continuousAt.add ((kamHomEmbed 1 (1 - 1) (3 / 2) w6_pred_le).continuous.continuousAt.comp
    hX)

section inv

variable {d : W6SeqData} {S0 : W6State}

/-- **Torus points** (`bpW:w6:invariance`, step `i-torus`): for `ξ ∈ Π_*`, `θ ∈ T_{s_∞}`,
`X_{H_0}(Φ^ν(ιθ)) = ι_{p→p-1}(∂_θ(Φ^ν∘ι)(θ) ω_ν/2π + DΦ^ν(ιθ) ι X_{P_ν}(ιθ))`. -/
theorem w6Invariance_step (hI : W6IterHyp d S0) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w6PiStarS d S0)
    {K0 : ℝ} (hΩ0 : ∀ j : ℕ+, |(w6Seq d S0 0).Om ξ j| ≤ K0 * ((j : ℝ) + 2))
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 d.sInfty) (ν : ℕ) :
    w6Field hΩ0 ((w6Seq d S0 0).om ξ) ((w6Seq d S0 0).X ξ) (w6PhiC d S0 ν ξ (w6TorusPt θ)) =
      w6IotaPred (fderiv ℂ (fun θ' => w6PhiC d S0 ν ξ (w6TorusPt θ')) θ
          (w6NuVec ((w6Seq d S0 ν).om ξ)) +
        fderiv ℂ (w6PhiC d S0 ν ξ) (w6TorusPt θ)
          (w6Iota ((w6Seq d S0 ν).X ξ (w6TorusPt θ)))) := by
  have hξ' := w6PiStarS_mem hξ ν
  have hw := w6TorusPt_mem hI.std hθ ν
  have hξν : ξ ∈ (w6Seq d S0 ν).Pi := mem_iInter.1 hξ ν
  have hΩν := homOmega_le (hI.stage ν).freq_spec hξν
  obtain ⟨-, hops⟩ := w6Compose_ops hI ν ξ hξ'
  obtain ⟨-, -, hs, hon⟩ := hops _ hw
  have hweak := w6Compose_weak hI ν ξ hξ' hΩ0 hΩν _ hw
  have key := w6StrongConjK _ hs hon _ _ hweak _ (w6Field_torus hΩν _ _ θ)
  have hd := (w6Compose_main hI ν ξ hξ' _ hw).2.2.1
  have hc : HasFDerivAt (fun θ' => w6PhiC d S0 ν ξ (w6TorusPt θ'))
      ((fderiv ℂ (w6PhiC d S0 ν ξ) (w6TorusPt θ)).comp w6TorusCLM) θ :=
    hd.hasFDerivAt.comp θ w6TorusCLM.hasFDerivAt
  have hfd : fderiv ℂ (w6PhiC d S0 ν ξ) (w6TorusPt θ) (w6TorusPt (w6NuVec ((w6Seq d S0 ν).om ξ)))
      = fderiv ℂ (fun θ' => w6PhiC d S0 ν ξ (w6TorusPt θ')) θ
          (w6NuVec ((w6Seq d S0 ν).om ξ)) := by
    rw [hc.fderiv]
    rfl
  have e2 := (fderiv ℂ (w6PhiC d S0 ν ξ) (w6TorusPt θ)).map_add
    (w6TorusPt (w6NuVec ((w6Seq d S0 ν).om ξ))) (w6Iota ((w6Seq d S0 ν).X ξ (w6TorusPt θ)))
  rw [key, e2, hfd]

/-- **Invariance** (blueprint `bpW:w6:invariance`) for an iteration with the hypotheses of every
stage: for `ξ ∈ Π_*` and `θ ∈ T_{s_0/2}`, with `H_0 = N_0 + P_0`, `ν_* = ω_*/(2π)`
(`ω_* = w6OmStar`, given as a limit of `ω_ν(ξ)`),
`X_{H_0}(Φ_*(θ)) = ∂_θΦ_*(θ) ν_*` in `𝒫^{p-1}`, the right side in `𝒫`. -/
theorem w6InvarianceIt (hI : W6IterHyp d S0) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w6PiStarS d S0)
    (hX0 : DifferentiableOn ℂ ((w6Seq d S0 0).X ξ) (d.domNu 0))
    {K0 : ℝ} (hΩ0 : ∀ j : ℕ+, |(w6Seq d S0 0).Om ξ j| ≤ K0 * ((j : ℝ) + 2))
    {ωs : Fin 2 → ℝ} (hωs : Tendsto (fun ν => (w6Seq d S0 ν).om ξ) atTop (𝓝 ωs))
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (d.s0 / 2)) :
    w6Field hΩ0 ((w6Seq d S0 0).om ξ) ((w6Seq d S0 0).X ξ) (w6PhiStar d S0 θ ξ) =
      w6IotaPred (fderiv ℂ (fun θ' => w6PhiStar d S0 θ' ξ) θ (w6NuVec ωs)) := by
  have hd := hI.std
  have hr0 := W6SeqData.w6r_pos hd.1 0
  have hθT : θ ∈ complexStrip 2 d.sInfty :=
    w6_ball_subset_strip (d := d) hθ (mem_ball_self (by have := hd.1.s0_pos; positivity))
  obtain ⟨-, -, -, -, -, himg, hcl, -, hder⟩ := w6ConvTorusIt hI
  -- left side
  have hmem : w6PhiStar d S0 θ ξ ∈ d.domNu 0 := hcl (himg θ hθT ξ hξ)
  have hXc : ContinuousAt ((w6Seq d S0 0).X ξ) (w6PhiStar d S0 θ ξ) :=
    (hX0.differentiableAt ((kamDomain_isOpen _ _).mem_nhds hmem)).continuousAt
  have hL := ((w6Field_continuousAt hΩ0 ((w6Seq d S0 0).om ξ) hXc).tendsto).comp
    (w6PhiT_tendsto hI hθT hξ)
  -- right side, main part
  have hmemq : ((θ, ξ) : (Fin 2 → ℂ) × (Fin 2 → ℝ)) ∈
      complexStrip 2 (d.s0 / 2) ×ˢ w6PiStarS d S0 := ⟨hθ, hξ⟩
  have hD := hder.tendsto_at hmemq
  simp only at hD
  have hcont : Continuous fun q : ((Fin 2 → ℂ) →L[ℂ] KamPhase) × (Fin 2 → ℂ) => q.1 q.2 :=
    isBoundedBilinearMap_apply.continuous
  have hG1 : Tendsto (fun ν => fderiv ℂ (fun θ' => w6PhiC d S0 ν ξ (w6TorusPt θ')) θ
      (w6NuVec ((w6Seq d S0 ν).om ξ))) atTop
      (𝓝 (fderiv ℂ (fun θ' => w6PhiStar d S0 θ' ξ) θ (w6NuVec ωs))) :=
    (hcont.tendsto _).comp (hD.prodMk_nhds ((w6NuVec_continuous.tendsto _).comp hωs))
  have hG := (w6IotaPred.continuous.tendsto _).comp hG1
  -- right side, remainder
  have hR : Tendsto (fun ν => w6IotaPred (fderiv ℂ (w6PhiC d S0 ν ξ) (w6TorusPt θ)
      (w6Iota ((w6Seq d S0 ν).X ξ (w6TorusPt θ))))) atTop (𝓝 0) := by
    rw [← map_zero w6IotaPred]
    refine (w6IotaPred.continuous.tendsto 0).comp ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun ν => ?_)
      (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 : ℝ) / 4 < 1)).const_mul (w6Cr d * (2 * d.eps0)))
    have hξν : ξ ∈ (w6Seq d S0 ν).Pi := mem_iInter.1 hξ ν
    have hw := w6TorusPt_mem hd hθT ν
    have hrν := W6SeqData.w6r_pos hd.1 ν
    obtain ⟨-, hops⟩ := w6Compose_ops hI ν ξ (w6PiStarS_mem hξ ν)
    obtain ⟨hq, -, -, -⟩ := hops _ hw
    obtain ⟨b0, b1, bs, bb, -⟩ := (hI.stage ν).bound_spec
    have hXb : kamNorm (d.rNu ν) ((w6Seq d S0 ν).X ξ (w6TorusPt θ)) ≤ d.eps ν := by
      have := bb ξ hξν _ hw
      have : 0 ≤ d.lam ν * W6Stage.w6StageE1 (hI.stage ν) :=
        mul_nonneg (W6SeqData.lam_pos hd.1 ν).le b1
      linarith
    have he := W6SeqData.eps_le_four_pow hd.1 hd.2 ν
    calc ‖fderiv ℂ (w6PhiC d S0 ν ξ) (w6TorusPt θ) (w6Iota ((w6Seq d S0 ν).X ξ (w6TorusPt θ)))‖
        ≤ w6Cr d * kamNorm (d.rNu 0) (fderiv ℂ (w6PhiC d S0 ν ξ) (w6TorusPt θ)
          (w6Iota ((w6Seq d S0 ν).X ξ (w6TorusPt θ)))) := norm_kamPhase_le_kamNorm hr0 _
      _ ≤ w6Cr d * (2 * kamNorm (d.rNu ν) ((w6Seq d S0 ν).X ξ (w6TorusPt θ))) := by
          refine mul_le_mul_of_nonneg_left ((hq _).trans ?_) w6Cr_pos.le
          exact mul_le_mul_of_nonneg_left (kamNorm_w6Iota_le hrν _) (by norm_num)
      _ ≤ w6Cr d * (2 * (d.eps0 / 4 ^ ν)) := by
          refine mul_le_mul_of_nonneg_left ?_ w6Cr_pos.le
          linarith
      _ = w6Cr d * (2 * d.eps0) * (4 ^ ν)⁻¹ := by ring
  have hsum := hG.add hR
  rw [add_zero] at hsum
  refine tendsto_nhds_unique hL (hsum.congr fun ν => ?_)
  simp only [Function.comp_apply]
  rw [w6Invariance_step hI hξ hΩ0 hθT ν, map_add]

end inv

section src

variable {d : W6SeqData} {Pm : Set (Fin 2 → ℝ)} {ω0 : (Fin 2 → ℝ) → Fin 2 → ℝ}
  {Ω0 : (Fin 2 → ℝ) → ℕ+ → ℝ} {P0 : (Fin 2 → ℝ) → KamPhase → ℂ}
  {X0 : (Fin 2 → ℝ) → KamPhase → KamPhase} {β₀ : ℝ}

/-- **Invariant tori in KAM coordinates** (blueprint `bpW:w6:invariance`). In the setting of
Proposition `bpW:w6:convergence` (`W6ConvHyp`), with `H_0 = N_0 + P_0`,
`X_{H_0} = X_{N_0} + ι X_{P_0}` (`X_{N_0}(w) = (ω_0/2π, 0, Ω_0 v, -Ω_0 u)`, any bound `K0` for
`Ω_0(ξ)`), `ν_* = ω_*/(2π)`: for `ξ ∈ Π_*` and `θ ∈ T_{s_0/2}`,
`X_{H_0}(Φ_*(θ)) = ι_{p→p-1}(∂_θΦ_*(θ) ν_*)` in `𝒫^{p-1}`; both sides lie in `𝒫`. Conditional
helper on the W5 dependency `W6StepSmooth`. -/
theorem w6Invariance_of_stepSmooth (hS : W6StepSmooth) (hC : W6ConvHyp d Pm ω0 Ω0 P0 X0 β₀)
    {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ w6PiStarIt d (w6Start d Pm ω0 Ω0 P0 X0))
    {K0 : ℝ} (hΩ0 : ∀ j : ℕ+, |Ω0 ξ j| ≤ K0 * ((j : ℝ) + 2))
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (d.s0 / 2)) :
    w6Field hΩ0 (ω0 ξ) (X0 ξ) (w6PhiStar d (w6Start d Pm ω0 Ω0 P0 X0) θ ξ) =
      w6IotaPred (fderiv ℂ (fun θ' => w6PhiStar d (w6Start d Pm ω0 Ω0 P0 X0) θ' ξ) θ
        (w6NuVec (w6OmStar d (w6Start d Pm ω0 Ω0 P0 X0) ξ))) := by
  have hI := w6IterHyp_of_conv hS hC
  have hξPm : ξ ∈ Pm := w6Pi0_subset (mem_iInter.1 hξ 0)
  exact w6InvarianceIt hI hξ (hC.smooth ξ hξPm).holoX hΩ0 ((w6ConvFreq hC).1.tendsto_at hξ) hθ

end src

end KAM.Wave
