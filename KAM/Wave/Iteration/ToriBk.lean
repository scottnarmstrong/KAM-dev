/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.SmoothSrc
public import KAM.Wave.Iteration.ToriBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: the tori in Birkhoff coordinates, basic clauses (`bpW:w6:tori` (i), (ii), (iv))

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:tori` (steps `t-hol`, `t-cont`, `t-close`).

The input Hamiltonian is `H_in = N_ξ + P_ξ` of W5's action–angle lemma (`bpW:w5:action-angle` (iv),
`a = p = 1`), `P = w6InP`, `X_P = w6InX`; `bpW:w5:initial` supplies the hypotheses of the
preparatory step (`w6PrepHyp_initial`). For the wave iteration with starting size
`ε₀ ∈ [ε^♭_0, γ₁ α̌]`:

* `W6PrepHyp.w6TorusBk H ε₀ θ ξ = 𝒜_ξ(Φ_P(Φ_*(θ)))` (`Ψ̃_ξ(θ)`), `W6PrepHyp.w6NuStar = ω_*/(2π)`;
* `W6PrepHyp.w6TorusKam_aaDom`: `Φ_P Φ_* θ` is in the domain of `𝒜_ξ` and `Ψ̃_ξ(θ) ∈ B_{ρ₁}`
  (`bpW:w5:action-angle` (ii), under `|ξ|_∞ ≤ t`, `ξ_i ≥ 2r²` on `Π`, `c_A(t + r²) < ρ₁²`);
* `W6PrepHyp.w6TorusBk_hol` ((i)), `W6PrepHyp.w6TorusBk_cont` ((ii)),
  `W6PrepHyp.w6TorusBk_close` ((iv)).
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology Complex

namespace KAM.Wave

open KAM

/-- `P_ξ` of `bpW:w5:action-angle` (iv) on real parameters (`a = p = 1`). -/
def w6InP (m : ℝ) (hm : 0 < m) : (Fin 2 → ℝ) → KamPhase → ℂ :=
  fun ξ => aaPfun m hm (zero_le_one' ℝ) (by norm_num : (1 : ℝ) / 2 ≤ 1) (aaOfReal ξ)

/-- `X_{P_ξ}` of `bpW:w5:action-angle` (v) on real parameters (`a = p = 1`). -/
def w6InX (m : ℝ) (hm : 0 < m) : (Fin 2 → ℝ) → KamPhase → KamPhase :=
  fun ξ => aaXP m hm (zero_le_one' ℝ) (by norm_num : (1 : ℝ) / 2 ≤ 1) (aaOfReal ξ)

variable {m : ℝ} {hm : 0 < m}

/-- **The preparatory step's hypotheses from the initial perturbation** (`bpW:w5:initial`
supplies `P`, as `bpW:w6:tori` assumes): under the hypotheses of `bpW:w5:initial` (`s = 1/8`) and
`ε_in(1 + 4λ/ρ_ξ) ≤ ε ≤ γα`, `λ = α/M`, the family `H_in = N + P` of `bpW:w5:action-angle` (iv)
satisfies the hypotheses of `bpW:w6:prep-step`. -/
theorem w6PrepHyp_initial {Pi : Set (Fin 2 → ℝ)} {α r t ρξ ε : ℝ} (hmeas : MeasurableSet Pi)
    (hsub : ∀ ξ ∈ Pi, ‖ξ‖ ≤ 1 / 2) (hα : 0 < α) (hα0 : α ≤ measAlpha0 m hm) (hr : 0 < r)
    (ht : 0 < t) (hρξ : 0 < ρξ)
    (hPar : ∀ ζ : Fin 2 → ℂ, (∃ ξ ∈ Pi, ‖ζ - aaOfReal ξ‖ < ρξ) →
      (∀ i, 2 * r ^ 2 ≤ (ζ i).re) ∧ ‖ζ‖ ≤ t)
    (hρ₁ : aaCA * (t + r ^ 2) < birkRho1 m 1 ^ 2) (hε : 0 < ε) (hεγ : ε ≤ w6Gamma m hm * α)
    (hin : aaEpsIn m r t * (1 + 4 * (α / w6M m hm) / ρξ) ≤ ε) :
    W6PrepHyp m hm Pi α r ε (w6InP m hm) (w6InX m hm) := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := initialPerturbation m hm (s := w6S) (by unfold w6S; norm_num)
    hr ht hρξ Pi hPar hρ₁
  obtain ⟨e0, e1, he0, he1, hs, hb, hl⟩ := h4 _ (div_pos hα (w6M_pos m hm)).le
  exact
  { meas := hmeas
    sub := hsub
    hα := hα
    hα0 := hα0
    hr := hr
    smooth := fun ξ hξ => h1 ξ hξ.1
    per := fun ξ hξ i w hw => h2 ξ hξ.1 i w hw
    real := fun ξ hξ w hw hre => h3 ξ hξ.1 w hw hre
    hε := hε
    hεγ := hεγ
    bound := ⟨e0, e1, he0, he1, hs.trans hin, fun ξ hξ => hb ξ hξ.1,
      fun ξ hξ ζ hζ => hl ξ hξ.1 ζ hζ.1⟩ }

theorem norm_homEmbed_gen_apply_le {a p pb : ℝ} (hpb : p ≤ pb) (x : HomL2) :
    ‖homEmbed_gen a p pb hpb x‖ ≤ ‖x‖ := by
  have h := norm_diagCLM_le (homEmbedCoef_gen a p pb) (norm_homEmbedCoef_le_gen hpb)
  calc ‖homEmbed_gen a p pb hpb x‖ ≤ ‖homEmbed_gen a p pb hpb‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = ‖x‖ := one_mul _

theorem w6_strip_add_single {s : ℝ} {z : Fin 2 → ℂ} (hz : z ∈ complexStrip 2 s) (i : Fin 2)
    (c : ℝ) : z + _root_.Pi.single i (c : ℂ) ∈ complexStrip 2 s := fun k => by
  by_cases hk : k = i
  · subst hk; simpa using hz k
  · simpa [Pi.single_apply, hk] using hz k

theorem w6_strip_half_subset (d : W6SeqData) (hd : d.s0 = w6S0) :
    complexStrip 2 (w6S0 / 2) ⊆ complexStrip 2 d.sInfty := fun θ hθ i => by
  have := hθ i
  unfold W6SeqData.sInfty
  rw [hd, w6S0_val] at *
  linarith

theorem w6_real_mem_strip_half (x : Fin 2 → ℝ) : aaOfReal x ∈ complexStrip 2 (w6S0 / 2) :=
  fun i => by simp [aaOfReal, w6S0_val]

theorem w6_continuousOn_aaMap_comp {F : (Fin 2 → ℂ) × (Fin 2 → ℝ) → KamPhase}
    {S : Set (Fin 2 → ℝ)} {T : Set (Fin 2 → ℂ)} (hF : ContinuousOn F (T ×ˢ S))
    (hT : ∀ x, aaOfReal x ∈ T)
    (hD : ∀ ξ ∈ S, ∀ x, ∀ i, 0 < (aaOfReal ξ i + (F (aaOfReal x, ξ)).2.1 i).re) :
    ContinuousOn (fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) => aaMap 1 1 (aaOfReal q.1)
      (F (aaOfReal q.2, q.1))) (S ×ˢ univ) := by
  have hc : Continuous (fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      ((aaOfReal q.2, q.1) : (Fin 2 → ℂ) × (Fin 2 → ℝ))) := by
    unfold aaOfReal; fun_prop
  have hg : ContinuousOn (fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) => F (aaOfReal q.2, q.1))
      (S ×ˢ univ) := hF.comp hc.continuousOn fun q hq => ⟨hT q.2, hq.1⟩
  have hc1 : Continuous (fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) => aaOfReal q.1) := by
    unfold aaOfReal; fun_prop
  have hk : ContinuousOn (fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      ((aaOfReal q.1, F (aaOfReal q.2, q.1)) : (Fin 2 → ℂ) × KamPhase)) (S ×ˢ univ) :=
    hc1.continuousOn.prodMk hg
  have hmap : MapsTo (fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      ((aaOfReal q.1, F (aaOfReal q.2, q.1)) : (Fin 2 → ℂ) × KamPhase)) (S ×ˢ univ) aaDomJ :=
    fun q hq => hD q.1 hq.1 q.2
  have := (aaMap_differentiableOn 1 1).continuousOn.comp hk hmap
  exact this

namespace W6PrepHyp

variable {Pi : Set (Fin 2 → ℝ)} {α r ε ε₀ t : ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}

/-- **The torus in Birkhoff coordinates** `Ψ̃_ξ(θ) = 𝒜_ξ(Φ_P(Φ_*(θ))) ∈ 𝔚` (`bpW:w6:tori`). -/
def w6TorusBk (H : W6PrepHyp m hm Pi α r ε P X) (ε₀ : ℝ) (θ : Fin 2 → ℂ) (ξ : Fin 2 → ℝ) :
    BirkSpace :=
  aaMap 1 1 (aaOfReal ξ) (H.w6TorusKam ε₀ θ ξ)

/-- `ω_*` of the wave iteration with starting size `ε₀`. -/
def w6OmStarW (H : W6PrepHyp m hm Pi α r ε P X) (ε₀ : ℝ) (ξ : Fin 2 → ℝ) : Fin 2 → ℝ :=
  w6OmStar (w6WaveSeq m hm α r ε ε₀) (w6Start (w6WaveSeq m hm α r ε ε₀)
    (Pi \ prepSet m hm Pi α) H.om0 H.Om0 H.w6P0 H.X0) ξ

/-- `ν_* = ω_*/(2π)`. -/
def w6NuStar (H : W6PrepHyp m hm Pi α r ε P X) (ε₀ : ℝ) (ξ : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => H.w6OmStarW ε₀ ξ i / (2 * π)

theorem mem_of_mem_wavePiStar (H : W6PrepHyp m hm Pi α r ε P X) {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ H.wavePiStar ε₀) : ξ ∈ Pi \ prepSet m hm Pi α :=
  w6Pi0_subset (mem_iInter.1 hξ 0)

/-- `Φ_P(Φ_*(θ))` is in the domain of `𝒜_ξ`, with `Re(ξ_i + y_i) > r²`, and `Ψ̃_ξ(θ) ∈ B_{ρ₁}`
(`bpW:w5:action-angle` (ii)). -/
theorem w6TorusKam_aaDom (H : W6PrepHyp m hm Pi α r ε P X) (hlo : w6EpsFlat α ε ≤ ε₀)
    (hhi : ε₀ ≤ w6Gamma1 m hm * alphaCheck α) (ht : 0 < t)
    (hPi : ∀ ξ ∈ Pi, (∀ i, 2 * r ^ 2 ≤ ξ i) ∧ ‖ξ‖ ≤ t)
    (hρ₁ : aaCA * (t + r ^ 2) < birkRho1 m 1 ^ 2) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 (w6WaveSeq m hm α r ε ε₀).sInfty) {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ H.wavePiStar ε₀) :
    (∀ i, r ^ 2 < (aaOfReal ξ i + (H.w6TorusKam ε₀ θ ξ).2.1 i).re) ∧
      H.w6TorusBk ε₀ θ ξ ∈ birkBall1 m 1 := by
  obtain ⟨-, -, hcl, -⟩ := H.w6ToriKam hlo hhi
  have hw := (hcl θ hθ ξ hξ).1
  have hξP : ξ ∈ Pi := (H.mem_of_mem_wavePiStar hξ).1
  have hη := H.prepStepHyp.hη
  have hη0 := H.prepStepHyp.hη0
  have hr := H.hr
  have hsub : kamDomain (w6S - 4 * w6SigmaP) (2 * w6EtaP α ε * r) ⊆ kamDomain (1 / 8) r :=
    kamDomain_mono (by rw [w6SigmaP_val]; unfold w6S; norm_num) (by positivity)
      (by nlinarith)
  have hnorm : ‖aaOfReal ξ‖ ≤ t := by
    have := norm_aaOfReal_sub ξ 0
    simp only [sub_zero] at this
    have e : aaOfReal ξ - aaOfReal 0 = aaOfReal ξ := by ext i; simp
    rw [e] at this
    rw [this]; exact (hPi ξ hξP).2
  have hre : ∀ i, 2 * r ^ 2 ≤ (aaOfReal ξ i).re := fun i => by simpa using (hPi ξ hξP).1 i
  exact ⟨(aaMap_domain le_rfl hr ht _ hnorm hre (hsub hw)).1,
    aaMap_mem_birkBall1 m hm le_rfl hr ht hρ₁ _ hnorm hre (hsub hw)⟩

/-- **(i)** (`bpW:w6:tori` (i), step `t-hol`): for `ξ ∈ Π_*`, `Ψ̃_ξ` is holomorphic on `T_{s_0/2}`
with values in `B_{ρ₁}`, `1`-periodic, `ϱ Ψ̃_ξ(θ) = Ψ̃_ξ(θ)` for real `θ`, and its normal part lies
in `𝔚^{p+1/2}` (it is `ι_{p+1/2 → p} y`). -/
theorem w6TorusBk_hol (H : W6PrepHyp m hm Pi α r ε P X) (hlo : w6EpsFlat α ε ≤ ε₀)
    (hhi : ε₀ ≤ w6Gamma1 m hm * alphaCheck α) (ht : 0 < t)
    (hPi : ∀ ξ ∈ Pi, (∀ i, 2 * r ^ 2 ≤ ξ i) ∧ ‖ξ‖ ≤ t)
    (hρ₁ : aaCA * (t + r ^ 2) < birkRho1 m 1 ^ 2) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ H.wavePiStar ε₀) :
    DifferentiableOn ℂ (fun θ => H.w6TorusBk ε₀ θ ξ) (complexStrip 2 (w6S0 / 2)) ∧
    (∀ θ ∈ complexStrip 2 (w6S0 / 2), H.w6TorusBk ε₀ θ ξ ∈ birkBall1 m 1) ∧
    (∀ θ ∈ complexStrip 2 (w6S0 / 2), ∀ i : Fin 2,
      H.w6TorusBk ε₀ (θ + _root_.Pi.single i 1) ξ = H.w6TorusBk ε₀ θ ξ) ∧
    (∀ x : Fin 2 → ℝ, birkRho (H.w6TorusBk ε₀ (aaOfReal x) ξ) = H.w6TorusBk ε₀ (aaOfReal x) ξ) ∧
    ∀ θ ∈ complexStrip 2 (w6S0 / 2), ∃ y : BirkSpace,
      birkNormalPart (H.w6TorusBk ε₀ θ ξ) = birkEmbed 1 (3 / 2) 1 (by norm_num) y := by
  obtain ⟨hi, -, hcl, -⟩ := H.w6ToriKam hlo hhi
  obtain ⟨hd, hper, hreal⟩ := hi ξ hξ
  have hT := w6_strip_half_subset (w6WaveSeq m hm α r ε ε₀) rfl
  have hTo : IsOpen (complexStrip 2 (w6WaveSeq m hm α r ε ε₀).sInfty) := isOpen_complexStrip 2 _
  have hdom := fun θ (hθ : θ ∈ complexStrip 2 (w6WaveSeq m hm α r ε ε₀).sInfty) =>
    H.w6TorusKam_aaDom hlo hhi ht hPi hρ₁ hθ hξ
  have hpos : ∀ θ ∈ complexStrip 2 (w6WaveSeq m hm α r ε ε₀).sInfty, ∀ i,
      0 < (aaOfReal ξ i + (H.w6TorusKam ε₀ θ ξ).2.1 i).re := fun θ hθ i =>
    lt_of_le_of_lt (sq_nonneg r) ((hdom θ hθ).1 i)
  refine ⟨fun θ hθ => ?_, fun θ hθ => (hdom θ (hT hθ)).2, fun θ hθ i => ?_, fun x => ?_,
    fun θ hθ => ?_⟩
  · have h1 := (hd.differentiableAt (hTo.mem_nhds (hT hθ))).hasFDerivAt
    exact ((hasFDerivAt_aaMap 1 1 (hpos θ (hT hθ))).comp θ h1).differentiableAt
      |>.differentiableWithinAt
  · unfold w6TorusBk
    rw [hper θ (hT hθ) i, aaMap_add_tau]
  · have hx := hT (w6_real_mem_strip_half x)
    unfold w6TorusBk
    refine aaMap_real 1 1 ξ _ (hreal x) fun i => ?_
    have := hpos _ hx i
    simpa [aaOfReal] using this
  · obtain ⟨-, V, hV, -⟩ := hcl θ (hT hθ) ξ hξ
    have hw : H.w6TorusKam ε₀ θ ξ = w6TorusPt θ + w6Iota V := by rw [← hV]; abel
    refine ⟨aaNormal V, ?_⟩
    unfold w6TorusBk
    rw [birkNormalPart_aaMap, hw, map_add, aaNormal_w6TorusPt, zero_add]
    exact aaNormal_kamHomEmbed _ V

/-- **(ii)** (`bpW:w6:tori` (ii), step `t-cont`): `(ξ, θ) ↦ Ψ̃_ξ(θ)` is continuous on
`Π_* × ℝ²`. -/
theorem w6TorusBk_cont (H : W6PrepHyp m hm Pi α r ε P X) (hlo : w6EpsFlat α ε ≤ ε₀)
    (hhi : ε₀ ≤ w6Gamma1 m hm * alphaCheck α) (ht : 0 < t)
    (hPi : ∀ ξ ∈ Pi, (∀ i, 2 * r ^ 2 ≤ ξ i) ∧ ‖ξ‖ ≤ t)
    (hρ₁ : aaCA * (t + r ^ 2) < birkRho1 m 1 ^ 2) :
    ContinuousOn (fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) => H.w6TorusBk ε₀ (aaOfReal q.2) q.1)
      (H.wavePiStar ε₀ ×ˢ univ) := by
  obtain ⟨-, hcont, -, -⟩ := H.w6ToriKam hlo hhi
  have hT := w6_strip_half_subset (w6WaveSeq m hm α r ε ε₀) rfl
  have hTr : ∀ x, aaOfReal x ∈ complexStrip 2 (w6WaveSeq m hm α r ε ε₀).sInfty := fun x =>
    hT (w6_real_mem_strip_half x)
  have hD : ∀ ξ ∈ H.wavePiStar ε₀, ∀ x, ∀ i,
      0 < (aaOfReal ξ i + (H.w6TorusKam ε₀ (aaOfReal x) ξ).2.1 i).re := fun ξ hξ x i =>
    lt_of_le_of_lt (sq_nonneg r) ((H.w6TorusKam_aaDom hlo hhi ht hPi hρ₁ (hTr x) hξ).1 i)
  have key := w6_continuousOn_aaMap_comp
    (F := fun q : (Fin 2 → ℂ) × (Fin 2 → ℝ) => H.w6TorusKam ε₀ q.1 q.2) hcont hTr hD
  exact key

/-- **(iv)** (`bpW:w6:tori` (iv), step `t-close`): on `T_{s_0/2}`,
`Φ_P(Φ_*(θ)) = (θ + X(θ), y(θ), u(θ), v(θ))` (`= ιθ + ιV`, `V ∈ 𝒫^{p_+}`) with `|X| ≤ e_tor`,
`|y| ≤ r² e_tor`, `‖u‖_{a,p+1/2} + ‖v‖_{a,p+1/2} ≤ r e_tor`; hence
`Ψ̃_ξ(θ)_{±i} = √(ξ_i + y_i(θ)) e^{∓2πi(θ_i + X_i(θ))}` and `‖Ψ̃̂_ξ(θ)‖ ≤ r e_tor`. -/
theorem w6TorusBk_close (H : W6PrepHyp m hm Pi α r ε P X) (hlo : w6EpsFlat α ε ≤ ε₀)
    (hhi : ε₀ ≤ w6Gamma1 m hm * alphaCheck α) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ H.wavePiStar ε₀)
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (w6S0 / 2)) :
    ∃ V : KamPhase, H.w6TorusKam ε₀ θ ξ = w6TorusPt θ + w6Iota V ∧
      ‖V.1‖ ≤ w6Etor m hm α r ε ε₀ ∧ ‖V.2.1‖ ≤ r ^ 2 * w6Etor m hm α r ε ε₀ ∧
      ‖V.2.2.1‖ + ‖V.2.2.2‖ ≤ r * w6Etor m hm α r ε ε₀ ∧
      (∀ (b : Bool) (i : Fin 2), birkCoord 1 1 (H.w6TorusBk ε₀ θ ξ) (b, modeIdx i) =
        aaSqrt ((ξ i : ℂ) + V.2.1 i) *
          cexp (-(birkSgn (b, modeIdx i)) * (2 * π * I * (θ i + V.1 i)))) ∧
      ‖birkNormalPart (H.w6TorusBk ε₀ θ ξ)‖ ≤ r * w6Etor m hm α r ε ε₀ := by
  obtain ⟨-, -, hcl, -⟩ := H.w6ToriKam hlo hhi
  have hT := w6_strip_half_subset (w6WaveSeq m hm α r ε ε₀) rfl
  obtain ⟨-, V, hV, hVb⟩ := hcl θ (hT hθ) ξ hξ
  have hw : H.w6TorusKam ε₀ θ ξ = w6TorusPt θ + w6Iota V := by rw [← hV]; abel
  have hr := H.hr
  unfold kamNorm at hVb
  have n1 := norm_nonneg V.1
  have n2 : 0 ≤ ‖V.2.1‖ / r ^ 2 := by positivity
  have n3 : 0 ≤ ‖V.2.2.1‖ / r := by positivity
  have n4 : 0 ≤ ‖V.2.2.2‖ / r := by positivity
  have hy : ‖V.2.1‖ ≤ r ^ 2 * w6Etor m hm α r ε ε₀ := by
    have : ‖V.2.1‖ / r ^ 2 ≤ w6Etor m hm α r ε ε₀ := by linarith
    rw [div_le_iff₀ (by positivity)] at this; linarith
  have huv : ‖V.2.2.1‖ + ‖V.2.2.2‖ ≤ r * w6Etor m hm α r ε ε₀ := by
    have : (‖V.2.2.1‖ + ‖V.2.2.2‖) / r ≤ w6Etor m hm α r ε ε₀ := by rw [add_div]; linarith
    rw [div_le_iff₀ hr] at this; linarith
  refine ⟨V, hw, by linarith, hy, huv, fun b i => ?_, ?_⟩
  · unfold w6TorusBk
    rw [birkCoord_aaMap_tan, hw]
    simp only [aaTanCoord, w6TorusPt, w6Iota, kamHomEmbed_apply, Prod.fst_add, Prod.snd_add,
      _root_.Pi.add_apply, _root_.Pi.zero_apply, zero_add, aaOfReal]
  · unfold w6TorusBk
    rw [birkNormalPart_aaMap, hw, map_add, aaNormal_w6TorusPt, zero_add]
    refine (aaNormal_norm_le _).trans ?_
    simp only [w6Iota, kamHomEmbed_apply]
    have := norm_homEmbed_gen_apply_le (a := 1) w6_one_le_three_halves V.2.2.1
    have := norm_homEmbed_gen_apply_le (a := 1) w6_one_le_three_halves V.2.2.2
    linarith

end W6PrepHyp

end KAM.Wave
