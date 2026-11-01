/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.ConvTorus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: convergence of the transformations (blueprint `bpW:w6:convergence` (iii), (iv))

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:convergence` (clauses (iii) and (iv)).

* `w6ConvTorusIt` (`bpW:w6:convergence` (iii)) for an iteration with the hypotheses of every stage
  (`W6IterHyp`), and `w6ConvOps` ((iv));
* `w6IterHyp_of_conv`: the iteration of Proposition `bpW:w6:convergence` (`W6ConvHyp`, started at
  `w6Start`) has these hypotheses (step `c-ind`, `w6Seq_stage`), so `w6ConvTorus` and
  `w6ConvOpsSrc` are the clauses for the source data.

Model: `𝒫` is `KamPhase` (product norm, equivalent to `|·|_{p,r}`), `𝒫^{p_+} = range ι`
(`w6Iota`), a point `ιθ = (θ,0,0,0)` (`w6TorusPt`), `T_{s'} = complexStrip 2 s'`. "Periodic"
is `Φ(θ + e_i) = Φ(θ) + τ_i` for the unit vectors (`τ_i = stepTau i`), i.e. the error `Φ - ι` is
`1`-periodic in each `θ_i`; "real" is `StepReal` at real `θ` (real angle, action and normal
components; equivalently the error is real, since `ιθ` is). The derivative `∂_θ` is `fderiv ℂ` in
`θ`.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Wave

open KAM

section main

variable {d : W6SeqData} {S0 : W6State}

theorem w6_real_mem_strip (hd : W6State.Std d) (x : Fin 2 → ℝ) :
    (fun i => (x i : ℂ)) ∈ complexStrip 2 d.sInfty := fun i => by
  simp only [Complex.ofReal_im, abs_zero]
  unfold W6SeqData.sInfty; have := hd.1.s0_pos; positivity

theorem w6_add_single_mem_strip {s' : ℝ} {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 s')
    (i : Fin 2) : θ + Pi.single i 1 ∈ complexStrip 2 s' := fun k => by
  have := hθ k
  by_cases hk : k = i
  · subst hk; simpa using this
  · simpa [Pi.single_apply, hk] using this

/-- `B(θ, s_0/4) ⊆ T_{s_∞}` for `θ ∈ T_{s_0/2}`. -/
theorem w6_ball_subset_strip {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (d.s0 / 2)) :
    ball θ (d.s0 / 4) ⊆ complexStrip 2 d.sInfty := fun θ' hθ' k => by
  have h1 : |(θ' k - θ k).im| ≤ ‖θ' - θ‖ :=
    (Complex.abs_im_le_norm _).trans (norm_le_pi_norm (θ' - θ) k)
  have h2 : ‖θ' - θ‖ < d.s0 / 4 := by rw [← dist_eq_norm]; exact hθ'
  have h3 := hθ k
  rw [Complex.sub_im] at h1
  unfold W6SeqData.sInfty
  have := abs_sub_abs_le_abs_sub (θ' k).im (θ k).im
  linarith

/-- The clause (iii) of `bpW:w6:convergence` (transformations on the torus) for the iteration
started at `S₀`. With `T = T_{s_∞}`, `Π_* = ⋂_ν Π_ν`:
* for `ξ ∈ Π_*` and every `ν`, `θ ↦ Φ^ν(ιθ)` is holomorphic on `T`, periodic and real;
* `Φ^ν(ιθ) = ιθ + ιΨ^ν(ιθ)` and `|Ψ_*(θ) - Ψ^ν(ιθ)|_{p_+,r_0} ≤ e_Φ 8^{-ν}` on `T × Π_*`;
* `Φ^ν ∘ ι → Φ_*` uniformly on `T × Π_*`;
* `θ ↦ Φ_*(θ)` is holomorphic on `T`, periodic and real;
* `(θ, ξ) ↦ Φ_*(θ)` is continuous on `T × Π_*`;
* `Φ_*(θ) ∈ closure D(s_0 - 4σ_0, 2η_0 r_0) ⊆ D_0`;
* `Φ_*(θ) - ιθ = ι V` with `|V|_{p_+,r_0} ≤ e_Φ = 5 c_F ε_0/(α_0 σ_0^{t-1})`;
* `∂_θ(Φ^ν ∘ ι) → ∂_θ Φ_*` uniformly on `T_{s_0/2} × Π_*`. -/
def W6ConvTorusClause (d : W6SeqData) (S0 : W6State) : Prop :=
    (∀ ξ ∈ w6PiStarS d S0, ∀ ν,
      DifferentiableOn ℂ (fun θ => w6PhiC d S0 ν ξ (w6TorusPt θ)) (complexStrip 2 d.sInfty) ∧
      (∀ θ ∈ complexStrip 2 d.sInfty, ∀ i : Fin 2,
        w6PhiC d S0 ν ξ (w6TorusPt (θ + Pi.single i 1)) =
          w6PhiC d S0 ν ξ (w6TorusPt θ) + stepTau i) ∧
      ∀ x : Fin 2 → ℝ, StepReal (w6PhiC d S0 ν ξ (w6TorusPt fun i => (x i : ℂ)))) ∧
    (∀ θ ∈ complexStrip 2 d.sInfty, ∀ ξ ∈ w6PiStarS d S0, ∀ ν,
      w6PhiC d S0 ν ξ (w6TorusPt θ) = w6TorusPt θ + w6Iota (w6PsiT d S0 ν θ ξ) ∧
      kamNorm (d.rNu 0) (w6PsiStar d S0 θ ξ - w6PsiT d S0 ν θ ξ) ≤ d.ePhi / 8 ^ ν) ∧
    TendstoUniformlyOn (fun ν (q : (Fin 2 → ℂ) × (Fin 2 → ℝ)) => w6PhiC d S0 ν q.2 (w6TorusPt q.1))
      (fun q => w6PhiStar d S0 q.1 q.2) atTop (complexStrip 2 d.sInfty ×ˢ w6PiStarS d S0) ∧
    (∀ ξ ∈ w6PiStarS d S0,
      DifferentiableOn ℂ (fun θ => w6PhiStar d S0 θ ξ) (complexStrip 2 d.sInfty) ∧
      (∀ θ ∈ complexStrip 2 d.sInfty, ∀ i : Fin 2,
        w6PhiStar d S0 (θ + Pi.single i 1) ξ = w6PhiStar d S0 θ ξ + stepTau i) ∧
      ∀ x : Fin 2 → ℝ, StepReal (w6PhiStar d S0 (fun i => (x i : ℂ)) ξ)) ∧
    ContinuousOn (fun q : (Fin 2 → ℂ) × (Fin 2 → ℝ) => w6PhiStar d S0 q.1 q.2)
      (complexStrip 2 d.sInfty ×ˢ w6PiStarS d S0) ∧
    (∀ θ ∈ complexStrip 2 d.sInfty, ∀ ξ ∈ w6PiStarS d S0,
      w6PhiStar d S0 θ ξ ∈ closure (kamDomain (d.s 0 - 4 * d.sigma 0) (2 * d.etaNu 0 * d.rNu 0))) ∧
    closure (kamDomain (d.s 0 - 4 * d.sigma 0) (2 * d.etaNu 0 * d.rNu 0)) ⊆ d.domNu 0 ∧
    (∀ θ ∈ complexStrip 2 d.sInfty, ∀ ξ ∈ w6PiStarS d S0, ∃ V : KamPhase,
      w6PhiStar d S0 θ ξ - w6TorusPt θ = w6Iota V ∧ kamNorm (d.rNu 0) V ≤ d.ePhi) ∧
    TendstoUniformlyOn
      (fun ν (q : (Fin 2 → ℂ) × (Fin 2 → ℝ)) =>
        fderiv ℂ (fun θ => w6PhiC d S0 ν q.2 (w6TorusPt θ)) q.1)
      (fun q => fderiv ℂ (fun θ => w6PhiStar d S0 θ q.2) q.1) atTop
      (complexStrip 2 (d.s0 / 2) ×ˢ w6PiStarS d S0)

/-- **Transformations on the torus** (blueprint `bpW:w6:convergence` (iii)), for an iteration with
the hypotheses of every stage (`W6ConvTorusClause`). -/
theorem w6ConvTorusIt (hI : W6IterHyp d S0) : W6ConvTorusClause d S0 := by
  unfold W6ConvTorusClause
  have hd := hI.std
  have hr0 := W6SeqData.w6r_pos hd.1 0
  have hs0 := hd.1.s0_pos
  set T := complexStrip 2 d.sInfty
  set PS := w6PiStarS d S0
  have hTo : IsOpen T := isOpen_complexStrip 2 _
  have hunifξ : ∀ ξ ∈ PS, TendstoUniformlyOn (fun ν θ => w6PhiC d S0 ν ξ (w6TorusPt θ))
      (fun θ => w6PhiStar d S0 θ ξ) atTop T := fun ξ hξ =>
    w6_tendstoUniformlyOn_geom (K := w6Cr d * d.ePhi) fun n θ hθ => w6PhiT_sub_le hI hθ hξ n
  have hhol : ∀ ξ ∈ PS, DifferentiableOn ℂ (fun θ => w6PhiStar d S0 θ ξ) T := fun ξ hξ =>
    (holomorphic_of_tendstoUniformlyOn hTo (fun n => w6PhiT_differentiableOn hI hξ n)
      (hunifξ ξ hξ)).1
  have hRP : ∀ ξ ∈ PS, ∀ ν θ, θ ∈ T → _ := fun ξ hξ ν θ hθ =>
    w6Compose_real_periodic hI ν ξ (w6PiStarS_mem hξ ν) _ (w6TorusPt_mem hd hθ ν)
  have hper : ∀ ξ ∈ PS, ∀ ν, ∀ θ ∈ T, ∀ i : Fin 2,
      w6PhiC d S0 ν ξ (w6TorusPt (θ + Pi.single i 1)) =
        w6PhiC d S0 ν ξ (w6TorusPt θ) + stepTau i := fun ξ hξ ν θ hθ i => by
    rw [w6TorusPt_add_single]; exact (hRP ξ hξ ν θ hθ).2 i
  have hreal : ∀ ξ ∈ PS, ∀ ν, ∀ x : Fin 2 → ℝ,
      StepReal (w6PhiC d S0 ν ξ (w6TorusPt fun i => (x i : ℂ))) := fun ξ hξ ν x =>
    (hRP ξ hξ ν _ (w6_real_mem_strip hd x)).1 (stepReal_w6TorusPt x)
  have hunif : TendstoUniformlyOn
      (fun ν (q : (Fin 2 → ℂ) × (Fin 2 → ℝ)) => w6PhiC d S0 ν q.2 (w6TorusPt q.1))
      (fun q => w6PhiStar d S0 q.1 q.2) atTop (T ×ˢ PS) :=
    w6_tendstoUniformlyOn_geom (K := w6Cr d * d.ePhi) fun n q hq => w6PhiT_sub_le hI hq.1 hq.2 n
  refine ⟨fun ξ hξ ν => ⟨w6PhiT_differentiableOn hI hξ ν, hper ξ hξ ν, hreal ξ hξ ν⟩,
    fun θ hθ ξ hξ ν => ⟨w6PhiT_eq hI hθ hξ ν, (w6PsiC_tail hI hθ hξ).2 ν⟩, hunif,
    fun ξ hξ => ⟨hhol ξ hξ, fun θ hθ i => ?_, fun x => ?_⟩, ?_, fun θ hθ ξ hξ => ?_, ?_,
    fun θ hθ ξ hξ => ?_, ?_⟩
  · -- periodicity of the limit
    have h1 := w6PhiT_tendsto hI (w6_add_single_mem_strip hθ i) hξ
    have h2 := (w6PhiT_tendsto hI hθ hξ).add_const (stepTau i)
    exact tendsto_nhds_unique h1 (h2.congr fun n => (hper ξ hξ n θ hθ i).symm)
  · -- reality of the limit
    exact isClosed_stepReal.mem_of_tendsto (w6PhiT_tendsto hI (w6_real_mem_strip hd x) hξ)
      (Eventually.of_forall fun n => hreal ξ hξ n x)
  · -- joint continuity
    refine hunif.continuousOn (Frequently.of_forall fun n => ?_)
    refine (w6PhiC_continuousOn hI n).comp
      ((w6TorusCLM.continuous.comp continuous_fst).prodMk continuous_snd).continuousOn
      fun q hq => ⟨w6TorusPt_mem hd hq.1 n, hq.2⟩
  · -- values in the closure
    refine mem_closure_of_tendsto (w6PhiT_tendsto hI hθ hξ) (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact w6PhiC_mem_image hI m ξ (w6PiStarS_mem hξ _) _ (w6TorusPt_mem hd hθ _)
  · have hη := W6SeqData.eta_le hd.1 hd.2 0
    have hη0 := W6SeqData.eta_pos hd.1 0
    exact closure_kamDomain_subset (by linarith [W6SeqData.sigmaNu_pos hd.1 0]) (by positivity)
      (by nlinarith)
  · -- the bound `e_Φ`
    refine ⟨w6PsiStar d S0 θ ξ, by unfold w6PhiStar; abel, ?_⟩
    have h := (w6PsiC_tail hI hθ hξ).2 0
    have e : w6PsiT d S0 0 θ ξ = 0 := rfl
    rw [e, sub_zero, pow_zero, div_one] at h
    exact h
  · -- uniform convergence of the derivatives on `T_{s_0/2} × Π_*`
    refine w6_tendstoUniformlyOn_geom (K := w6Cr d * d.ePhi / (d.s0 / 4)) fun n q hq => ?_
    obtain ⟨θ, ξ⟩ := q
    obtain ⟨hθ, hξ⟩ := hq
    have hball := w6_ball_subset_strip (d := d) hθ
    have hθT : θ ∈ T := hball (mem_ball_self (by positivity))
    have hdg := (hhol ξ hξ).differentiableAt (hTo.mem_nhds hθT)
    have hdf := (w6PhiT_differentiableOn hI hξ n).differentiableAt (hTo.mem_nhds hθT)
    simp only
    rw [← fderiv_sub hdg hdf]
    have hb := norm_fderiv_le_div_of_ball (f := fun θ' => w6PhiStar d S0 θ' ξ -
        w6PhiC d S0 n ξ (w6TorusPt θ')) (v := θ) (by positivity : 0 < d.s0 / 4)
      (by have := w6Cr_pos (d := d); have := w6ePhi_nonneg hd; positivity :
        0 ≤ w6Cr d * d.ePhi * (1 / 8) ^ n)
      (((hhol ξ hξ).sub (w6PhiT_differentiableOn hI hξ n)).mono hball)
      (fun θ' hθ' => w6PhiT_sub_le hI (hball hθ') hξ n)
    refine hb.trans (le_of_eq ?_)
    ring

/-- **Operator bounds** (blueprint `bpW:w6:convergence` (iv)) for an iteration with the hypotheses
of every stage: for `ξ ∈ Π_μ` (`μ < ν`), `Φ^ν` is holomorphic on `D_ν` and for `w ∈ D_ν`:
`|DΦ^ν(w)W|_{q,r_0} ≤ 2|W|_{q,r_ν}` for `q ∈ {p, p_+}` (`DΦ^ν(w)` maps `𝒫^{p_+}` into itself),
`DΦ^ν(w)` is symplectic and maps `𝒫^{p_+}` onto `𝒫^{p_+}`. -/
theorem w6ConvOps (hI : W6IterHyp d S0) (ν : ℕ) (ξ : Fin 2 → ℝ)
    (hξ : ∀ μ < ν, ξ ∈ (w6Seq d S0 μ).Pi) :
    DifferentiableOn ℂ (w6PhiC d S0 ν ξ) (d.domNu ν) ∧
    ∀ w ∈ d.domNu ν,
      (∀ W, kamNorm (d.rNu 0) (fderiv ℂ (w6PhiC d S0 ν ξ) w W) ≤ 2 * kamNorm (d.rNu ν) W) ∧
      (∀ W', ∃ W'', fderiv ℂ (w6PhiC d S0 ν ξ) w (w6Iota W') = w6Iota W'' ∧
        kamNorm (d.rNu 0) W'' ≤ 2 * kamNorm (d.rNu ν) W') ∧
      (∀ W W', w6Symp (fderiv ℂ (w6PhiC d S0 ν ξ) w W) (fderiv ℂ (w6PhiC d S0 ν ξ) w W') =
        w6Symp W W') ∧
      (∀ W'', ∃ W', fderiv ℂ (w6PhiC d S0 ν ξ) w (w6Iota W') = w6Iota W'') :=
  w6Compose_ops hI ν ξ hξ

end main

section src

variable {d : W6SeqData} {Pm : Set (Fin 2 → ℝ)} {ω0 : (Fin 2 → ℝ) → Fin 2 → ℝ}
  {Ω0 : (Fin 2 → ℝ) → ℕ+ → ℝ} {P0 : (Fin 2 → ℝ) → KamPhase → ℂ}
  {X0 : (Fin 2 → ℝ) → KamPhase → KamPhase} {β₀ : ℝ}

/-- The iteration of Proposition `bpW:w6:convergence` has the hypotheses of every stage (step
`c-ind`). -/
theorem w6IterHyp_of_conv (hS : W6StepSmooth) (hC : W6ConvHyp d Pm ω0 Ω0 P0 X0 β₀) :
    W6IterHyp d (w6Start d Pm ω0 Ω0 P0 X0) :=
  ⟨⟨hC.valid, hC.small⟩, w6Seq_stage hC, hS⟩

/-- **Transformations on the torus** (blueprint `bpW:w6:convergence` (iii)) for the data of the
proposition (`W6ConvHyp`, `Π_{-1} = Pm`, the iteration `w6Seq` started at `w6Start`); conditional
helper on the W5 dependency `W6StepSmooth`. -/
theorem w6ConvTorus_of_stepSmooth (hS : W6StepSmooth) (hC : W6ConvHyp d Pm ω0 Ω0 P0 X0 β₀) :
    W6ConvTorusClause d (w6Start d Pm ω0 Ω0 P0 X0) :=
  w6ConvTorusIt (w6IterHyp_of_conv hS hC)

/-- **Operator bounds** (blueprint `bpW:w6:convergence` (iv)) for the data of the proposition;
conditional helper on the W5 dependency `W6StepSmooth`. -/
theorem w6ConvOpsSrc_of_stepSmooth (hS : W6StepSmooth) (hC : W6ConvHyp d Pm ω0 Ω0 P0 X0 β₀)
    (ν : ℕ) (ξ : Fin 2 → ℝ)
    (hξ : ∀ μ < ν, ξ ∈ (w6Seq d (w6Start d Pm ω0 Ω0 P0 X0) μ).Pi) :
    DifferentiableOn ℂ (w6PhiC d (w6Start d Pm ω0 Ω0 P0 X0) ν ξ) (d.domNu ν) ∧
    ∀ w ∈ d.domNu ν,
      (∀ W, kamNorm (d.rNu 0) (fderiv ℂ (w6PhiC d (w6Start d Pm ω0 Ω0 P0 X0) ν ξ) w W) ≤
        2 * kamNorm (d.rNu ν) W) ∧
      (∀ W', ∃ W'', fderiv ℂ (w6PhiC d (w6Start d Pm ω0 Ω0 P0 X0) ν ξ) w (w6Iota W') =
        w6Iota W'' ∧ kamNorm (d.rNu 0) W'' ≤ 2 * kamNorm (d.rNu ν) W') ∧
      (∀ W W', w6Symp (fderiv ℂ (w6PhiC d (w6Start d Pm ω0 Ω0 P0 X0) ν ξ) w W)
        (fderiv ℂ (w6PhiC d (w6Start d Pm ω0 Ω0 P0 X0) ν ξ) w W') = w6Symp W W') ∧
      (∀ W'', ∃ W', fderiv ℂ (w6PhiC d (w6Start d Pm ω0 Ω0 P0 X0) ν ξ) w (w6Iota W') =
        w6Iota W'') :=
  w6ConvOps (w6IterHyp_of_conv hS hC) ν ξ hξ

/-- `Π_*` here is W6-ITER's `w6PiStarIt`. -/
theorem w6PiStarS_eq_It (S0 : W6State) : w6PiStarS d S0 = w6PiStarIt d S0 := rfl

end src

end KAM.Wave
