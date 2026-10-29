/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.Limit
public import KAM.Planetary.WeakKAM.ToriBridge

/-! # P11B tori: the field at the zero section of a finite stage

Source steps `lt-field` and `lt-cov` of `limit_torus`: at the zero section of stage `ν` the
Hamiltonian field of the initial Hamiltonian `H₀` at `Φ_ν(θ, 0)` equals
`DΦ_ν(θ, 0)` applied to `(ω_ν + ∂_η R_ν, -∂_θ R_ν)`, and the Cauchy bounds `ε_ν / s_ν` and
`ε_ν / r` for the two first-jet terms are small.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

/-- The initial Hamiltonian at the fixed real parameter `b`, in the shifted action `η`. -/
def toriH0 (d : SelectionData n) (f : SelectionPhaseC n → ℂ) (b : SelectionR n)
    (y : SelectionPhaseC n) : ℂ := selectionInitial d f (y, selectionReal b)

theorem tori_single_norm (i : Fin n) (w : ℂ) : ‖w • (Pi.single i 1 : Fin n → ℂ)‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem toriH0_diffAt (d : SelectionData n) {f : SelectionPhaseC n → ℂ} {ε : ℝ}
    (hf : SelectionPerturbation d f ε) {b : SelectionR n} (hb : b ∈ d.K)
    {y : SelectionPhaseC n} (hy : y.1 ∈ complexStrip n d.strip) (hη : ‖y.2‖ < d.ϑ) :
    DifferentiableAt ℂ (toriH0 d f b) y := by
  have hmem : ∀ y' : SelectionPhaseC n, ‖y'.2‖ < d.ϑ →
      selectionReal b + y'.2 ∈ actionNbhd d.K (2 * d.ϑ) := fun y' h' =>
    ⟨b, hb, by
      have : selectionReal b + y'.2 - (fun i => ((b i : ℝ) : ℂ)) = y'.2 := by
        funext i; simp [selectionReal]
      rw [this]; linarith [d.theta_pos]⟩
  have hshift : DifferentiableAt ℂ (fun y' : SelectionPhaseC n => selectionReal b + y'.2) y :=
    (differentiableAt_const _).add differentiableAt_snd
  have hopen : IsOpen (actionNbhd d.K (2 * d.ϑ)) := KAM.Head.isOpen_actionNbhd _ _
  have hh : DifferentiableAt ℂ d.h (selectionReal b + y.2) :=
    d.holo.differentiableAt (hopen.mem_nhds (hmem y hη))
  have hfo : IsOpen (complexStrip n d.strip ×ˢ actionNbhd d.K (2 * d.ϑ)) :=
    (KAM.isOpen_complexStrip n _).prod hopen
  have hff : DifferentiableAt ℂ f (y.1, selectionReal b + y.2) :=
    hf.holo.differentiableAt (hfo.mem_nhds ⟨hy, hmem y hη⟩)
  have h1 : DifferentiableAt ℂ (fun y' : SelectionPhaseC n => d.h (selectionReal b + y'.2)) y :=
    hh.comp y hshift
  have h2 : DifferentiableAt ℂ (fun y' : SelectionPhaseC n =>
      f (y'.1, selectionReal b + y'.2)) y :=
    hff.comp y (differentiableAt_fst.prodMk hshift)
  exact (h1.add h2).sub_const (d.h (selectionReal b))

section Stage
variable {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {a : SelectionSchedule n}
variable (cx : WeakBudgetCtx d a) (c : SelectionComposition d f a) {b : SelectionR n}

include cx

/-- Real points of the half strip are in the stage domain at the zero section (restated). -/
theorem tori_mem_dom (hb : b ∈ c.Kinf) (ν : ℕ) {θ : SelectionR n} :
    ((selectionReal θ, 0), selectionReal b) ∈ selectionCompDom a c.K ν :=
  selectionLim_mem cx c hb ν
    (selectionReal_mem_complexStrip (by linarith [cx.hyp.hstrip]) θ)

/-- The remainder at the fixed real parameter `b`. -/
def toriRem (ch : SelectionChain n) (ν : ℕ) (b : SelectionR n) (y : SelectionPhaseC n) : ℂ :=
  ch.R ν (y, selectionReal b)

/-- The first-jet vector `(ω_ν + ∂_η R_ν, -∂_θ R_ν)` at the zero section. -/
def toriJet (d : SelectionData n) (ch : SelectionChain n) (ν : ℕ) (b : SelectionR n)
    (z : SelectionPhaseC n) : SelectionPhaseC n :=
  (fun i => selectionFrequency d ch ν (selectionReal b) i +
      fderiv ℂ (toriRem ch ν b) z (0, Pi.single i 1),
    fun i => - fderiv ℂ (toriRem ch ν b) z (Pi.single i 1, 0))

theorem tori_s0_le_theta : a.s₀ ≤ d.ϑ := by
  have hadm := cx.adm
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast d.n_pos
  have hsq : 1 ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn
  have h1 := hadm.t_le
  have h2 := hadm.radius
  have ht := hadm.t_pos
  have h3 : a.t₀ ≤ d.ϑ := h1.trans (div_le_self d.theta_pos.le hsq)
  have h4 : a.t₀ / (8 * n) ≤ a.t₀ := div_le_self ht.le (by linarith)
  linarith

theorem tori_dom_mem (hb : b ∈ c.Kinf) (ν : ℕ) {p : SelectionPhaseC n}
    (hp1 : ∀ i, |(p.1 i).im| ≤ a.strip / 4) (hp2 : ‖p.2‖ ≤ selections a ν / 2) :
    (p, selectionReal b) ∈ selectionCompDom a c.K ν := by
  have hr := (iter_strip cx ν).1
  have hstrip := cx.hyp.hstrip
  have hs := wbud_s_pos cx.hyp ν
  refine ⟨fun i => ?_, by simp only; linarith, ?_⟩
  · exact (hp1 i).trans_lt (by linarith)
  · have hbK : b ∈ c.K ν := by
      have : b ∈ ⋂ j, c.K j := c.Kinf_eq ▸ hb
      exact mem_iInter.1 this ν
    refine ⟨b, hbK, ?_⟩
    rw [show selectionReal b - (fun i => ((b i : ℝ) : ℂ)) = 0 from sub_self _, norm_zero]
    exact wbud_t_pos cx ν

omit cx in
theorem tori_rem_diffAt (ν : ℕ) {y : SelectionPhaseC n}
    (hy : (y, selectionReal b) ∈ selectionCompDom a c.K ν) :
    DifferentiableAt ℂ (toriRem c.toSelectionChain ν b) y := by
  have h := (c.remainder_holo ν).differentiableAt
    ((isOpen_selectionCompDom a c.K ν).mem_nhds hy)
  exact h.comp y (differentiableAt_id.prodMk (differentiableAt_const _))

/-- Steps `lt-field`/`lt-cov` at finite stage: `X_{H₀}(Φ_ν z) = DΦ_ν(z) (jet)`. -/
theorem tori_stage_cov {ε : ℝ} (hf : SelectionPerturbation d f ε) (hb : b ∈ c.Kinf)
    (θ : SelectionR n) (ν : ℕ) :
    hamiltonianVectorFieldℂ (toriH0 d f b)
        (selectionCompose c.toSelectionChain (selectionReal b) ν (selectionReal θ, 0)) =
      fderiv ℂ (selectionCompose c.toSelectionChain (selectionReal b) ν) (selectionReal θ, 0)
        (toriJet d c.toSelectionChain ν b (selectionReal θ, 0)) := by
  set Φ := selectionCompose c.toSelectionChain (selectionReal b) ν with hΦdef
  set z : SelectionPhaseC n := (selectionReal θ, 0) with hz
  have hstrip := cx.hyp.hstrip
  have hθ : selectionReal θ ∈ complexStrip n (a.strip / 2) :=
    selectionReal_mem_complexStrip (by linarith) θ
  have hzdom := tori_mem_dom cx c hb ν (θ := θ)
  have hΦ : DifferentiableAt ℂ Φ z := selectionLim_fiber_diffAt cx c hb ν hθ
  have hbK : b ∈ d.K := by
    have h0 : b ∈ c.K 0 := by
      have : b ∈ ⋂ j, c.K j := c.Kinf_eq ▸ hb
      exact mem_iInter.1 this 0
    rwa [(c.chain 0).initial] at h0
  have hdom := c.composition_domain ν ((z, selectionReal b)) hzdom
  have hH0 : DifferentiableAt ℂ (toriH0 d f b) (Φ z) := by
    refine toriH0_diffAt d hf hbK ?_ ?_
    · rw [← cx.hstrip]; exact hdom.1
    · exact hdom.2.1.trans_le (tori_s0_le_theta cx)
  have hsymp : ∀ u v, Canonical.symplFormC (fderiv ℂ Φ z u) (fderiv ℂ Φ z v) =
      Canonical.symplFormC u v := fun u v =>
    c.composition_symplectic ν (z, selectionReal b) hzdom u v
  have hsurj : Function.Surjective (fderiv ℂ Φ z) := by
    refine tori_surjective_of_near_id _ ?_
    exact (c.composition_small ν (z, selectionReal b) hzdom).trans_lt (by norm_num)
  have hcov := tori_field_cov hΦ hH0 hsymp hsurj
  -- the field of `H₀ ∘ Φ` from the normal form
  have hρ : DifferentiableAt ℂ (toriRem c.toSelectionChain ν b) z := tori_rem_diffAt c ν hzdom
  set Lω : SelectionPhaseC n →L[ℂ] ℂ := ∑ j, selectionFrequency d c.toSelectionChain ν
    (selectionReal b) j • ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.snd ℂ (SelectionC n) (SelectionC n))) with hLω
  have hLωapply : ∀ y, Lω y = ∑ j, selectionFrequency d c.toSelectionChain ν
      (selectionReal b) j * y.2 j := fun y => by simp [hLω]
  have hk : HasFDerivAt (fun y : SelectionPhaseC n =>
      selectionEnergy c.toSelectionChain ν (selectionReal b) + Lω y +
        toriRem c.toSelectionChain ν b y) (Lω + fderiv ℂ (toriRem c.toSelectionChain ν b) z) z :=
    (((hasFDerivAt_const _ z).add Lω.hasFDerivAt).add hρ.hasFDerivAt).congr_fderiv (by simp)
  have hU : IsOpen {y : SelectionPhaseC n | (y, selectionReal b) ∈ selectionCompDom a c.K ν} :=
    (isOpen_selectionCompDom a c.K ν).preimage (continuous_id.prodMk continuous_const)
  have hev : (toriH0 d f b ∘ Φ) =ᶠ[𝓝 z] fun y : SelectionPhaseC n =>
      selectionEnergy c.toSelectionChain ν (selectionReal b) + Lω y +
        toriRem c.toSelectionChain ν b y := by
    filter_upwards [hU.mem_nhds hzdom] with y hy
    have := c.normal_form ν (y, selectionReal b) hy
    simp only [Function.comp_apply, hLωapply, toriH0, toriRem]
    exact this
  have hfd : fderiv ℂ (toriH0 d f b ∘ Φ) z =
      Lω + fderiv ℂ (toriRem c.toSelectionChain ν b) z := by
    rw [hev.fderiv_eq]; exact hk.fderiv
  have hfield : hamiltonianVectorFieldℂ (toriH0 d f b ∘ Φ) z =
      toriJet d c.toSelectionChain ν b z := by
    unfold hamiltonianVectorFieldℂ toriJet
    rw [hfd]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [hLωapply, Pi.single_apply]
    · simp [hLωapply]
  rw [← hcov, hfield]

/-- Cauchy bounds for the first jet of the remainder at the zero section (`lt-field`). -/
theorem tori_jet_bound (hb : b ∈ c.Kinf) (θ : SelectionR n) (ν : ℕ) :
    ‖toriJet d c.toSelectionChain ν b (selectionReal θ, 0) -
        (selectionFrequency d c.toSelectionChain ν (selectionReal b), 0)‖ ≤
      selectionε a ν / (selections a ν / 2) + selectionε a ν / (a.strip / 4) := by
  set z : SelectionPhaseC n := (selectionReal θ, 0) with hz
  have hstrip := cx.hyp.hstrip
  have hs := wbud_s_pos cx.hyp ν
  have hε := wbud_ε_pos cx.hyp ν
  have hzd : (z, selectionReal b) ∈ selectionCompDom a c.K ν := tori_mem_dom cx c hb ν
  -- the η-direction
  have hη : ∀ i, ‖fderiv ℂ (toriRem c.toSelectionChain ν b) z (0, Pi.single i 1)‖ ≤
      selectionε a ν / (selections a ν / 2) := fun i => by
    have hmem : ∀ w : ℂ, ‖w‖ ≤ selections a ν / 2 →
        (z + w • ((0 : SelectionC n), (Pi.single i 1 : SelectionC n)), selectionReal b) ∈
          selectionCompDom a c.K ν := fun w hw => by
      refine tori_dom_mem cx c hb ν ?_ ?_
      · intro j; simp [hz, selectionReal]; linarith
      · have := (tori_single_norm i w).trans hw
        simpa [hz] using this
    refine tori_cauchy_dir (by linarith) (fun w hw => tori_rem_diffAt c ν (hmem w hw))
      (fun w hw => ?_)
    exact c.remainder_bound ν _ (hmem w hw.le)
  have hθ : ∀ i, ‖fderiv ℂ (toriRem c.toSelectionChain ν b) z (Pi.single i 1, 0)‖ ≤
      selectionε a ν / (a.strip / 4) := fun i => by
    have hmem : ∀ w : ℂ, ‖w‖ ≤ a.strip / 4 →
        (z + w • ((Pi.single i 1 : SelectionC n), (0 : SelectionC n)), selectionReal b) ∈
          selectionCompDom a c.K ν := fun w hw => by
      refine tori_dom_mem cx c hb ν ?_ ?_
      · intro j
        have h1 := (Complex.abs_im_le_norm ((w • (Pi.single i 1 : SelectionC n)) j)).trans
          (norm_le_pi_norm (w • (Pi.single i 1 : SelectionC n)) j)
        simp only [hz, selectionReal, Prod.fst_add, Prod.smul_fst, Pi.add_apply,
          Complex.add_im, Complex.ofReal_im, zero_add]
        exact h1.trans ((tori_single_norm i w).trans hw)
      · simp [hz]; linarith
    refine tori_cauchy_dir (by linarith) (fun w hw => tori_rem_diffAt c ν (hmem w hw))
      (fun w hw => ?_)
    exact c.remainder_bound ν _ (hmem w hw.le)
  have h1 : 0 ≤ selectionε a ν / (selections a ν / 2) := by positivity
  have h2 : 0 ≤ selectionε a ν / (a.strip / 4) := by positivity
  have hdiff : toriJet d c.toSelectionChain ν b z -
      (selectionFrequency d c.toSelectionChain ν (selectionReal b), 0) =
      ((fun i => fderiv ℂ (toriRem c.toSelectionChain ν b) z (0, Pi.single i 1)),
        fun i => - fderiv ℂ (toriRem c.toSelectionChain ν b) z (Pi.single i 1, 0)) := by
    unfold toriJet
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp
  rw [hdiff, Prod.norm_def]
  refine max_le ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (hη i).trans ?_
    linarith
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [norm_neg]
    exact (hθ i).trans (by linarith)

end Stage

end KAM.Planetary

end
