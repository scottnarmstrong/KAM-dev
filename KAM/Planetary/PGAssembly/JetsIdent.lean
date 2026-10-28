/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.AnalyticTaylor
public import KAM.Planetary.PGAssembly.JetsDefs
public import KAM.Planetary.PGAssembly.JetsAverage
public import KAM.Planetary.PGAssembly.JetsReal
public import KAM.Planetary.PGAssembly.JetsPoly
public import KAM.Planetary.PGAssembly.JetsFourth

/-!
# P Part 5: identification of the jets on the real slice (`bpP:p5:be-coef`)

For `mu ∈ [0, mu0]` and `I ∈ V` the complex average restricted to real vectors is the frozen
`secularAverage`, so by `HasSecularBirkhoffForm` the real remainder `birkRem` is analytic and
`o(‖y‖⁴)`; `fourth_jet_unique` then makes the real jets of the average those of the Birkhoff
polynomial, which identifies `jetP0`, `jetOmega`, `jetBeta` with `P0`, `Omega`, `beta`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-JET.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology
open scoped BigOperators

namespace KAM.Planetary

variable {a b : ℕ}

theorem pgOscRadius_pos (d : PGData a b) : 0 < pgOscRadius d :=
  lt_min (half_pos d.hr0) (by have := (pgExtension d).delta_pos; positivity)

theorem mem_avgDom_zero (d : PGData a b) {I : Fin a → ℂ}
    (hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) :
    (I, (0 : PGComplexPhase b)) ∈ avgDom d :=
  ⟨hI, by simpa using pgOscRadius_pos d⟩

theorem realInclusion_mem_tube (d : PGData a b) {I : Fin a → ℝ} (hI : I ∈ closure d.V) :
    KAM.realInclusion a I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2) := by
  refine ⟨I, hI, ?_⟩
  have : KAM.realInclusion a I - (fun i => (I i : ℂ)) = 0 := by
    funext i; simp
  rw [this, norm_zero]
  have := (pgExtension d).delta_pos
  positivity

theorem complexAverage_analyticAt (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℂ} (hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) :
    AnalyticAt ℂ (complexAverage d mu I) 0 := by
  have han := KAM.analyticOnNhd_of_differentiableOn (isOpen_avgDom d)
    (avgFun_differentiableOn d hmu) (I, (0 : PGComplexPhase b)) (mem_avgDom_zero d hI)
  exact han.comp_of_eq (AnalyticAt.prod (analyticAt_const (v := I)) analyticAt_id) rfl

/-- The average restricted to real vectors `y = (q, p)`. -/
def realAvg (d : PGData a b) (mu : ℝ) (I : Fin a → ℝ) (y : RY b) : ℝ :=
  secularAverage d.P mu I y.2 y.1

/-- The Birkhoff polynomial with the frozen data `P0, Omega, beta`. -/
def birkPoly (d : PGData a b) (mu : ℝ) (I : Fin a → ℝ) : RY b → ℝ :=
  oscPoly (d.P0 mu I) (d.Omega mu I) (d.beta mu I)

/-- The real remainder. -/
def birkRem (d : PGData a b) (mu : ℝ) (I : Fin a → ℝ) (y : RY b) : ℝ :=
  realAvg d mu I y - birkPoly d mu I y

theorem norm_swap_eq (y : RY b) : ‖(y.2, y.1)‖ = ‖y‖ := by
  rw [Prod.norm_def, Prod.norm_def, max_comm]

theorem complexAverage_realY (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℝ} (hI : I ∈ d.V) (y : RY b) (hy : ‖y‖ < pgOscRadius d) :
    complexAverage d mu (KAM.realInclusion a I) (KAM.realInclusion₂ b y) =
      (realAvg d mu I y : ℂ) := by
  have := complexAverage_real d mu hmu I hI y.2 y.1 (by rwa [norm_swap_eq])
  simpa [realAvg] using this

theorem complexAverage_realY_eventually (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℝ} (hI : I ∈ d.V) :
    ∀ᶠ y in 𝓝 (0 : RY b), complexAverage d mu (KAM.realInclusion a I)
      (KAM.realInclusion₂ b y) = (realAvg d mu I y : ℂ) := by
  filter_upwards [Metric.ball_mem_nhds (0 : RY b) (pgOscRadius_pos d)] with y hy
  exact complexAverage_realY d hmu hI y (by simpa using hy)

theorem realAvg_analyticAt (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℝ} (hI : I ∈ d.V) : AnalyticAt ℝ (realAvg d mu I) 0 := by
  have hA := (complexAverage_analyticAt d hmu
    (realInclusion_mem_tube d (subset_closure hI))).restrictScalars (𝕜 := ℝ)
  have hcomp : AnalyticAt ℝ (complexAverage d mu (KAM.realInclusion a I) ∘
      KAM.realInclusion₂ b) 0 :=
    hA.comp_of_eq ((KAM.realInclusion₂ b).analyticAt 0) (by simp)
  have hre : AnalyticAt ℝ (fun y : RY b => (complexAverage d mu (KAM.realInclusion a I)
      (KAM.realInclusion₂ b y)).re) 0 := (Complex.reCLM.analyticAt _).comp hcomp
  refine hre.congr ?_
  filter_upwards [complexAverage_realY_eventually d hmu hI] with y hy
  rw [hy]; simp

theorem birkRem_isLittleO (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℝ} (hI : I ∈ d.V) :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ y : RY b, ‖y‖ < delta → |birkRem d mu I y| ≤ eps * ‖y‖ ^ 4 := by
  intro eps heps
  obtain ⟨δ, hδ, -, h⟩ := (d.hBNF mu hmu I hI).2 eps heps
  refine ⟨δ / 2, by positivity, fun y hy => ?_⟩
  have hb : ∀ k, y.2 k ^ 2 + y.1 k ^ 2 < δ ^ 2 := fun k => by
    have h1 : |y.2 k| < δ / 2 := (by
      have := norm_le_pi_norm y.2 k
      rw [Real.norm_eq_abs] at this
      exact this.trans_lt ((le_max_right _ _).trans_lt hy))
    have h2 : |y.1 k| < δ / 2 := (by
      have := norm_le_pi_norm y.1 k
      rw [Real.norm_eq_abs] at this
      exact this.trans_lt ((le_max_left _ _).trans_lt hy))
    have e1 : y.2 k ^ 2 < (δ / 2) ^ 2 := by
      rw [← sq_abs]; exact pow_lt_pow_left₀ h1 (abs_nonneg _) (by norm_num)
    have e2 : y.1 k ^ 2 < (δ / 2) ^ 2 := by
      rw [← sq_abs]; exact pow_lt_pow_left₀ h2 (abs_nonneg _) (by norm_num)
    nlinarith
  have := h y.2 y.1 hb
  rw [norm_swap_eq] at this
  exact this

theorem iteratedFDeriv_realAvg_eq (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℝ} (hI : I ∈ d.V) (k : ℕ) (hk : k ≤ 4) :
    iteratedFDeriv ℝ k (realAvg d mu I) 0 = iteratedFDeriv ℝ k (birkPoly d mu I) 0 := by
  have hfa := realAvg_analyticAt d hmu hI
  have hpa : AnalyticAt ℝ (birkPoly d mu I) 0 := analyticAt_oscPoly _ _ _ 0
  have h0 := fourth_jet_unique_gen (hfa.sub hpa) (birkRem_isLittleO d hmu hI) k hk
  have e : iteratedFDeriv ℝ k (realAvg d mu I - birkPoly d mu I) 0 =
      iteratedFDeriv ℝ k (realAvg d mu I) 0 - iteratedFDeriv ℝ k (birkPoly d mu I) 0 :=
    iteratedFDeriv_sub_apply hfa.contDiffAt hpa.contDiffAt
  have h0' : iteratedFDeriv ℝ k (realAvg d mu I - birkPoly d mu I) 0 = 0 := h0
  rw [e] at h0'
  exact sub_eq_zero.1 h0'

theorem realInclusion₂_yvec (j : Fin b) :
    KAM.realInclusion₂ b (yvec b j) = ((0 : Fin b → ℂ), Pi.single j (1 : ℂ)) := by
  refine Prod.ext (by simp [yvec]) (funext fun k => ?_)
  by_cases h : k = j <;> simp [yvec, h]

theorem birkRem_zero (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℝ} (hI : I ∈ d.V) : birkRem d mu I 0 = 0 := by
  obtain ⟨δ, hδ, h⟩ := birkRem_isLittleO d hmu hI 1 one_pos
  have := h 0 (by simpa using hδ)
  simp at this
  exact this

theorem realAvg_zero (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℝ} (hI : I ∈ d.V) : realAvg d mu I 0 = d.P0 mu I := by
  have h := birkRem_zero d hmu hI
  unfold birkRem at h
  have : birkPoly d mu I 0 = d.P0 mu I := by
    simp [birkPoly, oscPoly, oscQ2, oscQ4, oscS]
  linarith

theorem jetP0_real (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℝ} (hI : I ∈ d.V) : jetP0 d mu (KAM.realInclusion a I) = (d.P0 mu I : ℂ) := by
  have := complexAverage_realY d hmu hI 0 (by simpa using pgOscRadius_pos d)
  rw [map_zero] at this
  rw [jetP0, this, realAvg_zero d hmu hI]

theorem jetOmega_real (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℝ} (hI : I ∈ d.V) (j : Fin b) :
    jetOmega d mu (KAM.realInclusion a I) j = (d.Omega mu I j : ℂ) := by
  have h := jet_real_restrict (complexAverage_analyticAt d hmu
    (realInclusion_mem_tube d (subset_closure hI)))
    (complexAverage_realY_eventually d hmu hI) 2 (fun _ => yvec b j)
  simp only [realInclusion₂_yvec] at h
  rw [jetOmega, h, iteratedFDeriv_realAvg_eq d hmu hI 2 (by norm_num), birkPoly,
    iteratedFDeriv_two_oscPoly, oscQ2_yvec]
  push_cast
  ring

theorem jetBeta_real (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I : Fin a → ℝ} (hI : I ∈ d.V) (i j : Fin b) :
    jetBeta d mu (KAM.realInclusion a I) i j = (d.beta mu I i j : ℂ) := by
  have hA := complexAverage_analyticAt d hmu (realInclusion_mem_tube d (subset_closure hI))
  have hev := complexAverage_realY_eventually d hmu hI
  have h4 : ∀ y : RY b, iteratedFDeriv ℝ 4 (realAvg d mu I) 0 (fun _ => y) =
      24 * oscQ4 (d.beta mu I) y := fun y => by
    rw [iteratedFDeriv_realAvg_eq d hmu hI 4 le_rfl, birkPoly, iteratedFDeriv_four_oscPoly]
  unfold jetBeta
  by_cases hij : i = j
  · subst hij
    have h := jet_real_restrict hA hev 4 (fun _ => yvec b i)
    simp only [realInclusion₂_yvec] at h
    simp only [ite_true]
    rw [h, h4, oscQ4_yvec]
    push_cast
    ring
  · simp only [hij, ite_false]
    have htup : (fun k : Fin 4 => if k.val < 2 then
        ((0 : Fin b → ℂ), (Pi.single i (1 : ℂ) : Fin b → ℂ)) else
        ((0 : Fin b → ℂ), (Pi.single j (1 : ℂ) : Fin b → ℂ))) = fun k =>
        KAM.realInclusion₂ b (![yvec b i, yvec b i, yvec b j, yvec b j] k) := by
      funext k
      fin_cases k <;> simp [-KAM.realInclusion₂_apply, realInclusion₂_yvec]
    rw [htup, jet_real_restrict hA hev 4 ![yvec b i, yvec b i, yvec b j, yvec b j]]
    have hM : ∀ (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → RY b),
        iteratedFDeriv ℝ 4 (realAvg d mu I) 0 (v ∘ σ) = iteratedFDeriv ℝ 4 (realAvg d mu I) 0 v :=
      fun σ v => (realAvg_analyticAt d hmu hI).contDiffAt.iteratedFDeriv_comp_perm v σ
    rw [mixed_osc (d.beta mu I) (d.hsymm mu hmu I hI) i j hij _ hM h4]

end KAM.Planetary

end
