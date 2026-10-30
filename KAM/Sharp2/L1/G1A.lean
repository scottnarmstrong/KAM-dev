/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.L1.EntryScheme
public import KAM.Sharp2.RouteA.G1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The v2 a-posteriori theorem, route A with the ℓ¹ entry (package B10c, route-A part of B10e)

Blueprint `bp:p2s2l1:g1A`, `bp:p2s2l1:frozen` of `blueprint/parts/p2s2-l1hybrid.tex`:

* `g1_core_AL1`: from `routeAOkL1` at `X⋆` and `e/(γ⁴ δ₀^{2a}) ≤ X⋆`, the conclusion of the frozen
  G1 (B9's `KAM.Sharp2.RouteA.g1_core_A` on the scheme with the ℓ¹ entry);
* `g1_branch_AL1`: the ℓ¹-entry branch of the frozen form;
* `c2AL1`, `G1BodyAL1`, `g1_v2A_l1`: the repaired signatures, verbatim. `g1_v2A_l1` takes the
  minimum of three branches — v1 (`sharpC1`), B9's sup route A (`routeAOk` at `X⋆_A`), the ℓ¹ entry
  (`routeAOkL1` at `X⋆`) — for `C₁` and the maximum for `C₂`, by cases (AUDIT-B10D-1, F6).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology KAM.Sharp.Engine

namespace KAM.Sharp2.L1

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2.RouteA

/-- `C₂` of the entry branch (the ball sum, no `γ̄²`). -/
def c2AL1 (N : NumA) (E : EntryA) (Xs : ℝ) : ℝ :=
  N.ρ ^ (2 * N.τ) * sumA (2 * N.τ) 3 N.ρ N.ρinf 1 (xSL1 N E Xs) (fun s => (stageL1 N E s).CD)
      (2 * N.τ) N.kp /
    (Xs * delta0 3 N.ρ N.ρinf ^ (4 * N.τ))

/-- The frozen G1 body with B9's refined data and certificates and the ℓ¹ entry hypotheses. -/
def G1BodyAL1 (N : NumA) (I : InitA) (E : EntryA) (M σK σB σT μ γbar C₁ C₂ : ℝ) : Prop :=
  ∀ (𝔅 : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ))) (h : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ)
    (K : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)) (ω : Fin N.n → ℝ) (γ e : ℝ)
    (Ω : Set (Fin N.n → ℝ)),
    IsOpen 𝔅 →
    (∀ z ∈ 𝔅, ∀ k : Fin N.n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ 𝔅) →
    DifferentiableOn ℂ h 𝔅 →
    (∀ z ∈ 𝔅, ∀ k : Fin N.n → ℤ, h (z.1 + (fun i => (k i : ℂ)), z.2) = h z) →
    (∀ θ I : Fin N.n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ 𝔅 →
      (h ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0) →
    (∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ h z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M) →
    DifferentiableOn ℂ K (complexStrip N.n N.ρ) → IsPrimaryOnStrip K N.ρ → IsRealOnReals K →
    (∀ θ ∈ complexStrip N.n N.ρ, Metric.ball (K θ) μ ⊆ 𝔅) →
    (∀ θ ∈ complexStrip N.n N.ρ, ‖fderiv ℂ K θ‖ ≤ σK - μ) →
    (∀ θ ∈ complexStrip N.n N.ρ, IsUnit (gramMatrix K θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ σB - μ) →
    IsUnit (torsionAverage h K ω).det →
    (∀ i, ∑ j, ‖(torsionAverage h K ω)⁻¹ i j‖ ≤ σT - μ) →
    RefHypA N I 𝔅 h K ω → ω ∈ Ω → N.Cert γ Ω → EntryHypA N E h K ω e →
    0 < γ → γ ≤ γbar → IsDiophantine γ N.τ ω →
    (∀ θ ∈ complexStrip N.n N.ρ, ‖invarianceError h K ω θ‖ ≤ e) →
    C₁ * e / (γ ^ 4 * N.ρ ^ (4 * N.τ)) < 1 →
    ∃ Kinf : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip N.n N.ρinf) ∧ IsPrimaryOnStrip Kinf N.ρinf ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, invarianceError h Kinf ω θ = 0) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, ‖fderiv ℂ Kinf θ‖ ≤ σK - μ / 2) ∧
      ∀ θ ∈ complexStrip N.n N.ρinf, ‖Kinf θ - K θ‖ ≤ C₂ * e / (γ ^ 2 * N.ρ ^ (2 * N.τ))

variable {N : NumA} {E : EntryA}

/-- Blueprint `bp:p2s2l1:g1A`: the run of route A with the ℓ¹ entry. -/
theorem g1_core_AL1 (hN : N.Wf) (hE : E.Wf) (hfix : N.iso = false) (hΘ : N.Θ = 0)
    {τ M μ γ e Xs : ℝ} {𝔅 : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ))}
    {h : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ} {ω : Fin N.n → ℝ} {Ω : Set (Fin N.n → ℝ)}
    {m₀ : Fin 8 → ℝ} {K : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)}
    (hS : Standing N.n τ M N.sK N.sB N.sT 𝔅 h ω γ)
    (hd1 : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ N.M1)
    (hd2 : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ N.M2)
    (hγb : γ ≤ N.γb) (hω : ω ∈ Ω) (hC : N.Cert γ Ω) (hμ : 0 < μ) (hm0 : m₀ 0 = 0)
    (hOk : routeAOkL1 N E (N.capV (μ / 2)) m₀ Xs)
    (h0 : AdmA 𝔅 h ω (N.r 0) (N.r 0 - N.δ 0) μ e (m₀ 1) (m₀ 2) (m₀ 3) (m₀ 4) (m₀ 5) (m₀ 6) (m₀ 7) K)
    (hEH : EntryHypA N E h K ω e)
    (hX : e / (γ ^ 4 * delta0 3 N.ρ N.ρinf ^ (2 * (2 * N.τ))) ≤ Xs) (hXpos : 0 < Xs) :
    ∃ Kinf : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip N.n N.ρinf) ∧ IsPrimaryOnStrip Kinf N.ρinf ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, invarianceError h Kinf ω θ = 0) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, ‖fderiv ℂ Kinf θ‖ ≤ N.sK) ∧
      ∀ θ ∈ complexStrip N.n N.ρinf, ‖Kinf θ - K θ‖ ≤
        c2AL1 N E Xs * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) := by
  have hγ := hS.gamma_pos
  have hρ0 : 0 < N.ρ := hN.ρinf_pos.trans hN.ρinf_lt
  have hb : μ / 2 < μ := by linarith
  have hNw := schemeAL1_isNewton hN hE hfix hΘ hS hd1 hd2 hγb hω hC hb
  have R := hOk.runData hN hE
  have h0' : (schemeAL1 N E 𝔅 h ω μ).Adm 0 e m₀ K := by
    refine ⟨?_, fun _ => hEH⟩
    show AdmA 𝔅 h ω (N.r 0) (N.r 0 - N.δ 0) (μ - m₀ 0) e (m₀ 1) (m₀ 2) (m₀ 3) (m₀ 4) (m₀ 5)
      (m₀ 6) (m₀ 7) K
    rw [hm0, sub_zero]
    exact h0
  have hlam : (0 : ℝ) < 3 := by norm_num
  have hit := SchemeA.run hNw R hlam hN.ρinf_lt hγ hγb h0' hX
  obtain ⟨hconv, hconvd, hholo, hprim, hreal, hclose, hclose', -, -, -, hεz⟩ :=
    SchemeA.limit hNw R hlam hN.ρinf_pos hN.ρinf_lt hγ hγb h0' hX
  have hsub : ∀ s, complexStrip N.n N.ρinf ⊆ complexStrip N.n (N.r s) := fun s =>
    Triangular.strip_mono (hN.ρinf_lt_r s).le
  -- the ball budget
  have hball : ∀ θ ∈ complexStrip N.n N.ρinf,
      ‖(schemeAL1 N E 𝔅 h ω μ).limTor N.ρinf K θ - K θ‖ ≤ μ / 2 := fun θ hθ => by
    have h1 := hclose θ hθ
    have h2 := R.J3 0
    rw [hm0, zero_add] at h2
    have e1 : (2 * N.τ + ((jA 0 : ℕ) : ℝ)) = 2 * N.τ := by simp [jA]
    have hrc : (fun s => (stageL1 N E s).rate 0) = fun s => (stageL1 N E s).CD :=
      funext fun s => by unfold stageL1; split_ifs <;> rfl
    rw [e1, hrc] at h2
    exact h1.trans h2
  have hmarg : ∀ θ ∈ complexStrip N.n N.ρinf,
      Metric.ball ((schemeAL1 N E 𝔅 h ω μ).limTor N.ρinf K θ) (μ / 2) ⊆ 𝔅 := fun θ hθ => by
    have := PerturbationAux.ball_subset_of_close (h0.ball_sub θ (hsub 0 hθ)) (hball θ hθ)
    rwa [show μ - μ / 2 = μ / 2 by ring] at this
  refine ⟨_, hholo, hprim, hreal, fun θ hθ => ?_, hmarg, fun θ hθ => ?_, fun θ hθ => ?_⟩
  · exact lim_invariance hS
      (Ks := fun s => (schemeAL1 N E 𝔅 h ω μ).tor ((schemeAL1 N E 𝔅 h ω μ).iter K s))
      (ε := runEps (2 * N.τ) 3 N.ρ N.ρinf γ (stageL1 N E) e)
      (hmarg θ hθ (Metric.mem_ball_self (half_pos hμ))) (hconv.tendsto_at hθ)
      (hconvd.tendsto_at hθ) (fun s => AdmA.error_le (hit s).1.1 θ (hsub s hθ)) hεz
  · refine le_of_tendsto (hconvd.tendsto_at hθ).norm (Eventually.of_forall fun s => ?_)
    have h1 := AdmA.deriv_le (hit s).1.1 θ (hsub s hθ)
    exact h1.trans ((hit s).2.1 1)
  · refine (hclose' θ hθ).trans (le_of_eq ?_)
    have hD : 0 < delta0 3 N.ρ N.ρinf := delta0_pos hlam hN.ρinf_lt
    have hDp : 0 < delta0 3 N.ρ N.ρinf ^ (4 * N.τ) := Real.rpow_pos_of_pos hD _
    have hρp : 0 < N.ρ ^ (2 * N.τ) := Real.rpow_pos_of_pos hρ0 _
    rw [show 2 * (2 * N.τ) = 4 * N.τ by ring]
    unfold c2AL1
    have : sumA (2 * N.τ) 3 N.ρ N.ρinf 1 (xA (2 * N.τ) (fun s => (stageL1 N E s).CE) Xs)
        (fun s => (stageL1 N E s).CD) (2 * N.τ) N.kp =
      sumA (2 * N.τ) 3 N.ρ N.ρinf 1 (xSL1 N E Xs) (fun s => (stageL1 N E s).CD) (2 * N.τ) N.kp :=
      rfl
    rw [this]
    field_simp

/-- The ℓ¹-entry branch of the frozen form: every hypothesis of the frozen G1, B9's refined data and
certificates, the entry hypotheses, and `e/(γ⁴ δ₀^{2a}) < X⋆`. -/
theorem g1_branch_AL1 (hN : N.Wf) (hE : E.Wf) (hfix : N.iso = false) (hΘ : N.Θ = 0)
    (hτ : (N.n : ℝ) - 1 ≤ N.τ) {M σK σB σT μ γbar Xs : ℝ} {I : InitA} (hM : 0 < M) (hμ : 0 < μ)
    (hγbar : γbar = N.γb) (hsK : N.sK = σK - μ / 2)
    (hOk : routeAOkL1 N E (N.capV (μ / 2)) (initV I σK σB σT μ) Xs) (hXpos : 0 < Xs)
    {𝔅 : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ))} {h : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ}
    {K : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)} {ω : Fin N.n → ℝ} {γ e : ℝ}
    {Ω : Set (Fin N.n → ℝ)} (hopen : IsOpen 𝔅)
    (htransl : ∀ z ∈ 𝔅, ∀ k : Fin N.n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ 𝔅)
    (hholo : DifferentiableOn ℂ h 𝔅)
    (hper : ∀ z ∈ 𝔅, ∀ k : Fin N.n → ℤ, h (z.1 + (fun i => (k i : ℂ)), z.2) = h z)
    (hreal : ∀ θ I : Fin N.n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ 𝔅 →
      (h ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0)
    (hbd : ∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ h z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M)
    (hK : DifferentiableOn ℂ K (complexStrip N.n N.ρ)) (hKp : IsPrimaryOnStrip K N.ρ)
    (hKr : IsRealOnReals K) (hball : ∀ θ ∈ complexStrip N.n N.ρ, Metric.ball (K θ) μ ⊆ 𝔅)
    (hDK : ∀ θ ∈ complexStrip N.n N.ρ, ‖fderiv ℂ K θ‖ ≤ σK - μ)
    (hG : ∀ θ ∈ complexStrip N.n N.ρ, IsUnit (gramMatrix K θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ σB - μ)
    (hTu : IsUnit (torsionAverage h K ω).det)
    (hTb : ∀ i, ∑ j, ‖(torsionAverage h K ω)⁻¹ i j‖ ≤ σT - μ)
    (hRef : RefHypA N I 𝔅 h K ω) (hω : ω ∈ Ω) (hCt : N.Cert γ Ω) (hEH : EntryHypA N E h K ω e)
    (hγ : 0 < γ) (hγγbar : γ ≤ γbar) (hdio : IsDiophantine γ N.τ ω) (he0 : 0 ≤ e)
    (hE' : ∀ θ ∈ complexStrip N.n N.ρ, ‖invarianceError h K ω θ‖ ≤ e)
    (hsm : e / (γ ^ 4 * delta0 3 N.ρ N.ρinf ^ (2 * (2 * N.τ))) < Xs) :
    ∃ Kinf : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip N.n N.ρinf) ∧ IsPrimaryOnStrip Kinf N.ρinf ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, invarianceError h Kinf ω θ = 0) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, ‖fderiv ℂ Kinf θ‖ ≤ σK - μ / 2) ∧
      ∀ θ ∈ complexStrip N.n N.ρinf, ‖Kinf θ - K θ‖ ≤
        c2AL1 N E Xs * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) := by
  have hρ0 : 0 < N.ρ := hN.ρinf_pos.trans hN.ρinf_lt
  have hP : Params N.n N.τ M N.sK N.sB N.sT := ⟨hN.two_le, hτ, hM, hN.sK, hN.sB, hN.sT⟩
  have hS : Standing N.n N.τ M N.sK N.sB N.sT 𝔅 h ω γ :=
    { toParams := hP
      isOpen := hopen
      transl_mem := htransl
      holo := hholo
      periodic := hper
      real := hreal
      bounds := fun z hz => ⟨(hbd z hz).2.1, (hbd z hz).2.2.1, (hbd z hz).2.2.2⟩
      gamma_pos := hγ
      dio := hdio }
  have hr0 : N.r 0 = N.ρ := rSeq_zero
  have h0 : AdmA 𝔅 h ω (N.r 0) (N.r 0 - N.δ 0) μ e (σK - μ) (σB - μ) (σT - μ) I.iLt I.iN I.iNt
      I.iH K := by
    rw [hr0]
    exact
      { r_pos := hρ0
        β_pos := hμ
        ε_nonneg := he0
        holo := hK
        primary := hKp
        real := hKr
        ball_sub := hball
        deriv_le := hDK
        gram := fun θ hθ => ⟨(hG θ hθ).1, norm_le_of_rowSum_le hN.two_le (hG θ hθ).2⟩
        tangentT := hRef.tangentT
        normal := hRef.normal
        normalT := hRef.normalT
        tors := hRef.tors
        twist := ⟨hTu, norm_le_of_rowSum_le hN.two_le hTb⟩
        error_le := hE' }
  obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := g1_core_AL1 hN hE hfix hΘ hS hRef.dX hRef.d2X
    (hγγbar.trans_eq hγbar) hω hCt hμ rfl hOk h0 hEH hsm.le hXpos
  exact ⟨Kinf, h1, h2, h3, h4, h5, fun θ hθ => (h6 θ hθ).trans_eq hsK, h7⟩

/-- Blueprint `bp:p2s2l1:g1A` / `bp:p2s2l1:frozen` (route A, the PlasmaLean route), repaired: three
branches — v1 (`sharpC1`), B9's sup route A at `X⋆_A` (`routeAOk`), the ℓ¹ entry at `X⋆`
(`routeAOkL1`) — with caps `capV (μ/2)` and initial values `initV I` (F2); `C₁` the minimum, `C₂`
the maximum, proved by cases on the branch that applies (F6). Never worse than v1 or than B9's route
A by construction. -/
theorem g1_v2A_l1 {N : NumA} {E : EntryA} (hN : N.Wf) (hE : E.Wf) (hfix : N.iso = false)
    (hΘ : N.Θ = 0) (hτ : (N.n : ℝ) - 1 ≤ N.τ) {M σK σB σT μ γbar XsA Xs : ℝ} (I : InitA)
    (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB) (hσT : 0 < σT) (hμ : 0 < μ) (hγbar : γbar = N.γb)
    (hsK : N.sK = σK - μ / 2)
    (hOkA : routeAOk N (N.capV (μ / 2)) (initV I σK σB σT μ) XsA) (hXApos : 0 < XsA)
    (hOk : routeAOkL1 N E (N.capV (μ / 2)) (initV I σK σB σT μ) Xs) (hXpos : 0 < Xs) :
    0 < min (sharpC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf)
        (min (c1A N XsA) (c1A N Xs)) ∧
      0 < max (sharpC2 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf)
        (max (c2A N XsA) (c2AL1 N E Xs)) ∧
      G1BodyAL1 N I E M σK σB σT μ γbar
        (min (sharpC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf)
          (min (c1A N XsA) (c1A N Xs)))
        (max (sharpC2 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf)
          (max (c2A N XsA) (c2AL1 N E Xs))) := by
  have hρ0 : 0 < N.ρ := hN.ρinf_pos.trans hN.ρinf_lt
  have hlam : (0 : ℝ) < 3 := by norm_num
  have hD : 0 < delta0 3 N.ρ N.ρinf := delta0_pos hlam hN.ρinf_lt
  have hDp : 0 < delta0 3 N.ρ N.ρinf ^ (4 * N.τ) := Real.rpow_pos_of_pos hD _
  have hγb0 : 0 < γbar := hγbar ▸ hN.γb
  obtain ⟨hC1, hC2, hbody⟩ := g1_sharp (n := N.n) hN.two_le hτ hN.ρinf_pos hN.ρinf_lt hM hσK hσB
    hσT hμ hγb0
  have hc1A : 0 < c1A N XsA := div_pos (Real.rpow_pos_of_pos hρ0 _) (mul_pos hXApos hDp)
  have hc1 : 0 < c1A N Xs := div_pos (Real.rpow_pos_of_pos hρ0 _) (mul_pos hXpos hDp)
  refine ⟨lt_min hC1 (lt_min hc1A hc1), lt_max_of_lt_left hC2, ?_⟩
  intro 𝔅 h K ω γ e Ω hopen htransl hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hRef hω
    hCt hEH hγ hγγbar hdio hE' hsm
  have h00 : (0 : Fin N.n → ℂ) ∈ complexStrip N.n N.ρ := fun i => by simpa using hρ0
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hE' 0 h00)
  have hp2 : 0 ≤ e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) :=
    div_nonneg he0 (mul_pos (pow_pos hγ 2) (Real.rpow_pos_of_pos hρ0 _)).le
  have hclose_mono : ∀ {K' : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)} {c c' : ℝ}, c ≤ c' →
      (∀ θ ∈ complexStrip N.n N.ρinf, ‖K' θ - K θ‖ ≤ c * e / (γ ^ 2 * N.ρ ^ (2 * N.τ))) →
      ∀ θ ∈ complexStrip N.n N.ρinf, ‖K' θ - K θ‖ ≤ c' * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) :=
    fun {K' c c'} hc hb θ hθ => (hb θ hθ).trans (by
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hc hp2)
  -- the smallness of a route-A branch at `X⋆` in the normalised form
  have hsmall : ∀ {X : ℝ}, 0 < X → c1A N X * e / (γ ^ 4 * N.ρ ^ (4 * N.τ)) < 1 →
      e / (γ ^ 4 * delta0 3 N.ρ N.ρinf ^ (2 * (2 * N.τ))) < X := fun {X} hX hs => by
    rw [show 2 * (2 * N.τ) = 4 * N.τ by ring]
    have hρp : 0 < N.ρ ^ (4 * N.τ) := Real.rpow_pos_of_pos hρ0 _
    have e1 : c1A N X * e / (γ ^ 4 * N.ρ ^ (4 * N.τ)) =
        (e / (γ ^ 4 * delta0 3 N.ρ N.ρinf ^ (4 * N.τ))) / X := by
      unfold c1A
      field_simp
    rw [e1, div_lt_one hX] at hs
    exact hs
  by_cases hcase : sharpC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf ≤
      min (c1A N XsA) (c1A N Xs)
  · -- the branch of v1
    rw [min_eq_left hcase] at hsm
    obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := hbody 𝔅 h K ω γ e hopen htransl hholo hper hreal
      hbd hK hKp hKr hball hDK hG hTu hTb hγ hγγbar hdio hE' hsm
    exact ⟨Kinf, h1, h2, h3, h4, h5, h6, hclose_mono (le_max_left _ _) h7⟩
  · rw [min_eq_right (not_le.1 hcase).le] at hsm
    by_cases hAB : c1A N XsA ≤ c1A N Xs
    · -- B9's sup route A
      rw [min_eq_left hAB] at hsm
      obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := g1_branch_A hN hfix hΘ hτ hM hμ hγbar hsK hOkA
        hXApos hopen htransl hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hRef hω hCt hγ
        hγγbar hdio he0 hE' (hsmall hXApos hsm)
      exact ⟨Kinf, h1, h2, h3, h4, h5, h6,
        hclose_mono ((le_max_left _ _).trans (le_max_right _ _)) h7⟩
    · -- the ℓ¹ entry
      rw [min_eq_right (not_le.1 hAB).le] at hsm
      obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := g1_branch_AL1 hN hE hfix hΘ hτ hM hμ hγbar hsK
        hOk hXpos hopen htransl hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hRef hω hCt
        hEH hγ hγγbar hdio he0 hE' (hsmall hXpos hsm)
      exact ⟨Kinf, h1, h2, h3, h4, h5, h6,
        hclose_mono ((le_max_right _ _).trans (le_max_right _ _)) h7⟩

end KAM.Sharp2.L1

end
