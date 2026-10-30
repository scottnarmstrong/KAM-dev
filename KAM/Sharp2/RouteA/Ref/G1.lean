/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteA.G1
public import KAM.Sharp2.RouteA.Ref.Scheme
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lever L8′ of route A: the theorem

* `initR`: the initial cap values: nothing of the ball budget and of the budget of `𝒯_ab` is used;
* `Ref.g1_core_R`: Theorem `bp:p2s2:g1`, route A, with item (L8′) of `bp:p2s2:constantsA`;
* `Ref.g1_branch_R`: the route-A branch of the frozen form;
* `g1_v2A'`: the analogue of `g1_v2A` with the torsion against the initial torus. The numbers are
  `routeAOkR` and `Ref.Budget` in place of `routeAOk`, and the constants `c1A`, `c2A` are those of
  `g1_v2A`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology KAM.Sharp.Engine

namespace KAM.Sharp2.RouteA

open KAM KAM.Torus KAM.Apost KAM.Sharp

/-- The initial cap values. -/
def initR (I : InitA) (σK σB μ : ℝ) : Fin 7 → ℝ := ![0, σK - μ, σB - μ, 0, I.iLt, I.iN, I.iNt]

namespace Ref

variable {N : NumA}

theorem sumA_nonneg {a lam ρ ρinf γb b : ℝ} {x c : ℕ → ℝ} (hc : ∀ s, 0 ≤ c s)
    (hx : ∀ s, 0 ≤ x s) (hd : ∀ s, 0 ≤ deltaSeq lam ρ ρinf s) (kp : ℕ) :
    0 ≤ sumA a lam ρ ρinf γb x c b kp := by
  have hw : ∀ t, 0 ≤ γb ^ 2 * deltaSeq lam ρ ρinf t ^ (2 * a - b) := fun t =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hd t) _)
  unfold sumA
  refine add_nonneg (Finset.sum_nonneg fun t _ => ?_) ?_
  · exact mul_nonneg (mul_nonneg (hc t) (hx t)) (hw t)
  · exact mul_nonneg (mul_nonneg (mul_nonneg two_pos.le (hc kp)) (hx kp)) (hw kp)

theorem xS_nonneg (hN : N.Wf) {Xs : ℝ} (h0 : 0 ≤ Xs) (s : ℕ) : 0 ≤ N.xS Xs s :=
  (xA_mono (fun s => (hN.pos s).CE) h0 le_rfl s).1

/-- Theorem `bp:p2s2:g1`, route A, with the torsion against the initial torus. -/
theorem g1_core_R (hN : N.Wf) (hfix : N.iso = false) (hΘ : N.Θ = 0) {τ M μ γ e Xs bF bT iH mT : ℝ}
    {𝔅 : Set ((Fin N.n → ℂ) × (Fin N.n → ℂ))} {h : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ}
    {ω : Fin N.n → ℝ} {Ω : Set (Fin N.n → ℝ)} {m₀ : Fin 7 → ℝ}
    {K : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)}
    (hS : Standing N.n τ M N.sK N.sB N.sT 𝔅 h ω γ)
    (hd1 : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ N.M1)
    (hd2 : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ N.M2)
    (hγb : γ ≤ N.γb) (hω : ω ∈ Ω) (hC : N.Cert γ Ω) (hμ : 0 < μ) (hm0 : m₀ 0 = 0) (hm3 : m₀ 3 = 0)
    (hOk : routeAOkR N bF (N.capR (μ / 2) bT) m₀ Xs) (hB : Budget N mT iH bF bT)
    (h0 : Adm0 𝔅 h ω (N.r 0) μ e (m₀ 1) (m₀ 2) (m₀ 4) (m₀ 5) (m₀ 6) K)
    (hTu : IsUnit (torsionAverage h K ω).det) (hTb : ‖(torsionAverage h K ω)⁻¹‖ ≤ mT)
    (hTs : ∀ θ ∈ complexStrip N.n (N.r 0 - N.δ 0), ‖torsion h K ω θ‖ ≤ iH)
    (hX : e / (γ ^ 4 * delta0 3 N.ρ N.ρinf ^ (2 * (2 * N.τ))) ≤ Xs) (hXpos : 0 < Xs) :
    ∃ Kinf : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip N.n N.ρinf) ∧ IsPrimaryOnStrip Kinf N.ρinf ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, invarianceError h Kinf ω θ = 0) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, ‖fderiv ℂ Kinf θ‖ ≤ N.sK) ∧
      ∀ θ ∈ complexStrip N.n N.ρinf, ‖Kinf θ - K θ‖ ≤
        c2A N Xs * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) := by
  have hγ := hS.gamma_pos
  have hρ0 : 0 < N.ρ := hN.ρinf_pos.trans hN.ρinf_lt
  have hb : μ / 2 < μ := by linarith
  have R := hOk.runData hN
  have hlam : (0 : ℝ) < 3 := by norm_num
  -- the reference data of the initial torus
  have hcaps : ∀ i, m₀ i ≤ N.capR (μ / 2) bT i := fun i =>
    le_of_add_le_of_nonneg_left (hOk.J3 i) (sumA_nonneg
      (fun s => NumA.rateR_nonneg (hN.pos s) i) (xS_nonneg hN hOk.Xs_nonneg)
      (fun s => (hN.δ_pos s).le) _)
  have hδ0 : N.δ 0 = delta0 3 N.ρ N.ρinf := deltaSeq_zero
  have hX0 : e / (γ ^ 4 * N.δ 0 ^ (2 * (2 * N.τ))) ≤ Xs := by rw [hδ0]; exact hX
  have hc0 : N.CondR bF 0 Xs := by
    rcases Nat.eq_zero_or_pos N.kp with hk | hk
    · have := hOk.J1t
      rwa [hk] at this
    · exact hOk.J1 0 hk
  have hc0' := hc0.down hN hX0
  have hδ := hN.δ_pos 0
  have hδD := hN.δ_le_dS 0
  obtain ⟨hεδ, -, -, -⟩ := hc0'.base.facts (hN.pos 0) hγ hγb hδ hδD h0.ε_nonneg
  have hc2 : SDConst N.n N.τ γ (N.δ 0 / 2) (N.cS (0 + 1)) Ω := by
    have := (hC.at hN (0 + 1)).1
    rwa [NumA.δ_succ] at this
  have hcap0 : Adm0 𝔅 h ω (N.r 0) μ e N.sK N.sB N.sLt N.sN N.sNt K :=
    h0.mono (hcaps 1) (hcaps 2) (hcaps 4) (hcaps 5) (hcaps 6)
  have h3δ := hN.lam_δ_lt 0
  have hbL : N.bLocS 0 = (N.inp 0).bLoc0 (N.cS (0 + 1)) := by
    have hf : (N.inp 0).iso = false := hfix
    simp [NumA.bLocS, StepInA.bLoc, hf]
  have hR : RefT h K ω (N.r 0 - N.δ 0) bF iH mT :=
    { cont := cont_torsion hS hcap0
      unit := hTu
      inv := hTb
      tors := hTs
      loc := fun θ hθ => by
        have h1 := local_bound (hN.pos 0) rfl hS hd1 hγb hω hcap0 hδ hδD (by linarith) hεδ hc2 θ hθ
        refine h1.trans ?_
        have h2 := hc0'.loc
        rw [hbL] at h2
        exact h2 }
  have hNw := schemeR_isNewton hN hfix hΘ hS hd1 hd2 hγb hω hC hb hR hB
  have h0' : (schemeR N 𝔅 h ω μ K).Adm 0 e m₀ K := by
    show AdmR 𝔅 h ω K (N.r 0) (N.r 0 - N.δ 0) (μ - m₀ 0) e (m₀ 1) (m₀ 2) (m₀ 3) (m₀ 4) (m₀ 5)
      (m₀ 6) K
    rw [hm0, hm3, sub_zero]
    exact ⟨h0, fun θ _ => by simp⟩
  have hit := SchemeA.run hNw R hlam hN.ρinf_lt hγ hγb h0' hX
  obtain ⟨hconv, hconvd, hholo, hprim, hreal, hclose, hclose', -, -, -, hεz⟩ :=
    SchemeA.limit hNw R hlam hN.ρinf_pos hN.ρinf_lt hγ hγb h0' hX
  have hsub : ∀ s, complexStrip N.n N.ρinf ⊆ complexStrip N.n (N.r s) := fun s =>
    Triangular.strip_mono (hN.ρinf_lt_r s).le
  -- the ball budget
  have hball : ∀ θ ∈ complexStrip N.n N.ρinf,
      ‖(schemeR N 𝔅 h ω μ K).limTor N.ρinf K θ - K θ‖ ≤ μ / 2 := fun θ hθ => by
    have h1 := hclose θ hθ
    have h2 := R.J3 0
    rw [hm0, zero_add] at h2
    have e1 : (2 * N.τ + ((jR 0 : ℕ) : ℝ)) = 2 * N.τ := by simp [jR]
    rw [e1] at h2
    exact h1.trans h2
  have hmarg : ∀ θ ∈ complexStrip N.n N.ρinf,
      Metric.ball ((schemeR N 𝔅 h ω μ K).limTor N.ρinf K θ) (μ / 2) ⊆ 𝔅 := fun θ hθ => by
    have := PerturbationAux.ball_subset_of_close (h0.ball_sub θ (hsub 0 hθ)) (hball θ hθ)
    rwa [show μ - μ / 2 = μ / 2 by ring] at this
  refine ⟨_, hholo, hprim, hreal, fun θ hθ => ?_, hmarg, fun θ hθ => ?_, fun θ hθ => ?_⟩
  · exact lim_invariance hS (Ks := fun s => (schemeR N 𝔅 h ω μ K).tor
      ((schemeR N 𝔅 h ω μ K).iter K s))
      (ε := runEps (2 * N.τ) 3 N.ρ N.ρinf γ N.stageR e)
      (hmarg θ hθ (Metric.mem_ball_self (half_pos hμ))) (hconv.tendsto_at hθ)
      (hconvd.tendsto_at hθ) (fun s => Adm0.error_le (AdmR.toAdm0 (hit s).1) θ (hsub s hθ)) hεz
  · refine le_of_tendsto (hconvd.tendsto_at hθ).norm (Eventually.of_forall fun s => ?_)
    have h1 := Adm0.deriv_le (AdmR.toAdm0 (hit s).1) θ (hsub s hθ)
    exact h1.trans ((hit s).2.1 1)
  · refine (hclose' θ hθ).trans (le_of_eq ?_)
    have hD : 0 < delta0 3 N.ρ N.ρinf := delta0_pos hlam hN.ρinf_lt
    have hDp : 0 < delta0 3 N.ρ N.ρinf ^ (4 * N.τ) := Real.rpow_pos_of_pos hD _
    have hρp : 0 < N.ρ ^ (2 * N.τ) := Real.rpow_pos_of_pos hρ0 _
    rw [show 2 * (2 * N.τ) = 4 * N.τ by ring]
    unfold c2A
    have : sumA (2 * N.τ) 3 N.ρ N.ρinf 1 (xA (2 * N.τ) (fun s => (N.stageR s).CE) Xs)
        (fun s => (N.stageR s).CD) (2 * N.τ) N.kp =
      sumA (2 * N.τ) 3 N.ρ N.ρinf 1 (N.xS Xs) (fun s => (N.stage s).CD) (2 * N.τ) N.kp := rfl
    rw [this]
    field_simp

/-- The route-A branch of the frozen form, with the torsion against the initial torus. -/
theorem g1_branch_R (hN : N.Wf) (hfix : N.iso = false) (hΘ : N.Θ = 0) (hτ : (N.n : ℝ) - 1 ≤ N.τ)
    {M σK σB σT μ γbar Xs bF bT : ℝ} {I : InitA} (hM : 0 < M) (hμ : 0 < μ) (hγbar : γbar = N.γb)
    (hsK : N.sK = σK - μ / 2) (hOk : routeAOkR N bF (N.capR (μ / 2) bT) (initR I σK σB μ) Xs)
    (hB : Budget N (σT - μ) I.iH bF bT) (hXpos : 0 < Xs)
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
    (hRef : RefHypA N I 𝔅 h K ω) (hω : ω ∈ Ω) (hCt : N.Cert γ Ω) (hγ : 0 < γ) (hγγbar : γ ≤ γbar)
    (hdio : IsDiophantine γ N.τ ω) (he0 : 0 ≤ e)
    (hE : ∀ θ ∈ complexStrip N.n N.ρ, ‖invarianceError h K ω θ‖ ≤ e)
    (hsm : e / (γ ^ 4 * delta0 3 N.ρ N.ρinf ^ (2 * (2 * N.τ))) < Xs) :
    ∃ Kinf : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip N.n N.ρinf) ∧ IsPrimaryOnStrip Kinf N.ρinf ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, invarianceError h Kinf ω θ = 0) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip N.n N.ρinf, ‖fderiv ℂ Kinf θ‖ ≤ σK - μ / 2) ∧
      ∀ θ ∈ complexStrip N.n N.ρinf, ‖Kinf θ - K θ‖ ≤
        c2A N Xs * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) := by
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
  have h0 : Adm0 𝔅 h ω (N.r 0) μ e (initR I σK σB μ 1) (initR I σK σB μ 2) (initR I σK σB μ 4)
      (initR I σK σB μ 5) (initR I σK σB μ 6) K := by
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
        error_le := hE }
  have hTs : ∀ θ ∈ complexStrip N.n (N.r 0 - N.δ 0), ‖torsion h K ω θ‖ ≤ I.iH := by
    rw [hr0]
    exact hRef.tors
  obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := g1_core_R hN hfix hΘ hS hRef.dX hRef.d2X
    (hγγbar.trans_eq hγbar) hω hCt hμ rfl rfl hOk hB h0 hTu (norm_le_of_rowSum_le hN.two_le hTb) hTs
    hsm.le hXpos
  exact ⟨Kinf, h1, h2, h3, h4, h5, fun θ hθ => (h6 θ hθ).trans_eq hsK, h7⟩

end Ref

variable {N : NumA}

/-- The analogue of `g1_v2A` with lever L8′: the frozen conclusion with
`C₁ = min {C₁♯, ρ^{4τ}/(X⋆ δ₀^{4τ})}` and `C₂ = max {C₂♯, c2A}`, whenever `routeAOkR` and the
budgets `Ref.Budget` hold at `X⋆ > 0`. -/
theorem g1_v2A' (hN : N.Wf) (hfix : N.iso = false) (hΘ : N.Θ = 0) (hτ : (N.n : ℝ) - 1 ≤ N.τ)
    {M σK σB σT μ γbar Xs bF bT : ℝ} (I : InitA) (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB)
    (hσT : 0 < σT) (hμ : 0 < μ) (hγbar : γbar = N.γb) (hsK : N.sK = σK - μ / 2)
    (hOk : routeAOkR N bF (N.capR (μ / 2) bT) (initR I σK σB μ) Xs)
    (hB : Ref.Budget N (σT - μ) I.iH bF bT) (hXpos : 0 < Xs) :
    0 < min (sharpC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf) (c1A N Xs) ∧
      0 < max (sharpC2 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf) (c2A N Xs) ∧
      G1BodyA N I M σK σB σT μ γbar
        (min (sharpC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf) (c1A N Xs))
        (max (sharpC2 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf) (c2A N Xs)) := by
  have hρ0 : 0 < N.ρ := hN.ρinf_pos.trans hN.ρinf_lt
  have hlam : (0 : ℝ) < 3 := by norm_num
  have hD : 0 < delta0 3 N.ρ N.ρinf := delta0_pos hlam hN.ρinf_lt
  have hDp : 0 < delta0 3 N.ρ N.ρinf ^ (4 * N.τ) := Real.rpow_pos_of_pos hD _
  have hγb0 : 0 < γbar := hγbar ▸ hN.γb
  obtain ⟨hC1, hC2, hbody⟩ := g1_sharp (n := N.n) hN.two_le hτ hN.ρinf_pos hN.ρinf_lt hM hσK hσB hσT
    hμ hγb0
  have hc1 : 0 < c1A N Xs := div_pos (Real.rpow_pos_of_pos hρ0 _) (mul_pos hXpos hDp)
  refine ⟨lt_min hC1 hc1, lt_max_of_lt_left hC2, ?_⟩
  intro 𝔅 h K ω γ e Ω hopen htransl hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hRef hω hCt
    hγ hγγbar hdio hE hsm
  have h00 : (0 : Fin N.n → ℂ) ∈ complexStrip N.n N.ρ := fun i => by simpa using hρ0
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hE 0 h00)
  have hp2 : 0 ≤ e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) :=
    div_nonneg he0 (mul_pos (pow_pos hγ 2) (Real.rpow_pos_of_pos hρ0 _)).le
  have hclose_mono : ∀ {K' : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)} {c c' : ℝ}, c ≤ c' →
      (∀ θ ∈ complexStrip N.n N.ρinf, ‖K' θ - K θ‖ ≤ c * e / (γ ^ 2 * N.ρ ^ (2 * N.τ))) →
      ∀ θ ∈ complexStrip N.n N.ρinf, ‖K' θ - K θ‖ ≤ c' * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) :=
    fun {K' c c'} hc hb θ hθ => (hb θ hθ).trans (by
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hc hp2)
  by_cases hcase : sharpC1 N.n N.τ (cohConstR N.n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf ≤ c1A N Xs
  · -- the branch of v1
    rw [min_eq_left hcase] at hsm
    obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := hbody 𝔅 h K ω γ e hopen htransl hholo hper hreal
        hbd
      hK hKp hKr hball hDK hG hTu hTb hγ hγγbar hdio hE hsm
    exact ⟨Kinf, h1, h2, h3, h4, h5, h6, hclose_mono (le_max_left _ _) h7⟩
  · -- route A
    rw [min_eq_right (not_le.1 hcase).le] at hsm
    have hsm' : e / (γ ^ 4 * delta0 3 N.ρ N.ρinf ^ (2 * (2 * N.τ))) < Xs := by
      rw [show 2 * (2 * N.τ) = 4 * N.τ by ring]
      have hρp : 0 < N.ρ ^ (4 * N.τ) := Real.rpow_pos_of_pos hρ0 _
      have e1 : c1A N Xs * e / (γ ^ 4 * N.ρ ^ (4 * N.τ)) =
          (e / (γ ^ 4 * delta0 3 N.ρ N.ρinf ^ (4 * N.τ))) / Xs := by
        unfold c1A
        field_simp
      rw [e1, div_lt_one hXpos] at hsm
      exact hsm
    obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := Ref.g1_branch_R hN hfix hΘ hτ hM hμ hγbar hsK hOk
      hB hXpos hopen htransl hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hRef hω hCt hγ
      hγγbar hdio he0 hE hsm'
    exact ⟨Kinf, h1, h2, h3, h4, h5, h6, hclose_mono (le_max_right _ _) h7⟩

end KAM.Sharp2.RouteA

end
