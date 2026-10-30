/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteB.Core
public import KAM.Sharp.G1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The v2 a-posteriori theorem, route B (blueprint `bp:p2s2:g1`, `bp:p2s2:frozen-form`)

* `G1BodyB` (verbatim): the frozen G1 body with the refined data `RefHypB` and the certificates
  `N.Cert` on a set `Ω ∋ ω`;
* `g1_branch_B`: the route-B branch. The run starts at the normalized error
  `X₀ = e max {σ_{Lᵀ}, σ_{Nᵀ} γ̄ δ₀^τ}/(γ² δ₀^{2τ+1})` (`xinit`), an upper bound of the weighted
  error of `K` with the stage-0 weights of `NumB.Fits`; the smallness `c1B e/(γ⁴ ρ^{4τ}) < 1` is
  `X₀ < X⋆`; `RunHyp.core` gives the limit, and the closeness is
  `|K∞ - K| ≤ ballSum(X₀) ≤ (X₀/X⋆) ballSum(X⋆) = c2B e/(γ² ρ^{2τ})` (homogeneity of the
  recursion; no `γ̄²`, audit F6);
* `g1_v2B` (verbatim): `C₁ = min {C₁♯, c1B}`, `C₂ = max {C₂♯, c2B}`, by cases on the minimum;
  `c1B_min_le_sharpC1` (verbatim).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2.RouteB

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2

/-- The frozen G1 body with the refined data of route B and the certificates bound to the
frequency (as B9's `G1BodyA`): the additional hypotheses are `RefHypB` and `N.Cert` on a set
`Ω ∋ ω`. -/
def G1BodyB {n : ℕ} (N : NumB n) (I : InitB) (M σK σB σT μ γbar C₁ C₂ : ℝ) : Prop :=
  ∀ (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))) (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) (γ e : ℝ)
    (Ω : Set (Fin n → ℝ)),
    IsOpen 𝔅 →
    (∀ z ∈ 𝔅, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ 𝔅) →
    DifferentiableOn ℂ h 𝔅 →
    (∀ z ∈ 𝔅, ∀ k : Fin n → ℤ, h (z.1 + (fun i => (k i : ℂ)), z.2) = h z) →
    (∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ 𝔅 →
      (h ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0) →
    (∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ h z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M) →
    DifferentiableOn ℂ K (complexStrip n N.ρ) → IsPrimaryOnStrip K N.ρ → IsRealOnReals K →
    (∀ θ ∈ complexStrip n N.ρ, Metric.ball (K θ) μ ⊆ 𝔅) →
    (∀ θ ∈ complexStrip n N.ρ, ‖fderiv ℂ K θ‖ ≤ σK - μ) →
    (∀ θ ∈ complexStrip n N.ρ, IsUnit (gramMatrix K θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ σB - μ) →
    IsUnit (torsionAverage h K ω).det →
    (∀ i, ∑ j, ‖(torsionAverage h K ω)⁻¹ i j‖ ≤ σT - μ) →
    RefHypB N I 𝔅 h K N.ρ → ω ∈ Ω → N.Cert γ Ω →
    0 < γ → γ ≤ γbar → IsDiophantine γ N.τ ω →
    (∀ θ ∈ complexStrip n N.ρ, ‖invarianceError h K ω θ‖ ≤ e) →
    C₁ * e / (γ ^ 4 * N.ρ ^ (4 * N.τ)) < 1 →
    ∃ Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip n N.ρinf) ∧ IsPrimaryOnStrip Kinf N.ρinf ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip n N.ρinf, invarianceError h Kinf ω θ = 0) ∧
      (∀ θ ∈ complexStrip n N.ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip n N.ρinf, ‖fderiv ℂ Kinf θ‖ ≤ σK - μ / 2) ∧
      ∀ θ ∈ complexStrip n N.ρinf, ‖Kinf θ - K θ‖ ≤ C₂ * e / (γ ^ 2 * N.ρ ^ (2 * N.τ))



variable {n : ℕ} {N : NumB n}

/-- The initial normalized error of the run. -/
def xinit (N : NumB n) (I : InitB) (γ e : ℝ) : ℝ :=
  e * max I.iLt (pN N I * N.γb * N.δ0 ^ N.τ) / (γ ^ 2 * N.δ0 ^ (2 * N.τ + 1))

theorem norm_etaL_le' {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {θ : Fin n → ℂ} {a ε : ℝ}
    (hN : ‖(normalMat K θ)ᵀ‖ ≤ a) (hE : ‖invarianceError h K ω θ‖ ≤ ε) :
    ‖etaL h K ω θ‖ ≤ a * ε := by
  have ha : 0 ≤ a := (norm_nonneg _).trans hN
  unfold etaL
  rw [norm_neg]
  refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
  rw [norm_mul_omegaZeroMatrix, norm_sumVec]
  exact mul_le_mul hN hE (norm_nonneg _) ha

theorem norm_etaN_le' {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {θ : Fin n → ℂ} {a ε : ℝ}
    (hL : ‖(tangentMat K θ)ᵀ‖ ≤ a) (hE : ‖invarianceError h K ω θ‖ ≤ ε) :
    ‖etaN h K ω θ‖ ≤ a * ε := by
  have ha : 0 ≤ a := (norm_nonneg _).trans hL
  unfold etaN
  refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
  rw [norm_mul_omegaZeroMatrix, norm_sumVec]
  exact mul_le_mul hL hE (norm_nonneg _) ha

/-- The initial cap values lie below the caps ((J3) at stage `0`). -/
theorem init_le_caps (hN : N.Wf) {σ m₀ : Fin 7 → ℝ} {β Xs : ℝ} (hOk : routeBOk N σ m₀ β Xs) :
    ∀ i, m₀ i ≤ σ i := by
  intro i
  have hy1 : 0 < 1 - N.ybar := by linarith [hN.ybar.2]
  have hw : ∀ s, 0 ≤ N.rate s i * N.wt s i := fun s => by
    have := (stageC_nonneg hN (N.δ s)).2.2.2 i
    rwa [stageC_sched hN] at this
  have h1 : 0 ≤ ∑ s ∈ Finset.range N.kp, N.rate s i * N.wt s i * N.xS Xs s :=
    Finset.sum_nonneg fun s _ => mul_nonneg (hw s) (xS_nonneg hN hOk.Xs_nonneg s)
  have h2 : 0 ≤ N.rate N.kp i * N.wt N.kp i * N.xS Xs N.kp / (1 - N.ybar) :=
    div_nonneg (mul_nonneg (hw _) (xS_nonneg hN hOk.Xs_nonneg _)) hy1.le
  linarith [hOk.J3 i]

/-- The route-B branch of the frozen form. -/
theorem g1_branch_B (hN : N.Wf) (hfix : N.iso = false) (hτ : (n : ℝ) - 1 ≤ N.τ)
    {M σK σB σT μ γbar Xs : ℝ} {I : InitB} (hM : 0 < M) (hμ : 0 < μ) (hγbar : γbar = N.γb)
    (hsK : N.sK = σK - μ / 2) (hI : I.Wf N σT μ) (hfit : N.Fits I)
    (hOk : routeBOk N (capB N σT μ 0) (initB I σK σB μ) (μ / 2) Xs) (hXpos : 0 < Xs)
    {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {γ e : ℝ}
    {Ω : Set (Fin n → ℝ)} (hopen : IsOpen 𝔅)
    (htransl : ∀ z ∈ 𝔅, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ 𝔅)
    (hholo : DifferentiableOn ℂ h 𝔅)
    (hper : ∀ z ∈ 𝔅, ∀ k : Fin n → ℤ, h (z.1 + (fun i => (k i : ℂ)), z.2) = h z)
    (hreal : ∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ 𝔅 →
      (h ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0)
    (hbd : ∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ h z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M)
    (hK : DifferentiableOn ℂ K (complexStrip n N.ρ)) (hKp : IsPrimaryOnStrip K N.ρ)
    (hKr : IsRealOnReals K) (hball : ∀ θ ∈ complexStrip n N.ρ, Metric.ball (K θ) μ ⊆ 𝔅)
    (hDK : ∀ θ ∈ complexStrip n N.ρ, ‖fderiv ℂ K θ‖ ≤ σK - μ)
    (hG : ∀ θ ∈ complexStrip n N.ρ, IsUnit (gramMatrix K θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ σB - μ)
    (hTu : IsUnit (torsionAverage h K ω).det)
    (hTb : ∀ i, ∑ j, ‖(torsionAverage h K ω)⁻¹ i j‖ ≤ σT - μ)
    (hRef : RefHypB N I 𝔅 h K N.ρ) (hω : ω ∈ Ω) (hCt : N.Cert γ Ω) (hγ : 0 < γ)
    (hγγbar : γ ≤ γbar) (hdio : IsDiophantine γ N.τ ω)
    (hE : ∀ θ ∈ complexStrip n N.ρ, ‖invarianceError h K ω θ‖ ≤ e)
    (hsm : c1B N I Xs * e / (γ ^ 4 * N.ρ ^ (4 * N.τ)) < 1) :
    ∃ Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip n N.ρinf) ∧ IsPrimaryOnStrip Kinf N.ρinf ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip n N.ρinf, invarianceError h Kinf ω θ = 0) ∧
      (∀ θ ∈ complexStrip n N.ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip n N.ρinf, ‖fderiv ℂ Kinf θ‖ ≤ σK - μ / 2) ∧
      ∀ θ ∈ complexStrip n N.ρinf, ‖Kinf θ - K θ‖ ≤ c2B N I Xs * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) := by
  have hρ0 : 0 < N.ρ := hN.ρ_pos
  have hδ0 := hN.δ0_pos
  have h00 : (0 : Fin n → ℂ) ∈ complexStrip n N.ρ := fun i => by simpa using hρ0
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hE 0 h00)
  have hγb : γ ≤ N.γb := hγγbar.trans_eq hγbar
  have hγb0 : 0 < N.γb := hN.γb
  have hpN : pN N I = I.iNt := by simp [pN, hfix]
  obtain ⟨⟨hLt0, hN0, hNt0⟩, -, hT1, hT2⟩ := hI
  -- the standing data and the base data of the run
  have hS : Standing n N.τ M N.sK N.sB N.sT 𝔅 h ω γ :=
    { toParams := ⟨hN.two_le, hτ, hM, hN.caps.1, hN.caps.2.2.1, hN.caps.2.2.2.2.2⟩
      isOpen := hopen
      transl_mem := htransl
      holo := hholo
      periodic := hper
      real := hreal
      bounds := fun z hz => ⟨(hbd z hz).2.1, (hbd z hz).2.2.1, (hbd z hz).2.2.2⟩
      gamma_pos := hγ
      dio := hdio }
  have Rb : RunBase N 𝔅 h ω Ω γ :=
    { wf := hN, fix := hfix, std := ⟨N.τ, M, γ, hS⟩, dX := hRef.dX, d2X := hRef.d2X,
      comm := hRef.comm, lip := hRef.lip, γ_pos := hγ, γ_le := hγb, mem := hω, cert := hCt }
  -- the initial normalized error
  set P := max I.iLt (I.iNt * N.γb * N.δ0 ^ N.τ) with hP
  have hP0 : 0 < P := lt_max_of_lt_left hLt0
  set Xi := xinit N I γ e with hXid
  have hXi : Xi = e * P / (γ ^ 2 * N.δ0 ^ (2 * N.τ + 1)) := by rw [hXid, xinit, hpN]
  have hd1 : 0 < N.δ0 ^ N.τ := Real.rpow_pos_of_pos hδ0 _
  have hd2 : 0 < N.δ0 ^ (2 * N.τ + 1) := Real.rpow_pos_of_pos hδ0 _
  have hXi0 : 0 ≤ Xi := by rw [hXi]; positivity
  have hXiXs : Xi < Xs := by
    have hc1 : c1B N I Xs * e / (γ ^ 4 * N.ρ ^ (4 * N.τ)) =
        e * (N.γb ^ 2 * P) / (γ ^ 4 * Xs * N.δ0 ^ (2 * N.τ + 1)) := by
      have hm : max (I.iLt * N.γb ^ 2) (pN N I * N.γb ^ 3 * N.δ0 ^ N.τ) = N.γb ^ 2 * P := by
        rw [hpN, hP, mul_max_of_nonneg _ _ (sq_nonneg _)]
        congr 1 <;> ring
      have hρp : 0 < N.ρ ^ (4 * N.τ) := Real.rpow_pos_of_pos hρ0 _
      rw [c1B, hm]
      field_simp
    rw [hc1, div_lt_one (by positivity)] at hsm
    rw [hXi, div_lt_iff₀ (by positivity)]
    have hg2 : γ ^ 2 ≤ N.γb ^ 2 := pow_le_pow_left₀ hγ.le hγb 2
    nlinarith [mul_pos (mul_pos hXpos hd2) (pow_pos hγ 2)]
  set μ0 := γ * N.δ0 ^ (N.τ + 1) * Xi with hμ0d
  have hδτ1 : N.δ0 ^ (N.τ + 1) = N.δ0 ^ N.τ * N.δ0 := Real.rpow_add_one hδ0.ne' _
  have hδ2 : N.δ0 ^ (2 * N.τ + 1) = N.δ0 ^ N.τ * N.δ0 ^ N.τ * N.δ0 := by
    rw [show 2 * N.τ + 1 = N.τ + N.τ + 1 by ring, Real.rpow_add_one hδ0.ne',
      Real.rpow_add hδ0]
  have hμ0 : μ0 = e * P / (γ * N.δ0 ^ N.τ) := by
    rw [hμ0d, hXi, hδτ1, hδ2]; field_simp
  have hgμ : γ * N.δ0 ^ N.τ * μ0 = e * P := by rw [hμ0]; field_simp
  -- the stage-0 weight `p̄`
  set pb := max I.iNt (I.iLt / (N.γb * N.δ0 ^ N.τ)) with hpb
  have hpb0 : 0 < pb := lt_max_of_lt_left hNt0
  have hpbP : pb ≤ P / (γ * N.δ0 ^ N.τ) := by
    have hc : 0 < γ * N.δ0 ^ N.τ := by positivity
    rw [hpb, hP, le_div_iff₀ hc, max_mul_of_nonneg _ _ hc.le]
    refine max_le ?_ ?_
    · calc I.iNt * (γ * N.δ0 ^ N.τ) ≤ I.iNt * N.γb * N.δ0 ^ N.τ := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hγb hd1.le) hNt0.le
        _ ≤ _ := le_max_right _ _
    · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      calc I.iLt * (γ * N.δ0 ^ N.τ) ≤ I.iLt * (N.γb * N.δ0 ^ N.τ) := by
            have := mul_le_mul_of_nonneg_right hγb hd1.le
            exact mul_le_mul_of_nonneg_left this hLt0.le
        _ ≤ max I.iLt (I.iNt * N.γb * N.δ0 ^ N.τ) * (N.γb * N.δ0 ^ N.τ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hpbμ : pb * e ≤ μ0 := by
    rw [hμ0, le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hpbP he0
    rw [mul_div_assoc', le_div_iff₀ (by positivity)] at this
    linarith
  have hmax0 : max pb (if N.iso = true then 1 else 0) = pb := by
    simp [hfix, hpb0.le]
  have hlam0 : I.iNt ≤ N.lam0 * pb := by
    have := hfit.lam0
    rw [hmax0, div_le_iff₀ hpb0] at this
    linarith
  have hePer : 1 ≤ N.ePer0 * pb := by
    have := hfit.ePer0
    rw [hmax0, div_le_iff₀ hpb0] at this
    linarith
  -- the initial flagged state
  have G0 : Good N 𝔅 h ω γ Xi K 0 N.ρ (μ / 2) μ0 (initB I σK σB μ) K :=
    { r_eq := hN.r_zero.symm
      μ_nonneg := by rw [hμ0]; positivity
      μ_le := by rw [(NumB.Wf.δ_zero (N := N))]; exact le_rfl
      holo := hK
      primary := hKp
      real := hKr
      ball := fun θ hθ => (Metric.ball_subset_ball (by linarith)).trans (hball θ hθ)
      β_pos := by linarith
      L := fun θ hθ => by
        show ‖colMat (fderiv ℂ K θ)‖ ≤ _
        rw [norm_colMat]; exact hDK θ hθ
      Lt := hRef.tangentT
      G := fun θ hθ => ⟨(hG θ hθ).1, norm_le_of_rowSum_le hN.two_le (hG θ hθ).2⟩
      Nm := hRef.normal
      NmT := hRef.normalT
      drift := by
        show ‖torsionABAverage h K - torsionABAverage h K‖ ≤ 0
        rw [sub_self, norm_zero]
      ηL := fun θ hθ => by
        refine (norm_etaL_le' (hRef.normalT θ hθ) (hE θ hθ)).trans ?_
        show I.iNt * e ≤ N.lam0 * μ0
        calc I.iNt * e ≤ N.lam0 * pb * e := mul_le_mul_of_nonneg_right hlam0 he0
          _ ≤ N.lam0 * μ0 := by
              rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hpbμ hN.lam.1.le
      ηN := fun θ hθ => by
        refine (norm_etaN_le' (hRef.tangentT θ hθ) (hE θ hθ)).trans ?_
        rw [(NumB.Wf.δ_zero (N := N)), hgμ, mul_comm]
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) he0
      E0 := fun _ θ hθ => by
        refine (hE θ hθ).trans ?_
        calc e = 1 * e := (one_mul e).symm
          _ ≤ N.ePer0 * pb * e := mul_le_mul_of_nonneg_right hePer he0
          _ ≤ N.ePer0 * μ0 := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left hpbμ hN.nonneg.2.2.2.2.2.2.2 }
  have G0' : Good N 𝔅 h ω γ Xi K 0 (N.r 0) (μ / 2) μ0 (initB I σK σB μ) K := by
    rw [hN.r_zero]; exact G0
  have hcond0 : stepCondB (N.inp 0) (μ0 / (γ * N.δ 0 ^ (N.τ + 1))) := by
    have e1 : μ0 / (γ * N.δ 0 ^ (N.τ + 1)) = Xi := by
      rw [hμ0d, (NumB.Wf.δ_zero (N := N))]; field_simp
    rw [e1]
    exact cond_run hN hOk hXi0 hXiXs.le (xS_nonneg hN hXi0 0) le_rfl
  obtain ⟨-, hloc0⟩ := Rb.locpart G0' hcond0 (init_le_caps hN hOk)
  have R : RunHyp N 𝔅 h ω Ω γ σT μ K :=
    { toRunBase := Rb
      A0 := hTu
      A0inv := norm_le_of_rowSum_le hN.two_le hTb
      mT_pos := hT1
      mT_lt := hT2
      loc0 := hloc0 }
  obtain ⟨Kinf, h1, h2, h3, h4, h5, h6⟩ := R.core hS hOk hXi0 hXiXs.le G0
  have hbs : N.ballSum Xi < μ / 2 := (ballSum_mono hN hXi0 hXiXs.le).trans_lt hOk.J4
  have hsub : complexStrip n N.ρinf ⊆ complexStrip n N.ρ := Triangular.strip_mono hN.ρinf_lt.le
  refine ⟨Kinf, h1, h2, h3, h4, fun θ hθ => ?_, fun θ hθ => (h5 θ hθ).trans_eq hsK,
    fun θ hθ => ?_⟩
  · have := PerturbationAux.ball_subset_of_close (hball θ (hsub hθ)) (h6 θ hθ)
    exact (Metric.ball_subset_ball (by linarith)).trans this
  · refine (h6 θ hθ).trans ?_
    have ht0 : 0 ≤ Xi / Xs := div_nonneg hXi0 hXpos.le
    have ht1 : Xi / Xs ≤ 1 := (div_le_one hXpos).2 hXiXs.le
    have hsc := ballSum_scale hN hXpos.le ht0 ht1
    rw [div_mul_cancel₀ _ hXpos.ne'] at hsc
    refine hsc.trans (le_of_eq ?_)
    have hρp : 0 < N.ρ ^ (2 * N.τ) := Real.rpow_pos_of_pos hρ0 _
    rw [hXi, c2B, hpN, ← hP]
    field_simp

/-- Blueprint `bp:p2s2:g1` / `bp:p2s2:frozen-form`, route B, refined: `C₁ = min {C₁♯, c1B}`,
`C₂ = max {C₂♯, c2B}`, by cases on the branch of the minimum (audit F6). Never worse than v1. -/
theorem g1_v2B {n : ℕ} {N : NumB n} (hN : N.Wf) (hfix : N.iso = false) (hτ : (n : ℝ) - 1 ≤ N.τ)
    {M σK σB σT μ γbar Xs : ℝ} (I : InitB) (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB)
    (hσT : 0 < σT) (hμ : 0 < μ) (hγbar : γbar = N.γb) (hsK : N.sK = σK - μ / 2)
    (hsB : σB - μ < N.sB) (hI : I.Wf N σT μ) (hfit : N.Fits I)
    (hOk : routeBOk N (capB N σT μ 0) (initB I σK σB μ) (μ / 2) Xs) (hXpos : 0 < Xs) :
    0 < min (sharpC1 n N.τ (cohConstR n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf) (c1B N I Xs) ∧
      0 < max (sharpC2 n N.τ (cohConstR n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf) (c2B N I Xs) ∧
      G1BodyB N I M σK σB σT μ γbar
        (min (sharpC1 n N.τ (cohConstR n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf) (c1B N I Xs))
        (max (sharpC2 n N.τ (cohConstR n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf) (c2B N I Xs)) := by
  have _hsB := hsB
  have hρ0 : 0 < N.ρ := hN.ρ_pos
  have hδ0 := hN.δ0_pos
  have hγb0 : 0 < γbar := hγbar ▸ hN.γb
  obtain ⟨hC1, hC2, hbody⟩ := g1_sharp (n := n) hN.two_le hτ hN.ρinf_pos hN.ρinf_lt hM hσK hσB
    hσT hμ hγb0
  have hc1 : 0 < c1B N I Xs := by
    have hLt := hI.pos.1
    have : 0 < max (I.iLt * N.γb ^ 2) (pN N I * N.γb ^ 3 * N.δ0 ^ N.τ) :=
      lt_max_of_lt_left (mul_pos hLt (pow_pos hN.γb 2))
    unfold c1B
    have := Real.rpow_pos_of_pos hρ0 (4 * N.τ)
    have := Real.rpow_pos_of_pos hδ0 (2 * N.τ + 1)
    positivity
  refine ⟨lt_min hC1 hc1, lt_max_of_lt_left hC2, ?_⟩
  intro 𝔅 h K ω γ e Ω hopen htransl hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hRef hω
    hCt hγ hγγbar hdio hE hsm
  have h00 : (0 : Fin n → ℂ) ∈ complexStrip n N.ρ := fun i => by simpa using hρ0
  have he0 : 0 ≤ e := (norm_nonneg _).trans (hE 0 h00)
  have hp2 : 0 ≤ e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) :=
    div_nonneg he0 (mul_pos (pow_pos hγ 2) (Real.rpow_pos_of_pos hρ0 _)).le
  have hclose_mono : ∀ {K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {c c' : ℝ}, c ≤ c' →
      (∀ θ ∈ complexStrip n N.ρinf, ‖K' θ - K θ‖ ≤ c * e / (γ ^ 2 * N.ρ ^ (2 * N.τ))) →
      ∀ θ ∈ complexStrip n N.ρinf, ‖K' θ - K θ‖ ≤ c' * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) :=
    fun {K' c c'} hc hb θ hθ => (hb θ hθ).trans (by
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hc hp2)
  by_cases hcase : sharpC1 n N.τ (cohConstR n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf ≤ c1B N I Xs
  · rw [min_eq_left hcase] at hsm
    obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := hbody 𝔅 h K ω γ e hopen htransl hholo hper hreal
      hbd hK hKp hKr hball hDK hG hTu hTb hγ hγγbar hdio hE hsm
    exact ⟨Kinf, h1, h2, h3, h4, h5, h6, hclose_mono (le_max_left _ _) h7⟩
  · rw [min_eq_right (not_le.1 hcase).le] at hsm
    obtain ⟨Kinf, h1, h2, h3, h4, h5, h6, h7⟩ := g1_branch_B hN hfix hτ hM hμ hγbar hsK hI hfit
      hOk hXpos hopen htransl hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hRef hω hCt
      hγ hγγbar hdio hE hsm
    exact ⟨Kinf, h1, h2, h3, h4, h5, h6, hclose_mono (le_max_right _ _) h7⟩



/-- Never worse than v1. -/
theorem c1B_min_le_sharpC1 {n : ℕ} (N : NumB n) (I : InitB) {M σK σB σT μ γbar Xs : ℝ} :
    min (sharpC1 n N.τ (cohConstR n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf) (c1B N I Xs) ≤
      sharpC1 n N.τ (cohConstR n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf :=
  min_le_left _ _

end KAM.Sharp2.RouteB

end
