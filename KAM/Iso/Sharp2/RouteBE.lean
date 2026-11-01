/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.RouteBE.Core
public import KAM.Iso.Sharp2.RouteB
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The route-B branch of the isoenergetic theorem, with a separate gradient bound

`iso_g1_branch_E` is `iso_g1_branch_B` (`KAM/Iso/Sharp2/RouteB.lean`) with `N.y0 = Mh1 * N.sN` for a
real `Mh1` with `‖DH‖ ≤ Mh1` on `D`. The hypotheses gain only that bound on `H`, which is implied by
the standing bound for `Mh1 = M`: `iso_g1_branch_B_of_E` recovers the old theorem, statement for
statement, from the new one.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology MeasureTheory

namespace KAM.Iso.Sharp2.RouteBE

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteB KAM.Iso.Linear KAM.Iso.Apost
  KAM.Iso.Sharp2.RouteB KAM.Iso.Sharp

variable {n : ℕ} {N : NumB n}

/-- The route-B branch of the isoenergetic frozen form, with `y₀ = Mh1 s_N` and the gradient bound
`‖DH‖ ≤ Mh1` on `D`. -/
theorem iso_g1_branch_E (hN : N.Wf) (hiso : N.iso = true) (hτ : (n : ℝ) - 1 ≤ N.τ)
    {M Mh1 σK σB σT μ γbar σω ν Xs : ℝ} {I : InitB} (hM : 0 < M) (hμ : 0 < μ) (hσω : 1 < σω)
    (hν : 0 < ν) {ωstar : Fin n → ℝ} (hωstar : ωstar ≠ 0) (hγbar : γbar = N.γb)
    (hsK : N.sK = σK - μ / 2) (hΘ : N.Θ = σω * ‖ωstar‖) (hy0 : N.y0 = Mh1 * N.sN) (hI : I.Wf N σT μ)
    (hfit : N.Fits I) (hOk : routeBOk N (capB N σT μ ν) (initB I σK σB μ) (μ / 2) Xs)
    (hXpos : 0 < Xs) {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {s γ e E₀ : ℝ} {Ω : Set (Fin n → ℝ)}
    (hopen : IsOpen D)
    (htransl : ∀ z ∈ D, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ D)
    (hholo : DifferentiableOn ℂ H D)
    (hper : ∀ z ∈ D, ∀ k : Fin n → ℤ, H (z.1 + (fun i => (k i : ℂ)), z.2) = H z)
    (hreal : ∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ D →
      (H ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0)
    (hbd : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ H z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ M ∧ ‖iteratedFDeriv ℂ 2 H z‖ ≤ M)
    (hK : DifferentiableOn ℂ K (complexStrip n N.ρ)) (hKp : IsPrimaryOnStrip K N.ρ)
    (hKr : IsRealOnReals K) (hball : ∀ θ ∈ complexStrip n N.ρ, Metric.ball (K θ) μ ⊆ D)
    (hDK : ∀ θ ∈ complexStrip n N.ρ, ‖fderiv ℂ K θ‖ ≤ σK - μ)
    (hG : ∀ θ ∈ complexStrip n N.ρ, IsUnit (gramMatrix K θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ σB - μ)
    (hTu : IsUnit (KAM.Iso.extendedTorsionAverage H K (s • ωstar)).det)
    (hTb : ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹ i j‖ ≤ σT - μ)
    (hs1 : 1 < s) (hν1 : ν ≤ (s - 1) * ‖ωstar‖) (hν2 : ν ≤ (σω - s) * ‖ωstar‖)
    (hdH : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ Mh1)
    (hRef : RefHypB N I D H K N.ρ) (hd2H : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 H z‖ ≤ N.Mh2)
    (hΩ : ∀ s' : ℝ, 1 ≤ s' → s' • ωstar ∈ Ω) (hCt : N.Cert γ Ω) (hγ : 0 < γ) (hγγbar : γ ≤ γbar)
    (hdio : IsDiophantine γ N.τ ωstar) (he0 : 0 ≤ e)
    (hE : ∀ θ ∈ complexStrip n N.ρ, ‖invarianceError H K (s • ωstar) θ‖ ≤ e)
    (hEn : ‖KAM.Iso.energyAverage H K - (E₀ : ℂ)‖ ≤ e)
    (hsm : c1B N I Xs * e / (γ ^ 4 * N.ρ ^ (4 * N.τ)) < 1) :
    ∃ (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (sinf : ℝ),
      1 < sinf ∧ sinf < σω ∧ DifferentiableOn ℂ Kinf (complexStrip n N.ρinf) ∧
      IsPrimaryOnStrip Kinf N.ρinf ∧ IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip n N.ρinf, invarianceError H Kinf (sinf • ωstar) θ = 0) ∧
      (∀ θ ∈ complexStrip n N.ρinf, H (Kinf θ) = (E₀ : ℂ)) ∧
      (∀ θ ∈ complexStrip n N.ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ D) ∧
      (∀ θ ∈ complexStrip n N.ρinf, ‖fderiv ℂ Kinf θ‖ ≤ σK - μ / 2) ∧
      (∀ θ ∈ complexStrip n N.ρinf, ‖Kinf θ - K θ‖ ≤
        c2B N I Xs * e / (γ ^ 2 * N.ρ ^ (2 * N.τ))) ∧
      ‖sinf • ωstar - s • ωstar‖ ≤ c3B N I Xs * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) := by
  have hρ0 : 0 < N.ρ := hN.ρ_pos
  have hδ0 := hN.δ0_pos
  have hγb : γ ≤ N.γb := hγγbar.trans_eq hγbar
  have hγb0 : 0 < N.γb := hN.γb
  obtain ⟨⟨hLt0, hN0, hNt0⟩, -, hT1, hT2⟩ := hI
  -- the standing data and the base data of the run
  have hIS : IsoStanding n N.τ M N.sK N.sB N.sT σω ν ωstar D H γ :=
    { toParams := ⟨hN.two_le, hτ, hM, hN.caps.1, hN.caps.2.2.1, hN.caps.2.2.2.2.2⟩
      σω_gt := hσω
      ν_pos := hν
      ωstar_ne := hωstar
      isOpen := hopen
      transl_mem := htransl
      holo := hholo
      periodic := hper
      real := hreal
      bounds := hbd
      gamma_pos := hγ
      dio := hdio }
  have Rb : RunBaseE N.τ M Mh1 N D H ωstar Ω σω ν γ :=
    { wf := hN, iso := hiso, std := hIS, hΘ := hΘ, y0 := hy0, dH := hdH, dX := hRef.dX,
      d2X := hRef.d2X,
      d2H := hd2H, comm := hRef.comm, lip := hRef.lip, γ_le := hγb, mem := hΩ, cert := hCt }
  -- the initial normalized error
  set pn := pN N I with hpn
  have hpN : pn = max I.iNt 1 := by simp [hpn, pN, hiso]
  have hpn1 : 1 ≤ pn := by rw [hpN]; exact le_max_right _ _
  have hpnt : I.iNt ≤ pn := by rw [hpN]; exact le_max_left _ _
  set P := max I.iLt (pn * N.γb * N.δ0 ^ N.τ) with hP
  have hP0 : 0 < P := lt_max_of_lt_left hLt0
  set Xi := xinit N I γ e with hXid
  have hXi : Xi = e * P / (γ ^ 2 * N.δ0 ^ (2 * N.τ + 1)) := by rw [hXid, xinit]
  have hd1 : 0 < N.δ0 ^ N.τ := Real.rpow_pos_of_pos hδ0 _
  have hd2 : 0 < N.δ0 ^ (2 * N.τ + 1) := Real.rpow_pos_of_pos hδ0 _
  have hXi0 : 0 ≤ Xi := by rw [hXi]; positivity
  have hXiXs : Xi < Xs := by
    have hc1 : c1B N I Xs * e / (γ ^ 4 * N.ρ ^ (4 * N.τ)) =
        e * (N.γb ^ 2 * P) / (γ ^ 4 * Xs * N.δ0 ^ (2 * N.τ + 1)) := by
      have hm : max (I.iLt * N.γb ^ 2) (pN N I * N.γb ^ 3 * N.δ0 ^ N.τ) = N.γb ^ 2 * P := by
        rw [hP, mul_max_of_nonneg _ _ (sq_nonneg _)]
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
  set pb := max (max I.iNt (I.iLt / (N.γb * N.δ0 ^ N.τ))) 1 with hpb
  have hpb0 : 0 < pb := lt_max_of_lt_right one_pos
  have hc : 0 < γ * N.δ0 ^ N.τ := by positivity
  have hpbP : pb ≤ P / (γ * N.δ0 ^ N.τ) := by
    rw [hpb, le_div_iff₀ hc, max_mul_of_nonneg _ _ hc.le, max_mul_of_nonneg _ _ hc.le]
    have hn1 : γ * N.δ0 ^ N.τ ≤ pn * N.γb * N.δ0 ^ N.τ := by
      have h1 : γ ≤ pn * N.γb := by nlinarith
      exact mul_le_mul_of_nonneg_right h1 hd1.le
    refine max_le (max_le ?_ ?_) ?_
    · calc I.iNt * (γ * N.δ0 ^ N.τ) ≤ pn * (γ * N.δ0 ^ N.τ) :=
            mul_le_mul_of_nonneg_right hpnt hc.le
        _ ≤ pn * (N.γb * N.δ0 ^ N.τ) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hγb hd1.le) (by linarith)
        _ = pn * N.γb * N.δ0 ^ N.τ := by ring
        _ ≤ _ := le_max_right _ _
    · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      calc I.iLt * (γ * N.δ0 ^ N.τ) ≤ I.iLt * (N.γb * N.δ0 ^ N.τ) := by
            have := mul_le_mul_of_nonneg_right hγb hd1.le
            exact mul_le_mul_of_nonneg_left this hLt0.le
        _ ≤ max I.iLt (pn * N.γb * N.δ0 ^ N.τ) * (N.γb * N.δ0 ^ N.τ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · rw [one_mul]
      exact hn1.trans (le_max_right _ _)
  have hpbμ : pb * e ≤ μ0 := by
    rw [hμ0, le_div_iff₀ hc]
    have := mul_le_mul_of_nonneg_left hpbP he0
    rw [mul_div_assoc', le_div_iff₀ hc] at this
    linarith
  have hite : (if N.iso = true then (1 : ℝ) else 0) = 1 := by simp [hiso]
  have hlam0 : I.iNt ≤ N.lam0 * pb := by
    have := hfit.lam0
    rw [hite, div_le_iff₀ hpb0] at this
    exact this
  have hePer : 1 ≤ N.ePer0 * pb := by
    have := hfit.ePer0
    rw [hite, div_le_iff₀ hpb0] at this
    exact this
  have hlamW : 1 ≤ N.lamW0 * pb := by
    have := hfit.lamW0 hiso
    rw [div_le_iff₀ hpb0] at this
    exact this
  -- the initial flagged state
  have G0 : GoodI N D H ωstar E₀ σω ν γ Xi K s 0 N.ρ (μ / 2) μ0 (initB I σK σB μ) K s s :=
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
        show ‖torsionABAverage H K - torsionABAverage H K‖ + ‖s • ωstar - s • ωstar‖ ≤ 0
        simp
      drift' := by
        show (n : ℝ) * ‖s • ωstar - s • ωstar‖ ≤ 0
        simp
      ς_gt := hs1
      ray := by
        show ν - 0 ≤ rayMargin σω ωstar s
        rw [sub_zero]
        exact KAM.Iso.Apost.margin_of_le hν1 hν2
      incr := fun t ht => absurd ht (Nat.succ_ne_zero t).symm
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
      ηω := by
        refine hEn.trans ?_
        show e ≤ N.lamW0 * μ0
        calc e = 1 * e := (one_mul e).symm
          _ ≤ N.lamW0 * pb * e := mul_le_mul_of_nonneg_right hlamW he0
          _ ≤ N.lamW0 * μ0 := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hpbμ hN.lam.2.2.1.le
      E0 := fun _ θ hθ => by
        refine (hE θ hθ).trans ?_
        calc e = 1 * e := (one_mul e).symm
          _ ≤ N.ePer0 * pb * e := mul_le_mul_of_nonneg_right hePer he0
          _ ≤ N.ePer0 * μ0 := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left hpbμ hN.nonneg.2.2.2.2.2.2.2 }
  have G0' : GoodI N D H ωstar E₀ σω ν γ Xi K s 0 (N.r 0) (μ / 2) μ0 (initB I σK σB μ) K s s := by
    rw [hN.r_zero]; exact G0
  have hcond0 : stepCondB (N.inp 0) (μ0 / (γ * N.δ 0 ^ (N.τ + 1))) := by
    have e1 : μ0 / (γ * N.δ 0 ^ (N.τ + 1)) = Xi := by
      rw [hμ0d, (NumB.Wf.δ_zero (N := N))]; field_simp
    rw [e1]
    exact cond_run hN hOk hXi0 hXiXs.le (xS_nonneg hN hXi0 0) le_rfl
  obtain ⟨-, hloc0, hY0, hform0⟩ := Rb.local_parts G0' hcond0 (init_le_caps hN hOk)
  have R : RunHypE N.τ M Mh1 N D H ωstar Ω σω ν γ σT μ K s :=
    { toRunBaseE := Rb
      A0 := hTu
      A0inv := norm_le_of_rowSum_le_of_nonempty hTb
      mT_pos := hT1
      mT_lt := hT2
      loc0 := hloc0
      Y0 := hY0
      form0 := hform0 }
  obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := R.core hOk hXi0 hXiXs.le G0
  have hbs : N.ballSum Xi < μ / 2 := (ballSum_mono hN hXi0 hXiXs.le).trans_lt hOk.J4
  have hsub : complexStrip n N.ρinf ⊆ complexStrip n N.ρ := Triangular.strip_mono hN.ρinf_lt.le
  have ht0 : 0 ≤ Xi / Xs := div_nonneg hXi0 hXpos.le
  have ht1 : Xi / Xs ≤ 1 := (div_le_one hXpos).2 hXiXs.le
  have hρp : 0 < N.ρ ^ (2 * N.τ) := Real.rpow_pos_of_pos hρ0 _
  refine ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, fun θ hθ => ?_,
    fun θ hθ => (h8 θ hθ).trans_eq hsK, fun θ hθ => ?_, ?_⟩
  · have := PerturbationAux.ball_subset_of_close (hball θ (hsub hθ)) (h9 θ hθ)
    exact (Metric.ball_subset_ball (by linarith)).trans this
  · refine (h9 θ hθ).trans ?_
    have hsc := ballSum_scale hN hXpos.le ht0 ht1
    rw [div_mul_cancel₀ _ hXpos.ne'] at hsc
    refine hsc.trans (le_of_eq ?_)
    have e2 : c2B N I Xs = N.ρ ^ (2 * N.τ) * P * N.ballSum Xs / (Xs * N.δ0 ^ (2 * N.τ + 1)) := rfl
    rw [hXi, e2]
    field_simp
  · refine h10.trans ?_
    have hsc := freqSum_scale hN hXpos.le ht0 ht1
    rw [div_mul_cancel₀ _ hXpos.ne'] at hsc
    refine hsc.trans (le_of_eq ?_)
    have e3 : c3B N I Xs = N.ρ ^ (2 * N.τ) * P * N.freqSum Xs / (Xs * N.δ0 ^ (2 * N.τ + 1)) := rfl
    rw [hXi, e3]
    field_simp

/-- **The old branch is the specialization `Mh1 = M`.** The statement is that of
`KAM.Iso.Sharp2.RouteB.iso_g1_branch_B`, word for word; the gradient bound comes from `hbd`. -/
theorem iso_g1_branch_B_of_E (hN : N.Wf) (hiso : N.iso = true) (hτ : (n : ℝ) - 1 ≤ N.τ)
    {M σK σB σT μ γbar σω ν Xs : ℝ} {I : InitB} (hM : 0 < M) (hμ : 0 < μ) (hσω : 1 < σω)
    (hν : 0 < ν) {ωstar : Fin n → ℝ} (hωstar : ωstar ≠ 0) (hγbar : γbar = N.γb)
    (hsK : N.sK = σK - μ / 2) (hΘ : N.Θ = σω * ‖ωstar‖) (hy0 : N.y0 = M * N.sN) (hI : I.Wf N σT μ)
    (hfit : N.Fits I) (hOk : routeBOk N (capB N σT μ ν) (initB I σK σB μ) (μ / 2) Xs)
    (hXpos : 0 < Xs) {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {s γ e E₀ : ℝ} {Ω : Set (Fin n → ℝ)}
    (hopen : IsOpen D)
    (htransl : ∀ z ∈ D, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ D)
    (hholo : DifferentiableOn ℂ H D)
    (hper : ∀ z ∈ D, ∀ k : Fin n → ℤ, H (z.1 + (fun i => (k i : ℂ)), z.2) = H z)
    (hreal : ∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ D →
      (H ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0)
    (hbd : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ H z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ M ∧ ‖iteratedFDeriv ℂ 2 H z‖ ≤ M)
    (hK : DifferentiableOn ℂ K (complexStrip n N.ρ)) (hKp : IsPrimaryOnStrip K N.ρ)
    (hKr : IsRealOnReals K) (hball : ∀ θ ∈ complexStrip n N.ρ, Metric.ball (K θ) μ ⊆ D)
    (hDK : ∀ θ ∈ complexStrip n N.ρ, ‖fderiv ℂ K θ‖ ≤ σK - μ)
    (hG : ∀ θ ∈ complexStrip n N.ρ, IsUnit (gramMatrix K θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ σB - μ)
    (hTu : IsUnit (KAM.Iso.extendedTorsionAverage H K (s • ωstar)).det)
    (hTb : ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹ i j‖ ≤ σT - μ)
    (hs1 : 1 < s) (hν1 : ν ≤ (s - 1) * ‖ωstar‖) (hν2 : ν ≤ (σω - s) * ‖ωstar‖)
    (hRef : RefHypB N I D H K N.ρ) (hd2H : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 H z‖ ≤ N.Mh2)
    (hΩ : ∀ s' : ℝ, 1 ≤ s' → s' • ωstar ∈ Ω) (hCt : N.Cert γ Ω) (hγ : 0 < γ) (hγγbar : γ ≤ γbar)
    (hdio : IsDiophantine γ N.τ ωstar) (he0 : 0 ≤ e)
    (hE : ∀ θ ∈ complexStrip n N.ρ, ‖invarianceError H K (s • ωstar) θ‖ ≤ e)
    (hEn : ‖KAM.Iso.energyAverage H K - (E₀ : ℂ)‖ ≤ e)
    (hsm : c1B N I Xs * e / (γ ^ 4 * N.ρ ^ (4 * N.τ)) < 1) :
    ∃ (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (sinf : ℝ),
      1 < sinf ∧ sinf < σω ∧ DifferentiableOn ℂ Kinf (complexStrip n N.ρinf) ∧
      IsPrimaryOnStrip Kinf N.ρinf ∧ IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip n N.ρinf, invarianceError H Kinf (sinf • ωstar) θ = 0) ∧
      (∀ θ ∈ complexStrip n N.ρinf, H (Kinf θ) = (E₀ : ℂ)) ∧
      (∀ θ ∈ complexStrip n N.ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ D) ∧
      (∀ θ ∈ complexStrip n N.ρinf, ‖fderiv ℂ Kinf θ‖ ≤ σK - μ / 2) ∧
      (∀ θ ∈ complexStrip n N.ρinf, ‖Kinf θ - K θ‖ ≤
        c2B N I Xs * e / (γ ^ 2 * N.ρ ^ (2 * N.τ))) ∧
      ‖sinf • ωstar - s • ωstar‖ ≤ c3B N I Xs * e / (γ ^ 2 * N.ρ ^ (2 * N.τ)) :=
  iso_g1_branch_E hN hiso hτ hM hμ hσω hν hωstar hγbar hsK hΘ hy0 hI hfit hOk hXpos hopen htransl
    hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hs1 hν1 hν2
    (fun z hz => (hbd z hz).1) hRef hd2H hΩ hCt hγ hγγbar hdio he0 hE hEn hsm

/-- The two statements are the same proposition (`rfl` by proof irrelevance). -/
theorem iso_g1_branch_B_eq_of_E : @iso_g1_branch_B = @iso_g1_branch_B_of_E := rfl

end KAM.Iso.Sharp2.RouteBE

end
