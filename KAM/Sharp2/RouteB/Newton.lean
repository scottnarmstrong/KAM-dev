/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteB.Scheme
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# One stage of route B: the torsion against the initial torus and the modified step

`RunHyp` collects the fixed data of a run: the numbers, the standing data, the Hamiltonian data,
the certificates, and the reference data of the initial torus `K₀` (`⟨T₀⟩` invertible with
`|⟨T₀⟩⁻¹| ≤ m_T = σ_T - μ < σ̂_T`, and `|⟨T₀⟩ - ⟨𝒯_ab(K₀)⟩| ≤ b_F`).

At a flagged state of stage `s` (`Good`) satisfying the step conditions and the caps:

* `RunHyp.loc`: the local data `LocHyp` of the stage torus (weighted error `μ` with the weights
  `λ_s`, `γ δ_s^τ`), hence (`RunHyp.tors`) `bp:p2s2:torsion-local`: `|T| ≤ c_Th σ_{Nᵀ} σ_N + t_s` on
  `T_{r_s-δ_s}` and `|⟨T⟩ - ⟨𝒯_ab⟩| ≤ B_loc X ≤ b_F`; and `bp:p2s2:torsion-ref`: since
  `|⟨𝒯_ab(K)⟩ - ⟨𝒯_ab(K₀)⟩| ≤ m_Tab ≤ β_T - 2 b_F`, `|⟨T⟩ - ⟨T₀⟩| ≤ β_T`, and `inv_le_of_ref`
  gives `|⟨T⟩⁻¹| ≤ σ̂_T`;
* `RunHyp.good_step`: `modified_stepB` (SHARP2-B4B) at stage `s` gives the flagged state of stage
  `s + 1` with the engine's updates, and the displacement bound.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology MeasureTheory

namespace KAM.Sharp2.RouteB

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.ModStepB

variable {n : ℕ}

/-- The fixed data of a run of route B, with the reference data of the initial torus `K₀`. -/
structure RunHyp (N : NumB n) (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ω : Fin n → ℝ) (Ω : Set (Fin n → ℝ)) (γ σT μm : ℝ)
    (K0 : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) : Prop where
  wf : N.Wf
  fix : N.iso = false
  std : ∃ τ M γ₀ : ℝ, Standing n τ M N.sK N.sB N.sT 𝔅 h ω γ₀
  dX : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ N.M1
  d2X : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ N.M2
  comm : ∀ z ∈ 𝔅, ‖hamComm h z‖ ≤ N.cTh
  lip : ∀ z ∈ 𝔅, ∀ z' ∈ 𝔅, segment ℝ z z' ⊆ 𝔅 →
    ‖hamComm h z - hamComm h z'‖ ≤ N.cDTh * ‖z - z'‖
  γ_pos : 0 < γ
  γ_le : γ ≤ N.γb
  mem : ω ∈ Ω
  cert : N.Cert γ Ω
  A0 : IsUnit (torsionAverage h K0 ω).det
  A0inv : ‖(torsionAverage h K0 ω)⁻¹‖ ≤ σT - μm
  mT_pos : 0 < σT - μm
  mT_lt : σT - μm < N.sT
  loc0 : ‖torsionAverage h K0 ω - torsionABAverage h K0‖ ≤ N.bF

variable {N : NumB n} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {ω : Fin n → ℝ} {Ω : Set (Fin n → ℝ)} {γ σT μm Xi : ℝ}
  {K0 : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

namespace RunHyp

variable (R : RunHyp N 𝔅 h ω Ω γ σT μm K0)
include R

theorem gd_pos (s : ℕ) : 0 < γ * N.δ s ^ N.τ :=
  mul_pos R.γ_pos (Real.rpow_pos_of_pos (R.wf.δ_pos s) _)

theorem gd1_pos (s : ℕ) : 0 < γ * N.δ s ^ (N.τ + 1) :=
  mul_pos R.γ_pos (Real.rpow_pos_of_pos (R.wf.δ_pos s) _)

/-- With the weights `λ_s`, `γ δ_s^τ`, the weighted error of `modified_stepB` is `μ`. -/
theorem mu_eq (s : ℕ) {w : ℝ} :
    mu (N.inp s) γ ((N.inp s).lam * w) (γ * N.δ s ^ N.τ * w) (N.δ s) = w := by
  have hl := (R.wf.inp_lam_pos s).1
  have hg := R.gd_pos s
  show max ((N.inp s).lam * w / (N.inp s).lam) (γ * N.δ s ^ N.τ * w / (γ * N.δ s ^ N.τ)) = w
  rw [mul_div_cancel_left₀ _ hl.ne', mul_div_cancel_left₀ _ hg.ne', max_self]

theorem xX_eq (s : ℕ) {w : ℝ} :
    xX (N.inp s) γ ((N.inp s).lam * w) (γ * N.δ s ^ N.τ * w) (N.δ s) =
      w / (γ * N.δ s ^ (N.τ + 1)) := by
  rw [xX, R.mu_eq s]
  rfl

/-- The caps used in the local data. -/
theorem caps_of {s : ℕ} {w : ℝ} {m : Fin 7 → ℝ} (hw : 0 ≤ w)
    (hcap : ∀ i, m i + N.rate s i * N.wt s i * (w / (γ * N.δ s ^ (N.τ + 1))) ≤
      capB N σT μm 0 i) :
    ∀ i, m i ≤ capB N σT μm 0 i := by
  intro i
  have h0 := (stageC_nonneg R.wf (N.δ s)).2.2.2 i
  rw [stageC_sched R.wf] at h0
  have hX : 0 ≤ w / (γ * N.δ s ^ (N.τ + 1)) := div_nonneg hw (R.gd1_pos s).le
  have := hcap i
  have : 0 ≤ N.rate s i * N.wt s i * (w / (γ * N.δ s ^ (N.τ + 1))) := mul_nonneg h0 hX
  linarith

omit R in
/-- The rates and weights of the first six caps. -/
theorem rate_wt (s : ℕ) :
    N.rate s 0 * N.wt s 0 = n * (stepConstsB (N.inp s)).CDK ∧
      N.rate s 1 * N.wt s 1 = 2 * n * (stepConstsB (N.inp s)).CDK ∧
      N.rate s 2 * N.wt s 2 = (stepConstsB (N.inp s)).CBb ∧
      N.rate s 3 * N.wt s 3 = (stepConstsB (N.inp s)).CNb ∧
      N.rate s 4 * N.wt s 4 = (stepConstsB (N.inp s)).CNbT ∧
      N.rate s 5 * N.wt s 5 = (stepConstsB (N.inp s)).Cab := by
  simp [NumB.rate, NumB.wt]

/-- The local data `LocHyp` of a flagged stage torus. -/
theorem loc {s : ℕ} {β w : ℝ} {m : Fin 7 → ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hG : Good N 𝔅 h ω γ Xi K0 s (N.r s) β w m K)
    (hcond : stepCondB (N.inp s) (w / (γ * N.δ s ^ (N.τ + 1))))
    (hcaps : ∀ i, m i ≤ capB N σT μm 0 i) :
    ∃ c', LocHyp (N.inp s) 𝔅 h K ω Ω γ β ((N.inp s).lam * w) (γ * N.δ s ^ N.τ * w) (N.δ s)
      (N.r s) N.split c' ![m 0, m 1, m 2, m 3, m 4] := by
  obtain ⟨-, ⟨c', hc', hc1⟩, -⟩ := R.cert.at R.wf s
  obtain ⟨τ0, M0, γ0, hS⟩ := R.std
  refine ⟨c', ?_⟩
  exact
    { ok := R.wf.inp_ok s
      pn := rfl
      γ_pos := R.γ_pos
      γ_le := R.γ_le
      δ_pos := R.wf.δ_pos s
      δ_le := R.wf.δ_le_inp s
      three := R.wf.three_δ_lt s
      mem := R.mem
      s_pos := R.wf.split_pos
      s_lt := R.wf.split_lt_one
      cert' := hc'
      c1_le := hc1
      std := ⟨τ0, M0, γ0, hS⟩
      dX := R.dX
      holo := hG.holo
      primary := hG.primary
      ball := hG.ball
      β_pos' := hG.β_pos
      L := hG.L
      Lt := hG.Lt
      G := hG.G
      N := hG.Nm
      Nt := hG.NmT
      ηL := hG.ηL
      ηN := hG.ηN
      E0 := fun h0 θ hθ => by
        have hs0 : s = 0 := of_decide_eq_true h0
        rw [R.mu_eq s]
        exact hG.E0 hs0 θ hθ
      cond := by rw [R.xX_eq s]; exact hcond
      caps' := ⟨hcaps 0, hcaps 1, hcaps 2, hcaps 3, hcaps 4⟩ }

/-- The frame part of the torsion is continuous on the real torus. -/
theorem cont_AB {r β : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hr : 0 < r)
    (hβ : 0 < β) (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hball : ∀ θ ∈ complexStrip n r, Metric.ball (K θ) β ⊆ 𝔅)
    (hdK : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ N.sK)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ N.sB) :
    Continuous (fun x : Fin n → ℝ => torsionAB h K (fun i => (x i : ℂ))) ∧
      Continuous (fun x : Fin n → ℝ => torsion h K ω (fun i => (x i : ℂ))) := by
  obtain ⟨τ0, M0, γ0, hS⟩ := R.std
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hTc⟩, -⟩ :=
    frame_basic hS hr hβ hK hball hdK hG
  exact ⟨Triangular.continuous_ofReal_comp hr (diffOn_torsionAB hS hr hβ hK hball hdK hG), hTc⟩

/-- `bp:p2s2:torsion-local` and `bp:p2s2:torsion-ref` at a flagged stage torus: the torsion bound
on `T_{r_s-δ_s}` and the twist bound `|⟨T⟩⁻¹| ≤ σ̂_T`, with the local part `|⟨T⟩ - ⟨𝒯_ab⟩| ≤ b_F`. -/
theorem tors {s : ℕ} {β w : ℝ} {m : Fin 7 → ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hG : Good N 𝔅 h ω γ Xi K0 s (N.r s) β w m K)
    (hcond : stepCondB (N.inp s) (w / (γ * N.δ s ^ (N.τ + 1))))
    (hcaps : ∀ i, m i ≤ capB N σT μm 0 i) :
    (∀ θ ∈ complexStrip n (N.r s - N.δ s), ‖torsion h K ω θ‖ ≤
      (N.inp s).cTh * (N.inp s).sNt * (N.inp s).sN + (N.inp s).ts) ∧
      ‖torsionAverage h K ω - torsionABAverage h K‖ ≤ N.bF ∧
      IsUnit (torsionAverage h K ω).det ∧ ‖(torsionAverage h K ω)⁻¹‖ ≤ (N.inp s).sT := by
  obtain ⟨c', L⟩ := R.loc hG hcond hcaps
  obtain ⟨τ0, M0, γ0, hS⟩ := R.std
  have hr0 := R.wf.r_gt s
  have hr1 : 0 < N.r s - N.δ s := by linarith [R.wf.three_δ_lt s, R.wf.δ_pos s, R.wf.ρinf_pos]
  have hloc := L.torsion_sub_le hS
  have hBX : sBsup (N.inp s) * xX (N.inp s) γ ((N.inp s).lam * w) (γ * N.δ s ^ N.τ * w) (N.δ s)
      ≤ (N.inp s).ts := L.c_Bsup
  have hBl : sBloc (N.inp s) *
      xX (N.inp s) γ ((N.inp s).lam * w) (γ * N.δ s ^ N.τ * w) (N.δ s) ≤ (N.inp s).bF :=
    L.cond.2.2.2.2.2.2.2.2.2.1
  have hBlS : sBloc (N.inp s) = sBsup (N.inp s) := by
    rw [sBloc]; simp only [show (N.inp s).iso = false from R.fix, Bool.false_eq_true, ↓reduceIte]
  rw [hBlS] at hBl
  have hdK : ∀ θ ∈ complexStrip n (N.r s), ‖fderiv ℂ K θ‖ ≤ N.sK := fun θ hθ => by
    rw [← norm_colMat]; exact (hG.L θ hθ).trans (hcaps 0)
  have hGB : ∀ θ ∈ complexStrip n (N.r s),
      IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ N.sB := fun θ hθ =>
    ⟨(hG.G θ hθ).1, (hG.G θ hθ).2.trans (hcaps 2)⟩
  obtain ⟨hcAB, hcT⟩ := R.cont_AB (hr0.trans' R.wf.ρinf_pos) hG.β_pos hG.holo hG.ball hdK hGB
  -- the local part of the average
  have hlocA : ‖torsionAverage h K ω - torsionABAverage h K‖ ≤ N.bF := by
    rw [torsionAverage_eq' hcT, torsionABAverage_eq hcAB]
    refine norm_torusAverage_sub_le hcT hcAB fun x => (hloc _ ?_).trans hBl
    exact ofReal_mem_complexStrip hr1 x
  refine ⟨fun θ hθ => ?_, hlocA, ?_⟩
  · have hθr : θ ∈ complexStrip n (N.r s) :=
      Triangular.strip_mono (by linarith [R.wf.δ_pos s]) hθ
    have hab := norm_torsionAB_le (hG.G θ hθr).1 ((hG.Nm θ hθr).trans (hcaps 3))
      ((hG.NmT θ hθr).trans (hcaps 4)) (R.comm _ (hG.ball θ hθr (Metric.mem_ball_self hG.β_pos)))
    calc ‖torsion h K ω θ‖ ≤ ‖torsionAB h K θ‖ + ‖torsion h K ω θ - torsionAB h K θ‖ := by
          have := norm_add_le (torsionAB h K θ) (torsion h K ω θ - torsionAB h K θ)
          rwa [add_sub_cancel] at this
      _ ≤ N.sNt * N.cTh * N.sN + (N.inp s).ts := add_le_add hab ((hloc θ hθ).trans hBX)
      _ = _ := by show _ = N.cTh * N.sNt * N.sN + _; ring
  · -- the reference Neumann
    have hdrift : ‖torsionABAverage h K - torsionABAverage h K0‖ ≤
        (N.sT - (σT - μm)) / (N.sT * (σT - μm)) - 2 * N.bF := hG.drift.trans (hcaps 5)
    have hd : ‖torsionAverage h K ω - torsionAverage h K0 ω‖ ≤
        (N.sT - (σT - μm)) / (N.sT * (σT - μm)) := by
      have e : torsionAverage h K ω - torsionAverage h K0 ω =
          (torsionAverage h K ω - torsionABAverage h K) +
            (torsionABAverage h K - torsionABAverage h K0) -
              (torsionAverage h K0 ω - torsionABAverage h K0) := by abel
      rw [e]
      have := R.loc0
      calc _ ≤ ‖(torsionAverage h K ω - torsionABAverage h K) +
            (torsionABAverage h K - torsionABAverage h K0)‖ +
              ‖torsionAverage h K0 ω - torsionABAverage h K0‖ := norm_sub_le _ _
        _ ≤ (‖torsionAverage h K ω - torsionABAverage h K‖ +
            ‖torsionABAverage h K - torsionABAverage h K0‖) + N.bF :=
            add_le_add (norm_add_le _ _) R.loc0
        _ ≤ _ := by linarith
    exact inv_le_of_ref R.A0 R.A0inv R.mT_pos R.mT_lt hd

end RunHyp

end KAM.Sharp2.RouteB

end
