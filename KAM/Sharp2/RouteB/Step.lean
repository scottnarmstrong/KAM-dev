/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteB.Newton
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# One stage of route B: from stage `s` to stage `s + 1`

`RunHyp.good_step`: at a flagged state of stage `s` (`Good`) satisfying the step conditions, the
ball condition and the caps of the engine, the modified step `modNewton` (`modified_stepB`,
SHARP2-B4B, with the torsion data of `RunHyp.tors`) gives a flagged state of stage `s + 1`, with
the engine's updates of the strip, the ball, the weighted error `Q_s μ²/(γ δ_s^{τ+1})` and the cap
values, and the displacement `|K̄ - K| ≤ C_ΔK μ/(γ δ_s^τ)`.

The new weighted error with the weights of stage `s + 1` (`λ = 1`, `γ δ_{s+1}^τ`): `|η̄ᴸ| ≤ Q_L μ²/(γ
δ^{τ+1})` and `|η̄ᴺ| ≤ Q̄_N μ²/δ = a^τ Q̄_N γ δ_{s+1}^τ μ²/(γ δ^{τ+1})`, both `≤ Q · …` with
`Q = max {Q_L, a^τ Q̄_N}`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology MeasureTheory

namespace KAM.Sharp2.RouteB

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.ModStepB

variable {n : ℕ} {N : NumB n} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {Ω : Set (Fin n → ℝ)} {γ σT μm Xi : ℝ}
  {K0 : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

namespace RunHyp

variable (R : RunHyp N 𝔅 h ω Ω γ σT μm K0)
include R

/-- The new weighted error is at most `μ̄_{s+1}`. -/
theorem mu_succ_le {s : ℕ} {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ γ * N.δ s ^ (N.τ + 1) * N.xS Xi s) :
    N.Qs s * w ^ 2 / (γ * N.δ s ^ (N.τ + 1)) ≤
      γ * N.δ (s + 1) ^ (N.τ + 1) * N.xS Xi (s + 1) := by
  have hQ : 0 ≤ N.Qs s := by
    have := (stageC_nonneg R.wf (N.δ s)).1
    rwa [stageC_sched R.wf] at this
  have hg := R.gd1_pos s
  have ha := R.wf.a_pos
  have hδ := R.wf.δ_pos s
  have e1 : N.δ (s + 1) ^ (N.τ + 1) = N.δ s ^ (N.τ + 1) / N.a ^ (N.τ + 1) := by
    rw [R.wf.δ_succ, Real.div_rpow hδ.le ha.le]
  have e2 : N.xS Xi (s + 1) = N.a ^ (N.τ + 1) * N.Qs s * N.xS Xi s ^ 2 := rfl
  have hpa : 0 < N.a ^ (N.τ + 1) := Real.rpow_pos_of_pos ha _
  rw [e1, e2, div_le_iff₀ hg]
  have hsq : w ^ 2 ≤ (γ * N.δ s ^ (N.τ + 1) * N.xS Xi s) ^ 2 := pow_le_pow_left₀ hw0 hw 2
  have key : γ * (N.δ s ^ (N.τ + 1) / N.a ^ (N.τ + 1)) *
      (N.a ^ (N.τ + 1) * N.Qs s * N.xS Xi s ^ 2) * (γ * N.δ s ^ (N.τ + 1)) =
      N.Qs s * (γ * N.δ s ^ (N.τ + 1) * N.xS Xi s) ^ 2 := by
    field_simp
  rw [key]
  exact mul_le_mul_of_nonneg_left hsq hQ

/-- One stage of route B. -/
theorem good_step {s : ℕ} {β w : ℝ} {m : Fin 7 → ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hG : Good N 𝔅 h ω γ Xi K0 s (N.r s) β w m K)
    (hcond : stepCondB (N.inp s) (w / (γ * N.δ s ^ (N.τ + 1))))
    (hβ : (stepConstsB (N.inp s)).CDK * w / (γ * N.δ s ^ N.τ) < β)
    (hcap : ∀ i, m i + N.rate s i * N.wt s i * (w / (γ * N.δ s ^ (N.τ + 1))) ≤
      capB N σT μm 0 i) :
    Good N 𝔅 h ω γ Xi K0 (s + 1) (N.r s - 3 * N.δ s)
        (β - (stepConstsB (N.inp s)).CDK * w / (γ * N.δ s ^ N.τ))
        (N.Qs s * w ^ 2 / (γ * N.δ s ^ (N.τ + 1)))
        (fun i => m i + N.rate s i * N.wt s i * (w / (γ * N.δ s ^ (N.τ + 1))))
        (modNewton h K ω (N.r s - 2 * N.δ s)) ∧
      ∀ θ ∈ complexStrip n (N.r s - 3 * N.δ s),
        ‖modNewton h K ω (N.r s - 2 * N.δ s) θ - K θ‖ ≤
          (stepConstsB (N.inp s)).CDK * w / (γ * N.δ s ^ N.τ) := by
  have hw0 := hG.μ_nonneg
  have hcaps := R.caps_of hw0 hcap
  obtain ⟨hT, -, hTa⟩ := R.tors hG hcond hcaps
  obtain ⟨hc, ⟨c', hc', hc1⟩, cb, hcb, hcavg⟩ := R.cert.at R.wf s
  obtain ⟨τ0, M0, γ0, hS⟩ := R.std
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := RunBase.rate_wt (N := N) s
  set X := w / (γ * N.δ s ^ (N.τ + 1)) with hXd
  have hX0 : 0 ≤ X := div_nonneg hw0 (R.gd1_pos s).le
  have hmax : max ((N.inp s).lam * w / (N.inp s).lam)
      (γ * N.δ s ^ N.τ * w / (γ * N.δ s ^ (N.inp s).κ)) = w := R.mu_eq s
  have hst := modified_stepB (N.inp s) (𝔅 := 𝔅) (h := h) (K := K) (ω := ω) (Ω := Ω) (γ := γ)
    (β := β) (εL := (N.inp s).lam * w) (εN := γ * N.δ s ^ N.τ * w) (δ := N.δ s) (r := N.r s)
    (s := N.split) (c' := c') (b := N.bfull s) (cb := cb) (m := ![m 0, m 1, m 2, m 3, m 4])
    (R.wf.inp_ok s) rfl R.fix R.γ_pos R.γ_le (R.wf.δ_pos s) (R.wf.δ_le_inp s)
    (R.wf.three_δ_lt s) R.mem hc ⟨R.wf.split_pos, R.wf.split_lt_one⟩ hc' hc1
    ⟨R.wf.δ_le_bfull s, NumB.Wf.bfull_le (N := N) s⟩ hcb hcavg hS R.dX R.d2X R.comm R.lip hG.holo
    hG.primary hG.real hG.ball hG.L hG.Lt hG.G hG.Nm hG.NmT hT hTa hG.ηL hG.ηN
    (fun h0 θ hθ => by rw [hmax]; exact hG.E0 (of_decide_eq_true h0) θ hθ)
    (by rw [hmax]; exact hcond) (by rw [hmax]; exact hβ) (by
      dsimp only
      rw [hmax]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · have := hcap 0; rw [r0] at this
        show m 0 + (n : ℝ) * (stepConstsB (N.inp s)).CDK * X ≤ N.sK; exact this
      · have := hcap 1; rw [r1] at this
        show m 1 + 2 * (n : ℝ) * (stepConstsB (N.inp s)).CDK * X ≤ N.sLt; exact this
      · have := hcap 2; rw [r2] at this; exact this
      · have := hcap 3; rw [r3] at this; exact this
      · have := hcap 4; rw [r4] at this; exact this)
  dsimp only at hst
  rw [hmax] at hst
  obtain ⟨hKbd, hKbp, hKbr, hdisp, hηNb, hηLb, hLb, hGb, hNb, hTab, -⟩ := hst
  -- the strips
  have h32 : N.r s - 3 * N.δ s ≤ N.r s - 2 * N.δ s := by linarith [R.wf.δ_pos s]
  have h3r : N.r s - 3 * N.δ s ≤ N.r s := by linarith [R.wf.δ_pos s]
  have hsub2 := Triangular.strip_mono (n := n) h32
  have hsubr := Triangular.strip_mono (n := n) h3r
  have hr' : 0 < N.r s - 3 * N.δ s := by rw [R.wf.r_succ]; linarith [R.wf.r_gt (s + 1),
    R.wf.ρinf_pos]
  set Kb := modNewton h K ω (N.r s - 2 * N.δ s) with hKb
  set d := (stepConstsB (N.inp s)).CDK * w / (γ * N.δ s ^ N.τ) with hdd
  have hQ : 0 ≤ N.Qs s := by
    have := (stageC_nonneg R.wf (N.δ s)).1
    rwa [stageC_sched R.wf] at this
  have hcp := fun i => hcap i
  -- the new frames, against the caps
  have hLbn : ∀ θ ∈ complexStrip n (N.r s - 3 * N.δ s), ‖tangentMat Kb θ‖ ≤
      m 0 + N.rate s 0 * N.wt s 0 * X := fun θ hθ => by
    rw [r0]
    calc ‖tangentMat Kb θ‖ = ‖tangentMat K θ + (tangentMat Kb θ - tangentMat K θ)‖ := by
          rw [add_sub_cancel]
      _ ≤ m 0 + (N.inp s).n * (stepConstsB (N.inp s)).CDK * X :=
          (norm_add_le _ _).trans (add_le_add (hG.L θ (hsubr hθ)) (hLb θ hθ).1)
      _ = _ := rfl
  have hLtn : ∀ θ ∈ complexStrip n (N.r s - 3 * N.δ s), ‖(tangentMat Kb θ)ᵀ‖ ≤
      m 1 + N.rate s 1 * N.wt s 1 * X := fun θ hθ => by
    rw [r1]
    calc ‖(tangentMat Kb θ)ᵀ‖ = ‖(tangentMat K θ)ᵀ + ((tangentMat Kb θ)ᵀ - (tangentMat K θ)ᵀ)‖ :=
          by rw [add_sub_cancel]
      _ ≤ m 1 + 2 * (N.inp s).n * (stepConstsB (N.inp s)).CDK * X :=
          (norm_add_le _ _).trans (add_le_add (hG.Lt θ (hsubr hθ)) (hLb θ hθ).2)
      _ = _ := rfl
  have hGn : ∀ θ ∈ complexStrip n (N.r s - 3 * N.δ s), IsUnit (gramMatrix Kb θ).det ∧
      ‖(gramMatrix Kb θ)⁻¹‖ ≤ m 2 + N.rate s 2 * N.wt s 2 * X := fun θ hθ => by
    rw [r2]
    refine ⟨(hGb θ hθ).1, ?_⟩
    calc ‖(gramMatrix Kb θ)⁻¹‖ =
        ‖(gramMatrix K θ)⁻¹ + ((gramMatrix Kb θ)⁻¹ - (gramMatrix K θ)⁻¹)‖ := by rw [add_sub_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (hG.G θ (hsubr hθ)).2 (hGb θ hθ).2)
  have hNn : ∀ θ ∈ complexStrip n (N.r s - 3 * N.δ s), ‖normalMat Kb θ‖ ≤
      m 3 + N.rate s 3 * N.wt s 3 * X := fun θ hθ => by
    rw [r3]
    calc ‖normalMat Kb θ‖ = ‖normalMat K θ + (normalMat Kb θ - normalMat K θ)‖ := by
          rw [add_sub_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (hG.Nm θ (hsubr hθ)) (hNb θ hθ).1)
  have hNtn : ∀ θ ∈ complexStrip n (N.r s - 3 * N.δ s), ‖(normalMat Kb θ)ᵀ‖ ≤
      m 4 + N.rate s 4 * N.wt s 4 * X := fun θ hθ => by
    rw [r4]
    calc ‖(normalMat Kb θ)ᵀ‖ = ‖(normalMat K θ)ᵀ + ((normalMat Kb θ)ᵀ - (normalMat K θ)ᵀ)‖ := by
          rw [add_sub_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (hG.NmT θ (hsubr hθ)) (hNb θ hθ).2)
  -- the ball
  have hball' : ∀ θ ∈ complexStrip n (N.r s - 3 * N.δ s), Metric.ball (Kb θ) (β - d) ⊆ 𝔅 :=
    fun θ hθ => PerturbationAux.ball_subset_of_close (hG.ball θ (hsubr hθ))
      (hdisp θ (hsub2 hθ))
  have hβd : 0 < β - d := by rw [hdd]; linarith
  -- the drift of `⟨𝒯_ab⟩`
  have hdK' : ∀ θ ∈ complexStrip n (N.r s - 3 * N.δ s), ‖fderiv ℂ Kb θ‖ ≤ N.sK := fun θ hθ => by
    rw [← norm_colMat]; exact (hLbn θ hθ).trans (hcp 0)
  have hGB' : ∀ θ ∈ complexStrip n (N.r s - 3 * N.δ s),
      IsUnit (gramMatrix Kb θ).det ∧ ‖(gramMatrix Kb θ)⁻¹‖ ≤ N.sB := fun θ hθ =>
    ⟨(hGn θ hθ).1, (hGn θ hθ).2.trans (hcp 2)⟩
  have hdK : ∀ θ ∈ complexStrip n (N.r s), ‖fderiv ℂ K θ‖ ≤ N.sK := fun θ hθ => by
    rw [← norm_colMat]; exact (hG.L θ hθ).trans (hcaps 0)
  have hGB : ∀ θ ∈ complexStrip n (N.r s),
      IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ N.sB := fun θ hθ =>
    ⟨(hG.G θ hθ).1, (hG.G θ hθ).2.trans (hcaps 2)⟩
  obtain ⟨hcAB', -⟩ := R.cont_AB hr' hβd (hKbd.mono hsub2) hball' hdK' hGB'
  obtain ⟨hcAB, -⟩ := R.cont_AB (hr'.trans_le h3r) hG.β_pos hG.holo hG.ball hdK hGB
  have hdrift : ‖torsionABAverage h Kb - torsionABAverage h K0‖ ≤
      m 5 + N.rate s 5 * N.wt s 5 * X := by
    rw [r5]
    have h1 : ‖torsionABAverage h Kb - torsionABAverage h K‖ ≤ (stepConstsB (N.inp s)).Cab * X := by
      rw [torsionABAverage_eq hcAB', torsionABAverage_eq hcAB]
      exact norm_torusAverage_sub_le hcAB' hcAB fun x =>
        hTab _ (ofReal_mem_complexStrip hr' x)
    calc _ = ‖(torsionABAverage h Kb - torsionABAverage h K) +
          (torsionABAverage h K - torsionABAverage h K0)‖ := by abel_nf
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add h1 hG.drift)
      _ = _ := by ring
  -- the new weighted error
  have hlam1 : (N.inp (s + 1)).lam = 1 := by
    show (if s + 1 = 0 then N.lam0 else 1) = 1
    simp
  have hQL : (stepConstsB (N.inp s)).QL ≤ N.Qs s := le_max_left _ _
  have hQN : (N.inp s).a ^ (N.inp s).κ * (stepConstsB (N.inp s)).QbN ≤ N.Qs s := le_max_right _ _
  have hg1 := R.gd1_pos s
  have hηL' : ∀ θ ∈ complexStrip n (N.r s - 3 * N.δ s), ‖etaL h Kb ω θ‖ ≤
      (N.inp (s + 1)).lam * (N.Qs s * w ^ 2 / (γ * N.δ s ^ (N.τ + 1))) := fun θ hθ => by
    rw [hlam1, one_mul]
    refine (hηLb θ hθ).trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hQL (sq_nonneg _)) hg1.le
  have hηN' : ∀ θ ∈ complexStrip n (N.r s - 3 * N.δ s), ‖etaN h Kb ω θ‖ ≤
      γ * N.δ (s + 1) ^ N.τ * (N.Qs s * w ^ 2 / (γ * N.δ s ^ (N.τ + 1))) := fun θ hθ => by
    refine (hηNb θ hθ).trans ?_
    have ha := R.wf.a_pos
    have hδ := R.wf.δ_pos s
    have hpa : 0 < N.a ^ N.τ := Real.rpow_pos_of_pos ha _
    have e1 : N.δ (s + 1) ^ N.τ = N.δ s ^ N.τ / N.a ^ N.τ := by
      rw [R.wf.δ_succ, Real.div_rpow hδ.le ha.le]
    have e2 : N.δ s ^ (N.τ + 1) = N.δ s ^ N.τ * N.δ s := Real.rpow_add_one hδ.ne' _
    have hδτ : 0 < N.δ s ^ N.τ := Real.rpow_pos_of_pos hδ _
    have key : γ * N.δ (s + 1) ^ N.τ * (N.Qs s * w ^ 2 / (γ * N.δ s ^ (N.τ + 1))) =
        N.Qs s / N.a ^ N.τ * (w ^ 2 / N.δ s) := by
      have hγ0 := R.γ_pos.ne'
      rw [e1, e2]; field_simp
    rw [key, div_eq_mul_one_div ((stepConstsB (N.inp s)).QbN * w ^ 2), mul_assoc]
    have hQN' : (stepConstsB (N.inp s)).QbN ≤ N.Qs s / N.a ^ N.τ := by
      rw [le_div_iff₀ hpa, mul_comm]; exact hQN
    have hw2 : 0 ≤ w ^ 2 * (1 / N.δ s) := by positivity
    calc (stepConstsB (N.inp s)).QbN * (w ^ 2 * (1 / N.δ s)) ≤
        N.Qs s / N.a ^ N.τ * (w ^ 2 * (1 / N.δ s)) := mul_le_mul_of_nonneg_right hQN' hw2
      _ = _ := by ring
  refine ⟨{ r_eq := R.wf.r_succ s
            μ_nonneg := by positivity
            μ_le := R.mu_succ_le hw0 hG.μ_le
            holo := hKbd.mono hsub2
            primary := fun θ hθ k => hKbp θ (hsub2 hθ) k
            real := hKbr
            ball := hball'
            β_pos := hβd
            L := hLbn
            Lt := hLtn
            G := hGn
            Nm := hNn
            NmT := hNtn
            drift := hdrift
            ηL := hηL'
            ηN := hηN'
            E0 := fun h0 => absurd h0 (Nat.succ_ne_zero s) }, fun θ hθ => ?_⟩
  exact hdisp θ (hsub2 hθ)

end RunHyp

end KAM.Sharp2.RouteB

end
