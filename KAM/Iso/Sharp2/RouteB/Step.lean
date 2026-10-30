/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.RouteB.Scheme
public import KAM.Iso.Sharp2.RouteA.Correction
public import KAM.Sharp2.RouteB.Newton
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# One stage of the isoenergetic route B: from stage `s` to stage `s + 1`

`RunHypI.good_step`: at a flagged state of stage `s` (`GoodI`) satisfying the step conditions, the
ball condition and the caps of the engine, the bordered modified step (`modified_stepIB`, with the
torsion data of `RunHypI.tors`) gives a flagged state of stage `s + 1`, with the engine's updates,
the displacement `|K̄ - K| ≤ C_ΔK μ/(γ δ_s^τ)` and the frequency increment
`|ς̄ - ς| |ω*| ≤ Θ C_0 μ`.

The frequency part of `Tab`: with `μ ≤ g₁ X`, `C_ab X + Θ C_0 μ ≤ C^𝖳_ab X` for the first form of
the drift, and `n Θ C_0 μ ≤ C^𝖳_ab X` for the second. The new energy error is `Q_ω μ²/(γ δ^{τ+1})`,
with `Q_ω ≤ Q_L ≤ Q`, at the weight `λ_ω = 1` of stage `s + 1`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology MeasureTheory

namespace KAM.Iso.Sharp2.RouteB

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteB KAM.Iso.Linear KAM.Iso.Apost
open KAM.Iso.Sharp2.ModStepB (newK newOmega_smul muI xI)

variable {n : ℕ} {N : NumB n} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ωstar : Fin n → ℝ} {Ω : Set (Fin n → ℝ)}
  {τ M E₀ σω ν γ σT μm Xi ς0 : ℝ} {K0 : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

/-- A positive ray margin bounds the frequency by `σ_ω |ω*|` (as for route A, in dimension `n`). -/
theorem norm_smul_le_of_margin' {s ν' : ℝ} (hs : 1 < s) (hν' : 0 < ν')
    (h : ν' ≤ rayMargin σω ωstar s) : ‖s • ωstar‖ ≤ σω * ‖ωstar‖ := by
  have hpos : 0 < rayMargin σω ωstar s := hν'.trans_le h
  have hmin : 0 < min (s - 1) (σω - s) := by
    by_contra hneg
    exact absurd (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) (norm_nonneg ωstar))
      (not_le.2 hpos)
  have h2 : s < σω := by linarith [(lt_min_iff.1 hmin).2]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
  exact mul_le_mul_of_nonneg_right h2.le (norm_nonneg _)

namespace RunHypI

variable (R : RunHypI τ M N 𝔅 h ωstar Ω σω ν γ σT μm K0 ς0)
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

/-- `|η̄ᴺ| ≤ Q̄_N μ²/δ` is at most `γ δ_{s+1}^τ · Q_s μ²/(γ δ^{τ+1})`. -/
theorem etaN_succ_le {s : ℕ} {w : ℝ} :
    (stepConstsB (N.inp s)).QbN * w ^ 2 / N.δ s ≤
      γ * N.δ (s + 1) ^ N.τ * (N.Qs s * w ^ 2 / (γ * N.δ s ^ (N.τ + 1))) := by
  have hQN : (N.inp s).a ^ (N.inp s).κ * (stepConstsB (N.inp s)).QbN ≤ N.Qs s := le_max_right _ _
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

omit R in
/-- The frequency cap's rate and weight. -/
theorem rate_wt6 (s : ℕ) (hδ : 0 < N.δ (min s N.kp)) :
    N.rate s 6 * N.wt s 6 = (stepConstsB (N.inp s)).Cnu * sg1 (N.inp s) := by
  have e : sg1 (N.inp s) = N.wt s 6 := by
    show N.γb * N.δ (min s N.kp) ^ N.τ * N.δ (min s N.kp) =
      N.γb * N.δ (min s N.kp) ^ (N.τ + 1)
    rw [Real.rpow_add_one hδ.ne']
    ring
  rw [e]
  rfl

/-- The increments of the drift: `C_ab X + d ≤ C^𝖳_ab X`, `n d ≤ C^𝖳_ab X` for a frequency increment
`d ≤ Θ C_0 w`, `w ≤ g₁ X`. -/
theorem drift_incr {s : ℕ} {w d X : ℝ} (hX : 0 ≤ X) (hw : w ≤ sg1 (N.inp s) * X)
    (hd : d ≤ (stepConstsB (N.inp s)).Cnu * w) :
    sCab0 (N.inp s) * X + d ≤ (stepConstsB (N.inp s)).Cab * X ∧
      n * d ≤ (stepConstsB (N.inp s)).Cab * X := by
  have hok := R.wf.inp_ok s
  have hiso : (N.inp s).iso = true := R.iso
  have hnu : (stepConstsB (N.inp s)).Cnu = (N.inp s).Θ * sC0 (N.inp s) := by
    show sCnu (N.inp s) = _
    rw [sCnu]
    simp only [hiso, ↓reduceIte]
  have hcab : (stepConstsB (N.inp s)).Cab = max (sCab0 (N.inp s) +
      (N.inp s).Θ * sC0 (N.inp s) * sg1 (N.inp s))
      ((n : ℝ) * (N.inp s).Θ * sC0 (N.inp s) * sg1 (N.inp s)) := by
    show sCab (N.inp s) = _
    rw [sCab]
    simp only [hiso, ↓reduceIte]
    rfl
  have hc0 : 0 ≤ (N.inp s).Θ * sC0 (N.inp s) := mul_nonneg hok.nonneg.2.2.2.2.1 (nn_sC0 hok)
  have h1 : d ≤ (N.inp s).Θ * sC0 (N.inp s) * sg1 (N.inp s) * X := by
    rw [hnu] at hd
    calc d ≤ (N.inp s).Θ * sC0 (N.inp s) * w := hd
      _ ≤ (N.inp s).Θ * sC0 (N.inp s) * (sg1 (N.inp s) * X) := mul_le_mul_of_nonneg_left hw hc0
      _ = _ := by ring
  rw [hcab]
  constructor
  · calc _ ≤ sCab0 (N.inp s) * X + (N.inp s).Θ * sC0 (N.inp s) * sg1 (N.inp s) * X := by linarith
      _ = (sCab0 (N.inp s) + (N.inp s).Θ * sC0 (N.inp s) * sg1 (N.inp s)) * X := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hX
  · calc (n : ℝ) * d ≤ (n : ℝ) * ((N.inp s).Θ * sC0 (N.inp s) * sg1 (N.inp s) * X) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ = (n : ℝ) * (N.inp s).Θ * sC0 (N.inp s) * sg1 (N.inp s) * X := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hX

/-- One stage of the isoenergetic route B. -/
theorem good_step {s : ℕ} {β w : ℝ} {m : Fin 7 → ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ς : ℝ}
    (hG : GoodI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 s (N.r s) β w m K ς)
    (hcond : stepCondB (N.inp s) (w / (γ * N.δ s ^ (N.τ + 1))))
    (hβ : (stepConstsB (N.inp s)).CDK * w / (γ * N.δ s ^ N.τ) < β)
    (hcap : ∀ i, m i + N.rate s i * N.wt s i * (w / (γ * N.δ s ^ (N.τ + 1))) ≤
      capB N σT μm ν i) :
    GoodI N 𝔅 h ωstar E₀ σω ν γ Xi K0 ς0 (s + 1) (N.r s - 3 * N.δ s)
        (β - (stepConstsB (N.inp s)).CDK * w / (γ * N.δ s ^ N.τ))
        (N.Qs s * w ^ 2 / (γ * N.δ s ^ (N.τ + 1)))
        (fun i => m i + N.rate s i * N.wt s i * (w / (γ * N.δ s ^ (N.τ + 1))))
        (newK h K (ς • ωstar) E₀ (N.r s - 2 * N.δ s)) (isoNewS h K ωstar E₀ ς) ∧
      (∀ θ ∈ complexStrip n (N.r s - 3 * N.δ s),
        ‖newK h K (ς • ωstar) E₀ (N.r s - 2 * N.δ s) θ - K θ‖ ≤
          (stepConstsB (N.inp s)).CDK * w / (γ * N.δ s ^ N.τ)) ∧
      |isoNewS h K ωstar E₀ ς * ‖ωstar‖ - ς * ‖ωstar‖| ≤ (stepConstsB (N.inp s)).Cnu * w := by
  have hw0 := hG.μ_nonneg
  have hcaps := R.caps_of hw0 hcap
  obtain ⟨hT, hTa⟩ := R.tors hG hcond hcaps
  obtain ⟨hc, ⟨c', hc', hc1⟩, cb, hcb, hcavg⟩ := R.cert.at R.wf s
  have hSet := R.setting hG.ς_gt
  have hS := hSet.toStanding
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := KAM.Sharp2.RouteB.RunBase.rate_wt (N := N) s
  have r6 := rate_wt6 (N := N) s (R.wf.δ_pos _)
  obtain ⟨c2, L⟩ := R.loc hG hcond hcaps
  set X := w / (γ * N.δ s ^ (N.τ + 1)) with hXd
  have hX0 : 0 ≤ X := div_nonneg hw0 (R.gd1_pos s).le
  have hgd := R.gd_pos s
  have hlam := (R.wf.inp_lam_pos s).1
  have hlamW : 0 < (N.inp s).lamW := (R.wf.inp_ok s).lam.2.2.1
  have hmax : muI (N.inp s) γ ((N.inp s).lam * w) (γ * N.δ s ^ N.τ * w) ((N.inp s).lamW * w)
      (N.δ s) = w := by
    show max (max ((N.inp s).lam * w / (N.inp s).lam)
      (γ * N.δ s ^ N.τ * w / (γ * N.δ s ^ N.τ))) ((N.inp s).lamW * w / (N.inp s).lamW) = w
    rw [mul_div_cancel_left₀ _ hlam.ne', mul_div_cancel_left₀ _ hgd.ne',
      mul_div_cancel_left₀ _ hlamW.ne', max_self, max_self]
  have hXI : xI (N.inp s) γ ((N.inp s).lam * w) (γ * N.δ s ^ N.τ * w) ((N.inp s).lamW * w)
      (N.δ s) = X := by rw [xI, hmax]; rfl
  -- the frequency: the ray margin at `ς`
  have hν := R.std.ν_pos
  have hc6 : m 6 + (stepConstsB (N.inp s)).Cnu * sg1 (N.inp s) * X ≤ ν / 2 := by
    have := hcap 6
    rwa [r6] at this
  have hCnu : 0 ≤ (stepConstsB (N.inp s)).Cnu := (stepConstsB_nonneg (R.wf.inp_ok s)).2.2.2.2.2.2.2
  have hsgX : w ≤ sg1 (N.inp s) * X := by
    have h1 := L.mu_le
    rw [R.mu_eq s, R.xX_eq s] at h1
    exact h1
  have hdX : (stepConstsB (N.inp s)).Cnu * w ≤
      (stepConstsB (N.inp s)).Cnu * sg1 (N.inp s) * X := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hsgX hCnu
  have hdnn : 0 ≤ (stepConstsB (N.inp s)).Cnu * sg1 (N.inp s) * X :=
    (mul_nonneg hCnu hw0).trans hdX
  have hν' : 0 < ν - m 6 := by linarith
  have hΘ : ‖ς • ωstar‖ ≤ (N.inp s).Θ := by
    have := norm_smul_le_of_margin' hG.ς_gt hν' hG.ray
    show ‖ς • ωstar‖ ≤ N.Θ
    rw [R.hΘ]
    exact this
  -- the step
  have hst := modified_stepIB (N.inp s) (𝔅 := 𝔅) (h := h) (K := K) (ω := ς • ωstar) (Ω := Ω)
    (E₀ := E₀) (γ := γ) (β := β) (εL := (N.inp s).lam * w) (εN := γ * N.δ s ^ N.τ * w)
    (εω := (N.inp s).lamW * w) (δ := N.δ s) (r := N.r s) (s := N.split) (c' := c')
    (b := N.bfull s) (cb := cb) (m := ![m 0, m 1, m 2, m 3, m 4])
    (R.wf.inp_ok s) rfl R.iso R.γ_pos R.γ_le (R.wf.δ_pos s) (R.wf.δ_le_inp s)
    (R.wf.three_δ_lt s) (R.mem _ hG.ς_gt.le) hc ⟨R.wf.split_pos, R.wf.split_lt_one⟩ hc' hc1
    ⟨R.wf.δ_le_bfull s, NumB.Wf.bfull_le (N := N) s⟩ hcb hcavg hS R.dX R.d2X R.comm R.lip
    ⟨M, fun z hz => (R.std.bounds z hz).1⟩ R.d2H hG.holo hG.primary hG.real hG.ball hG.L hG.Lt hG.G
    hG.Nm hG.NmT hT hTa
    (fun θ hθ => by
      have hθr : θ ∈ complexStrip n (N.r s) :=
        Triangular.strip_mono (by linarith [R.wf.δ_pos s]) hθ
      have e : (N.inp s).y0 = M * (N.inp s).sN := R.y0
      rw [e]
      exact KAM.Iso.Sharp2.RouteA.sum_norm_energyRow_le_ref
        (R.std.bounds _ (hG.ball θ hθr (Metric.mem_ball_self hG.β_pos))).1
        ((hG.Nm θ hθr).trans (hcaps 3)))
    hΘ hG.ηL hG.ηN hG.ηω
    (fun h0 θ hθ => by rw [hmax]; exact hG.E0 (of_decide_eq_true h0) θ hθ)
    (by rw [hXI]; exact hcond) (by rw [hmax]; exact hβ) (by
      rw [hXI]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · have := hcap 0; rw [r0] at this
        show m 0 + (n : ℝ) * (stepConstsB (N.inp s)).CDK * X ≤ N.sK; exact this
      · have := hcap 1; rw [r1] at this
        show m 1 + 2 * (n : ℝ) * (stepConstsB (N.inp s)).CDK * X ≤ N.sLt; exact this
      · have := hcap 2; rw [r2] at this; exact this
      · have := hcap 3; rw [r3] at this; exact this
      · have := hcap 4; rw [r4] at this; exact this)
  dsimp only at hst
  rw [hmax, hXI, newOmega_smul] at hst
  obtain ⟨hKbd, hKbp, hKbr, hdisp, hfreq, hηNb, hηLb, hEn, hLb, hGb, hNb, hTab, -⟩ := hst
  set ς' := isoNewS h K ωstar E₀ ς with hς'
  -- the strips
  have h32 : N.r s - 3 * N.δ s ≤ N.r s - 2 * N.δ s := by linarith [R.wf.δ_pos s]
  have h3r : N.r s - 3 * N.δ s ≤ N.r s := by linarith [R.wf.δ_pos s]
  have hsub2 := Triangular.strip_mono (n := n) h32
  have hsubr := Triangular.strip_mono (n := n) h3r
  have hr' : 0 < N.r s - 3 * N.δ s := by rw [R.wf.r_succ]; linarith [R.wf.r_gt (s + 1),
    R.wf.ρinf_pos]
  set Kb := newK h K (ς • ωstar) E₀ (N.r s - 2 * N.δ s) with hKb
  set d := (stepConstsB (N.inp s)).CDK * w / (γ * N.δ s ^ N.τ) with hdd
  have hQ : 0 ≤ N.Qs s := by
    have := (stageC_nonneg R.wf (N.δ s)).1
    rwa [stageC_sched R.wf] at this
  have hcp := fun i => hcap i
  -- the frequency: the new ray margin
  have hνd : (stepConstsB (N.inp s)).Cnu * w < ν - m 6 := by linarith
  obtain ⟨hς1, -, hray'⟩ := (KAM.Iso.Apost.ray (σω := σω) R.std.dio).2.2.2.2.2 ς ς' (ν - m 6) _
    hG.ray hfreq hνd
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
  have hcAB' := Triangular.continuous_ofReal_comp hr'
    (diffOn_torsionAB hS hr' hβd (hKbd.mono hsub2) hball' hdK' hGB')
  have hcAB := Triangular.continuous_ofReal_comp (hr'.trans_le h3r)
    (diffOn_torsionAB hS (hr'.trans_le h3r) hG.β_pos hG.holo hG.ball hdK hGB)
  have h1 : ‖torsionABAverage h Kb - torsionABAverage h K‖ ≤ sCab0 (N.inp s) * X := by
    rw [torsionABAverage_eq hcAB', torsionABAverage_eq hcAB]
    exact norm_torusAverage_sub_le hcAB' hcAB fun x =>
      hTab _ (ofReal_mem_complexStrip hr' x)
  obtain ⟨hinc1, hinc2⟩ := R.drift_incr (s := s) hX0 hsgX (d := ‖ς' • ωstar - ς • ωstar‖) hfreq
  have hfr : ‖ς' • ωstar - ς0 • ωstar‖ ≤ ‖ς' • ωstar - ς • ωstar‖ + ‖ς • ωstar - ς0 • ωstar‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hab : ‖torsionABAverage h Kb - torsionABAverage h K0‖ ≤
      sCab0 (N.inp s) * X + ‖torsionABAverage h K - torsionABAverage h K0‖ :=
    (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add_left h1 _)
  have hdrift1 : ‖torsionABAverage h Kb - torsionABAverage h K0‖ + ‖ς' • ωstar - ς0 • ωstar‖ ≤
      m 5 + N.rate s 5 * N.wt s 5 * X := by
    rw [r5]
    linarith [hG.drift]
  have hdrift2 : (n : ℝ) * ‖ς' • ωstar - ς0 • ωstar‖ ≤ m 5 + N.rate s 5 * N.wt s 5 * X := by
    rw [r5]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hfr hn
    rw [mul_add] at this
    linarith [hG.drift']
  -- the new weighted error
  have hlam1 : (N.inp (s + 1)).lam = 1 := by
    show (if s + 1 = 0 then N.lam0 else 1) = 1
    simp
  have hlamW1 : (N.inp (s + 1)).lamW = 1 := by
    show (if s + 1 = 0 then N.lamW0 else 1) = 1
    simp
  have hQL : (stepConstsB (N.inp s)).QL ≤ N.Qs s := le_max_left _ _
  have hg1 := R.gd1_pos s
  have hQw : sQw (N.inp s) ≤ (stepConstsB (N.inp s)).QL := by
    show sQw (N.inp s) ≤ sQL (N.inp s)
    rw [sQL]
    simp only [show (N.inp s).iso = true from R.iso, ↓reduceIte]
    exact le_max_right _ _
  have hηL' : ∀ θ ∈ complexStrip n (N.r s - 3 * N.δ s), ‖etaL h Kb (ς' • ωstar) θ‖ ≤
      (N.inp (s + 1)).lam * (N.Qs s * w ^ 2 / (γ * N.δ s ^ (N.τ + 1))) := fun θ hθ => by
    rw [hlam1, one_mul]
    refine (hηLb θ hθ).trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hQL (sq_nonneg _)) hg1.le
  have hηN' : ∀ θ ∈ complexStrip n (N.r s - 3 * N.δ s), ‖etaN h Kb (ς' • ωstar) θ‖ ≤
      γ * N.δ (s + 1) ^ N.τ * (N.Qs s * w ^ 2 / (γ * N.δ s ^ (N.τ + 1))) := fun θ hθ =>
    (hηNb θ hθ).trans R.etaN_succ_le
  have hEn' : ‖KAM.Iso.energyAverage h Kb - (E₀ : ℂ)‖ ≤
      (N.inp (s + 1)).lamW * (N.Qs s * w ^ 2 / (γ * N.δ s ^ (N.τ + 1))) := by
    rw [hlamW1, one_mul]
    refine hEn.trans ?_
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hQw.trans hQL) (sq_nonneg _)) hg1.le
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
            drift := hdrift1
            drift' := hdrift2
            ς_gt := hς1
            ray := ?_
            ηL := hηL'
            ηN := hηN'
            ηω := hEn'
            E0 := fun h0 => absurd h0 (Nat.succ_ne_zero s) }, fun θ hθ => hdisp θ (hsub2 hθ), ?_⟩
  · have : ν - m 6 - (stepConstsB (N.inp s)).Cnu * sg1 (N.inp s) * X ≤
        rayMargin σω ωstar ς' := by linarith
    show ν - (m 6 + N.rate s 6 * N.wt s 6 * X) ≤ rayMargin σω ωstar ς'
    rw [r6]
    linarith
  · rw [← sub_mul, abs_mul, abs_of_nonneg (norm_nonneg ωstar),
      ← (KAM.Iso.Apost.ray (σω := σω) R.std.dio).2.2.2.1 ς ς']
    exact hfreq

end RunHypI

end KAM.Iso.Sharp2.RouteB

end
