/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.ActionBudgetData

/-!
# P Part 5: the Diophantine part of the budget (`stepP:p5:bu-dio`)

The set `D \ D₀` of actions of the Cantor domain lost to the two-scale Diophantine condition is
contained in the resonant set of the inner core times the action shell, to which the P4 measure
estimate `two_scale_diophantine_measure` applies with `α_i = 2π γ_i` (`resonanceBad_eq`).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-BU.
-/

@[expose] public noncomputable section

open Set MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

theorem twoScale_smul_inv {γ₁ γ₂ τ : ℝ} {ω : Fin (a+b) → ℝ}
    (hω : ω ∈ twoScaleDiophantine a b (2*Real.pi*γ₁) (2*Real.pi*γ₂) τ) :
    (2*Real.pi)⁻¹ • ω ∈ twoScaleDiophantine a b γ₁ γ₂ τ := by
  have hpi : 0 < 2*Real.pi := by positivity
  have hs : ∀ k : Fin (a+b) → ℤ, ∑ i, (k i : ℝ) * ((2*Real.pi)⁻¹ • ω) i =
      (2*Real.pi)⁻¹ * ∑ i, (k i : ℝ) * ω i := fun k => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  have key : ∀ (g N : ℝ) (S : ℝ), 2*Real.pi*g/N ≤ |S| → g/N ≤ |(2*Real.pi)⁻¹ * S| := by
    intro g N S hh
    rw [abs_mul, abs_of_pos (inv_pos.2 hpi)]
    rw [mul_div_assoc] at hh
    calc g/N = (2*Real.pi)⁻¹ * (2*Real.pi*(g/N)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (inv_pos.2 hpi).le
  refine ⟨fun k hk => ?_, fun k hk0 hk => ?_⟩
  · rw [hs]; exact key _ _ _ (hω.1 k hk)
  · rw [hs]; exact key _ _ _ (hω.2 k hk0 hk)

theorem dio_real {c1 U1 U2 k0 r mu lam : ℝ} (hc1 : c1 ≤ U1) (hc1' : 0 ≤ c1) (hU2 : 0 ≤ U2)
    (hk0 : 0 < k0) (hr0 : 0 < r) (hr1 : r < 1) (hmu0 : 0 < mu) (hmu : mu < r^6)
    (hlam : r^2/4 ≤ lam) :
    c1*(2*Real.pi*(k0*r^(5/2:ℝ)))*(1+mu/lam) +
      U2*(2*Real.pi*(mu*k0*r^(5/2:ℝ))/mu)/lam ≤
        2*Real.pi*k0*Real.sqrt r*(5*U1+4*U2) := by
  have hr2 : 0 < r^2 := by positivity
  have hlam0 : 0 < lam := lt_of_lt_of_le (by positivity) hlam
  have hsq : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have h52 : r^(5/2:ℝ) = r^2*Real.sqrt r := rpow_five_halves hr0
  have hX : 2*Real.pi*(mu*k0*r^(5/2:ℝ))/mu = 2*Real.pi*(k0*r^(5/2:ℝ)) := by
    field_simp
  rw [hX, h52]
  have hmul : mu/lam ≤ 4 := by
    rw [div_le_iff₀ hlam0]
    have : mu ≤ r^2 := by
      have : r^6 ≤ r^2 := pow_le_pow_of_le_one hr0.le hr1.le (by norm_num)
      linarith
    nlinarith
  have hpi := Real.pi_pos
  have hr2' : r^2 ≤ 1 := by nlinarith
  have hXnn : 0 ≤ 2*Real.pi*(k0*(r^2*Real.sqrt r)) := by positivity
  have h1 : c1*(2*Real.pi*(k0*(r^2*Real.sqrt r)))*(1+mu/lam) ≤
      U1*(2*Real.pi*(k0*Real.sqrt r))*5 := by
    have hXle : 2*Real.pi*(k0*(r^2*Real.sqrt r)) ≤ 2*Real.pi*(k0*Real.sqrt r) := by
      have : r^2*Real.sqrt r ≤ Real.sqrt r := by nlinarith
      gcongr
    have hU1 : 0 ≤ U1 := hc1'.trans hc1
    calc c1*(2*Real.pi*(k0*(r^2*Real.sqrt r)))*(1+mu/lam)
        ≤ U1*(2*Real.pi*(k0*(r^2*Real.sqrt r)))*5 := by
          have : 1+mu/lam ≤ 5 := by linarith
          have h0 : 0 ≤ c1*(2*Real.pi*(k0*(r^2*Real.sqrt r))) := by positivity
          calc _ ≤ c1*(2*Real.pi*(k0*(r^2*Real.sqrt r)))*5 :=
                mul_le_mul_of_nonneg_left this h0
            _ ≤ _ := by gcongr
      _ ≤ _ := by gcongr
  have h2 : U2*(2*Real.pi*(k0*(r^2*Real.sqrt r)))/lam ≤ U2*(2*Real.pi*(k0*Real.sqrt r))*4 := by
    rw [div_le_iff₀ hlam0]
    have : U2*(2*Real.pi*(k0*(r^2*Real.sqrt r))) =
        U2*(2*Real.pi*(k0*Real.sqrt r))*r^2 := by ring
    rw [this]
    have h0 : 0 ≤ U2*(2*Real.pi*(k0*Real.sqrt r)) := by positivity
    calc U2*(2*Real.pi*(k0*Real.sqrt r))*r^2 =
        U2*(2*Real.pi*(k0*Real.sqrt r))*4*(r^2/4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlam (by positivity)
  have : U2*(2*Real.pi*(k0*(r^2*Real.sqrt r))/1) = U2*(2*Real.pi*(k0*(r^2*Real.sqrt r))) := by
    ring
  calc _ ≤ U1*(2*Real.pi*(k0*Real.sqrt r))*5 + U2*(2*Real.pi*(k0*Real.sqrt r))*4 := by
        rw [mul_div_assoc] at h2 ⊢
        linarith
    _ = _ := by ring

theorem checkedCore_subset (d : PGData a b) (r mu : ℝ) :
    checkedCore d r mu ⊆ innerCore d.V (Real.sqrt r) := fun _ hI => hI.1

theorem actionShell_volume (d : PGData a b) (r mu : ℝ) :
    volume (actionShell b (params d r mu).l1 (params d r mu).l2top) =
      ENNReal.ofReal ((params d r mu).ell) ^ b := by
  have hl : (params d r mu).l2top - (params d r mu).l1 = (params d r mu).ell := by
    rw [params_l2top, params_ell]; ring
  rw [actionShell, Real.volume_pi_Ioo]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hl]

theorem volume_pgActionDomain (d : PGData a b) {r mu : ℝ} (h : admissible d (pgRstar d) r mu) :
    volume (pgActionDomain d r mu) =
      volume (checkedCore d r mu) * ENNReal.ofReal ((params d r mu).ell ^ b) := by
  obtain ⟨hr0, -, -, -, -, -, -, hell, -⟩ := budget_facts d h
  rw [pgActionDomain, volume_joinedActions, actionShell_volume d r mu,
    ENNReal.ofReal_pow (le_trans (by positivity) hell)]

theorem budget_dio (d : PGData a b) {r mu : ℝ} (h : admissible d (pgRstar d) r mu) :
    volume (pgActionDomain d r mu \ pgD0 d r mu) ≤
      ENNReal.ofReal (4^(b+1)*2*Real.pi*(pgScales d).k0*
        (5*pgMeasureUpper1 d+4*pgMeasureUpper2 d)*Real.sqrt r) *
        volume (pgActionDomain d r mu) := by
  obtain ⟨hr0, hr1, hmu0, hmur6, hmu1, hl1, hl1', hell, -, -, -, hhalf, hquart⟩ :=
    budget_facts d h
  have hsq : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  obtain ⟨hA0, hD0, hcl⟩ := pgBoundary_spec d
  have hcol := collar d.hV d.hVb hcl
  have hcompact : IsCompact (innerCore d.V (Real.sqrt r)) := (hcol.1 _ hsq).1
  have hcoreV : innerCore d.V (Real.sqrt r) ⊆ d.V := (hcol.1 _ hsq).2.1
  have hV0 : volume d.V ≠ 0 := (d.hV.measure_pos volume d.hVc.nonempty).ne'
  have hvol : 0 < volume (innerCore d.V (Real.sqrt r)) :=
    lt_of_lt_of_le (ENNReal.mul_pos (by simp) hV0) hhalf
  set md := pgMeasureData d (innerCore d.V (Real.sqrt r)) hcompact hcoreV hvol with hmd
  set p := params d r mu with hp
  have hlam_ge : r^2/4 ≤ p.l2top := by rw [params_l2top]; rw [params_ell] at hell; linarith
  have hlam_le : p.l2top ≤ 1 := by rw [params_l2top]; nlinarith
  have hlam_pos : 0 < p.l2top := by linarith [(by positivity : (0:ℝ) < r^2/4)]
  have h2lam : 2*p.l2top ≤ 4*p.ell := by rw [params_l2top]; rw [params_ell] at hell ⊢; nlinarith
  have hmem : mu ∈ Ioc 0 md.mu1 := ⟨hmu0, hmu1⟩
  have hsub : pgActionDomain d r mu \ pgD0 d r mu ⊆ resonanceBad
      (freq md.H0 md.P0 md.Omega md.beta mu)
      (joinedActions (innerCore d.V (Real.sqrt r)) (actionShell b p.l1 p.l2top))
      (2*Real.pi*((pgScales d).k0*r^(5/2:ℝ))) (2*Real.pi*(mu*(pgScales d).k0*r^(5/2:ℝ)))
      md.tau := by
    intro J ⟨hJ, hJ0⟩
    rw [resonanceBad_eq]
    refine ⟨⟨checkedCore_subset d r mu hJ.1, hJ.2⟩, fun hω => hJ0 ⟨hJ, ?_⟩⟩
    exact twoScale_smul_inv (γ₁ := p.gamma1) (γ₂ := p.gamma2) hω
  have hQsub : actionShell b p.l1 p.l2top ⊆ actionShell b (-p.l2top) p.l2top := by
    intro y hy i hi
    exact ⟨by linarith [(hy i hi).1], (hy i hi).2⟩
  have hQm : MeasurableSet (actionShell b p.l1 p.l2top) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hk0 := pgScales_k0_pos d
  have hpow : 0 < r^(5/2:ℝ) := Real.rpow_pos_of_pos hr0 _
  have hmain := two_scale_diophantine_measure md p.l2top mu
    (2*Real.pi*((pgScales d).k0*r^(5/2:ℝ))) (2*Real.pi*(mu*(pgScales d).k0*r^(5/2:ℝ)))
    hlam_pos hlam_le hmem (by positivity) (by positivity) _ hQm hQsub
  have hτ : md.tau - ((a+b:ℕ):ℝ) = 1 := by
    show pgTau a b - ((a+b:ℕ):ℝ) = 1
    unfold pgTau; ring
  have hc1 := measure_c1_le d hcompact hcoreV hvol hhalf
  have hc1' := measure_c1_nonneg d hcompact hcoreV hvol
  have hU2 : 0 ≤ pgMeasureUpper2 d := by
    unfold pgMeasureUpper2
    have := (pgAnalytic_spec d).2.2.2.2.2.2.1
    have hS : 0 ≤ latticeS b (pgTau a b+1) :=
      latticeS_nonneg (by have := pgTau_pos a b; have : (b:ℝ) ≤ ((a+b:ℕ):ℝ) := by
                            exact_mod_cast Nat.le_add_left b a
                          unfold pgTau at *; linarith)
    positivity
  have hE : measure_c1 md * (2*Real.pi*((pgScales d).k0*r^(5/2:ℝ))) *
      (1+mu^(md.tau-((a+b:ℕ):ℝ))/p.l2top) +
      measure_c2 md * ((2*Real.pi*(mu*(pgScales d).k0*r^(5/2:ℝ)))/mu)/p.l2top ≤
      2*Real.pi*(pgScales d).k0*Real.sqrt r*(5*pgMeasureUpper1 d+4*pgMeasureUpper2 d) := by
    rw [hτ, Real.rpow_one]
    exact dio_real hc1 hc1' hU2 hk0 hr0 hr1 hmu0 hmur6 hlam_ge
  have h4 : ENNReal.ofReal (1/4) = 4⁻¹ := by
    rw [show (1/4:ℝ) = (4:ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  have hVX : volume d.V ≤ 4 * volume (checkedCore d r mu) := by
    rw [h4] at hquart
    exact (ENNReal.inv_mul_le_iff (by norm_num) (by norm_num)).1 hquart
  have hcX : volume (innerCore d.V (Real.sqrt r)) ≤ 4 * volume (checkedCore d r mu) :=
    (measure_mono hcoreV).trans hVX
  have hpow4 : (2*p.l2top)^b ≤ 4^b*p.ell^b := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h2lam b
  have hell0 : 0 ≤ p.ell := le_trans (by positivity) hell
  have hT0 : 0 ≤ 2*Real.pi*(pgScales d).k0*Real.sqrt r*
      (5*pgMeasureUpper1 d+4*pgMeasureUpper2 d) := by
    have : 0 ≤ pgMeasureUpper1 d := hc1'.trans hc1
    positivity
  calc volume (pgActionDomain d r mu \ pgD0 d r mu)
      ≤ volume (resonanceBad (freq md.H0 md.P0 md.Omega md.beta mu)
        (joinedActions (innerCore d.V (Real.sqrt r)) (actionShell b p.l1 p.l2top))
        (2*Real.pi*((pgScales d).k0*r^(5/2:ℝ))) (2*Real.pi*(mu*(pgScales d).k0*r^(5/2:ℝ)))
        md.tau) := measure_mono hsub
    _ ≤ _ := hmain
    _ ≤ ENNReal.ofReal (2*Real.pi*(pgScales d).k0*Real.sqrt r*
          (5*pgMeasureUpper1 d+4*pgMeasureUpper2 d)) * (4 * volume (checkedCore d r mu)) *
        ENNReal.ofReal (4^b*p.ell^b) := by
      gcongr
      exact hcX
    _ = _ := by
      rw [volume_pgActionDomain d h]
      have e1 : ENNReal.ofReal (4^(b+1)*2*Real.pi*(pgScales d).k0*
          (5*pgMeasureUpper1 d+4*pgMeasureUpper2 d)*Real.sqrt r) =
          ENNReal.ofReal (2*Real.pi*(pgScales d).k0*Real.sqrt r*
            (5*pgMeasureUpper1 d+4*pgMeasureUpper2 d)) * (4 * ENNReal.ofReal (4^b)) := by
        rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul hT0]
        congr 1; ring
      have e2 : ENNReal.ofReal (4^b*p.ell^b) = ENNReal.ofReal (4^b) * ENNReal.ofReal (p.ell^b) :=
        ENNReal.ofReal_mul (by positivity)
      rw [e1, e2]; ring

end KAM.Planetary

end
