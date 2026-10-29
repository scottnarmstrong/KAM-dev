/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.WrapperEps
public import KAM.Planetary.Preparation.WrapperNodeCore

/-!
# Literal export of `stepP:p11:wr-chain` (GAP-WR)

The source states that the chain `Ξ_ε = Ψ_c ∘ Φ¹_ε ∘ Θ̂ ∘ Ψ₂ ∘ A_ε` is defined and real analytic on
`ℛ = {|r| < 2, |ρ'| < π/2}` (real points), is an `ε`-chart with the full integer angle lattice,
and satisfies `H_fix ∘ Ξ_ε = ε Ĥ_ε`. The earlier export `p11_wr_chain` proves this on the smaller
real prepared domain `p11WrO`; here it is proved on `ℛ` itself, from the same signed
specifications. The smallness `4 ε ≤ s₂` (an eventual condition, see `p11_four_eps_le_s2_ev`)
replaces `π ε ≤ s₂`, so that the action window `|ε r| < 2 ε` lies in the half-box of radius `s₂/2`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
namespace KAM.Planetary

section Node

variable {n : ℕ}

/-- The literal carrier `ℛ` of `stepP:p11:wr-chain`: real points with `|r|_∞ < 2` and
`|ρ'|_∞ < π/2`. -/
def p11WrR (n : ℕ) : Set (Phase (n+n)) :=
  {z | (∀ i : Fin n, |z.2 (Fin.castAdd n i)| < 2) ∧
    ∀ i : Fin n, |z.2 (Fin.natAdd n i)| < Real.pi/2}

theorem p11WrR_shift {z : Phase (n+n)} (hz : z ∈ p11WrR n) (k : Fin (n+n) → ℤ) :
    z + KAM.ODE.angleShift k ∈ p11WrR n := by
  simpa [p11WrR, KAM.ODE.angleShift] using hz

theorem p11_pe_of_four {eps s : ℝ} (heps : 0 < eps) (h4 : 4*eps ≤ s) : Real.pi*eps ≤ s :=
  le_trans (by nlinarith [Real.pi_lt_four]) h4

/-- `A_ε` maps the literal carrier into the half-box `V₂/2`. -/
theorem p11WrR_rescale {C : P11SecularData n} {nu eps : ℝ} (hσ : 0 < C.sigma) (heps : 0 < eps)
    (h4 : 4*eps ≤ p11s2 C nu eps) {z : Phase (n+n)} (hz : z ∈ p11WrR n) :
    p11Rescale C.J0 eps (KAM.realInclusion₂ (n+n) z) ∈
      KAM.complexStrip (n+n) (C.sigma/12/6) ×ˢ
        p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
  · have : C.sigma/12/6 = C.sigma/72 := by ring
    rw [this]
    simpa [p11Rescale] using (by positivity : 0 < C.sigma/72)
  · have : (p11Rescale C.J0 eps (KAM.realInclusion₂ (n+n) z)).2 (Fin.castAdd n i) -
        p11SlowCenter C eps (Fin.castAdd n i) = ((eps * z.2 (Fin.castAdd n i) : ℝ) : ℂ) := by
      simp [p11Rescale, p11SlowCenter, Fin.append_left]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos heps]
    have := hz.1 i
    nlinarith
  · have : (p11Rescale C.J0 eps (KAM.realInclusion₂ (n+n) z)).2 (Fin.natAdd n i) -
        p11SlowCenter C eps (Fin.natAdd n i) = ((eps * z.2 (Fin.natAdd n i) : ℝ) : ℂ) := by
      simp [p11Rescale, p11SlowCenter]; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos heps]
    have := hz.2 i
    nlinarith

/-- The domain chain at a real point of the literal carrier. -/
theorem p11_wrR_dom {D : P11Physical n} {nu eps : ℝ}
    (hC : P11SecularSpec D (p11SecularData D))
    (hF : P11FastSpec (p11SecularData D) eps (p11FastData D eps))
    (hS : P11SlowSpec D nu eps (p11SlowConstant D nu) (p11SlowData D nu eps))
    (heps : 0 < eps) (h4 : 4*eps ≤ p11s2 (p11SecularData D) nu eps)
    (hsm : 256*eps < (p11SecularData D).rz^2) {z : Phase (n+n)} (hz : z ∈ p11WrR n) :
    let y := p11RescaleReal (p11SecularData D).J0 eps z
    let w := p11WrPsiR D nu eps y
    let u := p11PolarR w
    let v := p11WrFastR D eps u
    KAM.realInclusion₂ (n+n) y ∈ p11WrSlowDom D nu eps ∧ (∀ i : Fin n, 0 < w.2 (Fin.natAdd n i)) ∧
      KAM.realInclusion₂ (n+n) u ∈ p11WrFastDom D eps ∧
      KAM.realInclusion₂ (n+n) v ∈ p11WorkingDom n (p11SecularData D).J0
        (2*(p11SecularData D).sigma) (2*(p11SecularData D).rC) (p11SecularData D).rz ∧
      (p11FastData D eps).map (p11PolarC ((p11SlowData D nu eps).Psi
        (p11Rescale (p11SecularData D).J0 eps (KAM.realInclusion₂ (n+n) z)))) =
        KAM.realInclusion₂ (n+n) v := by
  intro y w u v
  have hpe := p11_pe_of_four heps h4
  obtain ⟨-, -, -, hrC0, -, hσ0, -, -, -, -⟩ := fast_consts hC
  have hS' := hS
  have hF' := hF
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hPsiM, -, -, -, -, -, -⟩ := hS'
  obtain ⟨-, -, -, -, -, -, -, -, -, hFM, -⟩ := hF'
  have hdom := p11_wr_chain_dom (nu := nu) (Fast := p11FastData D eps)
    (A := p11SlowData D nu eps) hC heps hpe hsm hFM hPsiM (p11WrR_rescale hσ0 heps h4 hz)
  have hy : KAM.realInclusion₂ (n+n) y = p11Rescale (p11SecularData D).J0 eps
      (KAM.realInclusion₂ (n+n) z) := (p11Rescale_real _ _ _).symm
  have hyd : KAM.realInclusion₂ (n+n) y ∈ p11WrSlowDom D nu eps := hy ▸ hdom.1
  obtain ⟨-, -, hreal, -⟩ := p11WrPsiR_facts hS
  have hPsi : (p11SlowData D nu eps).Psi (KAM.realInclusion₂ (n+n) y) =
      KAM.realInclusion₂ (n+n) w := (hreal y hyd).symm
  have hbox := hdom.2.1
  rw [← hy, hPsi] at hbox
  have hpos : ∀ i : Fin n, 0 < w.2 (Fin.natAdd n i) := fun i => by
    have := p11_slowBox_re_pos (nu := nu) hbox.2 i
    have h2 : (KAM.realInclusion₂ (n+n) w).2 (Fin.natAdd n i) = (w.2 (Fin.natAdd n i) : ℂ) := rfl
    rw [h2, Complex.ofReal_re] at this
    nlinarith [Real.pi_pos]
  have hpol : p11PolarC (KAM.realInclusion₂ (n+n) w) = KAM.realInclusion₂ (n+n) u :=
    p11_polarC_real hpos
  have hud : KAM.realInclusion₂ (n+n) u ∈ p11WrFastDom D eps := by
    have := hdom.2.2.2.1
    rw [← hy, hPsi, hpol] at this
    exact this
  obtain ⟨-, -, hFreal, -⟩ := p11WrFastR_facts hF
  have hFv : (p11FastData D eps).map (KAM.realInclusion₂ (n+n) u) =
      KAM.realInclusion₂ (n+n) v := (hFreal u hud).symm
  have h5 := hdom.2.2.2.2
  rw [← hy, hPsi, hpol, hFv] at h5
  have hs1 : p11s1 (p11SecularData D) eps ≤ 2*(p11SecularData D).rC := by
    have := min_le_left (p11SecularData D).rC
      ((p11SecularData D).gamma/(4*(p11SecularData D).L*
        p11K1 (p11SecularData D) eps^((p11SecularData D).tau+1)))
    unfold p11s1; linarith
  refine ⟨hyd, hpos, hud, p11WorkingDom_mono (by linarith) hs1 le_rfl h5, ?_⟩
  rw [← hy, hPsi, hpol, hFv]


/-- `stepP:p11:wr-chain` on the literal carrier `|r| < 2`, `|ρ'| < π/2` (the Hamiltonian
identity is `p11_wr_ham_node`). -/
theorem p11_wr_chain_node {D : P11Physical n} {nu eps : ℝ}
    (hC : P11SecularSpec D (p11SecularData D))
    (hF : P11FastSpec (p11SecularData D) eps (p11FastData D eps))
    (hS : P11SlowSpec D nu eps (p11SlowConstant D nu) (p11SlowData D nu eps))
    (heps : 0 < eps) (h4 : 4*eps ≤ p11s2 (p11SecularData D) nu eps)
    (hsm : 256*eps < (p11SecularData D).rz^2) :
    AnalyticOnNhd ℝ (p11WrChain D nu eps) (p11WrR n) ∧
    KAM.Kepler.IsSymplecticOn eps (p11WrChain D nu eps) (p11WrR n) ∧
    (∀ z ∈ p11WrR n, ∀ k : Fin (n+n) → ℤ, z + KAM.ODE.angleShift k ∈ p11WrR n ∧
      p11WrChain D nu eps (z + KAM.ODE.angleShift k) = p11WrChain D nu eps z) ∧
    (∀ z ∈ p11WrR n, ∀ z' ∈ p11WrR n, p11WrChain D nu eps z' = p11WrChain D nu eps z →
      ∃ m : Fin (n+n) → ℤ, z' = z + KAM.ODE.angleShift m) := by
  obtain ⟨hPsiAn, hPsiSy, -, hPsiE, hPsiI⟩ := p11WrPsiR_facts hS
  obtain ⟨hFAn, hFSy, -, hFE, hFI⟩ := p11WrFastR_facts hF
  obtain ⟨cAn, cSy, -, cLat, cInj, -⟩ := hC.chart_part
  obtain ⟨tAn, tSy, tLat, tInj⟩ := total_chart (n := n)
  obtain ⟨rAn, rSy⟩ := p11RescaleReal_chart (p11SecularData D).J0 eps (p11WrR n)
  have hdom := fun z hz => p11_wrR_dom hC hF hS heps h4 hsm (z := z) hz
  have m1 : MapsTo (p11RescaleReal (p11SecularData D).J0 eps) (p11WrR n)
      (KAM.realInclusion₂ (n+n) ⁻¹' p11WrSlowDom D nu eps) := fun z hz => (hdom z hz).1
  have m2 : MapsTo (p11WrPsiR D nu eps ∘ p11RescaleReal (p11SecularData D).J0 eps) (p11WrR n)
      {z : Phase (n+n) | ∀ i : Fin n, 0 < z.2 (Fin.natAdd n i)} := fun z hz => (hdom z hz).2.1
  have m3 : MapsTo (p11PolarR ∘ p11WrPsiR D nu eps ∘ p11RescaleReal (p11SecularData D).J0 eps)
      (p11WrR n) (KAM.realInclusion₂ (n+n) ⁻¹' p11WrFastDom D eps) :=
    fun z hz => (hdom z hz).2.2.1
  have m4 : MapsTo (p11WrFastR D eps ∘ p11PolarR ∘ p11WrPsiR D nu eps ∘
      p11RescaleReal (p11SecularData D).J0 eps) (p11WrR n)
      (KAM.realInclusion₂ (n+n) ⁻¹' p11WorkingDom n (p11SecularData D).J0
        (2*(p11SecularData D).sigma) (2*(p11SecularData D).rC) (p11SecularData D).rz) :=
    fun z hz => (hdom z hz).2.2.2.1
  have a2 := hPsiAn.comp rAn m1
  have a3 := tAn.comp a2 m2
  have a4 := hFAn.comp a3 m3
  have a5 := cAn.comp a4 m4
  have s2 := KAM.Kepler.IsSymplecticOn.comp rSy hPsiSy (fun z hz => (rAn z hz).differentiableAt)
    (fun y hy => (hPsiAn y hy).differentiableAt) m1
  have s3 := KAM.Kepler.IsSymplecticOn.comp s2 tSy (fun z hz => (a2 z hz).differentiableAt)
    (fun y hy => (tAn y hy).differentiableAt) m2
  have s4 := KAM.Kepler.IsSymplecticOn.comp s3 hFSy (fun z hz => (a3 z hz).differentiableAt)
    (fun y hy => (hFAn y hy).differentiableAt) m3
  have s5 := KAM.Kepler.IsSymplecticOn.comp s4 cSy (fun z hz => (a4 z hz).differentiableAt)
    (fun y hy => (cAn y hy).differentiableAt) m4
  refine ⟨a5, by have h5 := s5; simp only [one_mul] at h5; exact h5,
    fun z hz k => ⟨p11WrR_shift hz k, ?_⟩, ?_⟩
  · obtain ⟨hy, hw, hu, hv, -⟩ := hdom z hz
    set y := p11RescaleReal (p11SecularData D).J0 eps z with hy_def
    set w := p11WrPsiR D nu eps y with hw_def
    set u := p11PolarR w with hu_def
    set v := p11WrFastR D eps u with hv_def
    obtain ⟨-, hwe⟩ := hPsiE y hy k
    obtain ⟨-, hue⟩ := hFE u hu (fun i => k (Fin.castAdd n i))
    have hce := cLat v hv (fun i => k (Fin.castAdd n i))
    simp only [p11WrChain, Function.comp_apply]
    rw [p11RescaleReal_shift, hwe, p11PolarR_angleShift hw, hue, ← hy_def, ← hw_def, ← hu_def,
      ← hv_def]
    rw [← hce]
    congr 1
    refine Prod.ext ?_ ?_ <;> simp [p11FastShift]
  · intro z hz z' hz' heq
    obtain ⟨hy, hw, hu, hv, -⟩ := hdom z hz
    obtain ⟨hy', hw', hu', hv', -⟩ := hdom z' hz'
    set y := p11RescaleReal (p11SecularData D).J0 eps z with hy_def
    set w := p11WrPsiR D nu eps y with hw_def
    set u := p11PolarR w with hu_def
    set v := p11WrFastR D eps u with hv_def
    set y' := p11RescaleReal (p11SecularData D).J0 eps z' with hy'_def
    set w' := p11WrPsiR D nu eps y' with hw'_def
    set u' := p11PolarR w' with hu'_def
    set v' := p11WrFastR D eps u' with hv'_def
    obtain ⟨kf, hkf⟩ := cInj v hv v' hv' (show (p11SecularData D).chart v = _ from heq.symm)
    have hvv : v' = v + p11FastShift kf := by
      rw [hkf]; refine Prod.ext ?_ ?_ <;> simp [p11FastShift]
    obtain ⟨hus, hvs⟩ := hFE u hu kf
    have hu2 : u' = u + p11FastShift kf :=
      hFI hu' hus (by rw [← hv_def] at hvs; rw [hvs, ← hvv])
    set m0 : Fin (n+n) → ℤ := Fin.append kf 0 with hm0
    have hpm : p11PolarR (w + KAM.ODE.angleShift m0) = u' := by
      rw [p11PolarR_angleShift hw, hu2]
      have : (fun i : Fin n => m0 (Fin.castAdd n i)) = kf := by
        funext i; simp [hm0]
      rw [this]
    have hwm : w + KAM.ODE.angleShift m0 ∈
        {z : Phase (n+n) | ∀ i : Fin n, 0 < z.2 (Fin.natAdd n i)} := by
      intro i; simpa [KAM.ODE.angleShift] using hw i
    obtain ⟨ks, hks⟩ := tInj _ hwm w' hw' hpm
    set m : Fin (n+n) → ℤ := fun i => m0 i + Fin.append (0 : Fin n → ℤ) ks i with hm_def
    have hww : w' = w + KAM.ODE.angleShift m := by
      rw [hks]
      refine Prod.ext ?_ ?_
      · funext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
          simp [hm_def, hm0, KAM.ODE.angleShift]
      · simp [KAM.ODE.angleShift]
    obtain ⟨hy2, hwe2⟩ := hPsiE y hy m
    have hyy : y' = y + KAM.ODE.angleShift m :=
      hPsiI hy' hy2 (by rw [← hw'_def, ← hw_def] at *; rw [hwe2, hww])
    refine ⟨m, p11RescaleReal_injective (J0 := (p11SecularData D).J0) heps.ne' ?_⟩
    rw [p11RescaleReal_shift, ← hy_def, ← hy'_def, hyy]

/-- `stepP:p11:wr-chain`, physical-time identity on the literal carrier:
`H_fix ∘ Ξ_ε = ε (h₀ + g₂ + f₃) ∘ A_ε / ε`, the Hamiltonian `Ĥ_ε = N_ε + P_ε` extended to `ℛ`. -/
theorem p11_wr_ham_node {D : P11Physical n} {nu eps : ℝ}
    (hC : P11SecularSpec D (p11SecularData D))
    (hF : P11FastSpec (p11SecularData D) eps (p11FastData D eps))
    (hS : P11SlowSpec D nu eps (p11SlowConstant D nu) (p11SlowData D nu eps))
    (heps : 0 < eps) (h4 : 4*eps ≤ p11s2 (p11SecularData D) nu eps)
    (hsm : 256*eps < (p11SecularData D).rz^2) {z : Phase (n+n)} (hz : z ∈ p11WrR n) :
    fixedHamiltonian D.G D.m0 D.m eps (p11WrChain D nu eps z) =
      eps*(((p11SlowData D nu eps).h0
          (p11Rescale (p11SecularData D).J0 eps (KAM.realInclusion₂ (n+n) z)).2 +
        (p11SlowData D nu eps).g2
          (p11Rescale (p11SecularData D).J0 eps (KAM.realInclusion₂ (n+n) z)).2)/(eps : ℂ) +
        (p11SlowData D nu eps).f3
          (p11Rescale (p11SecularData D).J0 eps (KAM.realInclusion₂ (n+n) z))/(eps : ℂ)).re := by
  have hpe := p11_pe_of_four heps h4
  have hσ0 : 0 < (p11SecularData D).sigma := by
    obtain ⟨-, -, -, -, -, hσ0, -, -, -, -⟩ := fast_consts hC
    exact hσ0
  have hsm' : 64*eps < (p11SecularData D).rz^2 := by
    have : 0 < (p11SecularData D).rz^2 := by
      obtain ⟨-, -, -, -, -, -, -, hrz0, -, -⟩ := fast_consts hC
      positivity
    linarith
  have hc : (p11SecularData D).chart
      ((fun i => (((p11FastData D eps).map (p11PolarC ((p11SlowData D nu eps).Psi
        (p11Rescale (p11SecularData D).J0 eps (KAM.realInclusion₂ (n+n) z))))).1 i).re),
       fun i => (((p11FastData D eps).map (p11PolarC ((p11SlowData D nu eps).Psi
        (p11Rescale (p11SecularData D).J0 eps (KAM.realInclusion₂ (n+n) z))))).2 i).re) =
      p11WrChain D nu eps z := by
    obtain ⟨-, -, -, -, h⟩ := p11_wrR_dom hC hF hS heps h4 hsm hz
    rw [h]
    rfl
  have hydom := p11WrR_rescale hσ0 heps h4 hz
  obtain ⟨hf2, -, -, -, -, -, -, -, -, -, -, -, -, hPsireal, -, -, -, -, -, hmaps, -, -, -, -,
    hid, -⟩ := hS
  obtain ⟨-, -, -, -, -, -, hFreal, -, -, hFmaps, -⟩ := hF
  rw [← hc]
  exact p11_wr_ham_core hC heps hpe hsm' (fixedHamiltonian D.G D.m0 D.m eps)
    (fun w hw => p11_secular_ham_chart hC eps w hw) hFreal hFmaps hPsireal hmaps hf2 hid hydom

theorem p11_wr_xi_node {D : P11Physical n} {nu eps : ℝ}
    (hC : P11SecularSpec D (p11SecularData D))
    (hF : P11FastSpec (p11SecularData D) eps (p11FastData D eps))
    (hS : P11SlowSpec D nu eps (p11SlowConstant D nu) (p11SlowData D nu eps))
    (heps : 0 < eps) (h4 : 4*eps ≤ p11s2 (p11SecularData D) nu eps)
    (hsm : 256*eps < (p11SecularData D).rz^2) :
    IsChart eps (p11WrXi D nu eps) (p11WrR n) ∧
    (∀ z ∈ p11WrR n, ∀ k : Fin (n+n) → ℤ, z + KAM.ODE.angleShift k ∈ p11WrR n ∧
      p11WrXi D nu eps (z + KAM.ODE.angleShift k) = p11WrXi D nu eps z) ∧
    (∀ z ∈ p11WrR n, ∀ z' ∈ p11WrR n, p11WrXi D nu eps z' = p11WrXi D nu eps z →
      ∃ m : Fin (n+n) → ℤ, z' = z + KAM.ODE.angleShift m) := by
  obtain ⟨hAn, hSy, hQ1, hQ2⟩ := p11_wr_chain_node hC hF hS heps h4 hsm
  have hcast : AnalyticOnNhd ℝ (KAM.Kepler.phaseCast (mul_two n) : Phase (n*2) → Phase (n+n))
      univ := fun x _ => ((KAM.Kepler.phaseCast (mul_two n) :
        Phase (n*2) →L[ℝ] Phase (n+n))).analyticAt x
  refine ⟨⟨hcast.comp hAn (fun _ _ => mem_univ _), ?_⟩, fun z hz k => ?_, fun z hz z' hz' h => ?_⟩
  · have := KAM.Kepler.IsSymplecticOn.comp hSy (KAM.Kepler.phaseCast_symplectic (mul_two n))
      (fun z hz => (hAn z hz).differentiableAt)
      (fun y _ => (KAM.Kepler.phaseCast (mul_two n)).differentiableAt) (fun _ _ => mem_univ _)
    rw [one_mul] at this
    exact this
  · obtain ⟨h1, h2⟩ := hQ1 z hz k
    exact ⟨h1, by unfold p11WrXi; rw [h2]⟩
  · refine hQ2 z hz z' hz' ?_
    unfold p11WrXi at h
    exact (KAM.Kepler.phaseCast (mul_two n)).injective h

/-- `4 ε ≤ s₂` for small `ε` (the eventual form of the smallness used by the literal node). -/
theorem p11_four_eps_le_s2_ev {D : P11Physical n} {C : P11SecularData n}
    (hC : P11SecularSpec D C) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0), 0 < eps → eps * C.MF ≤ Real.exp (-1) →
      4 * eps ≤ p11s2 C nu eps := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, hσ1, hrz0, -, hMF⟩ := fast_consts hC
  have hπ := Real.pi_pos
  have hL0 : 0 < C.L := by linarith
  have hs1c0 : 0 < min C.rC (C.gamma / (4 * C.L)) := lt_min hrC0 (by positivity)
  have hc3p : 0 < (6 / (Real.pi * C.sigma)) ^ (C.tau + 1) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hap : 0 < (3 * nu / (Real.pi * (C.sigma / 12))) ^ (C.tau + 1) :=
    Real.rpow_pos_of_pos (by have : 0 < nu := by linarith
                             positivity) _
  have hcs20 : 0 < min (min C.rC (C.gamma / (4 * C.L)) / (4 * (6 / (Real.pi * C.sigma)) ^
      (C.tau + 1))) (C.gamma / (8 * C.L * (3 * nu / (Real.pi * (C.sigma / 12))) ^
      (C.tau + 1))) := lt_min (by positivity) (by positivity)
  filter_upwards [eventually_eps_log_le (m := C.tau + 1) (by linarith) (div_pos hcs20 (by norm_num :
    (0:ℝ) < 4))]
    with eps h1 heps hεM
  have hs2 := p11s2_log_lower hC (nu := nu) (by linarith) heps hεM
  have hq : 0 < Real.log (1 / eps) ^ (C.tau + 1) :=
    Real.rpow_pos_of_pos (by have := slow_log_ge_one hC heps hεM; linarith) _
  refine le_trans ?_ hs2
  rw [le_div_iff₀ hq]
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)] at h1
  linarith

end Node

end KAM.Planetary

end
