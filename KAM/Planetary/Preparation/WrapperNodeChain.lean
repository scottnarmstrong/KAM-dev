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

end Node

end KAM.Planetary

end
