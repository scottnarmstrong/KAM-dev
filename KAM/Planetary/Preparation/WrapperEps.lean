/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.WrapperTubeMain
public import KAM.Planetary.Preparation.WrapperDatum
public import KAM.Planetary.Preparation.WrapperQI
public import KAM.Planetary.Preparation.WrapperTransport
public import KAM.Planetary.Preparation.WrapperMeasure
public import KAM.Planetary.Newtonian.AssemblyNodes

/-!
# The wrapper at fixed `ε` (P11A-P10, `stepP:p11:wr-tor`, `wr-meas`)

Given a family of lattice tori of `Ĥ_ε` with displacement at most `1/2`, the image of all of them
under `Ξ_ε` is a Borel set of positive finite measure in the circular tube, through every point of
which passes a physical torus of `H_fix` inside the set.
-/

@[expose] public noncomputable section
open Set MeasureTheory
namespace KAM.Planetary

section Eps

variable {n : ℕ}

theorem p11_phaseCast_cancel {d e : ℕ} (h : d = e) (x : Phase d) :
    KAM.Kepler.phaseCast h.symm (KAM.Kepler.phaseCast h x) = x := by
  subst h; ext i <;> rfl

theorem p11_wr_link {D : P11Physical n} {nu eps c : ℝ} {Q : P11PreparedData n}
    (hC : P11SecularSpec D (p11SecularData D))
    (hF : P11FastSpec (p11SecularData D) eps (p11FastData D eps))
    (hS : P11SlowSpec D nu eps (p11SlowConstant D nu) (p11SlowData D nu eps))
    (heps : 0 < eps) (hpe : Real.pi*eps ≤ p11s2 (p11SecularData D) nu eps)
    (hsm : 256*eps < (p11SecularData D).rz^2) (hspec : P11PreparedFullSpec D nu eps c Q)
    {z : Phase (n+n)} (hz : z ∈ p11WrO D) :
    fixedHamiltonian D.G D.m0 D.m eps (p11WrChain D nu eps z) =
      eps*(Q.N (KAM.realInclusion (n+n) z.2) + Q.P (KAM.realInclusion₂ (n+n) z)).re := by
  obtain ⟨⟨-, hch⟩, -, -, -, -, -, -, -, -, -, -, -, -, hHam⟩ := hspec.1
  rw [← (hch z hz).trans (p11_wr_chain_eq hC hF hS heps hpe hsm hz)]
  exact hHam z hz

/-- `Ξ_ε` with codomain reindexed to `Phase (n+n)`, so that Part 1 applies. -/
def p11WrXi (D : P11Physical n) (nu eps : ℝ) (z : Phase (n+n)) : Phase (n+n) :=
  KAM.Kepler.phaseCast (mul_two n) (p11WrChain D nu eps z)

theorem p11_wr_xi {D : P11Physical n} {nu eps : ℝ}
    (hC : P11SecularSpec D (p11SecularData D))
    (hF : P11FastSpec (p11SecularData D) eps (p11FastData D eps))
    (hS : P11SlowSpec D nu eps (p11SlowConstant D nu) (p11SlowData D nu eps))
    (heps : 0 < eps) (hpe : Real.pi*eps ≤ p11s2 (p11SecularData D) nu eps)
    (hsm : 256*eps < (p11SecularData D).rz^2) :
    IsChart eps (p11WrXi D nu eps) (p11WrO D) ∧
    (∀ z ∈ p11WrO D, ∀ k : Fin (n+n) → ℤ, z + KAM.ODE.angleShift k ∈ p11WrO D ∧
      p11WrXi D nu eps (z + KAM.ODE.angleShift k) = p11WrXi D nu eps z) ∧
    (∀ z ∈ p11WrO D, ∀ z' ∈ p11WrO D, p11WrXi D nu eps z' = p11WrXi D nu eps z →
      ∃ m : Fin (n+n) → ℤ, z' = z + KAM.ODE.angleShift m) := by
  obtain ⟨hAn, hSy, hQ1, hQ2⟩ := p11_wr_chain hC hF hS heps hpe hsm
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

theorem p11WrO_realDomain {D : P11Physical n} (β : ℝ) :
    p11c_realDomain (p11WrDatum D β) ⊆ p11WrO D := by
  intro z hz
  refine ⟨fun i => ?_, p11_actionNbhd_mono _ (by norm_num : (2*(1/4) : ℝ) ≤ 1) hz⟩
  have : 0 < (p11SecularData D).sigma/72 := by
    obtain ⟨-, -, -, -, -, hσ0, -⟩ := fast_consts (n := n) (D := D) (C := p11SecularData D)
      (holo_chart D).choose_spec.1
    positivity
  simpa using this

/-- `stepP:p11:wr-tor`: the transported torus is a physical torus of `H_fix`. -/
theorem p11_wr_torus {D : P11Physical n} {nu eps c : ℝ} {Q : P11PreparedData n}
    (hC : P11SecularSpec D (p11SecularData D))
    (hF : P11FastSpec (p11SecularData D) eps (p11FastData D eps))
    (hS : P11SlowSpec D nu eps (p11SlowConstant D nu) (p11SlowData D nu eps))
    (heps : 0 < eps) (hpe : Real.pi*eps ≤ p11s2 (p11SecularData D) nu eps)
    (hsm : 256*eps < (p11SecularData D).rz^2) (hspec : P11PreparedFullSpec D nu eps c Q)
    {β : ℝ} {w : Fin (n+n) → ℝ} {K : (Fin (n+n) → ℝ) → Phase (n+n)}
    (hlat : IsLatticeTorus KAM.ODE.angleShift (KAM.realHamiltonian Q.N Q.P)
      (p11c_realDomain (p11WrDatum D β)) w K) {γ τ : ℝ} (hγ : 0 < γ)
    (hτ : ((n+n : ℕ) : ℝ) - 1 < τ) (hdio : KAM.IsDiophantine γ τ w) :
    ∃ w' : Fin (n*2) → ℝ, ∃ Kf : (Fin (n*2) → ℝ) → Phase (n*2),
      IsPhysicalTorus (fixedHamiltonian D.G D.m0 D.m eps) w' Kf ∧
      ∀ θ, Kf θ = p11WrChain D nu eps (K (fun i => θ (Fin.cast (mul_two n).symm i))) := by
  obtain ⟨hchart, hQ1, hQ2⟩ := p11_wr_xi hC hF hS heps hpe hsm
  have hEq : EqOn (KAM.realHamiltonian Q.N Q.P)
      (chartPullback eps (fixedHamiltonian D.G D.m0 D.m eps ∘
        KAM.Kepler.phaseCast (mul_two n).symm) (p11WrXi D nu eps)) (p11WrO D) := by
    intro z hz
    have := p11_wr_link hC hF hS heps hpe hsm hspec hz
    simp only [chartPullback, p11WrXi, Function.comp_apply, p11_phaseCast_cancel (mul_two n)]
    rw [this, ← mul_assoc, inv_mul_cancel₀ heps.ne', one_mul]
    rfl
  have hK := p11_latticeTorus_congr hlat (p11WrO_isOpen D) (p11WrO_realDomain β) hEq
  have hphys := torus_transport_phys heps hchart hK (fun z hz k => hQ1 z hz k)
    (fun z hz z' hz' h => hQ2 z hz z' hz' h) hγ hτ hdio
  have hc := p11_isPhysicalTorus_cast (mul_two n).symm hphys
  refine ⟨_, _, hc, fun θ => ?_⟩
  simp only [Function.comp_apply, p11WrXi]
  exact p11_phaseCast_cancel (mul_two n) _

/-- `stepP:p11:wr-meas` and `wr-tor` at fixed `ε`: the set `S_ε`. -/
theorem p11_wr_set {D : P11Physical n} {nu eps c : ℝ} {Q : P11PreparedData n}
    (hC : P11SecularSpec D (p11SecularData D))
    (hF : P11FastSpec (p11SecularData D) eps (p11FastData D eps))
    (hS : P11SlowSpec D nu eps (p11SlowConstant D nu) (p11SlowData D nu eps))
    (heps : 0 < eps) (hεM : eps*(p11SecularData D).MF ≤ Real.exp (-1))
    (hpe : Real.pi*eps ≤ p11s2 (p11SecularData D) nu eps)
    (hsm : 256*eps < (p11SecularData D).rz^2)
    (hP1 : p11SlowConstant D nu*eps^(3/2 : ℝ)*Real.log (1/eps)^(3*(p11SecularData D).tau+1) ≤ eps)
    (hP2 : p11SlowConstant D nu*eps^(5/2 : ℝ)*Real.log (1/eps)^(3*(p11SecularData D).tau+1) ≤ eps)
    (hR1 : 2*eps + 3*eps*(p11SecularData D).MF/(2*Real.pi*p11Alpha1 (p11SecularData D) eps*
      (p11SecularData D).sigma) ≤ 7*Real.pi*p11PhysicalDelta D/4)
    (hR2 : 3*n*eps + 2*n*(9*eps*(p11SecularData D).MF/(2*Real.pi*
      p11Alpha1 (p11SecularData D) eps*(p11SecularData D).rz))^2 ≤ p11PhysicalDelta D)
    (hspec : P11PreparedFullSpec D nu eps c Q) {β : ℝ} {good : Set (Fin (n+n) → ℝ)}
    {torus : (Fin (n+n) → ℝ) → (Fin (n+n) → ℝ) → Phase (n+n)} {freq : (Fin (n+n) → ℝ) → Fin (n+n) → ℝ}
    (hgood : 0 < volume good) (hgoodsub : good ⊆ p11PreparedBox n)
    (hlat : ∀ b ∈ good, IsLatticeTorus KAM.ODE.angleShift (KAM.realHamiltonian Q.N Q.P)
      (p11c_realDomain (p11WrDatum D β)) (freq b) (torus b))
    {γ τ : ℝ} (hγ : 0 < γ) (hτ : ((n+n : ℕ) : ℝ) - 1 < τ)
    (hdio : ∀ b ∈ good, KAM.IsDiophantine γ τ (freq b))
    (hdisp : ∀ b ∈ good, ∀ θ, ‖torus b θ - (θ, b)‖ ≤ 1/2)
    (hbor : MeasurableSet ((fun z : Phase (n+n) => torus z.2 z.1) '' (unitCube (n+n) ×ˢ good)))
    (hcell : ENNReal.ofReal ((2 : ℝ)^(-(2*((n+n : ℕ) : ℤ)))) * volume good ≤
      volume ((fun z : Phase (n+n) => torus z.2 z.1) '' (unitCube (n+n) ×ˢ good))) :
    ∃ S : Set (Phase (n*2)), MeasurableSet S ∧ 0 < volume S ∧ volume S < ⊤ ∧
      S ⊆ circularTube D.G D.m0 D.m D.a (p11Zeta D) ∧
      ∀ z ∈ S, ∃ w : Fin (n*2) → ℝ, ∃ K : (Fin (n*2) → ℝ) → Phase (n*2), ∃ θ0, z = K θ0 ∧
        Set.range K ⊆ S ∧ IsPhysicalTorus (fixedHamiltonian D.G D.m0 D.m eps) w K := by
  obtain ⟨hchart, hQ1, hQ2⟩ := p11_wr_xi hC hF hS heps hpe hsm
  have hlat' : ∀ b ∈ good, ∀ θ (k : Fin (n+n) → ℤ),
      torus b (θ + fun i => (k i : ℝ)) = torus b θ + KAM.ODE.angleShift k :=
    fun b hb => (hlat b hb).2.1
  have hBpos : 0 < volume ((fun z : Phase (n+n) => torus z.2 z.1) '' (unitCube (n+n) ×ˢ good)) :=
    lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.ofReal_pos.2 (zpow_pos (by norm_num) _)).ne' hgood.ne') hcell
  obtain ⟨hAm, hAper, hApos⟩ := p11TorusUnion_props hlat' hbor hBpos
  have hAO : p11TorusUnion good torus ⊆ p11WrO D := by
    rintro _ ⟨b, hb, θ, rfl⟩
    exact p11WrO_realDomain β ((hlat b hb).1.2 θ).1
  have hL := liouville_lattice heps (p11WrO_isOpen D) hchart hQ1 hQ2 hAm.nullMeasurableSet hAO hAper
  have hmeas := liouville_lattice_measurableSet heps (p11WrO_isOpen D) hchart hQ1 hQ2 hAm hAO hAper
  set S := p11WrChain D nu eps '' p11TorusUnion good torus with hSdef
  have hXiS : p11WrXi D nu eps '' p11TorusUnion good torus =
      KAM.Kepler.phaseCast (mul_two n) '' S := by
    rw [hSdef, Set.image_image]; rfl
  have hSmeas : MeasurableSet S := by
    have := (KAM.Kepler.phaseCast (mul_two n)).continuous.measurable hmeas
    rw [hXiS, (KAM.Kepler.phaseCast (mul_two n)).injective.preimage_image] at this
    exact this
  have hvol : volume (p11WrXi D nu eps '' p11TorusUnion good torus) = volume S := by
    rw [hXiS]; exact KAM.Kepler.phaseCast_volume (mul_two n) S
  have hSpos : 0 < volume S := by rw [← hvol]; exact hL.2.2.2.1.2 hApos
  have hI : ∀ x ∈ p11TorusUnion good torus, ∀ j, |x.2 j| ≤ 1 := by
    rintro _ ⟨b, hb, θ, rfl⟩ j
    have h1 : |(torus b θ).2 j - b j| ≤ 1/2 := by
      have := (norm_le_pi_norm ((torus b θ - (θ, b)).2) j).trans
        ((le_max_right _ _).trans (hdisp b hb θ))
      simpa [Real.norm_eq_abs] using this
    have h2 : |b j| ≤ 1/2 := by
      have := hgoodsub hb j (mem_univ j)
      rw [abs_le]; exact ⟨by linarith [this.1], this.2⟩
    calc |(torus b θ).2 j| = |((torus b θ).2 j - b j) + b j| := by ring_nf
      _ ≤ |(torus b θ).2 j - b j| + |b j| := abs_add_le _ _
      _ ≤ 1 := by linarith
  have hSsub : S ⊆ circularTube D.G D.m0 D.m D.a (p11Zeta D) := by
    rintro _ ⟨x, hx, rfl⟩
    exact p11_wr_tube hC hF hS heps hεM hpe hsm hP1 hP2 hR1 hR2 (hAO hx) (hI x hx)
  have hfin : volume S < ⊤ := by
    obtain ⟨h1, h2⟩ := (mp_a_box D.G_pos D.m0_pos D.m_pos D.a_pos (p11_zeta_pos D)).2 S hSsub
    exact h1.trans_lt h2
  refine ⟨S, hSmeas, hSpos, hfin, hSsub, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨b, hb, θ, rfl⟩ := hx
  obtain ⟨w', Kf, hphys, hKf⟩ := p11_wr_torus hC hF hS heps hpe hsm hspec (hlat b hb) hγ hτ
    (hdio b hb)
  refine ⟨w', Kf, fun j => θ (Fin.cast (mul_two n) j), ?_, ?_, hphys⟩
  · rw [hKf]
    congr 2
  · rintro _ ⟨θ', rfl⟩
    rw [hKf]
    exact ⟨_, ⟨b, hb, _, rfl⟩, rfl⟩

end Eps

end KAM.Planetary

end
