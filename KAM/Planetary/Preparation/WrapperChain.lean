/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.WrapperParts
public import KAM.Planetary.Preparation.HoloAssembly
public import KAM.Planetary.Preparation.Polar

/-!
# The chain of charts `Ξ_ε` (P11A-P10, `stepP:p11:wr-chain`)

`Ξ_ε = chart ∘ FastR ∘ PolarR ∘ PsiR ∘ ResR` is a real analytic `ε`-chart on the real points of the
prepared domain, with the lattice properties (Q1)-(Q2) for the full integer angle lattice.
-/

@[expose] public noncomputable section
open Set
namespace KAM.Planetary

section Chain

variable {n : ℕ}

/-- The complex prepared domain `T_{σ/72} × (K + 1)`. -/
def p11WrV (D : P11Physical n) : Set (P11Phase (n+n)) :=
  KAM.complexStrip (n+n) ((p11SecularData D).sigma/72) ×ˢ
    KAM.actionNbhd (p11PreparedBox n) 1

/-- The real points of the prepared domain. -/
def p11WrO (D : P11Physical n) : Set (Phase (n+n)) := KAM.realInclusion₂ (n+n) ⁻¹' p11WrV D

/-- The chain `Ξ_ε` on real points. -/
def p11WrChain (D : P11Physical n) (nu eps : ℝ) : Phase (n+n) → Phase (n*2) :=
  (p11SecularData D).chart ∘ p11WrFastR D eps ∘ p11PolarR ∘ p11WrPsiR D nu eps ∘
    p11RescaleReal (p11SecularData D).J0 eps

theorem p11WrV_isOpen (D : P11Physical n) : IsOpen (p11WrV D) :=
  (KAM.isOpen_complexStrip _ _).prod (by
    unfold KAM.actionNbhd
    have : {I : Fin (n+n) → ℂ | ∃ J ∈ p11PreparedBox n, ‖I - (fun i => (J i : ℂ))‖ < 1} =
        ⋃ J ∈ p11PreparedBox n, Metric.ball (fun i => (J i : ℂ)) 1 := by
      ext I; simp [Metric.mem_ball, dist_eq_norm]
    rw [this]
    exact isOpen_biUnion fun J _ => Metric.isOpen_ball)

theorem p11WrO_isOpen (D : P11Physical n) : IsOpen (p11WrO D) :=
  (p11WrV_isOpen D).preimage (KAM.realInclusion₂ (n+n)).continuous

/-- Rescaling as an affine map. -/
theorem p11RescaleReal_eq (J0 : P11Vec n) (eps : ℝ) :
    p11RescaleReal J0 eps = fun x =>
      ((ContinuousLinearMap.fst ℝ _ _).prod (eps • ContinuousLinearMap.snd ℝ _ _) :
        Phase (n+n) →L[ℝ] Phase (n+n)) x +
        (0, Fin.append (fun i : Fin n => J0 i) (fun _ : Fin n => 2*Real.pi*eps)) := by
  funext x
  refine Prod.ext (by simp [p11RescaleReal]) (funext fun j => ?_)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [p11RescaleReal] <;> ring

theorem p11RescaleReal_chart (J0 : P11Vec n) (eps : ℝ) (O : Set (Phase (n+n))) :
    AnalyticOnNhd ℝ (p11RescaleReal J0 eps) O ∧
      KAM.Kepler.IsSymplecticOn eps (p11RescaleReal J0 eps) O := by
  rw [p11RescaleReal_eq]
  set L : Phase (n+n) →L[ℝ] Phase (n+n) :=
    (ContinuousLinearMap.fst ℝ _ _).prod (eps • ContinuousLinearMap.snd ℝ _ _) with hL
  refine ⟨fun x _ => (L.analyticAt x).add analyticAt_const, fun x _ u v => ?_⟩
  have : fderiv ℝ (fun x => L x + (0, Fin.append (fun i : Fin n => J0 i)
      (fun _ : Fin n => 2*Real.pi*eps))) x = L := by
    rw [fderiv_add_const]; exact L.fderiv
  rw [this]
  simp only [hL, KAM.symplecticForm, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_snd', Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem p11RescaleReal_shift (J0 : P11Vec n) (eps : ℝ) (z : Phase (n+n)) (k : Fin (n+n) → ℤ) :
    p11RescaleReal J0 eps (z + KAM.ODE.angleShift k) =
      p11RescaleReal J0 eps z + KAM.ODE.angleShift k := by
  refine Prod.ext (by simp [p11RescaleReal, KAM.ODE.angleShift]) (funext fun j => ?_)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [p11RescaleReal, KAM.ODE.angleShift]

theorem p11RescaleReal_injective {J0 : P11Vec n} {eps : ℝ} (he : eps ≠ 0) :
    Function.Injective (p11RescaleReal J0 eps) := by
  intro x x' h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine Prod.ext (by simpa [p11RescaleReal] using h1) (funext fun j => ?_)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · have := congrFun h2 (Fin.castAdd n i)
    simp only [p11RescaleReal, Fin.append_left] at this
    have := mul_left_cancel₀ he (add_left_cancel this)
    exact this
  · have := congrFun h2 (Fin.natAdd n i)
    simp only [p11RescaleReal, Fin.append_right] at this
    exact add_left_cancel (mul_left_cancel₀ he this)

/-- The domain chain at a real point of the prepared domain. -/
theorem p11_wr_dom {D : P11Physical n} {nu eps : ℝ}
    (hC : P11SecularSpec D (p11SecularData D))
    (hF : P11FastSpec (p11SecularData D) eps (p11FastData D eps))
    (hS : P11SlowSpec D nu eps (p11SlowConstant D nu) (p11SlowData D nu eps))
    (heps : 0 < eps) (hpe : Real.pi*eps ≤ p11s2 (p11SecularData D) nu eps)
    (hsm : 256*eps < (p11SecularData D).rz^2) {z : Phase (n+n)} (hz : z ∈ p11WrO D) :
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
  obtain ⟨-, -, -, hrC0, -, hσ0, -, -, -, -⟩ := fast_consts hC
  have hS' := hS
  have hF' := hF
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hPsiM, -, -, -, -, -, -⟩ := hS'
  obtain ⟨-, -, -, -, -, -, -, -, -, hFM, -⟩ := hF'
  have hdom := p11PreparedCoreOf_chain_dom (nu := nu) (Fast := p11FastData D eps)
    (A := p11SlowData D nu eps) hC heps hpe hsm hFM hPsiM hz
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

theorem p11WrO_shift {D : P11Physical n} {z : Phase (n+n)} (hz : z ∈ p11WrO D)
    (k : Fin (n+n) → ℤ) : z + KAM.ODE.angleShift k ∈ p11WrO D := by
  obtain ⟨h1, h2⟩ := hz
  rw [p11WrO, Set.mem_preimage, p11_realInclusion₂_add_angleShift]
  exact ⟨fun i => by simpa using h1 i, h2⟩

theorem p11PolarR_angleShift {w : Phase (n+n)} (hw : ∀ i : Fin n, 0 < w.2 (Fin.natAdd n i))
    (k : Fin (n+n) → ℤ) :
    p11PolarR (w + KAM.ODE.angleShift k) =
      p11PolarR w + p11FastShift (fun i => k (Fin.castAdd n i)) := by
  obtain ⟨-, -, tLat, -⟩ := total_chart (n := n)
  have hk := append_int_add k
  have h1 : w + KAM.ODE.angleShift k =
      ((w.1 + Fin.append (fun i => ((k (Fin.castAdd n i) : ℤ) : ℝ)) 0) +
        Fin.append 0 (fun i => ((k (Fin.natAdd n i) : ℤ) : ℝ)), w.2) := by
    refine Prod.ext ?_ (by simp [KAM.ODE.angleShift])
    simp only [KAM.ODE.angleShift, Prod.fst_add]
    rw [hk, add_assoc]
  rw [h1, tLat (w.1 + Fin.append (fun i => ((k (Fin.castAdd n i) : ℤ) : ℝ)) 0, w.2) hw,
    p11PolarR_fast_shift]
  refine Prod.ext ?_ ?_ <;> simp [p11FastShift]

/-- `stepP:p11:wr-chain`: `Ξ_ε` is a real analytic `ε`-chart on the real points of the prepared
domain, with the lattice properties (Q1)-(Q2) for the full integer angle lattice. -/
theorem p11_wr_chain {D : P11Physical n} {nu eps : ℝ}
    (hC : P11SecularSpec D (p11SecularData D))
    (hF : P11FastSpec (p11SecularData D) eps (p11FastData D eps))
    (hS : P11SlowSpec D nu eps (p11SlowConstant D nu) (p11SlowData D nu eps))
    (heps : 0 < eps) (hpe : Real.pi*eps ≤ p11s2 (p11SecularData D) nu eps)
    (hsm : 256*eps < (p11SecularData D).rz^2) :
    AnalyticOnNhd ℝ (p11WrChain D nu eps) (p11WrO D) ∧
    KAM.Kepler.IsSymplecticOn eps (p11WrChain D nu eps) (p11WrO D) ∧
    (∀ z ∈ p11WrO D, ∀ k : Fin (n+n) → ℤ, z + KAM.ODE.angleShift k ∈ p11WrO D ∧
      p11WrChain D nu eps (z + KAM.ODE.angleShift k) = p11WrChain D nu eps z) ∧
    (∀ z ∈ p11WrO D, ∀ z' ∈ p11WrO D, p11WrChain D nu eps z' = p11WrChain D nu eps z →
      ∃ m : Fin (n+n) → ℤ, z' = z + KAM.ODE.angleShift m) := by
  obtain ⟨hPsiAn, hPsiSy, -, hPsiE, hPsiI⟩ := p11WrPsiR_facts hS
  obtain ⟨hFAn, hFSy, -, hFE, hFI⟩ := p11WrFastR_facts hF
  obtain ⟨cAn, cSy, -, cLat, cInj, -⟩ := hC.chart_part
  obtain ⟨tAn, tSy, tLat, tInj⟩ := total_chart (n := n)
  obtain ⟨rAn, rSy⟩ := p11RescaleReal_chart (p11SecularData D).J0 eps (p11WrO D)
  have hdom := fun z hz => p11_wr_dom hC hF hS heps hpe hsm (z := z) hz
  have m1 : MapsTo (p11RescaleReal (p11SecularData D).J0 eps) (p11WrO D)
      (KAM.realInclusion₂ (n+n) ⁻¹' p11WrSlowDom D nu eps) := fun z hz => (hdom z hz).1
  have m2 : MapsTo (p11WrPsiR D nu eps ∘ p11RescaleReal (p11SecularData D).J0 eps) (p11WrO D)
      {z : Phase (n+n) | ∀ i : Fin n, 0 < z.2 (Fin.natAdd n i)} := fun z hz => (hdom z hz).2.1
  have m3 : MapsTo (p11PolarR ∘ p11WrPsiR D nu eps ∘ p11RescaleReal (p11SecularData D).J0 eps)
      (p11WrO D) (KAM.realInclusion₂ (n+n) ⁻¹' p11WrFastDom D eps) :=
    fun z hz => (hdom z hz).2.2.1
  have m4 : MapsTo (p11WrFastR D eps ∘ p11PolarR ∘ p11WrPsiR D nu eps ∘
      p11RescaleReal (p11SecularData D).J0 eps) (p11WrO D)
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
  refine ⟨a5, by have h5 := s5; simp only [one_mul] at h5; exact h5, fun z hz k => ⟨p11WrO_shift hz k, ?_⟩, ?_⟩
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
    have hwm : w + KAM.ODE.angleShift m0 ∈ {z : Phase (n+n) | ∀ i : Fin n, 0 < z.2 (Fin.natAdd n i)} := by
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

/-- The chain agrees with the formula of the prepared data. -/
theorem p11_wr_chain_eq {D : P11Physical n} {nu eps : ℝ}
    (hC : P11SecularSpec D (p11SecularData D))
    (hF : P11FastSpec (p11SecularData D) eps (p11FastData D eps))
    (hS : P11SlowSpec D nu eps (p11SlowConstant D nu) (p11SlowData D nu eps))
    (heps : 0 < eps) (hpe : Real.pi*eps ≤ p11s2 (p11SecularData D) nu eps)
    (hsm : 256*eps < (p11SecularData D).rz^2) {z : Phase (n+n)} (hz : z ∈ p11WrO D) :
    (p11SecularData D).chart
      ((fun i => (((p11FastData D eps).map (p11PolarC ((p11SlowData D nu eps).Psi
        (p11Rescale (p11SecularData D).J0 eps (KAM.realInclusion₂ (n+n) z))))).1 i).re),
       fun i => (((p11FastData D eps).map (p11PolarC ((p11SlowData D nu eps).Psi
        (p11Rescale (p11SecularData D).J0 eps (KAM.realInclusion₂ (n+n) z))))).2 i).re) =
      p11WrChain D nu eps z := by
  obtain ⟨-, -, -, -, h⟩ := p11_wr_dom hC hF hS heps hpe hsm hz
  rw [h]
  rfl

end Chain

end KAM.Planetary

end
