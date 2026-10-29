/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PreparedData
public import KAM.Planetary.Preparation.SlowAverageDom
public import KAM.Planetary.Preparation.SlowSmall
public import KAM.Planetary.Preparation.SlowDivisor
public import KAM.Weighted.SupWeighted

/-!
# Prepared data: the basic construction (P11A-P8a, `stepP:p11:pr-basic`, `stepP:p11:pr-a`)

The prepared data `Q = p11PreparedCore D nu eps W` is built from the signed `avg_slow`, `avg_fast`,
`holo_chart` data: `N_eps = (h_0 + g_2) o A_eps / eps` and `P_eps = f_3 o A_eps / eps` on the
rescaled domain, and the chain `Phi^1 o Theta-hat o Psi_2 o A_eps` read through the secular chart.
The frequency data `checkW` is a free parameter `W` (supplied by P8b/P8c/P8e).

Exported helper lemmas, one per clause of `P11PreparedSpec` that concerns only `N`, `P`, `chain`:
domain chain (`p11Rescale_*`, `p11PreparedCore_chain_mem`), holomorphy, periodicity, reality,
the sup bound of `P_eps` (`pr-a`) and the fixed Hamiltonian identity (`H_2 o A_eps = eps H-hat`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

section Core

variable {n : ℕ}

/-- The prepared data of `stepP:p11:pr-basic`, parametrised by the frequency datum `W`. -/
def p11PreparedCoreOf (C : P11SecularData n) (Fast : P11FastData n) (A : P11SlowData n)
    (eps : ℝ) (W : P11Vec (n+n) → P11Vec (n+n)) : P11PreparedData n where
  N := fun I => (A.h0 (p11Rescale C.J0 eps (0, I)).2 + A.g2 (p11Rescale C.J0 eps (0, I)).2)/eps
  P := fun z => A.f3 (p11Rescale C.J0 eps z)/eps
  chain := fun z =>
    let w := Fast.map
      (p11PolarC (A.Psi (p11Rescale C.J0 eps (KAM.realInclusion₂ (n+n) z))))
    C.chart ((fun i => (w.1 i).re), fun i => (w.2 i).re)
  checkW := W

/-- The prepared data of `stepP:p11:pr-basic` for the signed data of a physical datum. -/
def p11PreparedCore (D : P11Physical n) (nu eps : ℝ) (W : P11Vec (n+n) → P11Vec (n+n)) :
    P11PreparedData n :=
  p11PreparedCoreOf (p11SecularData D) (p11FastData D eps) (p11SlowData D nu eps) eps W

/-- Real rescaling of a real phase point (`A_eps` on real points). -/
def p11RescaleReal (J0 : P11Vec n) (eps : ℝ) (x : Phase (n+n)) : Phase (n+n) :=
  (x.1, Fin.append (fun i : Fin n => J0 i+eps*x.2 (Fin.castAdd n i))
    (fun i : Fin n => eps*(2*Real.pi+x.2 (Fin.natAdd n i))))

theorem p11Rescale_real (J0 : P11Vec n) (eps : ℝ) (x : Phase (n+n)) :
    p11Rescale J0 eps (KAM.realInclusion₂ (n+n) x) =
      KAM.realInclusion₂ (n+n) (p11RescaleReal J0 eps x) := by
  refine Prod.ext rfl (funext fun j => ?_)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [p11Rescale, p11RescaleReal, Fin.append_left]
  · simp [p11Rescale, p11RescaleReal]

end Core

section Geometry

variable {n : ℕ} {C : P11SecularData n} {nu eps : ℝ}

theorem p11Box_isOpen {a b : ℕ} (c : P11CVec (a+b)) (r1 r2 : ℝ) : IsOpen (p11Box c r1 r2) := by
  unfold p11Box
  rw [Set.ofPred_and]
  simp only [Set.ofPred_forall]
  refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_lt ?_ continuous_const)
    (isOpen_iInter_of_finite fun i => isOpen_lt ?_ continuous_const) <;> fun_prop

theorem p11Box_mono {a b : ℕ} (c : P11CVec (a+b)) {r1 r2 s1 s2 : ℝ} (h1 : r1 ≤ s1) (h2 : r2 ≤ s2) :
    p11Box c r1 r2 ⊆ p11Box c s1 s2 :=
  fun _ hI => ⟨fun i => (hI.1 i).trans_le h1, fun i => (hI.2 i).trans_le h2⟩

/-- Complex actions within `1` of the unit prepared box have all coordinates below `3/2`. -/
theorem p11_actionNbhd_norm_lt {z : P11CVec (n+n)}
    (hz : z ∈ KAM.actionNbhd (p11PreparedBox n) 1) (i : Fin (n+n)) : ‖z i‖ < 3/2 := by
  obtain ⟨J, hJ, hzJ⟩ := hz
  have h1 : ‖z i - (J i : ℂ)‖ < 1 := (norm_le_pi_norm (z - fun i => (J i : ℂ)) i).trans_lt hzJ
  have h2 : ‖(J i : ℂ)‖ ≤ 1/2 := by
    have := hJ i (mem_univ _)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [this.1], this.2⟩
  calc ‖z i‖ = ‖(z i - (J i : ℂ)) + (J i : ℂ)‖ := by ring_nf
    _ ≤ ‖z i - (J i : ℂ)‖ + ‖(J i : ℂ)‖ := norm_add_le _ _
    _ < 3/2 := by linarith

/-- `A_eps` maps the unit complex neighbourhood of the prepared box into `V_2/2`. -/
theorem p11Rescale_mem_box (heps : 0 < eps) (hpe : Real.pi*eps ≤ p11s2 C nu eps)
    {z : P11Phase (n+n)} (hz : z.2 ∈ KAM.actionNbhd (p11PreparedBox n) 1) :
    (p11Rescale C.J0 eps z).2 ∈
      p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2) := by
  have hb := p11_actionNbhd_norm_lt hz
  have h3 : 3 < Real.pi := Real.pi_gt_three
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have : (p11Rescale C.J0 eps z).2 (Fin.castAdd n i) - p11SlowCenter C eps (Fin.castAdd n i) =
        (eps : ℂ) * z.2 (Fin.castAdd n i) := by
      simp [p11Rescale, p11SlowCenter, Fin.append_left]
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos heps]
    have := hb (Fin.castAdd n i)
    nlinarith
  · have : (p11Rescale C.J0 eps z).2 (Fin.natAdd n i) - p11SlowCenter C eps (Fin.natAdd n i) =
        (eps : ℂ) * z.2 (Fin.natAdd n i) := by
      simp [p11Rescale, p11SlowCenter]; ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos heps]
    have := hb (Fin.natAdd n i)
    nlinarith

end Geometry

section Clauses

variable {n : ℕ} {C : P11SecularData n} {Fast : P11FastData n} {A : P11SlowData n} {nu eps : ℝ}
  {W : P11Vec (n+n) → P11Vec (n+n)}

theorem p11Rescale_differentiable (J0 : P11Vec n) (eps : ℝ) :
    Differentiable ℂ (p11Rescale J0 eps) := by
  refine Differentiable.prodMk differentiable_fst (differentiable_pi.2 fun j => ?_)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Fin.append_left]; fun_prop
  · simp only [Fin.append_right]; fun_prop

/-- The domain chain `A_eps(E_0) in T_{sigma_3/6} x V_2/2` (`stepP:p11:pr-basic`). -/
theorem p11Rescale_mem_dom (heps : 0 < eps) (hpe : Real.pi*eps ≤ p11s2 C nu eps)
    {z : P11Phase (n+n)}
    (hz : z ∈ KAM.complexStrip (n+n) (C.sigma/72) ×ˢ KAM.actionNbhd (p11PreparedBox n) 1) :
    p11Rescale C.J0 eps z ∈ KAM.complexStrip (n+n) (C.sigma/12/6) ×ˢ
      p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2) := by
  refine ⟨?_, p11Rescale_mem_box heps hpe hz.2⟩
  have : C.sigma/12/6 = C.sigma/72 := by ring
  rw [this]
  exact hz.1

theorem p11PreparedCoreOf_N_differentiableOn (heps : 0 < eps)
    (hpe : Real.pi*eps ≤ p11s2 C nu eps)
    (hh : DifferentiableOn ℂ A.h0 (p11Box (p11SlowCenter C eps) (p11s2 C nu eps) (Real.pi*eps)))
    (hg : DifferentiableOn ℂ A.g2
      (p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2))) :
    DifferentiableOn ℂ (p11PreparedCoreOf C Fast A eps W).N
      (KAM.actionNbhd (p11PreparedBox n) 1) := by
  have hsub := p11Box_mono (p11SlowCenter C eps) (r1 := p11s2 C nu eps/2) (r2 := Real.pi*eps/2)
    (s1 := p11s2 C nu eps) (s2 := Real.pi*eps)
    (by linarith [show 0 < p11s2 C nu eps from lt_of_lt_of_le (by positivity) hpe])
    (by nlinarith [Real.pi_pos])
  have hd : Differentiable ℂ (fun I : P11CVec (n+n) => (p11Rescale C.J0 eps (0, I)).2) :=
    (differentiable_snd.comp ((p11Rescale_differentiable C.J0 eps).comp
      (differentiable_const _ |>.prodMk differentiable_id)))
  have hm : MapsTo (fun I : P11CVec (n+n) => (p11Rescale C.J0 eps (0, I)).2)
      (KAM.actionNbhd (p11PreparedBox n) 1)
      (p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2)) :=
    fun I hI => p11Rescale_mem_box heps hpe (z := (0, I)) hI
  have key := ((hh.mono hsub).add hg).comp hd.differentiableOn hm
  show DifferentiableOn ℂ (fun I => ((A.h0 + A.g2) ((fun I : P11CVec (n+n) =>
    (p11Rescale C.J0 eps (0, I)).2) I)) / (eps : ℂ)) _
  exact (key.mul (differentiableOn_const ((eps : ℂ)⁻¹))).congr (fun x _ => by simp [div_eq_mul_inv])

theorem p11PreparedCoreOf_P_differentiableOn (heps : 0 < eps)
    (hpe : Real.pi*eps ≤ p11s2 C nu eps)
    (hf : DifferentiableOn ℂ A.f3 (KAM.complexStrip (n+n) (C.sigma/12/6) ×ˢ
      p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2))) :
    DifferentiableOn ℂ (p11PreparedCoreOf C Fast A eps W).P
      (KAM.complexStrip (n+n) (C.sigma/72) ×ˢ KAM.actionNbhd (p11PreparedBox n) 1) :=
  by
  have key := hf.comp (p11Rescale_differentiable C.J0 eps).differentiableOn
    fun _ hz => p11Rescale_mem_dom heps hpe hz
  show DifferentiableOn ℂ (fun z => (A.f3 ∘ p11Rescale C.J0 eps) z / (eps : ℂ)) _
  exact (key.mul (differentiableOn_const ((eps : ℂ)⁻¹))).congr (fun x _ => by simp [div_eq_mul_inv])

theorem p11PreparedCoreOf_P_periodic (heps : 0 < eps) (hpe : Real.pi*eps ≤ p11s2 C nu eps)
    (hper : ∀ z ∈ KAM.complexStrip (n+n) (C.sigma/12/6) ×ˢ
      p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2),
      ∀ i : Fin (n+n), A.f3 (z.1+Pi.single i 1, z.2) = A.f3 z)
    {z : P11Phase (n+n)}
    (hz : z ∈ KAM.complexStrip (n+n) (C.sigma/72) ×ˢ KAM.actionNbhd (p11PreparedBox n) 1)
    (i : Fin (n+n)) :
    (p11PreparedCoreOf C Fast A eps W).P (z.1+Pi.single i 1, z.2) =
      (p11PreparedCoreOf C Fast A eps W).P z := by
  have := hper _ (p11Rescale_mem_dom heps hpe hz) i
  simp only [p11PreparedCoreOf]
  congr 1

theorem p11_im_div_ofReal (z : ℂ) (r : ℝ) : (z/(r : ℂ)).im = z.im/r :=
  Complex.div_ofReal_im z r

/-- Real points of the prepared strip go to real points of `T_{sigma_3/6} x V_2/2`. -/
theorem p11PreparedCoreOf_rescale_real_mem (heps : 0 < eps)
    (hpe : Real.pi*eps ≤ p11s2 C nu eps) {x : Phase (n+n)}
    (hx : KAM.realInclusion₂ (n+n) x ∈
      KAM.complexStrip (n+n) (C.sigma/72) ×ˢ KAM.actionNbhd (p11PreparedBox n) 1) :
    KAM.realInclusion₂ (n+n) (p11RescaleReal C.J0 eps x) ∈
      KAM.complexStrip (n+n) (C.sigma/12/6) ×ˢ
        p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2) := by
  have := p11Rescale_mem_dom (C := C) (nu := nu) heps hpe hx
  rwa [p11Rescale_real] at this

theorem p11PreparedCoreOf_N_real (heps : 0 < eps) (hpe : Real.pi*eps ≤ p11s2 C nu eps)
    (hreal : ∀ I : P11Vec (n+n), KAM.realInclusion (n+n) I ∈
      p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2) →
      (A.g2 (KAM.realInclusion (n+n) I)).im = 0 ∧ (A.h0 (KAM.realInclusion (n+n) I)).im = 0)
    {I : P11Vec (n+n)} (hI : KAM.realInclusion (n+n) I ∈ KAM.actionNbhd (p11PreparedBox n) 1) :
    ((p11PreparedCoreOf C Fast A eps W).N (KAM.realInclusion (n+n) I)).im = 0 := by
  have h0 : ((0 : P11CVec (n+n)), KAM.realInclusion (n+n) I) =
      KAM.realInclusion₂ (n+n) (0, I) := by simp
  have hm := p11Rescale_mem_box (C := C) (nu := nu) heps hpe
    (z := ((0 : P11CVec (n+n)), KAM.realInclusion (n+n) I)) hI
  have hy : (p11Rescale C.J0 eps ((0 : P11CVec (n+n)), KAM.realInclusion (n+n) I)).2 =
      KAM.realInclusion (n+n) (p11RescaleReal C.J0 eps (0, I)).2 := by
    rw [h0, p11Rescale_real]; rfl
  rw [hy] at hm
  obtain ⟨hg, hh⟩ := hreal _ hm
  show ((A.h0 (p11Rescale C.J0 eps ((0 : P11CVec (n+n)), KAM.realInclusion (n+n) I)).2 +
    A.g2 (p11Rescale C.J0 eps ((0 : P11CVec (n+n)), KAM.realInclusion (n+n) I)).2)/(eps : ℂ)).im = 0
  rw [hy, p11_im_div_ofReal, Complex.add_im, hg, hh]
  simp

theorem p11PreparedCoreOf_P_real (heps : 0 < eps) (hpe : Real.pi*eps ≤ p11s2 C nu eps)
    (hreal : KAM.Canonical.RealOn (KAM.complexStrip (n+n) (C.sigma/12/6) ×ˢ
      p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2)) A.f3) :
    KAM.Canonical.RealOn
      (KAM.complexStrip (n+n) (C.sigma/72) ×ˢ KAM.actionNbhd (p11PreparedBox n) 1)
      (p11PreparedCoreOf C Fast A eps W).P := by
  intro x hx
  have := hreal _ (p11PreparedCoreOf_rescale_real_mem heps hpe hx)
  show (A.f3 (p11Rescale C.J0 eps (KAM.realInclusion₂ (n+n) x))/(eps : ℂ)).im = 0
  rw [p11Rescale_real, p11_im_div_ofReal, this]
  simp

theorem p11PreparedCoreOf_NP_real (heps : 0 < eps) (hpe : Real.pi*eps ≤ p11s2 C nu eps)
    (hreal : ∀ I : P11Vec (n+n), KAM.realInclusion (n+n) I ∈
      p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2) →
      (A.g2 (KAM.realInclusion (n+n) I)).im = 0 ∧ (A.h0 (KAM.realInclusion (n+n) I)).im = 0)
    (hrealf : KAM.Canonical.RealOn (KAM.complexStrip (n+n) (C.sigma/12/6) ×ˢ
      p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2)) A.f3) :
    KAM.Canonical.RealOn
      (KAM.complexStrip (n+n) (C.sigma/72) ×ˢ KAM.actionNbhd (p11PreparedBox n) 1)
      (fun z => (p11PreparedCoreOf C Fast A eps W).N z.2 +
        (p11PreparedCoreOf C Fast A eps W).P z) := by
  intro x hx
  have h1 := p11PreparedCoreOf_N_real (Fast := Fast) (W := W) heps hpe hreal (I := x.2) hx.2
  have h2 := p11PreparedCoreOf_P_real (Fast := Fast) (W := W) heps hpe hrealf x hx
  simp only [KAM.realInclusion₂_apply] at h2 ⊢
  rw [Complex.add_im, h1, h2]
  simp

/-- A pointwise weighted bound over an open action set bounds the sup (`N:bpN:p4:sup-weighted`). -/
theorem p11_norm_le_of_wbound_open {s M : ℝ} {f : P11Phase (n+n) → ℂ} {V : Set (P11CVec (n+n))}
    (hV : IsOpen V) (hd : DifferentiableOn ℂ f (KAM.complexStrip (n+n) s ×ˢ V))
    (hper : ∀ z ∈ KAM.complexStrip (n+n) s ×ˢ V, ∀ i, f (z.1+Pi.single i 1, z.2) = f z)
    (hb : p11WBound V s f M) : ∀ z ∈ KAM.complexStrip (n+n) s ×ˢ V, ‖f z‖ ≤ M := by
  intro z hz
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hV z.2 hz.2
  have hsub : KAM.Weighted.Dom (n+n) ({z.2} : Set (P11CVec (n+n))) δ s ⊆
      KAM.complexStrip (n+n) s ×ˢ V := by
    rintro w ⟨hw1, I', hI', hw2⟩
    rw [Set.mem_singleton_iff] at hI'
    subst hI'
    exact ⟨hw1, hball (by simpa [Metric.mem_ball, dist_eq_norm] using hw2)⟩
  have hu : KAM.Weighted.InClass ({z.2} : Set (P11CVec (n+n))) δ s f :=
    ⟨hd.mono hsub, fun j w hw => hper w (hsub hw) j⟩
  have hb' : KAM.Weighted.WBound ({z.2} : Set (P11CVec (n+n))) δ s f M := by
    intro I hI
    obtain ⟨I', hI', hI2⟩ := hI
    rw [Set.mem_singleton_iff] at hI'
    subst hI'
    exact hb I (hball (by simpa [Metric.mem_ball, dist_eq_norm] using hI2))
  exact KAM.Weighted.sup_le_wbound hu hb' z ⟨hz.1, z.2, rfl, by simpa using hδ⟩

/-- `stepP:p11:pr-a`: `sup |P_eps| <= eps^{-1} sup |f_3| <= c eps^{nu+3/2} ell^{2 tau_0+1}`. -/
theorem p11PreparedCoreOf_P_bound (heps : 0 < eps) (hpe : Real.pi*eps ≤ p11s2 C nu eps)
    (hd : DifferentiableOn ℂ A.f3 (KAM.complexStrip (n+n) (C.sigma/12/6) ×ˢ
      p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2)))
    (hper : ∀ z ∈ KAM.complexStrip (n+n) (C.sigma/12/6) ×ˢ
      p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2),
      ∀ i : Fin (n+n), A.f3 (z.1+Pi.single i 1, z.2) = A.f3 z)
    {c : ℝ}
    (hb : p11WBound (p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2))
      (C.sigma/12/6) A.f3 (eps^nu*(c*eps^(5/2 : ℝ)*Real.log (1/eps)^(2*C.tau+1)))) :
    p11Bound (KAM.complexStrip (n+n) (C.sigma/72) ×ˢ KAM.actionNbhd (p11PreparedBox n) 1)
      (p11PreparedCoreOf C Fast A eps W).P
      (c*eps^(nu+3/2)*Real.log (1/eps)^(2*C.tau+1)) := by
  intro z hz
  have hsup := p11_norm_le_of_wbound_open (p11Box_isOpen _ _ _) hd hper hb _
    (p11Rescale_mem_dom heps hpe hz)
  show ‖A.f3 (p11Rescale C.J0 eps z)/(eps : ℂ)‖ ≤ _
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos heps, div_le_iff₀ heps]
  refine hsup.trans (le_of_eq ?_)
  have h1 : eps^(nu+3/2)*eps = eps^nu*eps^(5/2 : ℝ) := by
    rw [← Real.rpow_add_one heps.ne', ← Real.rpow_add heps]; ring_nf
  calc eps^nu*(c*eps^(5/2 : ℝ)*Real.log (1/eps)^(2*C.tau+1))
      = c*(eps^nu*eps^(5/2 : ℝ))*Real.log (1/eps)^(2*C.tau+1) := by ring
    _ = _ := by rw [← h1]; ring

end Clauses

end KAM.Planetary

end
