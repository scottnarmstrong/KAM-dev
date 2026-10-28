/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.Analytic
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Planetary.PG.Setting
public import KAM.Planetary.PGAssembly.ExtensionTube
public import KAM.Planetary.PGAssembly.Extension

/-!
# P Part 5: complex Lipschitz bounds and the complex fast frequency map
(`bpP:p5:lip-complex`, `bpP:p5:bilip`)

`lip_complex`: a bounded holomorphic map on `actionNbhd X (2ρ)` is Lipschitz on `actionNbhd X ρ`
(Cauchy estimate on closed polydiscs for close pairs, the sup bound for far pairs).
`complexFast`, `bilip`: the complex fast frequency map `∂H̃₀` of the extension is bi-Lipschitz on
`actionNbhd (closure V) ρ` with `‖∂²H̃₀‖` bounded on `actionNbhd (closure V) (2ρ)`
(steps `bl-real`, `bl-comp`: injectivity and invertible derivative at real points from the frozen
inverse; a compactness contradiction with the local linearisation).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-BL.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology
open scoped BigOperators

namespace KAM.Planetary

variable {a b n : ℕ}

/-- Cauchy estimate: a holomorphic map bounded by `A` on a closed polydisc of radius `r` about `w`
has derivative of norm at most `A / r` at `w`. -/
theorem norm_fderiv_le_of_closedBall {N m : ℕ} {U : Set (Fin N → ℂ)} {f : (Fin N → ℂ) → Fin m → ℂ}
    {w : Fin N → ℂ} {r A : ℝ} (hr : 0 < r) (hf : DifferentiableOn ℂ f U)
    (hball : closedBall w r ⊆ U) (hb : ∀ z ∈ closedBall w r, ‖f z‖ ≤ A) :
    ‖fderiv ℂ f w‖ ≤ A / r := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (hb w (mem_closedBall_self hr.le))
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hA hr.le) fun v => ?_
  by_cases hv : v = 0
  · simp [hv]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  set R : ℝ := r / ‖v‖ with hR
  have hRpos : 0 < R := div_pos hr hvpos
  set g : ℂ → Fin m → ℂ := fun t => f (w + t • v) with hg
  have hmaps : ∀ t : ℂ, ‖t‖ ≤ R → w + t • v ∈ closedBall w r := by
    intro t ht
    rw [mem_closedBall_iff_norm, add_sub_cancel_left, norm_smul]
    calc ‖t‖ * ‖v‖ ≤ R * ‖v‖ := mul_le_mul_of_nonneg_right ht hvpos.le
      _ = r := by rw [hR]; field_simp
  have hgd : DifferentiableOn ℂ g (closedBall 0 R) := by
    refine hf.comp ?_ (fun t ht => hball (hmaps t (by simpa using ht)))
    exact ((differentiable_const w).add (differentiable_id.smul_const v)).differentiableOn
  have hdc : DiffContOnCl ℂ g (ball 0 R) := by
    refine ⟨hgd.mono ball_subset_closedBall, ?_⟩
    rw [closure_ball 0 hRpos.ne']
    exact hgd.continuousOn
  have hCauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos hdc
    (C := A) (fun t ht => hb _ (hmaps t (by rw [mem_sphere_zero_iff_norm] at ht; exact ht.le)))
  have hfd : DifferentiableAt ℂ f w := (hf.differentiableAt (by
    exact mem_of_superset (closedBall_mem_nhds w hr) hball))
  have hderiv : deriv g 0 = fderiv ℂ f w v := by
    have h1 : HasDerivAt (fun t : ℂ => w + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0:ℂ)).smul_const v).const_add w
    have h2 : HasFDerivAt f (fderiv ℂ f w) (w + (0:ℂ) • v) := by
      simpa using hfd.hasFDerivAt
    exact (h2.comp_hasDerivAt (0:ℂ) h1).deriv
  rw [hderiv] at hCauchy
  calc ‖fderiv ℂ f w v‖ ≤ A / R := hCauchy
    _ = A / r * ‖v‖ := by rw [hR]; field_simp

theorem lip_complex {m N : ℕ} (hN : 0 < N) {X : Set (Fin N → ℝ)} {rho A : ℝ}
    (hrho : 0 < rho) {f : (Fin N → ℂ) → Fin m → ℂ}
    (hf : DifferentiableOn ℂ f (KAM.actionNbhd X (2*rho)))
    (hb : ∀ z ∈ KAM.actionNbhd X (2*rho), ‖f z‖ ≤ A) :
    ∀ z ∈ KAM.actionNbhd X rho, ∀ z' ∈ KAM.actionNbhd X rho,
      ‖f z-f z'‖ ≤ (2*N*A/rho)*‖z-z'‖ := by
  intro z hz z' hz'
  have hzU : z ∈ KAM.actionNbhd X (2*rho) := by
    obtain ⟨J, hJ, hzJ⟩ := hz
    exact ⟨J, hJ, by linarith⟩
  have hA : 0 ≤ A := (norm_nonneg _).trans (hb z hzU)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hcoef : 2 * A / rho ≤ 2 * N * A / rho := by
    apply div_le_div_of_nonneg_right _ hrho.le
    nlinarith
  have hmono : ∀ {e : Fin N → ℂ}, e ∈ KAM.actionNbhd X rho → ∀ {w : Fin N → ℂ},
      ‖w - e‖ < rho / 2 → closedBall w (rho / 2) ⊆ KAM.actionNbhd X (2*rho) := by
    intro e he w hwe u hu
    obtain ⟨J, hJ, heJ⟩ := he
    refine ⟨J, hJ, ?_⟩
    have heJ' : ‖e - KAM.realInclusion N J‖ < rho := heJ
    rw [mem_closedBall_iff_norm] at hu
    calc ‖u - KAM.realInclusion N J‖ = ‖(u - w) + (w - e) + (e - KAM.realInclusion N J)‖ := by
          congr 1; abel
      _ ≤ ‖u - w‖ + ‖w - e‖ + ‖e - KAM.realInclusion N J‖ := norm_add₃_le
      _ < 2 * rho := by linarith
  by_cases hclose : ‖z - z'‖ < rho
  · -- close pair: Cauchy on the segment, mean value inequality
    have hseg : ∀ w ∈ segment ℝ z z', DifferentiableAt ℂ f w ∧ ‖fderiv ℂ f w‖ ≤ 2 * A / rho := by
      intro w hw
      have hsum := dist_add_dist_of_mem_segment hw
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at hsum
      have hsub : closedBall w (rho / 2) ⊆ KAM.actionNbhd X (2*rho) := by
        by_cases hwz : ‖z - w‖ ≤ ‖w - z'‖
        · exact hmono hz (by rw [norm_sub_rev]; linarith)
        · exact hmono hz' (by linarith)
      refine ⟨hf.differentiableAt (mem_of_superset (closedBall_mem_nhds w (by positivity)) hsub),
        ?_⟩
      have := norm_fderiv_le_of_closedBall (by positivity : 0 < rho / 2) hf hsub
        (fun u hu => hb u (hsub hu))
      calc ‖fderiv ℂ f w‖ ≤ A / (rho / 2) := this
        _ = 2 * A / rho := by field_simp
    have key := (convex_segment z z').norm_image_sub_le_of_norm_fderiv_le
      (fun w hw => (hseg w hw).1) (fun w hw => (hseg w hw).2) (left_mem_segment ℝ z z')
      (right_mem_segment ℝ z z')
    rw [norm_sub_rev, norm_sub_rev z z']
    exact key.trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _))
  · -- far pair: the sup bound
    replace hclose := not_lt.1 hclose
    have hz'U : z' ∈ KAM.actionNbhd X (2*rho) := by
      obtain ⟨J, hJ, hzJ⟩ := hz'
      exact ⟨J, hJ, by linarith⟩
    calc ‖f z - f z'‖ ≤ ‖f z‖ + ‖f z'‖ := norm_sub_le _ _
      _ ≤ 2 * A := by linarith [hb z hzU, hb z' hz'U]
      _ = (2 * A / rho) * rho := by field_simp
      _ ≤ (2 * A / rho) * ‖z - z'‖ := mul_le_mul_of_nonneg_left hclose (by positivity)
      _ ≤ (2 * N * A / rho) * ‖z - z'‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)

def complexFast (d : PGData a b) (I : Fin a → ℂ) (i : Fin a) : ℂ :=
  fderiv ℂ (pgExtension d).H0 I (Pi.single i 1)

/-- The coordinate map `L ↦ (L eᵢ)ᵢ` on continuous linear forms. -/
def partialsCLM (n : ℕ) : ((Fin n → ℂ) →L[ℂ] ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1)

theorem complexFast_eq (d : PGData a b) :
    complexFast d = fun I => partialsCLM a (fderiv ℂ (pgExtension d).H0 I) := rfl

theorem norm_partialsCLM_le (n : ℕ) : ‖partialsCLM n‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have h := L.le_opNorm (Pi.single i (1 : ℂ))
  have h1 : ‖(Pi.single i (1 : ℂ) : Fin n → ℂ)‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => by
      by_cases hj : j = i <;> simp [hj]
  simp only [partialsCLM, ContinuousLinearMap.pi_apply, ContinuousLinearMap.apply_apply]
  rw [one_mul]
  exact h.trans (mul_le_of_le_one_right (norm_nonneg _) h1)

theorem analyticOnNhd_fderiv_H0 (d : PGData a b) :
    AnalyticOnNhd ℂ (fderiv ℂ (pgExtension d).H0)
      (KAM.actionNbhd (closure d.V) (pgExtension d).delta) :=
  by
  have h := KAM.analyticOnNhd_of_differentiableOn
    (isOpen_actionNbhd (closure d.V) (pgExtension d).delta) (pgExtension d).h0holo
  exact h.fderiv

theorem analyticOnNhd_complexFast (d : PGData a b) :
    AnalyticOnNhd ℂ (complexFast d) (KAM.actionNbhd (closure d.V) (pgExtension d).delta) :=
  fun z hz => (partialsCLM a).analyticAt _ |>.comp (analyticOnNhd_fderiv_H0 d z hz)

theorem differentiableOn_complexFast (d : PGData a b) :
    DifferentiableOn ℂ (complexFast d) (KAM.actionNbhd (closure d.V) (pgExtension d).delta) :=
  (analyticOnNhd_complexFast d).differentiableOn

theorem continuousOn_fderiv_complexFast (d : PGData a b) :
    ContinuousOn (fderiv ℂ (complexFast d))
      (KAM.actionNbhd (closure d.V) (pgExtension d).delta) :=
  (analyticOnNhd_complexFast d).fderiv.continuousOn

theorem norm_fderiv_complexFast_le (d : PGData a b) {z : Fin a → ℂ}
    (hz : z ∈ KAM.actionNbhd (closure d.V) (pgExtension d).delta) :
    ‖fderiv ℂ (complexFast d) z‖ ≤ (pgExtension d).M0 := by
  have hd : DifferentiableAt ℂ (fderiv ℂ (pgExtension d).H0) z :=
    (analyticOnNhd_fderiv_H0 d z hz).differentiableAt
  have h := ((partialsCLM a).hasFDerivAt.comp z hd.hasFDerivAt).fderiv
  rw [complexFast_eq, show (fun I => partialsCLM a (fderiv ℂ (pgExtension d).H0 I)) =
    (partialsCLM a) ∘ (fderiv ℂ (pgExtension d).H0) from rfl, h]
  calc ‖(partialsCLM a).comp (fderiv ℂ (fderiv ℂ (pgExtension d).H0) z)‖
      ≤ ‖partialsCLM a‖ * ‖fderiv ℂ (fderiv ℂ (pgExtension d).H0) z‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (pgExtension d).M0 :=
        mul_le_mul (norm_partialsCLM_le a) ((pgExtension d).h0bounds z hz).2.2 (ContinuousLinearMap.opNorm_nonneg _)
          zero_le_one
    _ = _ := one_mul _

theorem realInclusion_single (i : Fin n) :
    KAM.realInclusion n (Pi.single i 1) = Pi.single i 1 := by
  ext j
  by_cases hj : j = i <;> simp [hj]

theorem mem_actionNbhd_real {X : Set (Fin n → ℝ)} {r : ℝ} (hr : 0 < r) {x : Fin n → ℝ}
    (hx : x ∈ X) : KAM.realInclusion n x ∈ KAM.actionNbhd X r :=
  ⟨x, hx, by
    show ‖KAM.realInclusion n x - KAM.realInclusion n x‖ < r
    simpa using hr⟩

/-- Real points of the tube: `H̃₀` restricts to the real `H₀`, and its complex frequency map
restricts to the real frequency map (`stepP:p5:bl-real`). -/
theorem real_relation (d : PGData a b) {y : Fin a → ℝ}
    (hy : KAM.realInclusion a y ∈ KAM.actionNbhd (closure d.V) (pgExtension d).delta) :
    DifferentiableAt ℝ d.H0 y ∧
      complexFast d (KAM.realInclusion a y) = KAM.realInclusion a (fastFrequency d.H0 y) := by
  have hopen := isOpen_actionNbhd (closure d.V) (pgExtension d).delta
  have hN : (KAM.realInclusion a) ⁻¹' KAM.actionNbhd (closure d.V) (pgExtension d).delta ∈ 𝓝 y :=
    (hopen.preimage (KAM.realInclusion a).continuous).mem_nhds hy
  have hHd : DifferentiableAt ℂ (pgExtension d).H0 (KAM.realInclusion a y) :=
    (pgExtension d).h0holo.differentiableAt (hopen.mem_nhds hy)
  have h2 : HasFDerivAt (fun y' => (pgExtension d).H0 (KAM.realInclusion a y'))
      (((fderiv ℂ (pgExtension d).H0 (KAM.realInclusion a y)).restrictScalars ℝ).comp
        (KAM.realInclusion a)) y :=
    (hHd.hasFDerivAt.restrictScalars ℝ).comp y (KAM.realInclusion a).hasFDerivAt
  have hev : (fun y' => (pgExtension d).H0 (KAM.realInclusion a y')) =ᶠ[𝓝 y]
      fun y' => ((d.H0 y' : ℝ) : ℂ) := by
    filter_upwards [hN] with y' hy'
    exact (pgExtension d).h0real y' hy'
  have h3 := Complex.reCLM.hasFDerivAt.comp y h2
  have hev' : d.H0 =ᶠ[𝓝 y]
      (Complex.reCLM ∘ fun y' => (pgExtension d).H0 (KAM.realInclusion a y')) := by
    filter_upwards [hev] with y' hy'
    simp [hy']
  have hdiff : DifferentiableAt ℝ d.H0 y := (h3.congr_of_eventuallyEq hev').differentiableAt
  have h5 : HasFDerivAt (fun y' => ((d.H0 y' : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ d.H0 y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y hdiff.hasFDerivAt
  have h6 := (h2.congr_of_eventuallyEq hev.symm).unique h5
  refine ⟨hdiff, ?_⟩
  funext i
  have h7 := congrArg (fun L => L (Pi.single i (1:ℝ))) h6
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    realInclusion_single] at h7
  exact h7

/-- The real frequency map is differentiable at real points of the tube, with the derivative the
real part of the complex derivative on real vectors, and the complex derivative maps real vectors
to real vectors accordingly. -/
theorem omega_hasFDerivAt (d : PGData a b) {x : Fin a → ℝ}
    (hx : KAM.realInclusion a x ∈ KAM.actionNbhd (closure d.V) (pgExtension d).delta) :
    ∃ T : (Fin a → ℝ) →L[ℝ] (Fin a → ℝ), HasFDerivAt (fastFrequency d.H0) T x ∧
      ∀ v, fderiv ℂ (complexFast d) (KAM.realInclusion a x) (KAM.realInclusion a v) =
        KAM.realInclusion a (T v) := by
  have hopen := isOpen_actionNbhd (closure d.V) (pgExtension d).delta
  have hΩd : DifferentiableAt ℂ (complexFast d) (KAM.realInclusion a x) :=
    (differentiableOn_complexFast d).differentiableAt (hopen.mem_nhds hx)
  have h2 : HasFDerivAt (fun y => complexFast d (KAM.realInclusion a y))
      (((fderiv ℂ (complexFast d) (KAM.realInclusion a x)).restrictScalars ℝ).comp
        (KAM.realInclusion a)) x :=
    (hΩd.hasFDerivAt.restrictScalars ℝ).comp x (KAM.realInclusion a).hasFDerivAt
  have hN : (KAM.realInclusion a) ⁻¹' KAM.actionNbhd (closure d.V) (pgExtension d).delta ∈ 𝓝 x :=
    (hopen.preimage (KAM.realInclusion a).continuous).mem_nhds hx
  have hev : (fun y => complexFast d (KAM.realInclusion a y)) =ᶠ[𝓝 x]
      fun y => KAM.realInclusion a (fastFrequency d.H0 y) := by
    filter_upwards [hN] with y hy
    exact (real_relation d hy).2
  have h3 := (KAM.realPartCLM a).hasFDerivAt.comp x h2
  have hev' : fastFrequency d.H0 =ᶠ[𝓝 x]
      (KAM.realPartCLM a ∘ fun y => complexFast d (KAM.realInclusion a y)) := by
    filter_upwards [hev] with y hy
    simp [hy]
  have h4 := h3.congr_of_eventuallyEq hev'
  refine ⟨_, h4, fun v => ?_⟩
  have h5 := (KAM.realInclusion a).hasFDerivAt.comp x h4
  have h6 := (h2.congr_of_eventuallyEq hev.symm).unique h5
  have h7 := congrArg (fun L => L v) h6
  exact h7

/-- Injectivity of the real derivative from the frozen inverse (`stepP:p5:bl-real`). -/
theorem omega_deriv_injective (d : PGData a b) {x : Fin a → ℝ} (hxK : x ∈ closure d.V)
    {T : (Fin a → ℝ) →L[ℝ] (Fin a → ℝ)} (hT : HasFDerivAt (fastFrequency d.H0) T x) :
    Function.Injective T := by
  obtain ⟨-, hopen, g, hgc, hginv, -⟩ := d.hfreq
  have hxW : x ∈ d.W := d.hVW hxK
  have hgd : DifferentiableAt ℝ g (fastFrequency d.H0 x) :=
    (hgc.contDiffAt (hopen.mem_nhds ⟨x, hxW, rfl⟩)).differentiableAt one_ne_zero
  have hcomp := hgd.hasFDerivAt.comp x hT
  have hev : (id : (Fin a → ℝ) → (Fin a → ℝ)) =ᶠ[𝓝 x] (g ∘ fastFrequency d.H0) := by
    filter_upwards [d.hW.mem_nhds hxW] with y hy
    exact (hginv y hy).symm
  have huniq := (hasFDerivAt_id x).unique (hcomp.congr_of_eventuallyEq hev)
  intro v w hvw
  have h1 := congrArg (fun L => L v) huniq
  have h2 := congrArg (fun L => L w) huniq
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, hvw] at h1 h2
  exact h1.trans h2.symm

/-- Invertibility of `∂Ω̃` at real points of `closure V`, quantitatively (`stepP:p5:bl-real`). -/
theorem fderiv_complexFast_lower (d : PGData a b) {x : Fin a → ℝ} (hxK : x ∈ closure d.V) :
    ∃ c > 0, ∀ u, c * ‖u‖ ≤ ‖fderiv ℂ (complexFast d) (KAM.realInclusion a x) u‖ := by
  have hx := mem_actionNbhd_real (pgExtension d).delta_pos hxK
  obtain ⟨T, hT, hDι⟩ := omega_hasFDerivAt d hx
  have hinj := omega_deriv_injective d hxK hT
  set Dc := fderiv ℂ (complexFast d) (KAM.realInclusion a x) with hDc
  have hker : LinearMap.ker (Dc : (Fin a → ℂ) →ₗ[ℂ] (Fin a → ℂ)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    have hu' : u = KAM.realInclusion a (fun i => (u i).re) +
        Complex.I • KAM.realInclusion a (fun i => (u i).im) := by
      ext i
      simp [Complex.ext_iff]
    have h0 : KAM.realInclusion a (T fun i => (u i).re) +
        Complex.I • KAM.realInclusion a (T fun i => (u i).im) = 0 := by
      have := hu
      rw [hu', map_add, map_smul] at this
      simpa [hDι] using this
    have hre : T (fun i => (u i).re) = T 0 := by
      ext i
      have := congrFun h0 i
      simpa [map_zero] using congrArg Complex.re this
    have him : T (fun i => (u i).im) = T 0 := by
      ext i
      have := congrFun h0 i
      simpa [map_zero] using congrArg Complex.im this
    have h1 := hinj hre
    have h2 := hinj him
    rw [hu']
    simp [h1, h2]
  obtain ⟨K, hK, hanti⟩ := LinearMap.exists_antilipschitzWith _ hker
  refine ⟨(K : ℝ)⁻¹, by positivity, fun u => ?_⟩
  have h := hanti.le_mul_dist u 0
  simp only [dist_zero_right, map_zero] at h
  rw [inv_mul_le_iff₀ (by exact_mod_cast hK)]
  exact h

end KAM.Planetary

end
