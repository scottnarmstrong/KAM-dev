/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Charts.Coordinates
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Part 3 (local charts): the chart `Φ_c = (h, m_c)` is a local `C¹` diffeomorphism, and the cover

Blueprint nodes `bpI:p3:chart` and
`bpI:p3:cover`. `n = 2`.

* `chart` (`bpI:p3:chart`): at a centre `c ∈ closure B'` the Jacobian of `Φ_c = (Re h, m_c)` is
  `-det 𝖡_h(c) / (∇h(c) ⬝ ∇h(c)) ≠ 0`, and `Φ_c` has a `C¹` local inverse `Ψ` on an open image
  `Φ_c(W)`, with `W` inside any given neighbourhood of `c` and inside `𝒰_c`. The Jacobian is
  computed from `fderiv_chartM_apply` (the derivative of the slope coordinate at its own centre)
  and the expansion `borderedHessian_det_eq`; the inverse is
  `ContDiffAt.toOpenPartialHomeomorph` (inverse function theorem) restricted to a neighbourhood
  on which the local inverse is `C¹`.
* `cover` (`bpI:p3:cover`): finitely many patches (`IsPatch`, with the specific chart inverse)
  cover `closure B'`. Each centre has a patch `exists_isPatch` (the window `δ_E, δ_m` from the open
  image, the radius `ρ_c` from the continuity of `h` and `m_c` at `c`); compactness of
  `closure B'` gives the finite subfamily.
-/

public section

open scoped Matrix.Norms.Operator
open Matrix Set Metric Topology Filter

namespace KAM.Iso.Charts

open KAM KAM.Torus KAM.Iso.Confinement

variable {B : Set (Fin 2 → ℝ)} {s₀ r₀ : ℝ} {h : (Fin 2 → ℂ) → ℂ} {B' : Set (Fin 2 → ℝ)} {η : ℝ}

/-! ### The Jacobian of the chart at its centre -/

/-- The derivative of the slope coordinate `m_c` at its own centre `c`:
`D m_c(c) v = det (∇h(c), D(∇h)(c) v) / (∇h(c) ⬝ ∇h(c))` (the numerator vanishes at `c`). -/
theorem fderiv_chartM_apply (hd : HeadData B s₀ r₀ h B' η) {c : Fin 2 → ℝ}
    (hc : c ∈ realAct B r₀) (v : Fin 2 → ℝ) :
    fderiv ℝ (chartM h c) c v =
      det2 (frequencyMap h c) (fderiv ℝ (frequencyMap h) c v) /
        (frequencyMap h c ⬝ᵥ frequencyMap h c) := by
  have hg : frequencyMap h c ≠ 0 := (det_identity hd hc).2.2.1
  have hq : 0 < frequencyMap h c ⬝ᵥ frequencyMap h c := dotProduct_self_pos hg
  have hfd : DifferentiableAt ℝ (frequencyMap h) c :=
    ((contDiffOn_frequencyMap hd).contDiffAt
      ((isOpen_realAct_charts B r₀).mem_nhds hc)).differentiableAt (by norm_num)
  have hG := hfd.hasFDerivAt
  have hcomp : ∀ i : Fin 2, HasFDerivAt (fun I => frequencyMap h I i)
      ((ContinuousLinearMap.proj i).comp (fderiv ℝ (frequencyMap h) c)) c :=
    hasFDerivAt_pi'.1 hG
  set g := frequencyMap h c with hgdef
  have hN : HasFDerivAt (fun I => g 0 * frequencyMap h I 1 - g 1 * frequencyMap h I 0)
      (g 0 • (ContinuousLinearMap.proj 1).comp (fderiv ℝ (frequencyMap h) c) -
        g 1 • (ContinuousLinearMap.proj 0).comp (fderiv ℝ (frequencyMap h) c)) c :=
    ((hcomp 1).const_mul (g 0)).sub ((hcomp 0).const_mul (g 1))
  have hD : HasFDerivAt (fun I => g 0 * frequencyMap h I 0 + g 1 * frequencyMap h I 1)
      (g 0 • (ContinuousLinearMap.proj 0).comp (fderiv ℝ (frequencyMap h) c) +
        g 1 • (ContinuousLinearMap.proj 1).comp (fderiv ℝ (frequencyMap h) c)) c :=
    ((hcomp 0).const_mul (g 0)).add ((hcomp 1).const_mul (g 1))
  have hDc : g 0 * frequencyMap h c 0 + g 1 * frequencyMap h c 1 = g ⬝ᵥ g := by
    simp only [dotProduct, Fin.sum_univ_two, hgdef]
  have hDne : g 0 * frequencyMap h c 0 + g 1 * frequencyMap h c 1 ≠ 0 := by
    rw [hDc]; exact hq.ne'
  have hDinv := (hasDerivAt_inv hDne).comp_hasFDerivAt c hD
  have hNc : g 0 * frequencyMap h c 1 - g 1 * frequencyMap h c 0 = 0 := by
    simp only [hgdef]; ring
  have hm := hN.fun_mul hDinv
  have hfun : chartM h c = fun I => (g 0 * frequencyMap h I 1 - g 1 * frequencyMap h I 0) *
      ((fun y => y⁻¹) ∘ fun I => g 0 * frequencyMap h I 0 + g 1 * frequencyMap h I 1) I := by
    funext I
    simp only [chartM, slope, det2, dotProduct, Fin.sum_univ_two, Function.comp_apply,
      div_eq_mul_inv, hgdef]
  rw [hfun, hm.fderiv]
  simp only [_root_.smul_apply, hNc, zero_smul, zero_add, Function.comp_apply,
    hDc, smul_eq_mul, _root_.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, det2, div_eq_inv_mul]

/-- `bpI:p3:chart`, the Jacobian: `det DΦ_c(c) = -det 𝖡_h(c) / (∇h(c) ⬝ ∇h(c))`, with the two
columns of `DΦ_c(c)` computed from `fderiv_chartM_apply`. -/
theorem jac2_chartPhi (hd : HeadData B s₀ r₀ h B' η) {c : Fin 2 → ℝ} (hc : c ∈ realAct B r₀) :
    jac2 (chartPhi h c) c =
      -(KAM.Iso.borderedHessian h c).det / (frequencyMap h c ⬝ᵥ frequencyMap h c) := by
  have hg : frequencyMap h c ≠ 0 := (det_identity hd hc).2.2.1
  have hq : 0 < frequencyMap h c ⬝ᵥ frequencyMap h c := dotProduct_self_pos hg
  have hre : ∀ b : Fin 2, fderiv ℝ (fun y => (chartPhi h c y).1) c (Pi.single b 1) =
      frequencyMap h c b := fun b => rfl
  have hm : ∀ b : Fin 2, fderiv ℝ (fun y => (chartPhi h c y).2) c (Pi.single b 1) =
      det2 (frequencyMap h c) (fderiv ℝ (frequencyMap h) c (Pi.single b 1)) /
        (frequencyMap h c ⬝ᵥ frequencyMap h c) := fun b => fderiv_chartM_apply hd hc _
  have hHess : ∀ a b : Fin 2, fderiv ℝ (frequencyMap h) c (Pi.single b 1) a = hessR h c a b :=
    fun a b => rfl
  have hdet := borderedHessian_det_eq h c
  unfold jac2
  rw [hre, hre, hm, hm, hdet]
  simp only [det2, perp, dotProduct, mulVec, Fin.sum_univ_two, hHess, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  field_simp
  ring

/-! ### The inverse function theorem for `Φ_c` -/

/-- A linear map `ℝ² → ℝ × ℝ` with nonzero Jacobian `L e₀ . 1 * L e₁ . 2 - L e₁ . 1 * L e₀ . 2`
is bijective. -/
theorem bijective_of_jac_ne_zero (L : (Fin 2 → ℝ) →L[ℝ] ℝ × ℝ)
    (hJ : (L (Pi.single 0 1)).1 * (L (Pi.single 1 1)).2 -
      (L (Pi.single 1 1)).1 * (L (Pi.single 0 1)).2 ≠ 0) :
    LinearMap.ker (L : (Fin 2 → ℝ) →ₗ[ℝ] ℝ × ℝ) = ⊥ ∧
      LinearMap.range (L : (Fin 2 → ℝ) →ₗ[ℝ] ℝ × ℝ) = ⊤ := by
  have hinj : Function.Injective (L : (Fin 2 → ℝ) →ₗ[ℝ] ℝ × ℝ) := by
    rw [← LinearMap.ker_eq_bot]
    refine LinearMap.ker_eq_bot'.2 fun v hv => ?_
    have hv' : L v = 0 := hv
    have hdec : v = v 0 • (Pi.single 0 1 : Fin 2 → ℝ) + v 1 • (Pi.single 1 1 : Fin 2 → ℝ) := by
      ext i
      fin_cases i <;> simp
    rw [hdec, map_add, map_smul, map_smul] at hv'
    have h1 := congrArg Prod.fst hv'
    have h2 := congrArg Prod.snd hv'
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Prod.fst_zero, Prod.snd_zero] at h1 h2
    have e0 : v 0 * ((L (Pi.single 0 1)).1 * (L (Pi.single 1 1)).2 -
        (L (Pi.single 1 1)).1 * (L (Pi.single 0 1)).2) = 0 := by
      linear_combination (L (Pi.single 1 1)).2 * h1 - (L (Pi.single 1 1)).1 * h2
    have e1 : v 1 * ((L (Pi.single 0 1)).1 * (L (Pi.single 1 1)).2 -
        (L (Pi.single 1 1)).1 * (L (Pi.single 0 1)).2) = 0 := by
      linear_combination (L (Pi.single 0 1)).1 * h2 - (L (Pi.single 0 1)).2 * h1
    have hv0 : v 0 = 0 := (mul_eq_zero.1 e0).resolve_right hJ
    have hv1 : v 1 = 0 := (mul_eq_zero.1 e1).resolve_right hJ
    ext i
    fin_cases i
    · exact hv0
    · exact hv1
  refine ⟨LinearMap.ker_eq_bot.2 hinj, ?_⟩
  have hsurj : Function.Surjective (L : (Fin 2 → ℝ) →ₗ[ℝ] ℝ × ℝ) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  exact LinearMap.range_eq_top.2 hsurj

/-- `bpI:p3:chart`. -/
theorem chart (hd : HeadData B s₀ r₀ h B' η) {c : Fin 2 → ℝ} (hc : c ∈ closure B') :
    jac2 (chartPhi h c) c =
      -(KAM.Iso.borderedHessian h c).det / (frequencyMap h c ⬝ᵥ frequencyMap h c) ∧
    jac2 (chartPhi h c) c ≠ 0 ∧
    ∀ N : Set (Fin 2 → ℝ), IsOpen N → c ∈ N → ∃ (W : Set (Fin 2 → ℝ)) (Ψ : ℝ × ℝ → Fin 2 → ℝ),
      IsOpen W ∧ c ∈ W ∧ W ⊆ N ∩ chartDom h B r₀ c ∧ IsOpen (chartPhi h c '' W) ∧
      ContDiffOn ℝ 1 Ψ (chartPhi h c '' W) ∧ (∀ v ∈ chartPhi h c '' W, Ψ v ∈ W) ∧
      (∀ I ∈ W, Ψ (chartPhi h c I) = I) ∧ ∀ v ∈ chartPhi h c '' W, chartPhi h c (Ψ v) = v := by
  have hcU : c ∈ realAct B r₀ := subset_realAct_charts hd.hr (hd.inside hc)
  have hdet : (KAM.Iso.borderedHessian h c).det ≠ 0 := hd.iso c hcU
  have hg : frequencyMap h c ≠ 0 := (det_identity hd hcU).2.2.1
  have hq : 0 < frequencyMap h c ⬝ᵥ frequencyMap h c := dotProduct_self_pos hg
  have hjac := jac2_chartPhi hd hcU
  have hjne : jac2 (chartPhi h c) c ≠ 0 := by
    rw [hjac]; exact div_ne_zero (neg_ne_zero.2 hdet) hq.ne'
  refine ⟨hjac, hjne, fun N hN hcN => ?_⟩
  obtain ⟨-, hdomopen, hcdom, hcd, -⟩ := coordinates hd hcU
  set Φ := chartPhi h c with hΦdef
  have hΦ : ContDiffAt ℝ 1 Φ c := hcd.contDiffAt (hdomopen.mem_nhds hcdom)
  set L := fderiv ℝ Φ c with hLdef
  have hL : HasFDerivAt Φ L c := hΦ.differentiableAt (by norm_num) |>.hasFDerivAt
  have hjL : jac2 Φ c = (L (Pi.single 0 1)).1 * (L (Pi.single 1 1)).2 -
      (L (Pi.single 1 1)).1 * (L (Pi.single 0 1)).2 := by
    unfold jac2
    rw [hL.fst.fderiv, hL.snd.fderiv]
    rfl
  obtain ⟨hker, hrange⟩ := bijective_of_jac_ne_zero L (hjL ▸ hjne)
  let e : (Fin 2 → ℝ) ≃L[ℝ] ℝ × ℝ := ContinuousLinearEquiv.ofBijective L hker hrange
  have he : HasFDerivAt Φ (e : (Fin 2 → ℝ) →L[ℝ] ℝ × ℝ) c := hL
  let ep := hΦ.toOpenPartialHomeomorph Φ he one_ne_zero
  have hepc : ∀ x, ep x = Φ x := fun x => rfl
  have hcsrc : c ∈ ep.source := hΦ.mem_toOpenPartialHomeomorph_source he one_ne_zero
  have hsymm : ContDiffAt ℝ 1 ep.symm (Φ c) := hΦ.to_localInverse he one_ne_zero
  obtain ⟨V2, hV2, hV2open, hΦcV2⟩ := _root_.eventually_nhds_iff.1
    (hsymm.eventually (by norm_num))
  -- the open image of a neighbourhood of `c` on which the inverse is `C¹`
  have hS0 : IsOpen (ep.source ∩ N ∩ chartDom h B r₀ c) :=
    (ep.open_source.inter hN).inter hdomopen
  have hV0 : IsOpen (ep '' (ep.source ∩ N ∩ chartDom h B r₀ c)) :=
    ep.isOpen_image_of_subset_source hS0 fun x hx => hx.1.1
  have hV : IsOpen (ep '' (ep.source ∩ N ∩ chartDom h B r₀ c) ∩ V2) := hV0.inter hV2open
  have hcV : Φ c ∈ ep '' (ep.source ∩ N ∩ chartDom h B r₀ c) ∩ V2 :=
    ⟨⟨c, ⟨⟨hcsrc, hcN⟩, hcdom⟩, rfl⟩, hΦcV2⟩
  set V := ep '' (ep.source ∩ N ∩ chartDom h B r₀ c) ∩ V2 with hVdef
  set W := N ∩ chartDom h B r₀ c ∩ (ep.source ∩ ep ⁻¹' V) with hWdef
  have hWopen : IsOpen W := (hN.inter hdomopen).inter (ep.isOpen_inter_preimage hV)
  have hcW : c ∈ W := ⟨⟨hcN, hcdom⟩, hcsrc, hcV⟩
  have hWsrc : ∀ x ∈ W, x ∈ ep.source := fun x hx => hx.2.1
  have himg : Φ '' W = V := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2.2
    · intro hv
      obtain ⟨x, ⟨⟨hxs, hxN⟩, hxd⟩, hxv⟩ := hv.1
      exact ⟨x, ⟨⟨hxN, hxd⟩, hxs, by rw [Set.mem_preimage, hxv]; exact hv⟩, hxv⟩
  have hleft : ∀ x ∈ W, ep.symm (Φ x) = x := fun x hx => ep.left_inv (hWsrc x hx)
  refine ⟨W, ep.symm, hWopen, hcW, fun x hx => hx.1, himg ▸ hV, ?_, ?_, hleft, ?_⟩
  · rw [himg]
    exact fun v hv => (hV2 v hv.2).contDiffWithinAt
  · rintro v ⟨x, hx, rfl⟩
    rw [hleft x hx]
    exact hx
  · rintro v ⟨x, hx, rfl⟩
    rw [hleft x hx]

/-! ### Patches and the cover -/

/-- The first chart coordinate `Re h` is `C¹` on the real slice. -/
theorem contDiffOn_realPart (hd : HeadData B s₀ r₀ h B' η) :
    ContDiffOn ℝ 1 (realPart h) (realAct B r₀) :=
  (KAM.Iso.Linear.freq_map_contDiff (KAM.Head.isOpen_actionNbhd B r₀) hd.holo hd.real).1

/-- A window `Q = [h(c) ± δ_E] × [-δ_m, δ_m]` inside an open set containing `(h(c), 0)`. -/
theorem exists_window {V : Set (ℝ × ℝ)} (hV : IsOpen V) {e : ℝ} (he : (e, (0 : ℝ)) ∈ V) :
    ∃ δE δm : ℝ, 0 < δE ∧ 0 < δm ∧ Icc (e - δE) (e + δE) ×ˢ Icc (-δm) δm ⊆ V := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV _ he
  refine ⟨ε / 2, ε / 2, half_pos hε, half_pos hε, ?_⟩
  rintro ⟨x, y⟩ ⟨⟨hx1, hx2⟩, hy1, hy2⟩
  apply hball
  rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
  constructor
  · rw [abs_lt]; constructor <;> linarith
  · rw [abs_lt]; constructor <;> linarith

/-- Every centre `c ∈ closure B'` carries a patch of radius `η₁ = eta1 η B B'`. -/
theorem exists_isPatch (hd : HeadData B s₀ r₀ h B' η) (hne : B'.Nonempty) {c : Fin 2 → ℝ}
    (hc : c ∈ closure B') :
    ∃ (W : Set (Fin 2 → ℝ)) (Ψ : ℝ × ℝ → Fin 2 → ℝ) (δE δm ρc : ℝ),
      IsPatch h B r₀ B' (eta1 η B B') c W Ψ δE δm ρc := by
  obtain ⟨hdB, -, -, hSB, -⟩ := compact hd hne
  have hη₁ : 0 < eta1 η B B' := lt_min hd.hη (half_pos hdB)
  have hη₁le : eta1 η B B' ≤ dB B B' / 2 := min_le_right _ _
  have hcU : c ∈ realAct B r₀ := subset_realAct_charts hd.hr (hd.inside hc)
  -- the ball around `c` lies in `B`
  have hballB : ball c (eta1 η B B' / 4) ⊆ B := by
    intro y hy
    apply hSB
    exact Metric.mem_cthickening_of_dist_le y c _ _ hc (by
      have := mem_ball.1 hy
      linarith)
  obtain ⟨-, hdomopen, hcdom, hcd, hΦc⟩ := coordinates hd hcU
  obtain ⟨-, -, hch⟩ := chart hd hc
  obtain ⟨W, Ψ, hWopen, hcW, hWsub, hV, hΨ, hΨmem, hΨleft, hΨright⟩ :=
    hch (ball c (eta1 η B B' / 4)) isOpen_ball (mem_ball_self (by positivity))
  have hWdom : W ⊆ chartDom h B r₀ c := fun x hx => (hWsub hx).2
  have hWball : W ⊆ ball c (eta1 η B B' / 4) := fun x hx => (hWsub hx).1
  have hRe : ContDiffOn ℝ 1 (realPart h) W :=
    (contDiffOn_realPart hd).mono fun x hx => (hWdom hx).1
  have hmW : ContDiffOn ℝ 1 (chartM h c) W :=
    contDiff_snd.comp_contDiffOn (hcd.mono hWdom)
  -- the window
  have hΦcV : (realPart h c, (0 : ℝ)) ∈ chartPhi h c '' W := ⟨c, hcW, hΦc⟩
  obtain ⟨δE, δm, hδE, hδm, hQ⟩ := exists_window hV hΦcV
  -- the radius
  have hRec : ContinuousAt (realPart h) c := hRe.continuousOn.continuousAt (hWopen.mem_nhds hcW)
  have hmc : ContinuousAt (chartM h c) c := hmW.continuousOn.continuousAt (hWopen.mem_nhds hcW)
  have hm0 : chartM h c c = 0 := by
    have := congrArg Prod.snd hΦc
    exact this
  obtain ⟨ρ₁, hρ₁, h₁⟩ := Metric.isOpen_iff.1 hWopen c hcW
  obtain ⟨ρ₂, hρ₂, h₂⟩ := Metric.continuousAt_iff.1 hRec (δE / 2) (half_pos hδE)
  obtain ⟨ρ₃, hρ₃, h₃⟩ := Metric.continuousAt_iff.1 hmc (δm / 4) (by positivity)
  have hρ : 0 < min (min ρ₁ ρ₂) (min ρ₃ (eta1 η B B' / 4)) :=
    lt_min (lt_min hρ₁ hρ₂) (lt_min hρ₃ (by positivity))
  refine ⟨W, Ψ, δE, δm, min (min ρ₁ ρ₂) (min ρ₃ (eta1 η B B' / 4)), ?_⟩
  have hρ₁' : min (min ρ₁ ρ₂) (min ρ₃ (eta1 η B B' / 4)) ≤ ρ₁ :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hρ₂' : min (min ρ₁ ρ₂) (min ρ₃ (eta1 η B B' / 4)) ≤ ρ₂ :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hρ₃' : min (min ρ₁ ρ₂) (min ρ₃ (eta1 η B B' / 4)) ≤ ρ₃ :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hρ₄' : min (min ρ₁ ρ₂) (min ρ₃ (eta1 η B B' / 4)) ≤ eta1 η B B' / 4 :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨hc, hWopen, hWdom, fun x hx => hballB (hWball hx), hWball, hRe, hmW, hV, hΨ, hΨmem,
    hΨleft, hΨright, hδE, hδm, hρ, hQ, hρ₄', ?_, ?_, ?_⟩
  · intro x hx
    exact h₁ (mem_ball.2 ((mem_ball.1 hx).trans_le hρ₁'))
  · intro x hx
    have := h₂ ((mem_ball.1 hx).trans_le hρ₂')
    rwa [Real.dist_eq] at this
  · intro x hx
    have := h₃ ((mem_ball.1 hx).trans_le hρ₃')
    rwa [Real.dist_eq, hm0, sub_zero] at this

/-- `bpI:p3:cover`: finitely many patches `(c, W_c, Ψ_c, δ_E, δ_m, ρ_c)` cover `closure B'`. -/
theorem cover (hd : HeadData B s₀ r₀ h B' η) (hne : B'.Nonempty) :
    ∃ (P : Finset (Fin 2 → ℝ)) (W : (Fin 2 → ℝ) → Set (Fin 2 → ℝ))
      (Ψ : (Fin 2 → ℝ) → ℝ × ℝ → Fin 2 → ℝ) (δE δm ρc : (Fin 2 → ℝ) → ℝ),
      (∀ c ∈ P, IsPatch h B r₀ B' (eta1 η B B') c (W c) (Ψ c) (δE c) (δm c) (ρc c)) ∧
      closure B' ⊆ ⋃ c ∈ P, ball c (ρc c) := by
  choose! W Ψ δE δm ρc hP using fun c (hc : c ∈ closure B') => exists_isPatch hd hne hc
  obtain ⟨P, hPsub, hPcov⟩ := hd.compact.elim_nhds_subcover (fun c => ball c (ρc c))
    fun c hc => ball_mem_nhds c (hP c hc).ρc_pos
  exact ⟨P, W, Ψ, δE, δm, ρc, fun c hc => hP c (hPsub c hc), hPcov⟩

end KAM.Iso.Charts
