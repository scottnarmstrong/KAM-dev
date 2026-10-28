/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.Extension
public import KAM.Planetary.PGAssembly.JetsParam
public import KAM.Planetary.PGAssembly.JetsFamily

/-!
# P Part 5: holomorphy and continuity of the complex average (`bpP:p5:be-an`)

On the product domain `avgDom d = {(I, x) | I ∈ actionNbhd (closure V) (δ/2), ‖x‖ < r}` the
complex average `(I, x) ↦ complexAverage d mu I x` is holomorphic for every `mu ∈ [0, mu0]` and
jointly continuous in `(mu, I, x)`. Proof: the integrand is `P mu` composed with an affine map,
`holomorphic_parametric_integral` for holomorphy; dominated convergence (the bound `MP`) for the
joint continuity in `mu`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-JET.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Filter Topology

namespace KAM.Planetary

variable {a b : ℕ}

/-- The jet domain carrier `ℂᵃ × (ℂᵇ × ℂᵇ)`. -/
abbrev JetE (a b : ℕ) := (Fin a → ℂ) × PGComplexPhase b

theorem isOpen_extensionDomain (d : PGData a b) (delta : ℝ) : IsOpen (extensionDomain d delta) := by
  have : extensionDomain d delta = ⋃ w : Phase (a + b), ⋃ (_ : blockFast w.2 ∈ closure d.V ∧
      ‖(blockSlow w.2, blockSlow w.1)‖ ≤ d.r0 / 2), ball (KAM.realInclusion₂ (a + b) w) delta := by
    ext z
    simp [extensionDomain, dist_eq_norm, and_assoc]
  rw [this]
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball

def avgDom (d : PGData a b) : Set (JetE a b) :=
  {z | z.1 ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2) ∧ ‖z.2‖ < pgOscRadius d}

theorem isOpen_avgDom (d : PGData a b) : IsOpen (avgDom d) :=
  ((isOpen_actionNbhd _ _).preimage continuous_fst).inter
    (isOpen_lt continuous_snd.norm continuous_const)

/-- The complex average as a function on the product domain. -/
def avgFun (d : PGData a b) (mu : ℝ) (z : JetE a b) : ℂ := complexAverage d mu z.1 z.2

/-- The integrand of the complex average. -/
def avgInt (d : PGData a b) (mu : ℝ) (phi : Fin a → ℝ) (z : JetE a b) : ℂ :=
  (pgExtension d).P mu (assembleComplex z.1 (KAM.realInclusion a phi) z.2.2 z.2.1)

/-- The linear part of `assembleComplex` in the variables `(I, x)`. -/
def assembleLin (a b : ℕ) : JetE a b →L[ℂ] PGComplexPhase (a + b) :=
  (ContinuousLinearMap.pi fun i : Fin (a + b) =>
      Fin.addCases (motive := fun _ => JetE a b →L[ℂ] ℂ) (fun _ => 0)
        (fun j => (ContinuousLinearMap.proj j).comp
          ((ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _))) i).prod
    (ContinuousLinearMap.pi fun i : Fin (a + b) =>
      Fin.addCases (motive := fun _ => JetE a b →L[ℂ] ℂ)
        (fun j => (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℂ _ _))
        (fun j => (ContinuousLinearMap.proj j).comp
          ((ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _))) i)

theorem assembleComplex_eq_add (phi : Fin a → ℝ) (z : JetE a b) :
    assembleComplex z.1 (KAM.realInclusion a phi) z.2.2 z.2.1 =
      assembleComplex 0 (KAM.realInclusion a phi) 0 0 + assembleLin a b z := by
  refine Prod.ext ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [assembleComplex, assembleLin]

theorem avgInt_mem (d : PGData a b) {z : JetE a b} (hz : z ∈ avgDom d) (phi : Fin a → ℝ) :
    assembleComplex z.1 (KAM.realInclusion a phi) z.2.2 z.2.1 ∈
      extensionDomain d (pgExtension d).delta := by
  have hpi := Real.pi_pos
  have hd := (pgExtension d).delta_pos
  have hx : ‖z.2‖ < (pgExtension d).delta / 4 := hz.2.trans_le (min_le_right _ _)
  have hθ : (fun j => ((phi j / (2 * Real.pi) : ℝ) : ℂ)) ∈
      KAM.complexStrip a ((pgExtension d).delta / (2 * Real.pi)) := fun j => by
    simp only [Complex.ofReal_im, abs_zero]
    positivity
  have h := strip_mem_extensionDomain d hd hz.1 hx hθ
  have e : (2 * Real.pi : ℂ) • (fun j => ((phi j / (2 * Real.pi) : ℝ) : ℂ)) =
      KAM.realInclusion a phi := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, KAM.realInclusion_apply]
    push_cast
    field_simp
  rw [e] at h
  exact h

theorem continuous_assembleComplex_real :
    Continuous fun y : (Fin a → ℝ) × JetE a b =>
      assembleComplex y.2.1 (KAM.realInclusion a y.1) y.2.2.2 y.2.2.1 := by
  refine Continuous.prodMk (continuous_pi fun j => ?_) (continuous_pi fun j => ?_)
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp only [Fin.append_left, Fin.append_right, KAM.realInclusion_apply] <;>
      fun_prop
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp only [Fin.append_left, Fin.append_right] <;> fun_prop

theorem avgInt_eq_comp (d : PGData a b) (mu : ℝ) (phi : Fin a → ℝ) :
    avgInt d mu phi = fun z => (pgExtension d).P mu
      (assembleComplex 0 (KAM.realInclusion a phi) 0 0 + assembleLin a b z) := by
  funext z
  unfold avgInt
  rw [assembleComplex_eq_add]

theorem avgFun_differentiableOn (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) :
    DifferentiableOn ℂ (avgFun d mu) (avgDom d) := by
  set Q : Set (Fin a → ℝ) := pi univ fun _ : Fin a => Icc (0 : ℝ) (2 * Real.pi) with hQdef
  have hQ : IsCompact Q := isCompact_univ_pi fun _ => isCompact_Icc
  have hPd := (pgExtension d).holo mu hmu
  have hext := isOpen_extensionDomain d (pgExtension d).delta
  have hmaps : MapsTo (fun y : (Fin a → ℝ) × JetE a b =>
      assembleComplex y.2.1 (KAM.realInclusion a y.1) y.2.2.2 y.2.2.1) (Q ×ˢ avgDom d)
      (extensionDomain d (pgExtension d).delta) := fun y hy => avgInt_mem d hy.2 y.1
  have hcont := continuous_assembleComplex_real (a := a) (b := b)
  have hfd : ContinuousOn (fderiv ℂ ((pgExtension d).P mu)) (extensionDomain d (pgExtension d).delta) :=
    (KAM.differentiableOn_fderiv_of_isOpen hext hPd).continuousOn
  have hG : ContinuousOn (fun y : (Fin a → ℝ) × JetE a b => avgInt d mu y.1 y.2)
      (Q ×ˢ avgDom d) := hPd.continuousOn.comp hcont.continuousOn hmaps
  have hGd : ∀ phi ∈ Q, DifferentiableOn ℂ (avgInt d mu phi) (avgDom d) := by
    intro phi _
    rw [avgInt_eq_comp]
    refine hPd.comp ?_ (fun z hz => ?_)
    · exact (assembleLin a b).differentiable.const_add _ |>.differentiableOn
    · rw [← assembleComplex_eq_add]; exact avgInt_mem d hz phi
  have hDG : ContinuousOn (fun y : (Fin a → ℝ) × JetE a b => fderiv ℂ (avgInt d mu y.1) y.2)
      (Q ×ˢ avgDom d) := by
    have hcongr : ∀ y ∈ Q ×ˢ avgDom d, fderiv ℂ (avgInt d mu y.1) y.2 =
        (fderiv ℂ ((pgExtension d).P mu) (assembleComplex y.2.1 (KAM.realInclusion a y.1)
          y.2.2.2 y.2.2.1)).comp (assembleLin a b) := by
      intro y hy
      rw [avgInt_eq_comp]
      have hmem := avgInt_mem d hy.2 y.1
      rw [assembleComplex_eq_add y.1 y.2] at hmem ⊢
      exact (((hPd.differentiableAt (hext.mem_nhds hmem)).hasFDerivAt).comp y.2
        ((assembleLin a b).hasFDerivAt.const_add _)).fderiv
    refine ContinuousOn.congr ?_ hcongr
    exact ContinuousOn.clm_comp (hfd.comp hcont.continuousOn hmaps) continuousOn_const
  have := holomorphic_parametric_integral_gen hQ (isOpen_avgDom d) hG hGd hDG
  exact this.const_mul _

theorem avgFun_continuousOn (d : PGData a b) :
    ContinuousOn (fun p : ℝ × JetE a b => avgFun d p.1 p.2) (Icc 0 d.mu0 ×ˢ avgDom d) := by
  set Q : Set (Fin a → ℝ) := pi univ fun _ : Fin a => Icc (0 : ℝ) (2 * Real.pi) with hQdef
  have hQ : IsCompact Q := isCompact_univ_pi fun _ => isCompact_Icc
  have hQm : MeasurableSet Q := hQ.isClosed.measurableSet
  have hext := isOpen_extensionDomain d (pgExtension d).delta
  have hcont := continuous_assembleComplex_real (a := a) (b := b)
  have : IsFiniteMeasure (volume.restrict Q) :=
    ⟨by simp [hQ.measure_lt_top]⟩
  have hint : ContinuousOn (fun p : ℝ × JetE a b => ∫ phi in Q, avgInt d p.1 phi p.2)
      (Icc 0 d.mu0 ×ˢ avgDom d) := by
    intro p0 hp0
    refine tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict Q)
      (fun _ => (pgExtension d).MP) ?_ ?_ (integrable_const _) ?_
    · refine eventually_nhdsWithin_of_forall fun p hp => ?_
      refine ContinuousOn.aestronglyMeasurable ?_ hQm
      have hc : Continuous fun phi : Fin a → ℝ =>
          assembleComplex p.2.1 (KAM.realInclusion a phi) p.2.2.2 p.2.2.1 :=
        hcont.comp (continuous_id.prodMk continuous_const)
      exact ((pgExtension d).holo p.1 hp.1).continuousOn.comp hc.continuousOn
        (fun phi _ => avgInt_mem d hp.2 phi)
    · refine eventually_nhdsWithin_of_forall fun p hp => ?_
      exact (ae_restrict_iff' hQm).2 (Eventually.of_forall fun phi _ =>
        (pgExtension d).bound p.1 hp.1 _ (avgInt_mem d hp.2 phi))
    · refine (ae_restrict_iff' hQm).2 (Eventually.of_forall fun phi _ => ?_)
      have hc : Continuous fun p : ℝ × JetE a b =>
          (p.1, assembleComplex p.2.1 (KAM.realInclusion a phi) p.2.2.2 p.2.2.1) :=
        continuous_fst.prodMk (hcont.comp (continuous_const.prodMk continuous_snd))
      have hm : MapsTo (fun p : ℝ × JetE a b =>
          (p.1, assembleComplex p.2.1 (KAM.realInclusion a phi) p.2.2.2 p.2.2.1))
          (Icc 0 d.mu0 ×ˢ avgDom d) (Icc 0 d.mu0 ×ˢ extensionDomain d (pgExtension d).delta) :=
        fun p hp => ⟨hp.1, avgInt_mem d hp.2 phi⟩
      exact ((pgExtension d).continuous.comp hc.continuousOn hm) p0 hp0
  exact hint.const_mul _

end KAM.Planetary

end
