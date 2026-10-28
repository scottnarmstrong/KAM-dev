/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Weighted.Parametric
public import KAM.Strip.Bridges
public import KAM.Planetary.MaximalStep.Basic

/-!
# Fourier cutoff: coefficients of an admissible function (P11A-C1)

For `F` holomorphic on `domain_def n r s B` the angle coefficient
`(η, b) ↦ û_k(η, b) = ∫_{[0,1]ⁿ} F(x, η, b) e^{-2πi k·x} dx` is holomorphic on the
action-and-parameter set `{‖η‖ < s} × B` (`coeff_joint_differentiableOn`), the parametric-integral
step of `bpP:p11a:fourier-cutoff`. The parameters `(η, b)` of two blocks are transported to
`Fin (n+n) → ℂ` by a continuous linear equivalence, the shape of `holomorphic_parametric_integral`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace KAM.Planetary

/-- The two parameter blocks `(η, b)` as one vector of `Fin (n+n) → ℂ`. -/
def p11ParamEquiv (n : ℕ) : (P11CVec n × P11CVec n) ≃L[ℂ] (Fin (n + n) → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    ((LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin n) ℂ ℂ).symm.trans
      (LinearEquiv.funCongrLeft ℂ ℂ (finSumFinEquiv (m := n) (n := n)).symm))

private abbrev cube (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Icc (0 : ℝ) 1

private theorem continuous_realPt {n : ℕ} :
    Continuous fun x : Fin n → ℝ => fun j => (x j : ℂ) :=
  continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)

/-- The embedding of a parameter vector `v` of `Fin (n+n) → ℂ` into the family, linear part. -/
private def lin (n : ℕ) : (Fin (n + n) → ℂ) →L[ℂ] P11Family n :=
  ((ContinuousLinearMap.inr ℂ (P11CVec n) (P11CVec n)).comp
      ((ContinuousLinearMap.fst ℂ _ _).comp (p11ParamEquiv n).symm.toContinuousLinearMap)).prod
    ((ContinuousLinearMap.snd ℂ _ _).comp (p11ParamEquiv n).symm.toContinuousLinearMap)

private def emb {n : ℕ} (x : Fin n → ℝ) (v : Fin (n + n) → ℂ) : P11Family n :=
  (((fun j => (x j : ℂ)), 0), 0) + lin n v

private theorem emb_E {n : ℕ} (x : Fin n → ℝ) (w : P11CVec n × P11CVec n) :
    emb x (p11ParamEquiv n w) = (((fun j => (x j : ℂ)), w.1), w.2) := by
  simp [emb, lin]

/-- The coefficient integrand in the parameters. -/
private def cG {n : ℕ} (F : P11Family n → ℂ) (k : Fin n → ℤ) (x : Fin n → ℝ)
    (v : Fin (n + n) → ℂ) : ℂ :=
  KAM.character (-k) (fun j => (x j : ℂ)) • F (emb x v)

theorem coeff_joint_differentiableOn {n : ℕ} {r s : ℝ} (hr : 0 < r) {B : Set (P11CVec n)}
    (hB : IsOpen B) {F : P11Family n → ℂ} (hF : DifferentiableOn ℂ F (domain_def n r s B))
    (k : Fin n → ℤ) :
    DifferentiableOn ℂ (fun w : P11CVec n × P11CVec n =>
      KAM.torusCoeffW (fun x : Fin n → ℝ => F (((fun j => (x j : ℂ)), w.1), w.2)) k)
      (KAM.Weighted.polyNbhd {0} s ×ˢ B) := by
  set E := p11ParamEquiv n with hE
  set V : Set (P11CVec n × P11CVec n) := KAM.Weighted.polyNbhd {0} s ×ˢ B with hV
  set U : Set (Fin (n + n) → ℂ) := E.symm ⁻¹' V with hU
  have hVo : IsOpen V := (KAM.Weighted.isOpen_polyNbhd _ _).prod hB
  have hUo : IsOpen U := hVo.preimage E.symm.continuous
  have hDo : IsOpen (domain_def n r s B) := (KAM.Weighted.isOpen_Dom _ _ _).prod hB
  have hemb : ∀ x : Fin n → ℝ, ∀ v ∈ U, emb x v ∈ domain_def n r s B := by
    intro x v hv
    have hv' : E.symm v ∈ V := hv
    have : emb x v = (((fun j => (x j : ℂ)), (E.symm v).1), (E.symm v).2) := by
      conv_lhs => rw [← E.apply_symm_apply v]
      exact emb_E x _
    rw [this]
    exact ⟨⟨KAM.ofReal_mem_complexStrip hr x, hv'.1⟩, hv'.2⟩
  have hembc : Continuous fun y : (Fin n → ℝ) × (Fin (n + n) → ℂ) => emb y.1 y.2 := by
    unfold emb
    exact (((continuous_realPt.comp continuous_fst).prodMk continuous_const).prodMk
      continuous_const).add ((lin n).continuous.comp continuous_snd)
  have hreg := KAM.holomorphic_regularity_of_finiteDimensional hDo hF
  have hmaps : MapsTo (fun y : (Fin n → ℝ) × (Fin (n + n) → ℂ) => emb y.1 y.2)
      (cube n ×ˢ U) (domain_def n r s B) := fun y hy => hemb y.1 y.2 hy.2
  have hchar : Continuous fun y : (Fin n → ℝ) × (Fin (n + n) → ℂ) =>
      KAM.character (-k) (fun j => (y.1 j : ℂ)) :=
    ((KAM.differentiable_character (-k)).continuous.comp continuous_realPt).comp continuous_fst
  have hder : ∀ x : Fin n → ℝ, ∀ v ∈ U, HasFDerivAt (cG F k x)
      (KAM.character (-k) (fun j => (x j : ℂ)) • (fderiv ℂ F (emb x v)).comp (lin n)) v := by
    intro x v hv
    have hz := hemb x v hv
    have hud : HasFDerivAt F (fderiv ℂ F (emb x v)) (emb x v) :=
      (hF.differentiableAt (hDo.mem_nhds hz)).hasFDerivAt
    have hl : HasFDerivAt (emb x) (lin n) v := by
      unfold emb
      exact (lin n).hasFDerivAt.const_add _
    exact (hud.comp v hl).const_smul (KAM.character (-k) fun j => (x j : ℂ))
  have hg : DifferentiableOn ℂ (fun v => ∫ x in cube n, cG F k x v) U ∧
      ∀ I ∈ U, fderiv ℂ (fun I' => ∫ x in cube n, cG F k x I') I =
        ∫ x in cube n, fderiv ℂ (cG F k x) I := by
    refine KAM.Weighted.holomorphic_parametric_integral (isCompact_univ_pi fun _ => isCompact_Icc)
      hUo ?_ ?_ ?_
    · exact hchar.continuousOn.smul (hF.continuousOn.comp hembc.continuousOn hmaps)
    · intro x _ v hv
      exact (hder x v hv).differentiableAt.differentiableWithinAt
    · have hcong : ∀ y ∈ cube n ×ˢ U, fderiv ℂ (cG F k y.1) y.2 =
          KAM.character (-k) (fun j => (y.1 j : ℂ)) • (fderiv ℂ F (emb y.1 y.2)).comp (lin n) :=
        fun y hy => (hder y.1 y.2 hy.2).fderiv
      refine ContinuousOn.congr ?_ hcong
      exact hchar.continuousOn.smul (ContinuousOn.clm_comp
        (hreg.1.continuousOn.comp hembc.continuousOn hmaps) continuousOn_const)
  have hcomp : DifferentiableOn ℂ ((fun v => ∫ x in cube n, cG F k x v) ∘ E) V := by
    refine hg.1.comp E.differentiableOn ?_
    intro w hw
    show E.symm (E w) ∈ V
    simpa using hw
  refine hcomp.congr fun w _ => ?_
  show _ = ∫ x in cube n, cG F k x (E w)
  have hE' : ∀ x : Fin n → ℝ, emb x (E w) = (((fun j => (x j : ℂ)), w.1), w.2) :=
    fun x => emb_E x w
  simp only [cG, hE']
  unfold KAM.torusCoeffW KAM.torusAverage
  rfl

end KAM.Planetary
