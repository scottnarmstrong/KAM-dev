/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.Holomorphic
public import KAM.Planetary.PGAssembly.JetsParam
public import KAM.Strip.Bridges

/-!
# Holomorphy of the fast mean (P11A-P2e, `stepP:p11:hc-mean`)

`p11_fastMean_differentiableOn`: if `F` is holomorphic on the working domain
`p11WorkingDom n J₀ s r rz` (with `s > 0`), then `(J, z) ↦ p11FastMean F J z` is holomorphic
jointly in `(J, z)` on the product set `‖J - ι J₀‖ < r`, `‖z‖ < rz`
(`Weighted.holomorphic_parametric_integral` through `holomorphic_parametric_integral_gen`).
-/

@[expose] public noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace KAM.Planetary

section Holo

variable {n : ℕ}

theorem isOpen_p11WorkingDom (J0 : P11Vec n) (s r rz : ℝ) :
    IsOpen (p11WorkingDom n J0 s r rz) := by
  have h1 : IsOpen {z : P11Phase (n + n) |
      (fun i : Fin n => z.1 (Fin.castAdd n i)) ∈ KAM.complexStrip n s} :=
    (KAM.isOpen_complexStrip n s).preimage (by fun_prop)
  have h2 : IsOpen {z : P11Phase (n + n) | ‖(fun i : Fin n => z.2 (Fin.castAdd n i)) -
      KAM.realInclusion n J0‖ < r} := isOpen_lt (by fun_prop) continuous_const
  have h3 : IsOpen {z : P11Phase (n + n) | ‖(fun i : Fin n => z.1 (Fin.natAdd n i))‖ < rz} :=
    isOpen_lt (by fun_prop) continuous_const
  have h4 : IsOpen {z : P11Phase (n + n) | ‖(fun i : Fin n => z.2 (Fin.natAdd n i))‖ < rz} :=
    isOpen_lt (by fun_prop) continuous_const
  exact h1.inter (h2.inter (h3.inter h4))

/-- The product domain of the mean in the variables `(J, (x, y))`. -/
def p11MeanDom (J0 : P11Vec n) (r rz : ℝ) : Set (P11CVec n × P11Phase n) :=
  {u | ‖u.1 - KAM.realInclusion n J0‖ < r ∧ ‖u.2‖ < rz}

theorem isOpen_p11MeanDom (J0 : P11Vec n) (r rz : ℝ) : IsOpen (p11MeanDom J0 r rz) := by
  have h1 : IsOpen {u : P11CVec n × P11Phase n | ‖u.1 - KAM.realInclusion n J0‖ < r} :=
    isOpen_lt (by fun_prop) continuous_const
  have h2 : IsOpen {u : P11CVec n × P11Phase n | ‖u.2‖ < rz} :=
    isOpen_lt (by fun_prop) continuous_const
  exact h1.inter h2

/-- The linear part of `u = (J, (x, y)) ↦ ((θ, x), (J, y))` (in the variables other than `θ`). -/
def p11MeanLin (n : ℕ) : (P11CVec n × P11Phase n) →L[ℂ] P11Phase (n + n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => (Fin.append (0 : P11CVec n) u.2.1, Fin.append u.1 u.2.2)
      map_add' := fun u v => by
        refine Prod.ext ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
          simp
      map_smul' := fun c u => by
        refine Prod.ext ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
          simp }

theorem p11MeanLin_apply (u : P11CVec n × P11Phase n) :
    p11MeanLin n u = (Fin.append (0 : P11CVec n) u.2.1, Fin.append u.1 u.2.2) := rfl

/-- The integrand point of the mean. -/
def p11MeanPt (θ : P11Vec n) (u : P11CVec n × P11Phase n) : P11Phase (n + n) :=
  (Fin.append (KAM.realInclusion n θ) u.2.1, Fin.append u.1 u.2.2)

theorem p11MeanPt_eq (θ : P11Vec n) (u : P11CVec n × P11Phase n) :
    p11MeanPt θ u = (Fin.append (KAM.realInclusion n θ) (0 : P11CVec n), (0 : P11CVec (n + n)))
      + p11MeanLin n u := by
  refine Prod.ext ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [p11MeanPt, p11MeanLin_apply]

theorem p11MeanPt_mem {J0 : P11Vec n} {s r rz : ℝ} (hs : 0 < s) (θ : P11Vec n)
    {u : P11CVec n × P11Phase n} (hu : u ∈ p11MeanDom J0 r rz) :
    p11MeanPt θ u ∈ p11WorkingDom n J0 s r rz := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [p11MeanPt] using KAM.ofReal_mem_complexStrip hs θ
  · simpa [p11MeanPt] using hu.1
  · have := hu.2
    rw [Prod.norm_def, max_lt_iff] at this
    simpa [p11MeanPt] using this.1
  · have := hu.2
    rw [Prod.norm_def, max_lt_iff] at this
    simpa [p11MeanPt] using this.2

theorem continuous_p11MeanPt : Continuous (fun y : P11Vec n × (P11CVec n × P11Phase n) =>
    p11MeanPt y.1 y.2) := by
  refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun i => ?_) <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp <;> fun_prop

/-- `hc-mean`: the fast mean is holomorphic jointly in `(J, z)`. -/
theorem p11_fastMean_differentiableOn {F : P11Phase (n + n) → ℂ} {J0 : P11Vec n}
    {s r rz : ℝ} (hs : 0 < s) (hF : DifferentiableOn ℂ F (p11WorkingDom n J0 s r rz)) :
    DifferentiableOn ℂ (fun u : P11CVec n × P11Phase n => p11FastMean F u.1 u.2)
      (p11MeanDom J0 r rz) := by
  have hW := isOpen_p11WorkingDom J0 s r rz
  have hreg := KAM.holomorphic_regularity_of_finiteDimensional hW hF
  have hQ : IsCompact (Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hmaps : MapsTo (fun y : P11Vec n × (P11CVec n × P11Phase n) => p11MeanPt y.1 y.2)
      (Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1) ×ˢ p11MeanDom J0 r rz)
      (p11WorkingDom n J0 s r rz) := fun y hy => p11MeanPt_mem hs y.1 hy.2
  have hGd : ∀ θ : P11Vec n, DifferentiableOn ℂ (fun u => F (p11MeanPt θ u))
      (p11MeanDom J0 r rz) := by
    intro θ
    have hd : Differentiable ℂ (p11MeanPt θ : P11CVec n × P11Phase n → P11Phase (n + n)) := by
      have : (p11MeanPt θ : P11CVec n × P11Phase n → P11Phase (n + n)) = fun u =>
          (Fin.append (KAM.realInclusion n θ) (0 : P11CVec n), (0 : P11CVec (n + n)))
            + p11MeanLin n u := funext (p11MeanPt_eq θ)
      rw [this]
      exact (differentiable_const _).add (p11MeanLin n).differentiable
    exact hF.comp hd.differentiableOn fun u hu => p11MeanPt_mem hs θ hu
  have hfd : ∀ θ : P11Vec n, ∀ u ∈ p11MeanDom J0 r rz,
      fderiv ℂ (fun u => F (p11MeanPt θ u)) u =
        (fderiv ℂ F (p11MeanPt θ u)).comp (p11MeanLin n) := by
    intro θ u hu
    have hFd : HasFDerivAt F (fderiv ℂ F (p11MeanPt θ u)) (p11MeanPt θ u) :=
      (hF.differentiableAt (hW.mem_nhds (p11MeanPt_mem hs θ hu))).hasFDerivAt
    have hpt : HasFDerivAt (p11MeanPt θ : P11CVec n × P11Phase n → P11Phase (n + n))
        (p11MeanLin n) u := by
      have : (p11MeanPt θ : P11CVec n × P11Phase n → P11Phase (n + n)) = fun u =>
          (Fin.append (KAM.realInclusion n θ) (0 : P11CVec n), (0 : P11CVec (n + n)))
            + p11MeanLin n u := funext (p11MeanPt_eq θ)
      rw [this]
      exact (p11MeanLin n).hasFDerivAt.const_add _
    exact (hFd.comp u hpt).fderiv
  have := holomorphic_parametric_integral_gen hQ (isOpen_p11MeanDom J0 r rz)
    (G := fun θ u => F (p11MeanPt θ u))
    (hF.continuousOn.comp continuous_p11MeanPt.continuousOn hmaps)
    (fun θ _ => hGd θ)
    (by
      refine ContinuousOn.congr ?_ (fun y hy => hfd y.1 y.2 hy.2)
      exact ContinuousOn.clm_comp (hreg.1.continuousOn.comp continuous_p11MeanPt.continuousOn hmaps)
        continuousOn_const)
  exact this

end Holo

end KAM.Planetary

end
