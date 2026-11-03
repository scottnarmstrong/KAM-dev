/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusChain.Domain

/-!
# Chains of torus steps: the angle-derivative bound (track B, B4-TMULTI)

`tchChainDrift_le` bounds `|∂_{φ_j} R (x)|` for `R = H ∘ Ψ - Nact ∘ J` of a chain at a real point
of the closed cylinder: the polynomial `P` by `ftAngleDriftBound`, the summed holomorphic
remainder by one Cauchy estimate on a `δc`-polydisc.
-/

@[expose] public noncomputable section

open Set KAM.Canonical Filter
open scoped Topology

namespace KAM.EffectiveStability

variable {n : ℕ}

theorem tchBound_of_cpolydisc {r : Fin n → ℝ} {δc : ℝ} {x : (Fin n → ℝ) × (Fin n → ℝ)}
    (hxr : ∀ i, |x.2 i| ≤ r i) {w : (Fin n → ℂ) × (Fin n → ℂ)}
    (hw : w ∈ cpolydisc (KAM.realInclusion₂ n x) δc) : TChBound r δc δc w := by
  intro i
  obtain ⟨h1, h2⟩ := hw i
  have e1 : |(w.1 i).im| ≤ δc := by
    have : (w.1 i).im = (w.1 i - (KAM.realInclusion₂ n x).1 i).im := by simp
    rw [this]; exact (Complex.abs_im_le_norm _).trans h1
  have e2 : ‖w.2 i‖ ≤ ‖(KAM.realInclusion₂ n x).2 i‖ +
      ‖w.2 i - (KAM.realInclusion₂ n x).2 i‖ := by
    simpa using norm_add_le ((KAM.realInclusion₂ n x).2 i)
      (w.2 i - (KAM.realInclusion₂ n x).2 i)
  simp only [KAM.realInclusion₂_apply, KAM.realInclusion_apply, Complex.norm_real,
    Real.norm_eq_abs] at e2 h2
  exact ⟨e1, by linarith [hxr i]⟩

/-- **Chain drift bound** at a real point `x` of the closed cylinder. -/
theorem tchChainDrift_le {H Nact P : FTPoly} (hH : FTFits n H) (hP : FTFits n P)
    (hA : ftActOnly Nact = true) {l : List TChStep} (hok : TChChainOK n Nact P l H)
    {b r : Fin n → ℝ} {εb δc : ℝ} (hdom : TChDomOK n b r εb δc l) (hδc : 0 < δc)
    (hεb : 0 < εb) (bl : List ℚ) (η : Fin n → ℝ)
    (hbl : ∀ i : Fin n, ((bl.getD i 0 : ℚ) : ℝ) = b i) (hbr : ∀ i, b i ≤ r i)
    (hdrift : ∀ j : Fin n, ((ftAngleDriftBound P j ftPiUB bl : ℚ) : ℝ) +
      (tchChainBound n l H : ℝ) / δc ≤ η j)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : ∀ j, |x.2 j| ≤ b j) (j : Fin n) :
    |fderiv ℝ (fun w => ftEvalR H (tchChainMap l w) - ftEvalR Nact ((0 : Fin n → ℝ), w.2)) x
      (Pi.single j 1, 0)| ≤ η j := by
  have hl := hok.tchStepsOK
  obtain ⟨hUo, -⟩ := tchDom_isOpen_and_differentiableOn hl
  have hxr : ∀ i, |x.2 i| ≤ r i := fun i => (hx i).trans (hbr i)
  have hxD : x ∈ cyl (fun j => b j + εb) := fun i => by linarith [hx i]
  have hxB : TChBound r δc δc (KAM.realInclusion₂ n x) := by
    intro i
    simp only [KAM.realInclusion₂_apply, KAM.realInclusion_apply, Complex.ofReal_im, abs_zero,
      Complex.norm_real, Real.norm_eq_abs]
    exact ⟨hδc.le, by linarith [hxr i]⟩
  have hxU : KAM.realInclusion₂ n x ∈ tchDom l := (tchTheta_bound hl hdom hxB).1
  have hev : (fun w => ftEvalR H (tchChainMap l w) - ftEvalR Nact ((0 : Fin n → ℝ), w.2))
      =ᶠ[𝓝 x] fun y => ftEvalR P y + (tchRem l H (KAM.realInclusion₂ n y)).re := by
    filter_upwards [(isOpen_cyl (fun j => b j + εb)).mem_nhds hxD] with y hy
    rw [tchChain_identity hA hok hdom hy]
    ring
  have hdP : DifferentiableAt ℝ (fun y : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR P y) x :=
    ((ftEvalR_contDiff P 1).differentiable one_ne_zero).differentiableAt
  have hdRe := differentiableAt_realPart hUo (differentiableOn_tchRem hl H) hxU
  rw [hev.fderiv_eq, fderiv_fun_add hdP hdRe]
  simp only [add_apply]
  have hpoly := abs_fderiv_ftEvalR_le P hP bl pi_le_ftPiUB x (fun i => by rw [hbl]; exact hx i) j
  have hsub : cpolydisc (KAM.realInclusion₂ n x) δc ⊆ tchDom l :=
    fun w hw => (tchTheta_bound hl hdom (tchBound_of_cpolydisc hxr hw)).1
  have hM : ∀ w ∈ cpolydisc (KAM.realInclusion₂ n x) δc,
      ‖tchRem l H w‖ ≤ (tchChainBound n l H : ℝ) := fun w hw =>
    norm_tchRem_le hH hok hdom (tchBound_of_cpolydisc hxr hw)
  have hcau := abs_fderiv_realPart_fst_le hUo (differentiableOn_tchRem hl H) hxU hδc hsub hM j
  have := hdrift j
  exact (abs_add_le _ _).trans (by linarith)

end KAM.EffectiveStability
