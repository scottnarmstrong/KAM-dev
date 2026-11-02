/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepReweight
public import KAM.Wave.KamStep.TaylorFieldBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Taylor element of the reweighted field (blueprint-W `bpW:w5:step`, modified case)

For `(P, X) ∈ 𝒮_{p+1}(D(s,r))` the element `T = stepTaylorOf …` of `𝒯_s` (`p̄ = p+1`) and the
  element
`T' = stepTaylorOf …` of the pair `(P, D_ρ ∘ X) ∈ 𝒮_{p₊}` are related by `T' = D_ρ T` on the strip
(componentwise). Consequences, used to transfer the homological equation of `bpW:w5:w4-modified`
(which is stated for `T`) to `T'`:
* `stepFun_taylorRho`: `waveStepFun T' w = waveStepFun T w` for `θ ∈ T_s`;
* `stepFun_nhat_taylorRho`: the same for `N̂`;
* `homNhat_taylorRho`: `N̂` of `T'` and of `T` agree.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s r : ℝ}

theorem kamNorm_stepRhoK_sub_le (hc : pb ≤ p + 1) (hr : 0 < r) (W W' : KamPhase) :
    kamNorm r (stepRhoK a p pb hc W - stepRhoK a p pb hc W') ≤ kamNorm r (W - W') := by
  rw [← map_sub]
  exact kamNorm_stepRhoK_le hc hr _

theorem stepRhoK_fderiv {X : KamPhase → KamPhase} (hc : pb ≤ p + 1) {w : KamPhase}
    (hX : DifferentiableAt ℂ X w) :
    fderiv ℂ (fun x => stepRhoK a p pb hc (X x)) w =
      (stepRhoK a p pb hc).comp (fderiv ℂ X w) :=
  ((stepRhoK a p pb hc).hasFDerivAt.comp w hX.hasFDerivAt).fderiv

theorem blockP_rhoK (hc : pb ≤ p + 1) (A : KamPhase →L[ℂ] KamPhase) :
    blockP ((stepRhoK a p pb hc).comp A) = (homModRho a p pb hc).comp (blockP A) := by
  unfold blockP
  refine ContinuousLinearMap.ext fun z => ?_
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, stepZb_stepRhoK,
    map_smul]

theorem blockP'_rhoK (hc : pb ≤ p + 1) (A : KamPhase →L[ℂ] KamPhase) :
    blockP' ((stepRhoK a p pb hc).comp A) = (homModRho a p pb hc).comp (blockP' A) := by
  unfold blockP'
  refine ContinuousLinearMap.ext fun z => ?_
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, stepZ_stepRhoK,
    map_smul]

theorem blockQ_rhoK (hc : pb ≤ p + 1) (A : KamPhase →L[ℂ] KamPhase) :
    blockQ ((stepRhoK a p pb hc).comp A) = (homModRho a p pb hc).comp (blockQ A) := by
  unfold blockQ
  refine ContinuousLinearMap.ext fun z => ?_
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, stepZ_stepRhoK,
    map_smul]

theorem blockQt_rhoK (hc : pb ≤ p + 1) (A : KamPhase →L[ℂ] KamPhase) :
    blockQt ((stepRhoK a p pb hc).comp A) = (homModRho a p pb hc).comp (blockQt A) := by
  unfold blockQt
  refine ContinuousLinearMap.ext fun z => ?_
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, stepZb_stepRhoK,
    map_smul]

theorem stepPr_rho (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hc : pb ≤ p + 1) (c z : HomL2) :
    stepPr ha (homPP hp hpb) (homModRho a p pb hc c) z =
      stepPr ha (homPP hp (homModPP1 p)) c z := by
  rw [stepPr_eq_homPairL2, stepPr_eq_homPairL2, homLamDiag_rho ha hp hpb hc]

theorem homCoeff_congr_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u v : (Fin 2 → ℂ) → E}
    (h : ∀ x : Fin 2 → ℝ, u (fun j => (x j : ℂ)) = v (fun j => (x j : ℂ))) (k : Fin 2 → ℤ) :
    homCoeff u k = homCoeff v k := by
  unfold homCoeff
  rw [show (fun x : Fin 2 → ℝ => u fun j => (x j : ℂ)) = fun x => v fun j => (x j : ℂ) from
    funext h]

theorem realTheta_mem_strip {s : ℝ} (hs : 0 < s) (x : Fin 2 → ℝ) :
    (fun j => (x j : ℂ)) ∈ complexStrip 2 s := fun i => by simpa using hs

section taylor

variable {P : KamPhase → ℂ} {X : KamPhase → KamPhase}

/-- Components of the reweighted Taylor element at `θ ∈ T_s`. -/
theorem tCp_rhoK (hc : pb ≤ p + 1) (θ : Fin 2 → ℂ) :
    tCp (fun x => stepRhoK a p pb hc (X x)) θ = homModRho a p pb hc (tCp X θ) := by
  unfold tCp
  rw [stepZb_stepRhoK, map_smul]

theorem tCm_rhoK (hc : pb ≤ p + 1) (θ : Fin 2 → ℂ) :
    tCm (fun x => stepRhoK a p pb hc (X x)) θ = homModRho a p pb hc (tCm X θ) := by
  unfold tCm
  rw [stepZ_stepRhoK, map_smul]

variable (hr : 0 < r) (hh : DifferentiableOn ℂ X (kamDomain s r))
include hr hh

theorem tDX_rhoK (hc : pb ≤ p + 1) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 s) :
    fderiv ℂ (fun x => stepRhoK a p pb hc (X x)) (stepW0L θ) =
      (stepRhoK a p pb hc).comp (fderiv ℂ X (stepW0L θ)) :=
  stepRhoK_fderiv hc (hh.differentiableAt ((kamDomain_isOpen s r).mem_nhds (stepW0L_mem hr hθ)))

theorem tP_rhoK (hc : pb ≤ p + 1) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 s) :
    tP (fun x => stepRhoK a p pb hc (X x)) θ = (homModRho a p pb hc).comp (tP X θ) := by
  unfold tP
  rw [tDX_rhoK hr hh hc hθ, blockP_rhoK]

theorem tP'_rhoK (hc : pb ≤ p + 1) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 s) :
    tP' (fun x => stepRhoK a p pb hc (X x)) θ = (homModRho a p pb hc).comp (tP' X θ) := by
  unfold tP'
  rw [tDX_rhoK hr hh hc hθ, blockP'_rhoK]

theorem tQ_rhoK (hc : pb ≤ p + 1) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 s) :
    tQ (fun x => stepRhoK a p pb hc (X x)) θ = (homModRho a p pb hc).comp (tQ X θ) := by
  unfold tQ
  rw [tDX_rhoK hr hh hc hθ, blockQ_rhoK]

end taylor

/-- The reweighted pair satisfies the bound of `stepTaylorOf`. -/
theorem stepRhoK_bound {X : KamPhase → KamPhase} {ε : ℝ} (hc : pb ≤ p + 1) (hr : 0 < r)
    (hb : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε) :
    ∀ z ∈ kamDomain s r, kamNorm r (stepRhoK a p pb hc (X z)) ≤ ε :=
  fun z hz => (kamNorm_stepRhoK_le hc hr _).trans (hb z hz)

theorem stepRho_nn1 {p pb : ℝ} (hp : 0 ≤ p) (hpb : p ≤ pb) : 0 ≤ pb + p := by linarith

theorem stepRho_nn2 {p : ℝ} (hp : 0 ≤ p) : 0 ≤ (p + 1) + p := by linarith

section agree

variable {P : KamPhase → ℂ} {X : KamPhase → KamPhase}
  (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hc : pb ≤ p + 1) (hs : 0 < s) (hr : 0 < r)
  (hP : IsSmoothing (p := p) (pb := p + 1) ha (stepRho_nn2 hp) (kamDomain s r) P X)
  (hper : ∀ i, ∀ w ∈ kamDomain s r, P (w + stepTau i) = P w) {ε : ℝ}
  (hb : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε)

/-- **The Taylor element of the reweighted field**: `stepTaylorOf` for the pair
`(P, D_ρ ∘ X) ∈ 𝒮_{p₊}`. -/
def stepTaylorRho : HomTaylor_gen a p pb s :=
  stepTaylorOf ha hp hpb hs hr
    (IsSmoothing.rhoK (X := X) ha hc (stepRho_nn1 hp hpb) (stepRho_nn2 hp) hP) hper
    (stepRhoK_bound hc hr hb)

/-- The element for the `p+1` class. -/
def stepTaylorP1 : HomTaylor_gen a p (p + 1) s :=
  stepTaylorOf ha hp (homModPP1 p) hs hr hP hper hb

/-- **`T' = D_ρ T` on the strip.** -/
theorem stepFun_taylorRho {w : KamPhase} (hw : w.1 ∈ complexStrip 2 s) :
    waveStepFun ha (homPP hp hpb) (stepTaylorRho ha hp hpb hc hs hr hP hper hb) w =
      waveStepFun ha (homPP hp (homModPP1 p)) (stepTaylorP1 ha hp hs hr hP hper hb) w := by
  have hh := hP.holoX
  have e1 : (stepTaylorRho ha hp hpb hc hs hr hP hper hb).cp w.1 =
      homModRho a p pb hc ((stepTaylorP1 ha hp hs hr hP hper hb).cp w.1) :=
    tCp_rhoK hc w.1
  have e2 : (stepTaylorRho ha hp hpb hc hs hr hP hper hb).cm w.1 =
      homModRho a p pb hc ((stepTaylorP1 ha hp hs hr hP hper hb).cm w.1) :=
    tCm_rhoK hc w.1
  have e3 : (stepTaylorRho ha hp hpb hc hs hr hP hper hb).P w.1 =
      (homModRho a p pb hc).comp ((stepTaylorP1 ha hp hs hr hP hper hb).P w.1) :=
    tP_rhoK hr hh hc hw
  have e4 : (stepTaylorRho ha hp hpb hc hs hr hP hper hb).Q w.1 =
      (homModRho a p pb hc).comp ((stepTaylorP1 ha hp hs hr hP hper hb).Q w.1) :=
    tQ_rhoK hr hh hc hw
  have e5 : (stepTaylorRho ha hp hpb hc hs hr hP hper hb).P' w.1 =
      (homModRho a p pb hc).comp ((stepTaylorP1 ha hp hs hr hP hper hb).P' w.1) :=
    tP'_rhoK hr hh hc hw
  unfold waveStepFun
  rw [e1, e2, e3, e4, e5]
  simp only [ContinuousLinearMap.comp_apply, stepPr_rho ha hp hpb hc]
  rfl

theorem homNhat_taylorRho (y : Fin 2 → ℂ) (z zb : HomL2) :
    homNhat_gen (stepTaylorRho ha hp hpb hc hs hr hP hper hb) y z zb =
      homNhat_gen (stepTaylorP1 ha hp hs hr hP hper hb) y z zb := by
  have hh := hP.holoX
  rw [← homNhat_reweight hs hc (stepTaylorP1 ha hp hs hr hP hper hb)]
  have hQ : homCoeff (stepTaylorRho ha hp hpb hc hs hr hP hper hb).Q 0 =
      homCoeff (homReweight hc (stepTaylorP1 ha hp hs hr hP hper hb)).Q 0 :=
    homCoeff_congr_real (fun x => tQ_rhoK hr hh hc (realTheta_mem_strip hs x)) 0
  unfold homNhat_gen
  rw [hQ]
  rfl

theorem stepFun_nhat_taylorRho (w : KamPhase) :
    waveStepFun ha (homPP hp hpb)
      (homNhatTaylor_gen (stepTaylorRho ha hp hpb hc hs hr hP hper hb)) w =
      waveStepFun ha (homPP hp (homModPP1 p))
        (homNhatTaylor_gen (stepTaylorP1 ha hp hs hr hP hper hb)) w := by
  rw [stepFun_eq_homRval ha hp hpb, stepFun_eq_homRval ha hp (homModPP1 p),
    homNhatTaylor_val_gen, homNhatTaylor_val_gen, homNhat_taylorRho]

end agree

end KAM.Wave
