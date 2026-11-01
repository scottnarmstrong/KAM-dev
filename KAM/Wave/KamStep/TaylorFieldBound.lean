/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.TaylorValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Taylor element satisfies W4's field bound (blueprint-W `bpW:w5:taylor` (iii))

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`stepTaylor_fieldBound`: `|X_R|_r ≤ 3ε` on `D(s,r)` in the form `HomFieldBound_gen` required by
W4's Lemma 1, for `R = stepTaylorOf …`, via `taylorXR_bound` and `stepField_taylorOf_eq`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s r : ℝ} {P : KamPhase → ℂ} {X : KamPhase → KamPhase}

theorem stepZ_of_hom (θ y : Fin 2 → ℂ) (z zb : HomL2) :
    stepZ (θ, y, homU z zb, homV z zb) = z := by
  rw [stepZ_apply]
  unfold homU homV
  have h2 := homSqrt2_inv_sq
  ext j
  simp only [lp.coeFn_smul, lp.coeFn_add, lp.coeFn_sub, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
    smul_eq_mul]
  linear_combination (2 * (z j : ℂ)) * h2 +
    (-(homSqrt2⁻¹ * homSqrt2⁻¹ * ((z j : ℂ) - (zb j : ℂ)))) * Complex.I_sq

theorem stepZb_of_hom (θ y : Fin 2 → ℂ) (z zb : HomL2) :
    stepZb (θ, y, homU z zb, homV z zb) = zb := by
  rw [stepZb_apply]
  unfold homU homV
  have h2 := homSqrt2_inv_sq
  ext j
  simp only [lp.coeFn_smul, lp.coeFn_add, lp.coeFn_sub, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
    smul_eq_mul]
  linear_combination (2 * (zb j : ℂ)) * h2 +
    ((homSqrt2⁻¹ * homSqrt2⁻¹ * ((z j : ℂ) - (zb j : ℂ)))) * Complex.I_sq

theorem kamDomain_of_hom {θ y : Fin 2 → ℂ} {z zb : HomL2} (h : HomDomain s r θ y z zb) :
    (θ, y, homU z zb, homV z zb) ∈ kamDomain s r :=
  ⟨fun i => h.1 i, h.2.1, h.2.2⟩

/-- **`|X_R|_r ≤ 3ε` in W4's form** (`bpW:w5:taylor` (iii)). -/
theorem stepTaylor_fieldBound (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hs : 0 < s) (hr : 0 < r)
    (hP : IsSmoothing (p := p) ha (by linarith : 0 ≤ pb + p) (kamDomain s r) P X)
    (hper : ∀ i, ∀ w ∈ kamDomain s r, P (w + stepTau i) = P w) {ε : ℝ}
    (hb : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε) :
    HomFieldBound_gen ha hp hpb r (3 * ε) (stepTaylorOf ha hp hpb hs hr hP hper hb) := by
  intro θ y z zb hdom
  have hw := kamDomain_of_hom hdom
  have hbd := taylorXR_bound hP.holoX hb hr hw
  have := stepField_taylorOf_eq ha hp hpb hs hr hP hper hb hw
  have e := kamNorm_stepField ha hp hpb (stepTaylorOf ha hp hpb hs hr hP hper hb) hr
    (θ, y, homU z zb, homV z zb)
  simp only [stepZ_of_hom, stepZb_of_hom] at e
  change kamNorm r (stepField ha hp hpb (stepTaylorOf ha hp hpb hs hr hP hper hb)
    (θ, y, homU z zb, homV z zb)) = homXnorm_gen ha hp hpb r _ θ y z zb at e
  rw [← e, this]
  exact hbd

end KAM.Wave
