/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Basic
public import KAM.Kepler.Plane
public import KAM.Frozen.Planetary.Defs.KeplerMeanLongitude
public import KAM.Frozen.Planetary.Defs.LongitudeJacobian
public import KAM.Frozen.Planetary.Defs.SecularEccVector
public import KAM.Frozen.Planetary.Defs.OrbitalUnit

/-!
# The real regular Kepler equation

`Φ(F, v) = F - v₀ sin F + v₁ cos F`, its Jacobian, the unique real solution `keplerLong` of
`Φ(F, v) = λ` for `ℓ v < 1`, its real analyticity (analytic implicit function theorem), derivatives,
and the eccentric anomaly `eccAnom ℓ e = keplerLong ℓ (e, 0)` (`bpP:p7:regular-kepler` (a), (c);
`bpI:p7:kepler-eq` (c), real part).
-/

@[expose] public noncomputable section

open Set Metric Real
open scoped ContDiff Topology

namespace KAM.Kepler

open KAM KAM.Planetary

section Equation

/-- `Φ(F, v) = F - v₀ sin F + v₁ cos F`: the frozen `keplerMeanLongitude` for
`v = secularEccVector`. -/
def keplerPhi (v : Fin 2 → ℝ) (F : ℝ) : ℝ := F - v 0 * Real.sin F + v 1 * Real.cos F

/-- `J(F, v) = ∂_F Φ = 1 - v·(cos F, sin F)`: the frozen `longitudeJacobian`. -/
def keplerJac (v : Fin 2 → ℝ) (F : ℝ) : ℝ := 1 - planeDot v (orbitalUnit F)

theorem keplerMeanLongitude_eq (w : Phase (2 + 2)) (i : Fin 2) (F : ℝ) :
    keplerMeanLongitude w i F = keplerPhi (secularEccVector w i) F := rfl

private theorem planeDot_eq (v w : Fin 2 → ℝ) : planeDot v w = v 0 * w 0 + v 1 * w 1 := by
  simp [planeDot, Fin.sum_univ_two]

private theorem planeSq_eq (v : Fin 2 → ℝ) : planeSq v = v 0 ^ 2 + v 1 ^ 2 := by
  simp [planeSq, Fin.sum_univ_two]

private theorem planeLength_mk (a b : ℝ) : planeLength ![a, b] = √(a ^ 2 + b ^ 2) := by
  simp [planeLength, planeSq_eq]

private theorem planeLength_orbitalUnit (F : ℝ) : planeLength (orbitalUnit F) = 1 := by
  simp [orbitalUnit, planeLength_mk, Real.cos_sq_add_sin_sq]

theorem longitudeJacobian_eq (w : Phase (2 + 2)) (i : Fin 2) (F : ℝ) :
    longitudeJacobian w i F = keplerJac (secularEccVector w i) F := rfl

theorem keplerJac_eq (v : Fin 2 → ℝ) (F : ℝ) :
    keplerJac v F = 1 - v 0 * Real.cos F - v 1 * Real.sin F := by
  simp [keplerJac, planeDot_eq, orbitalUnit]; ring

theorem hasDerivAt_keplerPhi (v : Fin 2 → ℝ) (F : ℝ) :
    HasDerivAt (keplerPhi v) (keplerJac v F) F := by
  have h := (((hasDerivAt_id F).sub ((Real.hasDerivAt_sin F).const_mul (v 0))).add
    ((Real.hasDerivAt_cos F).const_mul (v 1)))
  rw [keplerJac_eq]
  unfold keplerPhi
  refine HasDerivAt.congr_deriv h ?_
  ring

theorem keplerPhi_shift (v : Fin 2 → ℝ) (F : ℝ) :
    keplerPhi v (F + 2 * π) = keplerPhi v F + 2 * π := by
  simp [keplerPhi]; ring

theorem keplerPhi_zero (F : ℝ) : keplerPhi 0 F = F := by simp [keplerPhi]

theorem keplerJac_ge {v : Fin 2 → ℝ} (F : ℝ) : 1 - planeLength v ≤ keplerJac v F := by
  have h := (abs_le.mp ((abs_planeDot_le v (orbitalUnit F)).trans_eq
    (by rw [planeLength_orbitalUnit, mul_one]))).2
  unfold keplerJac; linarith

theorem keplerJac_pos {v : Fin 2 → ℝ} (hv : planeLength v < 1) (F : ℝ) : 0 < keplerJac v F := by
  linarith [keplerJac_ge (v := v) F]

private theorem abs_keplerPhi_sub_le (v : Fin 2 → ℝ) (F : ℝ) :
    |keplerPhi v F - F| ≤ planeLength v := by
  have h := abs_planeDot_le v ![-Real.sin F, Real.cos F]
  rw [planeLength_mk, planeDot_eq] at h
  have e : (-Real.sin F) ^ 2 + Real.cos F ^ 2 = 1 := by nlinarith [Real.sin_sq_add_cos_sq F]
  rw [e, Real.sqrt_one, mul_one] at h
  have e2 : keplerPhi v F - F = v 1 * Real.cos F + -(v 0 * Real.sin F) := by unfold keplerPhi; ring
  rw [e2]
  simpa [add_comm, mul_comm] using h

theorem keplerPhi_strictMono {v : Fin 2 → ℝ} (hv : planeLength v < 1) : StrictMono (keplerPhi v) :=
  strictMono_of_deriv_pos fun F => by
    rw [(hasDerivAt_keplerPhi v F).deriv]; exact keplerJac_pos hv F

theorem keplerPhi_bijective {v : Fin 2 → ℝ} (hv : planeLength v < 1) :
    Function.Bijective (keplerPhi v) := by
  refine ⟨(keplerPhi_strictMono hv).injective, fun lam => ?_⟩
  have hc : Continuous (keplerPhi v) := by
    unfold keplerPhi; fun_prop
  have h1 := abs_keplerPhi_sub_le v (lam - 1)
  have h2 := abs_keplerPhi_sub_le v (lam + 1)
  rw [abs_le] at h1 h2
  have := intermediate_value_Icc (show lam - 1 ≤ lam + 1 by linarith) hc.continuousOn
  obtain ⟨F, -, hF⟩ := this (show lam ∈ Icc (keplerPhi v (lam - 1)) (keplerPhi v (lam + 1)) from
    ⟨by linarith, by linarith⟩)
  exact ⟨F, hF⟩

open scoped Classical in
/-- The unique real solution `F(λ, v)` of `Φ(F, v) = λ` (junk `0` when `ℓ v ≥ 1`). -/
def keplerLong (lam : ℝ) (v : Fin 2 → ℝ) : ℝ :=
  if h : planeLength v < 1 then (keplerPhi_bijective h).surjective lam |>.choose else 0

/-- `bpP:p7:regular-kepler` (a), the real part. All statements are for `ℓ v < 1`. -/
theorem keplerPhi_keplerLong {v : Fin 2 → ℝ} (hv : planeLength v < 1) (lam : ℝ) :
    keplerPhi v (keplerLong lam v) = lam := by
  simp only [keplerLong, hv, ↓reduceDIte]
  exact ((keplerPhi_bijective hv).surjective lam).choose_spec

theorem keplerLong_unique {v : Fin 2 → ℝ} (hv : planeLength v < 1) {lam F : ℝ}
    (h : keplerPhi v F = lam) : keplerLong lam v = F :=
  (keplerPhi_strictMono hv).injective ((keplerPhi_keplerLong hv lam).trans h.symm)

theorem keplerLong_shift {v : Fin 2 → ℝ} (hv : planeLength v < 1) (lam : ℝ) :
    keplerLong (lam + 2 * π) v = keplerLong lam v + 2 * π :=
  keplerLong_unique hv (by rw [keplerPhi_shift, keplerPhi_keplerLong hv])

theorem keplerLong_zero_vec (lam : ℝ) : keplerLong lam 0 = lam :=
  keplerLong_unique (by simp [planeLength, planeSq_eq]) (by rw [keplerPhi_zero])

private theorem continuous_planeLength : Continuous planeLength := by
  have : planeLength = fun v : Fin 2 → ℝ => √(v 0 ^ 2 + v 1 ^ 2) := by
    funext v; simp [planeLength, planeSq_eq]
  rw [this]; fun_prop

theorem isOpen_planeLength_lt_one : IsOpen {v : Fin 2 → ℝ | planeLength v < 1} :=
  isOpen_lt continuous_planeLength continuous_const

/-- The implicit equation `Φ(F, v) - λ = 0` in the variables `((λ, v), F)`. -/
private def keplerEq (x : (ℝ × (Fin 2 → ℝ)) × ℝ) : ℝ := keplerPhi x.1.2 x.2 - x.1.1

private theorem contDiff_keplerEq : ContDiff ℝ ω keplerEq := by
  unfold keplerEq keplerPhi; fun_prop

private theorem analyticAt_keplerLong_aux {lam : ℝ} {v : Fin 2 → ℝ} (hv : planeLength v < 1) :
    AnalyticAt ℝ (fun x : ℝ × (Fin 2 → ℝ) => keplerLong x.1 x.2) (lam, v) := by
  set F0 := keplerLong lam v with hF0
  set u : (ℝ × (Fin 2 → ℝ)) × ℝ := ((lam, v), F0) with hu
  have hcd : ContDiffAt ℝ ω keplerEq u := contDiff_keplerEq.contDiffAt
  have hpn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  have hderiv : HasFDerivAt keplerEq (fderiv ℝ keplerEq u) u :=
    (contDiff_keplerEq.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hg : HasDerivAt (fun t : ℝ => ((lam, v), t)) ((0 : ℝ × (Fin 2 → ℝ)), (1 : ℝ)) F0 :=
    (hasDerivAt_const F0 (lam, v)).prodMk (hasDerivAt_id F0)
  have h1 := hderiv.comp_hasDerivAt F0 hg
  have h2 : HasDerivAt (fun t => keplerEq ((lam, v), t)) (keplerJac v F0) F0 :=
    (hasDerivAt_keplerPhi v F0).sub_const lam
  have h3 := h1.unique h2
  have hL : (fderiv ℝ keplerEq u ∘L .inr ℝ (ℝ × (Fin 2 → ℝ)) ℝ) =
      keplerJac v F0 • (1 : ℝ →L[ℝ] ℝ) := by
    ext
    simpa using h3
  have hinv : (fderiv ℝ keplerEq u ∘L .inr ℝ (ℝ × (Fin 2 → ℝ)) ℝ).IsInvertible := by
    have hJ := (keplerJac_pos hv F0).ne'
    rw [hL]
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := (keplerJac v F0)⁻¹ • (1 : ℝ →L[ℝ] ℝ)) ?_ ?_
    · ext; simp [hJ]
    · ext; simp [hJ]
  have hψ : AnalyticAt ℝ (hcd.implicitFunction hpn hinv) (lam, v) :=
    (hcd.contDiffAt_implicitFunction hpn hinv).analyticAt
  refine hψ.congr ?_
  have hopen : ∀ᶠ x in 𝓝 (lam, v), planeLength x.2 < 1 :=
    (isOpen_planeLength_lt_one.preimage continuous_snd).mem_nhds hv
  filter_upwards [hcd.eventually_apply_implicitFunction hpn hinv, hopen] with x hx hxo
  have hu0 : keplerEq u = 0 := by simp [keplerEq, hu, hF0, keplerPhi_keplerLong hv]
  rw [hu0] at hx
  symm
  exact keplerLong_unique hxo (by simpa [keplerEq, sub_eq_zero] using hx)

/-- Real analyticity on `ℝ × {ℓ v < 1}`: by Mathlib's implicit function theorem at `C^ω`
(`ContDiffAt.implicitFunction`), glued by uniqueness. -/
theorem analyticOnNhd_keplerLong :
    AnalyticOnNhd ℝ (fun x : ℝ × (Fin 2 → ℝ) => keplerLong x.1 x.2) {x | planeLength x.2 < 1} :=
  fun x hx => by
    obtain ⟨lam, v⟩ := x
    exact analyticAt_keplerLong_aux hx

private theorem differentiableAt_keplerLong_lam {v : Fin 2 → ℝ} (hv : planeLength v < 1) (lam : ℝ) :
    DifferentiableAt ℝ (fun t => keplerLong t v) lam := by
  have h1 : DifferentiableAt ℝ (fun x : ℝ × (Fin 2 → ℝ) => keplerLong x.1 x.2) (lam, v) :=
    (analyticOnNhd_keplerLong (lam, v) hv).differentiableAt
  have h2 : DifferentiableAt ℝ (fun t : ℝ => (t, v)) lam :=
    differentiableAt_id.prodMk (differentiableAt_const v)
  exact h1.comp lam h2

private theorem differentiableAt_keplerLong_vec {v : Fin 2 → ℝ} (hv : planeLength v < 1) (lam : ℝ) :
    DifferentiableAt ℝ (fun u => keplerLong lam u) v := by
  have h1 : DifferentiableAt ℝ (fun x : ℝ × (Fin 2 → ℝ) => keplerLong x.1 x.2) (lam, v) :=
    (analyticOnNhd_keplerLong (lam, v) hv).differentiableAt
  have h2 : DifferentiableAt ℝ (fun u : Fin 2 → ℝ => (lam, u)) v :=
    (differentiableAt_const lam).prodMk differentiableAt_id
  exact h1.comp v h2

theorem hasDerivAt_keplerLong_lambda {v : Fin 2 → ℝ} (hv : planeLength v < 1) (lam : ℝ) :
    HasDerivAt (fun t => keplerLong t v) (1 / keplerJac v (keplerLong lam v)) lam := by
  have hd := (differentiableAt_keplerLong_lam hv lam).hasDerivAt
  have h1 := (hasDerivAt_keplerPhi v (keplerLong lam v)).comp lam hd
  have h2 : HasDerivAt (fun t => keplerPhi v (keplerLong t v)) 1 lam := by
    have : (fun t => keplerPhi v (keplerLong t v)) = id := funext (keplerPhi_keplerLong hv)
    rw [this]; exact hasDerivAt_id lam
  have h3 := h1.unique h2
  have hJ := (keplerJac_pos hv (keplerLong lam v)).ne'
  refine hd.congr_deriv ?_
  field_simp
  linarith [h3]

private theorem fderiv_keplerLong_vec_apply {v : Fin 2 → ℝ} (hv : planeLength v < 1) (lam : ℝ)
    (d : Fin 2 → ℝ) :
    fderiv ℝ (fun u => keplerLong lam u) v d * keplerJac v (keplerLong lam v) =
      Real.sin (keplerLong lam v) * d 0 - Real.cos (keplerLong lam v) * d 1 := by
  set G := keplerLong lam v with hG
  have hD := (differentiableAt_keplerLong_vec hv lam).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => v + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add v
  have hD' : HasFDerivAt (fun u => keplerLong lam u) (fderiv ℝ (fun u => keplerLong lam u) v)
      (v + (0 : ℝ) • d) := by simpa using hD
  have hφ := hD'.comp_hasDerivAt (0 : ℝ) hline
  set g := fderiv ℝ (fun u => keplerLong lam u) v d with hg
  set φ : ℝ → ℝ := fun t => keplerLong lam (v + t • d) with hφdef
  have hφ0 : ((fun u => keplerLong lam u) ∘ fun t : ℝ => v + t • d) 0 = G := by simp [hG]
  have hopen : ∀ᶠ t in 𝓝 (0 : ℝ), planeLength (v + t • d) < 1 := by
    have hc : Continuous (fun t : ℝ => v + t • d) := by fun_prop
    exact (isOpen_planeLength_lt_one.preimage hc).mem_nhds (by simpa using hv)
  have hconst : HasDerivAt (fun t : ℝ => φ t - (v 0 + t * d 0) * Real.sin (φ t)
      + (v 1 + t * d 1) * Real.cos (φ t)) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) lam).congr_of_eventuallyEq ?_
    filter_upwards [hopen] with t ht
    have := keplerPhi_keplerLong ht lam
    simpa [keplerPhi, hφdef] using this
  have ha : HasDerivAt (fun t : ℝ => v 0 + t * d 0) (d 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d 0)).const_add (v 0)
  have hb : HasDerivAt (fun t : ℝ => v 1 + t * d 1) (d 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d 1)).const_add (v 1)
  have hall := (hφ.sub (ha.mul hφ.sin)).add (hb.mul hφ.cos)
  have heq := hall.unique hconst
  rw [hφ0] at heq
  simp only [keplerJac_eq]
  simp at heq
  linear_combination heq

/-- `∂_{v₀} F = sin F / J`, `∂_{v₁} F = -cos F / J`. -/
theorem fderiv_keplerLong_vec {v : Fin 2 → ℝ} (hv : planeLength v < 1) (lam : ℝ) :
    fderiv ℝ (fun u => keplerLong lam u) v (Pi.single 0 1) =
        Real.sin (keplerLong lam v) / keplerJac v (keplerLong lam v) ∧
      fderiv ℝ (fun u => keplerLong lam u) v (Pi.single 1 1) =
        -Real.cos (keplerLong lam v) / keplerJac v (keplerLong lam v) := by
  have hJ := (keplerJac_pos hv (keplerLong lam v)).ne'
  have h0 := fderiv_keplerLong_vec_apply hv lam (Pi.single 0 1)
  have h1 := fderiv_keplerLong_vec_apply hv lam (Pi.single 1 1)
  constructor
  · rw [eq_div_iff hJ, h0]; simp
  · rw [eq_div_iff hJ, h1]; simp

/-- The eccentric anomaly `u_ℝ(ℓ, e)`: Kepler's equation `u - e sin u = ℓ`, the case
`v = (e, 0)`. -/
def eccAnom (ℓ e : ℝ) : ℝ := keplerLong ℓ ![e, 0]

theorem planeLength_eccVec {e : ℝ} (he : |e| < 1) : planeLength (![e, 0] : Fin 2 → ℝ) < 1 := by
  rw [planeLength_mk]
  simpa [Real.sqrt_sq_eq_abs] using he

private theorem keplerPhi_eccVec (e F : ℝ) : keplerPhi ![e, 0] F = F - e * Real.sin F := by
  simp [keplerPhi]

/-- `bpI:p7:kepler-eq` (c), real part. -/
theorem eccAnom_eq (ℓ : ℝ) {e : ℝ} (he : |e| < 1) :
    eccAnom ℓ e - e * Real.sin (eccAnom ℓ e) = ℓ := by
  have := keplerPhi_keplerLong (planeLength_eccVec he) ℓ
  rwa [keplerPhi_eccVec] at this

theorem analyticOnNhd_eccAnom :
    AnalyticOnNhd ℝ (fun x : ℝ × ℝ => eccAnom x.1 x.2) {x | |x.2| < 1} := by
  have hf : AnalyticOnNhd ℝ (fun x : ℝ × ℝ => (x.1, (![x.2, 0] : Fin 2 → ℝ))) Set.univ := by
    intro x _
    have : (fun x : ℝ × ℝ => (x.1, (![x.2, 0] : Fin 2 → ℝ))) =
        fun x => (x.1, x.2 • (Pi.single 0 1 : Fin 2 → ℝ)) := by
      funext x; refine Prod.ext rfl (funext fun i => ?_); fin_cases i <;> simp
    rw [this]
    exact AnalyticAt.prod (analyticAt_fst (𝕜 := ℝ))
      (AnalyticAt.smul (analyticAt_snd (𝕜 := ℝ)) analyticAt_const)
  exact analyticOnNhd_keplerLong.comp (hf.mono (subset_univ _)) fun x hx => planeLength_eccVec hx

theorem eccAnom_zero_left {e : ℝ} (he : |e| < 1) : eccAnom 0 e = 0 :=
  keplerLong_unique (planeLength_eccVec he) (by simp [keplerPhi_eccVec])

theorem eccAnom_two_pi {e : ℝ} (he : |e| < 1) : eccAnom (2 * π) e = 2 * π :=
  keplerLong_unique (planeLength_eccVec he) (by simp [keplerPhi_eccVec])

theorem eccAnom_zero_ecc (ℓ : ℝ) : eccAnom ℓ 0 = ℓ :=
  keplerLong_unique (by simp [planeLength_mk]) (by simp [keplerPhi_eccVec])

theorem hasDerivAt_eccAnom {e : ℝ} (he : |e| < 1) (ℓ : ℝ) :
    HasDerivAt (fun t => eccAnom t e) (1 / (1 - e * Real.cos (eccAnom ℓ e))) ℓ := by
  have := hasDerivAt_keplerLong_lambda (planeLength_eccVec he) ℓ
  simpa [eccAnom, keplerJac_eq] using this

theorem strictMono_eccAnom {e : ℝ} (he : |e| < 1) : StrictMono (fun ℓ => eccAnom ℓ e) := by
  intro a b hab
  have h := keplerPhi_strictMono (planeLength_eccVec he)
  refine h.lt_iff_lt.mp ?_
  simp only [eccAnom, keplerPhi_keplerLong (planeLength_eccVec he)]
  exact hab

private theorem planeLength_ex (g : ℝ) : planeLength (ex g) = 1 := by
  simp [ex, planeLength_mk, Real.cos_sq_add_sin_sq]

/-- The eccentric longitude is `g + u` (`bpP:p7:regular-kepler` (c)). -/
theorem keplerLong_eq_add_eccAnom {e g : ℝ} (he0 : 0 < e) (he1 : e < 1) (lam : ℝ) :
    keplerLong lam (e • ex g) = g + eccAnom (lam - g) e := by
  have hl : planeLength (e • ex g) < 1 := by
    rw [planeLength_smul, planeLength_ex, mul_one, abs_of_pos he0]; exact he1
  have he : |e| < 1 := by rwa [abs_of_pos he0]
  refine keplerLong_unique hl ?_
  have h := eccAnom_eq (lam - g) he
  set u := eccAnom (lam - g) e
  have hs : Real.sin (g + u) = Real.sin g * Real.cos u + Real.cos g * Real.sin u := Real.sin_add g u
  have hc : Real.cos (g + u) = Real.cos g * Real.cos u - Real.sin g * Real.sin u := Real.cos_add g u
  simp only [keplerPhi, Pi.smul_apply, ex, smul_eq_mul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hs, hc]
  have : Real.sin g ^ 2 + Real.cos g ^ 2 = 1 := Real.sin_sq_add_cos_sq g
  linear_combination h - e * Real.sin u * this

end Equation

end KAM.Kepler

end
