/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Basic
public import KAM.Kepler.Plane
public import KAM.Kepler.Energy
public import KAM.Kepler.Equation
public import KAM.Kepler.Orbit

/-!
# Jacobian of the Delaunay map: explicit columns

The explicit Jacobian columns `orbitMapColumn` of the orbit map `(ℓ, g, L, e) ↦ orbitMapR ℓ g L e`
(`fderiv_orbitMapR_basis`) and of the Delaunay map (`fderiv_delaunay_basis`, the chain rule through
`e = eccOf L G`), obtained from a single curve lemma `hasDerivAt_orbitMapR_curve`
(`bpI:p7:symplectic`, first half). The curve lemma computes the derivative of the frame
entries by `HasDerivAt` algebra and implicit differentiation of Kepler's equation
(`hasDerivAt_eccAnom_curve`); `fderiv` on a basis vector is the derivative along the coordinate line
(`fderiv_apply_eq_of_hasDerivAt_line`).
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology
open scoped ContDiff

namespace KAM.Kepler

open KAM KAM.Planetary

private theorem hasDerivAt_mk2 {a b : ℝ → ℝ} {a' b' t : ℝ} (ha : HasDerivAt a a' t)
    (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => (![a s, b s] : Fin 2 → ℝ)) ![a', b'] t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa using ha
  · simpa using hb

/-- Derivative of the rotation of a curve. -/
private theorem hasDerivAt_rot_curve {g a b : ℝ → ℝ} {g' a' b' t : ℝ} (hg : HasDerivAt g g' t)
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => rot (g s) ![a s, b s])
      (g' • quarterTurn (rot (g t) ![a t, b t]) + rot (g t) ![a', b']) t := by
  have h0 : HasDerivAt (fun s => Real.cos (g s) * a s - Real.sin (g s) * b s)
      (-Real.sin (g t) * g' * a t + Real.cos (g t) * a' - (Real.cos (g t) * g' * b t + Real.sin (g
          t) * b')) t :=
    ((hg.cos.mul ha).sub (hg.sin.mul hb))
  have h1 : HasDerivAt (fun s => Real.sin (g s) * a s + Real.cos (g s) * b s)
      (Real.cos (g t) * g' * a t + Real.sin (g t) * a' + (-Real.sin (g t) * g' * b t + Real.cos (g
          t) * b')) t :=
    ((hg.sin.mul ha).add (hg.cos.mul hb))
  have := hasDerivAt_mk2 h0 h1
  refine this.congr_deriv ?_
  ext i; fin_cases i <;> simp [rot, quarterTurn] <;> ring

section Frame
variable {L e u : ℝ → ℝ} {L' e' u' t : ℝ}

private theorem one_sub_sq_pos {x : ℝ} (h : |x| < 1) : 0 < 1 - x ^ 2 := by
  have : x ^ 2 < 1 := by simpa using (sq_lt_one_iff_abs_lt_one x).2 h
  linarith

private theorem hasDerivAt_sqrtOneSub (he : HasDerivAt e e' t) (h : |e t| < 1) :
    HasDerivAt (fun s => √(1 - e s ^ 2)) (-(e t * e') / √(1 - e t ^ 2)) t := by
  have hpos : (1 - e t ^ 2) ≠ 0 := (one_sub_sq_pos h).ne'
  have hin : HasDerivAt (fun s => 1 - e s ^ 2) (-(2 * e t * e')) t := by
    have := (hasDerivAt_const t (1 : ℝ)).sub (he.pow 2)
    refine this.congr_deriv ?_
    simp
  refine (hin.sqrt hpos).congr_deriv ?_
  have : √(1 - e t ^ 2) ≠ 0 := Real.sqrt_ne_zero'.2 (one_sub_sq_pos h)
  field_simp

private theorem hasDerivAt_frameX (hL : HasDerivAt L L' t) (he : HasDerivAt e e' t)
    (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => L s ^ 2 * (Real.cos (u s) - e s))
      (L' * (2 * L t * (Real.cos (u t) - e t)) + e' * (-L t ^ 2)
        + u' * (-L t ^ 2 * Real.sin (u t))) t := by
  refine ((hL.pow 2).mul (hu.cos.sub he)).congr_deriv ?_
  simp; ring

private theorem hasDerivAt_frameY (hL : HasDerivAt L L' t) (he : HasDerivAt e e' t)
    (hu : HasDerivAt u u' t) (h : |e t| < 1) :
    HasDerivAt (fun s => L s ^ 2 * √(1 - e s ^ 2) * Real.sin (u s))
      (L' * (2 * L t * √(1 - e t ^ 2) * Real.sin (u t))
        + e' * (-L t ^ 2 * e t * Real.sin (u t) / √(1 - e t ^ 2))
        + u' * (L t ^ 2 * √(1 - e t ^ 2) * Real.cos (u t))) t := by
  refine (((hL.pow 2).mul (hasDerivAt_sqrtOneSub he h)).mul hu.sin).congr_deriv ?_
  simp; ring


private theorem one_sub_mul_cos_pos' {e c : ℝ} (he0 : 0 ≤ e) (he1 : e < 1) (hc : c ≤ 1) :
    0 < 1 - e * c := by nlinarith

private theorem hasDerivAt_frameDen (hL : HasDerivAt L L' t) (he : HasDerivAt e e' t)
    (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => L s * (1 - e s * Real.cos (u s)))
      (L' * (1 - e t * Real.cos (u t)) + L t * (-(e' * Real.cos (u t) + e t * (-Real.sin (u t) *
          u')))) t := by
  refine (hL.mul ((hasDerivAt_const t (1:ℝ)).sub (he.mul hu.cos))).congr_deriv ?_
  simp

private theorem hasDerivAt_framePX (hL : HasDerivAt L L' t) (he : HasDerivAt e e' t)
    (hu : HasDerivAt u u' t) (hL0 : 0 < L t) (he0 : 0 ≤ e t) (he1 : e t < 1) :
    HasDerivAt (fun s => -Real.sin (u s) / (L s * (1 - e s * Real.cos (u s))))
      (L' * (Real.sin (u t) / (L t ^ 2 * (1 - e t * Real.cos (u t))))
        + e' * (-Real.sin (u t) * Real.cos (u t) / (L t * (1 - e t * Real.cos (u t)) ^ 2))
        + u' * (-(Real.cos (u t) - e t) / (L t * (1 - e t * Real.cos (u t)) ^ 2))) t := by
  have hD := one_sub_mul_cos_pos' he0 he1 (Real.cos_le_one (u t))
  have hs := Real.sin_sq_add_cos_sq (u t)
  have hn : HasDerivAt (fun s => -Real.sin (u s)) (-(Real.cos (u t) * u')) t := hu.sin.neg
  have hDne : 1 - e t * Real.cos (u t) ≠ 0 := hD.ne'
  have hDne' : 1 - Real.cos (u t) * e t ≠ 0 := by rw [mul_comm]; exact hDne
  have hLne : L t ≠ 0 := hL0.ne'
  refine (hn.div (hasDerivAt_frameDen hL he hu) (by positivity)).congr_deriv ?_
  field_simp
  linear_combination (u' * L t * e t) * hs


private theorem hasDerivAt_framePY (hL : HasDerivAt L L' t) (he : HasDerivAt e e' t)
    (hu : HasDerivAt u u' t) (hL0 : 0 < L t) (he0 : 0 ≤ e t) (he1 : e t < 1) :
    HasDerivAt (fun s => √(1 - e s ^ 2) * Real.cos (u s) / (L s * (1 - e s * Real.cos (u s))))
      (L' * (-√(1 - e t ^ 2) * Real.cos (u t) / (L t ^ 2 * (1 - e t * Real.cos (u t))))
        + e' * (Real.cos (u t) * (Real.cos (u t) - e t)
          / (L t * (1 - e t * Real.cos (u t)) ^ 2 * √(1 - e t ^ 2)))
        + u' * (-√(1 - e t ^ 2) * Real.sin (u t) / (L t * (1 - e t * Real.cos (u t)) ^ 2))) t := by
  have hD := one_sub_mul_cos_pos' he0 he1 (Real.cos_le_one (u t))
  have habs : |e t| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hk := Real.sq_sqrt (one_sub_sq_pos habs).le
  have hk0 : √(1 - e t ^ 2) ≠ 0 := Real.sqrt_ne_zero'.2 (one_sub_sq_pos habs)
  have hDne : 1 - e t * Real.cos (u t) ≠ 0 := hD.ne'
  have hDne' : 1 - Real.cos (u t) * e t ≠ 0 := by rw [mul_comm]; exact hDne
  have hLne : L t ≠ 0 := hL0.ne'
  refine (((hasDerivAt_sqrtOneSub he habs).mul hu.cos).div (hasDerivAt_frameDen hL he hu)
    (by positivity)).congr_deriv ?_
  simp only [Pi.mul_apply]
  field_simp
  rw [hk]
  ring

end Frame

/-- Chain rule for `eccAnom` along a curve. -/
theorem hasDerivAt_eccAnom_curve {ℓ e : ℝ → ℝ} {ℓ' e' t : ℝ} (hℓ : HasDerivAt ℓ ℓ' t)
    (he : HasDerivAt e e' t) (h : |e t| < 1) :
    HasDerivAt (fun s => eccAnom (ℓ s) (e s))
      ((ℓ' + Real.sin (eccAnom (ℓ t) (e t)) * e') / (1 - e t * Real.cos (eccAnom (ℓ t) (e t)))) t
          := by
  have hdiff : DifferentiableAt ℝ (fun x : ℝ × ℝ => eccAnom x.1 x.2) (ℓ t, e t) :=
    (analyticOnNhd_eccAnom (ℓ t, e t) h).differentiableAt
  have hcurve : DifferentiableAt ℝ (fun s => ((ℓ s, e s) : ℝ × ℝ)) t :=
    hℓ.differentiableAt.prodMk he.differentiableAt
  have hu : DifferentiableAt ℝ (fun s => eccAnom (ℓ s) (e s)) t :=
    (hdiff.comp t hcurve : DifferentiableAt ℝ ((fun x : ℝ × ℝ => eccAnom x.1 x.2) ∘ fun s => (ℓ s,
        e s)) t)
  have hu' := hu.hasDerivAt
  set u' := deriv (fun s => eccAnom (ℓ s) (e s)) t with hu'def
  have hev : ∀ᶠ s in 𝓝 t, |e s| < 1 :=
    (continuous_abs.continuousAt.comp he.continuousAt).eventually (Iio_mem_nhds h)
  have hconst : HasDerivAt (fun s => eccAnom (ℓ s) (e s) - e s * Real.sin (eccAnom (ℓ s) (e s))) ℓ'
      t := by
    refine hℓ.congr_of_eventuallyEq ?_
    filter_upwards [hev] with s hs
    exact eccAnom_eq (ℓ s) hs
  have hall := hu'.sub (he.mul hu'.sin)
  have heq := hall.unique hconst
  have hD : 0 < 1 - e t * Real.cos (eccAnom (ℓ t) (e t)) := by
    have h1 := mul_nonneg (abs_nonneg (e t)) (sub_nonneg.2 (abs_cos_le_one (eccAnom (ℓ t) (e t))))
    have h2 := abs_mul (e t) (Real.cos (eccAnom (ℓ t) (e t)))
    have h3 := le_abs_self (e t * Real.cos (eccAnom (ℓ t) (e t)))
    nlinarith
  refine hu'.congr_deriv ?_
  field_simp
  linear_combination heq

/-- Explicit Jacobian columns.
Frame derivatives, with `u = eccAnom ℓ e`, `c = cos u`, `s = sin u`, `k = √(1-e²)`, `D = 1 - e c`:
`∂_u (X, Y, P_X, P_Y) = (-L² s, L² k c, -(c-e)/(L D²), -k s/(L D²))`,
`∂_e (at fixed u) = (-L², -L² e s/k, -s c/(L D²), c (c-e)/(L D² k))`,
`∂_L = (2 L (c-e), 2 L k s, s/(L² D), -k c/(L² D))`, and `∂_ℓ u = 1/D`, `∂_e u = s/D`. -/
def orbitMapColumn (ℓ g L e : ℝ) : Fin 4 → Phase 2 :=
  let u := eccAnom ℓ e
  let c := Real.cos u
  let s := Real.sin u
  let k := √(1 - e ^ 2)
  let D := 1 - e * c
  let fu : Phase 2 := (![-L ^ 2 * s, L ^ 2 * k * c], ![-(c - e) / (L * D ^ 2), -k * s / (L * D ^
      2)])
  let fe : Phase 2 := (![-L ^ 2, -L ^ 2 * e * s / k], ![-s * c / (L * D ^ 2), c * (c - e) / (L * D
      ^ 2 * k)])
  let fL : Phase 2 := (![2 * L * (c - e), 2 * L * k * s], ![s / (L ^ 2 * D), -k * c / (L ^ 2 * D)])
  let q := (orbitMapR ℓ g L e)
  ![(rot g ((1 / D) • fu.1), rot g ((1 / D) • fu.2)),
    (quarterTurn q.1, quarterTurn q.2),
    (rot g fL.1, rot g fL.2),
    (rot g (fe.1 + (s / D) • fu.1), rot g (fe.2 + (s / D) • fu.2))]

/-- The chain rule for the orbit map along a curve `(ℓ, g, L, e)(s)` (with `0 < L`, `0 ≤ e < 1`):
the derivative is the combination of the four explicit columns. -/
theorem hasDerivAt_orbitMapR_curve {ℓ g L e : ℝ → ℝ} {ℓ' g' L' e' t : ℝ}
    (hℓ : HasDerivAt ℓ ℓ' t) (hg : HasDerivAt g g' t) (hL : HasDerivAt L L' t)
    (he : HasDerivAt e e' t) (hL0 : 0 < L t) (he0 : 0 ≤ e t) (he1 : e t < 1) :
    HasDerivAt (fun s => orbitMapR (ℓ s) (g s) (L s) (e s))
      (ℓ' • orbitMapColumn (ℓ t) (g t) (L t) (e t) 0 + g' • orbitMapColumn (ℓ t) (g t) (L t) (e t) 1
        + L' • orbitMapColumn (ℓ t) (g t) (L t) (e t) 2
        + e' • orbitMapColumn (ℓ t) (g t) (L t) (e t) 3) t := by
  have habs : |e t| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hu := hasDerivAt_eccAnom_curve hℓ he habs
  have hX := hasDerivAt_frameX hL he hu
  have hY := hasDerivAt_frameY hL he hu habs
  have hPX := hasDerivAt_framePX hL he hu hL0 he0 he1
  have hPY := hasDerivAt_framePY hL he hu hL0 he0 he1
  have h1 := hasDerivAt_rot_curve hg hX hY
  have h2 := hasDerivAt_rot_curve hg hPX hPY
  have h12 := h1.prodMk h2
  refine h12.congr_deriv ?_
  refine Prod.ext ?_ ?_
  · ext i; fin_cases i
    · simp [orbitMapColumn, rot, quarterTurn, orbitMapR, orbitFrame]
      ring
    · simp [orbitMapColumn, rot, quarterTurn, orbitMapR, orbitFrame]
      ring
  · ext i; fin_cases i
    · simp [orbitMapColumn, rot, quarterTurn, orbitMapR, orbitFrame]
      ring
    · simp [orbitMapColumn, rot, quarterTurn, orbitMapR, orbitFrame]
      ring

/-- `fderiv` in the direction `v` is the derivative along the line `t ↦ x + t • v`. -/
theorem fderiv_apply_eq_of_hasDerivAt_line {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x v : E} {d : F}
    (hf : DifferentiableAt ℝ f x) (h : HasDerivAt (fun t : ℝ => f (x + t • v)) d 0) :
    fderiv ℝ f x v = d := by
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by simpa using hf.hasFDerivAt
  exact (hf'.comp_hasDerivAt (0 : ℝ) hline).unique h

theorem hasDerivAt_orbitMapR_line (ℓ g L e a b c d : ℝ) (hL : 0 < L) (he0 : 0 ≤ e) (he1 : e < 1) :
    HasDerivAt (fun t : ℝ => orbitMapR (ℓ + t * a) (g + t * b) (L + t * c) (e + t * d))
      (a • orbitMapColumn ℓ g L e 0 + b • orbitMapColumn ℓ g L e 1
        + c • orbitMapColumn ℓ g L e 2 + d • orbitMapColumn ℓ g L e 3) 0 := by
  have hc : ∀ x y : ℝ, HasDerivAt (fun s : ℝ => x + s * y) y 0 := fun x y => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const y).const_add x
  have := hasDerivAt_orbitMapR_curve (hc ℓ a) (hc g b) (hc L c) (hc e d) (by simpa using hL)
    (by simpa using he0) (by simpa using he1)
  simpa using this

/-- The column of the Jacobian of `(ℓ, g, L, e) ↦ orbitMapR ℓ g L e` in the direction `i`. -/
theorem fderiv_orbitMapR_basis {ℓ g L e : ℝ} (hL : 0 < L) (he0 : 0 < e) (he1 : e < 1) (i : Fin 4) :
    fderiv ℝ (fun x : Fin 4 → ℝ => orbitMapR (x 0) (x 1) (x 2) (x 3)) ![ℓ, g, L, e] (Pi.single i 1)
        =
      orbitMapColumn ℓ g L e i := by
  have hd : DifferentiableAt ℝ (fun x : Fin 4 → ℝ => orbitMapR (x 0) (x 1) (x 2) (x 3)) ![ℓ, g, L,
      e] :=
    (analyticOnNhd_orbitMapR _ ⟨by simpa using hL, by simpa using he0.le, by simpa using
        he1⟩).differentiableAt
  refine fderiv_apply_eq_of_hasDerivAt_line hd ?_
  fin_cases i
  · simpa using hasDerivAt_orbitMapR_line ℓ g L e 1 0 0 0 hL he0.le he1
  · simpa using hasDerivAt_orbitMapR_line ℓ g L e 0 1 0 0 hL he0.le he1
  · simpa using hasDerivAt_orbitMapR_line ℓ g L e 0 0 1 0 hL he0.le he1
  · simpa using hasDerivAt_orbitMapR_line ℓ g L e 0 0 0 1 hL he0.le he1

theorem eccOf_data {L G : ℝ} (hG : 0 < G) (hGL : G < L) :
    0 < eccOf L G ∧ eccOf L G < 1 ∧ 0 < 1 - G ^ 2 / L ^ 2 := by
  have hm := eccOf_mem_Ioo (L := L) (G := G) (by simpa using hGL) hG
  have hL : 0 < L := hG.trans hGL
  have h1 : G ^ 2 / L ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  exact ⟨hm.1, hm.2, by linarith⟩

theorem hasDerivAt_eccOf_line {L G : ℝ} (a b : ℝ) (hG : 0 < G) (hGL : G < L) :
    HasDerivAt (fun s : ℝ => eccOf (L + s * a) (G + s * b))
      ((G ^ 2 * a / L ^ 3 - G * b / L ^ 2) / eccOf L G) 0 := by
  have hL : 0 < L := hG.trans hGL
  obtain ⟨he0, -, hpos⟩ := eccOf_data hG hGL
  have hc : ∀ x y : ℝ, HasDerivAt (fun s : ℝ => x + s * y) y 0 := fun x y => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const y).const_add x
  have hLne : L ≠ 0 := hL.ne'
  have hq : HasDerivAt (fun s : ℝ => (G + s * b) ^ 2 / (L + s * a) ^ 2)
      ((2 * G * b * L ^ 2 - G ^ 2 * (2 * L * a)) / (L ^ 2) ^ 2) 0 := by
    have := ((hc G b).pow 2).div ((hc L a).pow 2) (by simpa using pow_ne_zero 2 hLne)
    refine this.congr_deriv ?_
    simp
  have hin : HasDerivAt (fun s : ℝ => 1 - (G + s * b) ^ 2 / (L + s * a) ^ 2)
      (-((2 * G * b * L ^ 2 - G ^ 2 * (2 * L * a)) / (L ^ 2) ^ 2)) 0 := by
    refine ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hq).congr_deriv ?_
    simp
  have hne : (1 - (G + 0 * b) ^ 2 / (L + 0 * a) ^ 2) ≠ 0 := by simpa using hpos.ne'
  have hs := hin.sqrt hne
  have hsq : eccOf L G ≠ 0 := he0.ne'
  unfold eccOf at hsq ⊢
  refine hs.congr_deriv ?_
  simp only [zero_mul, add_zero]
  field_simp
  ring

private theorem hasDerivAt_delaunay_line {w : Phase 2} (hw : w ∈ deDom) (a b c d E : ℝ)
    (hE : E = (w.2 1 ^ 2 * c / w.2 0 ^ 3 - w.2 1 * d / w.2 0 ^ 2) / eccOf (w.2 0) (w.2 1)) :
    HasDerivAt (fun t : ℝ => orbitMapR (w.1 0 + t * a) (w.1 1 + t * b) (w.2 0 + t * c)
        (eccOf (w.2 0 + t * c) (w.2 1 + t * d)))
      (a • orbitMapColumn (w.1 0) (w.1 1) (w.2 0) (eccOf (w.2 0) (w.2 1)) 0
        + b • orbitMapColumn (w.1 0) (w.1 1) (w.2 0) (eccOf (w.2 0) (w.2 1)) 1
        + c • orbitMapColumn (w.1 0) (w.1 1) (w.2 0) (eccOf (w.2 0) (w.2 1)) 2
        + E • orbitMapColumn (w.1 0) (w.1 1) (w.2 0) (eccOf (w.2 0) (w.2 1)) 3) 0 := by
  obtain ⟨hG, hGL⟩ := hw
  have hL : 0 < w.2 0 := hG.trans hGL
  obtain ⟨he0, he1, -⟩ := eccOf_data hG hGL
  have hc : ∀ x y : ℝ, HasDerivAt (fun s : ℝ => x + s * y) y 0 := fun x y => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const y).const_add x
  have he := hasDerivAt_eccOf_line (L := w.2 0) (G := w.2 1) c d hG hGL
  have := hasDerivAt_orbitMapR_curve (hc (w.1 0) a) (hc (w.1 1) b) (hc (w.2 0) c) he
    (by simpa using hL) (by simpa using he0.le) (by simpa using he1)
  rw [hE]
  simpa using this

/-- Chain rule through `e(L, G)`: `∂_L e = G²/(L³ e)`, `∂_G e = -G/(L² e)`. -/
theorem fderiv_delaunay_basis {w : Phase 2} (hw : w ∈ deDom) :
    fderiv ℝ delaunay w (Pi.single 0 1, 0) = orbitMapColumn (w.1 0) (w.1 1) (w.2 0) (eccOf (w.2 0)
        (w.2 1)) 0 ∧
    fderiv ℝ delaunay w (Pi.single 1 1, 0) = orbitMapColumn (w.1 0) (w.1 1) (w.2 0) (eccOf (w.2 0)
        (w.2 1)) 1 ∧
    fderiv ℝ delaunay w (0, Pi.single 0 1) =
      orbitMapColumn (w.1 0) (w.1 1) (w.2 0) (eccOf (w.2 0) (w.2 1)) 2 +
        (w.2 1 ^ 2 / (w.2 0 ^ 3 * eccOf (w.2 0) (w.2 1))) •
          orbitMapColumn (w.1 0) (w.1 1) (w.2 0) (eccOf (w.2 0) (w.2 1)) 3 ∧
    fderiv ℝ delaunay w (0, Pi.single 1 1) =
      (-w.2 1 / (w.2 0 ^ 2 * eccOf (w.2 0) (w.2 1))) •
        orbitMapColumn (w.1 0) (w.1 1) (w.2 0) (eccOf (w.2 0) (w.2 1)) 3 := by
  have hd : DifferentiableAt ℝ delaunay w := (analyticOnNhd_delaunay w hw).differentiableAt
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine fderiv_apply_eq_of_hasDerivAt_line hd ?_
    simpa [delaunay] using hasDerivAt_delaunay_line hw 1 0 0 0 0 (by simp)
  · refine fderiv_apply_eq_of_hasDerivAt_line hd ?_
    simpa [delaunay] using hasDerivAt_delaunay_line hw 0 1 0 0 0 (by simp)
  · refine fderiv_apply_eq_of_hasDerivAt_line hd ?_
    simpa [delaunay] using hasDerivAt_delaunay_line hw 0 0 1 0 (w.2 1 ^ 2 / (w.2 0 ^ 3 * eccOf (w.2
        0) (w.2 1)))
      (by ring)
  · refine fderiv_apply_eq_of_hasDerivAt_line hd ?_
    simpa [delaunay] using hasDerivAt_delaunay_line hw 0 0 0 1 (-w.2 1 / (w.2 0 ^ 2 * eccOf (w.2 0)
        (w.2 1)))
      (by ring)

end KAM.Kepler

end
