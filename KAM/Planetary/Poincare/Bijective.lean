/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Poincare.Symplectic
public import KAM.Kepler.DelaunayChart

/-!
# The Poincaré chart: bijectivity

`bpP:p7:poincare` (e): the chart `poincare m κ` maps `𝒪` onto `𝒦_{m,κ}`, is injective modulo
`2πℤ` in `λ`, is a local analytic diffeomorphism, and has the explicit inverse `poincareInv`.

Proof plan.

* Injectivity: `Λ` and `Γ` are recovered by `poincare_elements`; for `Γ = 0` the circular formula
  `poincare_circular` gives `(cos λ, sin λ)`; for `Γ > 0` the chart is `delaunayMK` in the
  variables `(λ - g, g, Λ, Λ - Γ)` (`poincare_eq_delaunayMK`) and `delaunayMK_eq_iff` applies.
* Local diffeomorphism: the derivative is symplectic (`poincare_symplectic`), hence injective,
  hence invertible; then `ContDiffAt.toOpenPartialHomeomorph`.
* Surjectivity: `C < Λ` is `delaunayMK_image` through `Γ > 0`; `C = Λ` is the circular torus
  (`cross_eq_action_iff`).
* The inverse formula is the algebra of `poincare_elements`, with `F` recovered by `Complex.arg`.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology
open scoped ContDiff

namespace KAM.Planetary

open KAM KAM.Kepler

section PoincareBijective

private theorem bj_polar (x y : ℝ) :
    ∃ g : ℝ, x = √(x ^ 2 + y ^ 2) * Real.cos g ∧ y = √(x ^ 2 + y ^ 2) * Real.sin g := by
  refine ⟨Complex.arg ⟨x, y⟩, ?_, ?_⟩
  · have h := Complex.norm_mul_cos_arg (⟨x, y⟩ : ℂ)
    rw [Complex.norm_def, Complex.normSq_mk] at h
    simpa [sq] using h.symm
  · have h := Complex.norm_mul_sin_arg (⟨x, y⟩ : ℂ)
    rw [Complex.norm_def, Complex.normSq_mk] at h
    simpa [sq] using h.symm

private theorem bj_exists_int {x y : ℝ} (hc : Real.cos x = Real.cos y)
    (hs : Real.sin x = Real.sin y) : ∃ k : ℤ, y = x + 2 * π * k := by
  have h : Real.cos (y - x) = 1 := by
    rw [Real.cos_sub, ← hc, ← hs]
    exact Real.cos_sq_add_sin_sq x |>.symm ▸ by nlinarith [Real.cos_sq_add_sin_sq x]
  obtain ⟨n, hn⟩ := Real.cos_eq_one_iff _ |>.1 h
  exact ⟨n, by linarith⟩

private theorem bj_cos (x : ℝ) (k : ℤ) : Real.cos (x + 2 * π * k) = Real.cos x := by
  rw [show x + 2 * π * k = x + k * (2 * π) by ring]
  exact Real.cos_add_int_mul_two_pi x k

private theorem bj_sin (x : ℝ) (k : ℤ) : Real.sin (x + 2 * π * k) = Real.sin x := by
  rw [show x + 2 * π * k = x + k * (2 * π) by ring]
  exact Real.sin_add_int_mul_two_pi x k

private theorem bj_circ_eq {w : Phase 2} (h : poincareGamma w = 0) :
    w = ((![w.1 0, 0] : Fin 2 → ℝ), (![w.2 0, 0] : Fin 2 → ℝ)) := by
  have h1 : w.1 1 = 0 := by
    have : w.1 1 ^ 2 = 0 := by
      unfold poincareGamma at h; nlinarith [sq_nonneg (w.1 1), sq_nonneg (w.2 1)]
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  have h2 : w.2 1 = 0 := by
    have : w.2 1 ^ 2 = 0 := by
      unfold poincareGamma at h; nlinarith [sq_nonneg (w.1 1), sq_nonneg (w.2 1)]
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp [h1, h2]

/-- Off the circular locus the chart is `delaunayMK` in the variables `(λ - g, g, Λ, Λ - Γ)`. -/
private theorem bj_noncirc {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {w : Phase 2}
    (hw : w ∈ poincareDom) (hΓ : 0 < poincareGamma w) :
    ∃ g : ℝ, w.1 1 = √(2 * poincareGamma w) * Real.cos g ∧
      w.2 1 = √(2 * poincareGamma w) * Real.sin g ∧
      poincare m κ w =
        delaunayMK m κ (![w.1 0 - g, g], ![w.2 0, w.2 0 - poincareGamma w]) := by
  obtain ⟨g, hg1, hg2⟩ := bj_polar (w.1 1) (w.2 1)
  have hsum : w.1 1 ^ 2 + w.2 1 ^ 2 = 2 * poincareGamma w := by unfold poincareGamma; ring
  rw [hsum] at hg1 hg2
  refine ⟨g, hg1, hg2, ?_⟩
  have hw_eq : w = ((![w.1 0, √(2 * poincareGamma w) * Real.cos g] : Fin 2 → ℝ),
      (![w.2 0, √(2 * poincareGamma w) * Real.sin g] : Fin 2 → ℝ)) := by
    refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i
    · simp
    · simpa using hg1
    · simp
    · simpa using hg2
  calc poincare m κ w = poincare m κ ((![w.1 0, √(2 * poincareGamma w) * Real.cos g] :
          Fin 2 → ℝ), (![w.2 0, √(2 * poincareGamma w) * Real.sin g] : Fin 2 → ℝ)) :=
        congrArg _ hw_eq
    _ = _ := poincare_eq_delaunayMK hm hκ hΓ hw.2

theorem poincare_eq_iff {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {w w' : Phase 2} (hw : w ∈ poincareDom)
    (hw' : w' ∈ poincareDom) :
    poincare m κ w = poincare m κ w' ↔ ∃ k : ℤ, w'.1 = ![w.1 0 + 2 * π * k, w.1 1] ∧
      w'.2 = w.2 := by
  constructor
  · intro h
    obtain ⟨-, -, -, hA, hC, -⟩ := poincare_elements hm hκ hw
    obtain ⟨-, -, -, hA', hC', -⟩ := poincare_elements hm hκ hw'
    have hΛ : w'.2 0 = w.2 0 := by rw [← hA, ← hA', h]
    have hΓ : poincareGamma w' = poincareGamma w := by
      have : w.2 0 - poincareGamma w = w'.2 0 - poincareGamma w' := by rw [← hC, ← hC', h]
      linarith
    rcases (poincare_facts hw).1.eq_or_lt with h0 | hpos
    · have h0' : poincareGamma w' = 0 := by rw [hΓ]; exact h0.symm
      have c1 := bj_circ_eq h0.symm
      have c2 := bj_circ_eq h0'
      have e1 := poincare_circular hm hκ (lam := w.1 0) (Λ := w.2 0) hw.1
      have e2 := poincare_circular hm hκ (lam := w'.1 0) (Λ := w'.2 0) hw'.1
      rw [← c1] at e1
      rw [← c2] at e2
      rw [e1, e2, hΛ] at h
      have hq := congrArg Prod.fst h
      have hA0 : 0 < w.2 0 ^ 2 / (m ^ 2 * κ) := by have := hw.1; positivity
      have q0 := congrFun hq 0
      have q1 := congrFun hq 1
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one] at q0 q1
      obtain ⟨k, hk⟩ := bj_exists_int (mul_left_cancel₀ hA0.ne' q0)
        (mul_left_cancel₀ hA0.ne' q1)
      refine ⟨k, ?_, ?_⟩
      · ext i; fin_cases i
        · simpa using hk
        · have a := congrFun (congrArg Prod.fst c1) 1
          have b := congrFun (congrArg Prod.fst c2) 1
          simp at a b
          simp [a, b]
      · ext i; fin_cases i
        · simpa using hΛ
        · have a := congrFun (congrArg Prod.snd c1) 1
          have b := congrFun (congrArg Prod.snd c2) 1
          simp at a b
          simp [a, b]
    · have hpos' : 0 < poincareGamma w' := by rw [hΓ]; exact hpos
      obtain ⟨g, hg1, hg2, hd⟩ := bj_noncirc hm hκ hw hpos
      obtain ⟨g', hg1', hg2', hd'⟩ := bj_noncirc hm hκ hw' hpos'
      rw [hd, hd'] at h
      have hdw : (![w.1 0 - g, g], ![w.2 0, w.2 0 - poincareGamma w]) ∈ deDom :=
        by refine ⟨?_, ?_⟩ <;> simp <;> linarith [hw.2]
      have hdw' : (![w'.1 0 - g', g'], ![w'.2 0, w'.2 0 - poincareGamma w']) ∈ deDom :=
        by refine ⟨?_, ?_⟩ <;> simp <;> linarith [hw'.2]
      have h' := (delaunayMK_eq_iff hm hκ hdw hdw').1 h
      obtain ⟨k, k', hk1, hk2⟩ := h'
      have a1 := congrFun hk1 0
      have a2 := congrFun hk1 1
      simp at a1 a2
      refine ⟨k + k', ?_, ?_⟩
      · ext i; fin_cases i
        · simp only [Fin.zero_eta, Matrix.cons_val_zero]
          push_cast
          linarith
        · show w'.1 1 = w.1 1
          rw [hg1', hg1, hΓ, show g' = g + 2 * π * k' by linarith, bj_cos]
      · ext i; fin_cases i
        · simpa using hΛ
        · show w'.2 1 = w.2 1
          rw [hg2', hg2, hΓ, show g' = g + 2 * π * k' by linarith, bj_sin]
  · rintro ⟨k, h1, h2⟩
    have : w' = (![w.1 0 + 2 * π * k, w.1 1], w.2) := Prod.ext h1 h2
    rw [this]
    exact (poincare_periodic hm hκ hw k).symm

section LocalDiffeo

/-- Nondegeneracy of the symplectic form in the first argument. -/
private theorem bj_eq_zero_of_sf {u : Phase 2} (h : ∀ v, symplecticForm u v = 0) : u = 0 := by
  have h0 : u.2 0 = 0 := by simpa [KAM.Kepler.sf_eq] using h ((![1, 0], ![0, 0]) : Phase 2)
  have h1 : u.2 1 = 0 := by simpa [KAM.Kepler.sf_eq] using h ((![0, 1], ![0, 0]) : Phase 2)
  have h2 : u.1 0 = 0 := by simpa [KAM.Kepler.sf_eq] using h ((![0, 0], ![1, 0]) : Phase 2)
  have h3 : u.1 1 = 0 := by simpa [KAM.Kepler.sf_eq] using h ((![0, 0], ![0, 1]) : Phase 2)
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;> simp [*]

/-- `D poincare` is invertible on `𝒪`: a symplectic endomorphism of the finite-dimensional space
`Phase 2` is injective (nondegeneracy), hence bijective. -/
private theorem bj_fderiv_equiv {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {w : Phase 2}
    (hw : w ∈ poincareDom) :
    ∃ A : Phase 2 ≃L[ℝ] Phase 2, (A : Phase 2 →L[ℝ] Phase 2) = fderiv ℝ (poincare m κ) w := by
  have hs := poincare_symplectic hm hκ w hw
  set A := fderiv ℝ (poincare m κ) w with hA
  have hker : LinearMap.ker (A : Phase 2 →ₗ[ℝ] Phase 2) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    refine bj_eq_zero_of_sf fun v => ?_
    have := hs u v
    rw [one_mul] at this
    rw [← this]
    have hu' : A u = 0 := hu
    rw [hu']
    simp [KAM.Kepler.sf_eq]
  have hinj : Function.Injective (A : Phase 2 →ₗ[ℝ] Phase 2) := LinearMap.ker_eq_bot.1 hker
  have hsurj : Function.Surjective (A : Phase 2 →ₗ[ℝ] Phase 2) :=
    LinearMap.injective_iff_surjective.1 hinj
  refine ⟨ContinuousLinearEquiv.ofBijective A hker ?_, ?_⟩
  · exact LinearMap.range_eq_top.2 hsurj
  · exact ContinuousLinearMap.ext fun z => rfl

theorem poincare_localDiffeo {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {w : Phase 2}
    (hw : w ∈ poincareDom) :
    ∃ φ : OpenPartialHomeomorph (Phase 2) (Phase 2), w ∈ φ.source ∧
      (φ : Phase 2 → Phase 2) = poincare m κ ∧ AnalyticOnNhd ℝ φ.symm φ.target := by
  have hana := analyticOnNhd_poincare hm hκ
  obtain ⟨A, hA⟩ := bj_fderiv_equiv hm hκ hw
  have hc : ContDiffAt ℝ ω (poincare m κ) w := (hana w hw).contDiffAt
  have hf' : HasFDerivAt (poincare m κ) (A : Phase 2 →L[ℝ] Phase 2) w := by
    rw [hA]; exact (hana w hw).differentiableAt.hasFDerivAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  let φ0 := hc.toOpenPartialHomeomorph (poincare m κ) hf' hn
  let φ := φ0.restrOpen poincareDom isOpen_poincareDom
  have hcoe : (φ : Phase 2 → Phase 2) = poincare m κ := rfl
  refine ⟨φ, ⟨hc.mem_toOpenPartialHomeomorph_source hf' hn, hw⟩, hcoe, ?_⟩
  intro y hy
  have hxs : φ.symm y ∈ φ.source := φ.map_target hy
  have hx : φ.symm y ∈ poincareDom := hxs.2
  obtain ⟨B, hB⟩ := bj_fderiv_equiv hm hκ hx
  have hB' : HasFDerivAt φ (B : Phase 2 →L[ℝ] Phase 2) (φ.symm y) := by
    rw [hcoe, hB]
    exact (hana _ hx).differentiableAt.hasFDerivAt
  have hcd : ContDiffAt ℝ ω φ (φ.symm y) := by
    rw [hcoe]; exact (hana _ hx).contDiffAt
  exact (φ.contDiffAt_symm hy hB' hcd).analyticAt

end LocalDiffeo

section Surjective

private theorem bj_planeSq (v : Fin 2 → ℝ) : planeSq v = v 0 ^ 2 + v 1 ^ 2 := by
  simp [planeSq, Fin.sum_univ_two]

/-- Points of `𝒦` with `C < Λ` are hit through `Γ > 0` (the Delaunay chart). -/
private theorem bj_surj_lt {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {z : Phase 2}
    (hz : z ∈ regionMK m κ) (hlt : planeCross z.1 z.2 < actionMK m κ z) :
    ∃ w ∈ poincareDom, poincare m κ w = z := by
  obtain ⟨y, hy, rfl⟩ := (delaunayMK_image hm hκ).symm.subset (show z ∈ _ from ⟨hz, hlt⟩)
  obtain ⟨hy1, hy2⟩ := hy
  set Γ := y.2 0 - y.2 1 with hΓdef
  have hΓ : 0 < Γ := by simp only [hΓdef]; linarith
  have hρ2 : √(2 * Γ) ^ 2 = 2 * Γ := Real.sq_sqrt (by linarith)
  set w : Phase 2 := (![y.1 0 + y.1 1, √(2 * Γ) * Real.cos (y.1 1)],
    ![y.2 0, √(2 * Γ) * Real.sin (y.1 1)]) with hw
  have hGw : poincareGamma w = Γ := by
    simp only [poincareGamma, hw, Matrix.cons_val_one, Matrix.cons_val_zero]
    nlinarith [Real.cos_sq_add_sin_sq (y.1 1)]
  have hwd : w ∈ poincareDom := by
    refine ⟨?_, ?_⟩
    · show 0 < y.2 0
      linarith
    · rw [hGw]; show Γ < y.2 0
      simp only [hΓdef]; linarith
  refine ⟨w, hwd, ?_⟩
  have h := poincare_eq_delaunayMK hm hκ (lam := y.1 0 + y.1 1) (Λ := y.2 0) (Γ := Γ)
    (g := y.1 1) hΓ (by simp only [hΓdef]; linarith)
  rw [show w = ((![y.1 0 + y.1 1, √(2 * Γ) * Real.cos (y.1 1)] : Fin 2 → ℝ),
    (![y.2 0, √(2 * Γ) * Real.sin (y.1 1)] : Fin 2 → ℝ)) from rfl, h]
  congr 1
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;> simp [hΓdef]

/-- Points of `𝒦` with `C = Λ` lie on the circular torus. -/
private theorem bj_surj_eq {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {z : Phase 2}
    (hz : z ∈ regionMK m κ) (heq : planeCross z.1 z.2 = actionMK m κ z) :
    ∃ w ∈ poincareDom, poincare m κ w = z := by
  obtain ⟨hd, hr⟩ := (cross_eq_action_iff hm hκ hz).1 heq
  obtain ⟨hr0, hE, hc0⟩ := hz
  set r := planeLength z.1 with hrdef
  set Λ := actionMK m κ z with hΛdef
  have hcr : z.1 0 * z.2 1 - z.1 1 * z.2 0 = Λ := heq
  have hd' : z.1 0 * z.2 0 + z.1 1 * z.2 1 = 0 := by
    simpa [planeDot, Fin.sum_univ_two] using hd
  have hΛpos : 0 < Λ := by rw [← heq]; exact hc0
  have hΛsq : Λ ^ 2 = m ^ 2 * κ * r := by
    have : 0 ≤ κ * axisMK m κ z := by rw [← hr]; positivity
    rw [hΛdef]; unfold actionMK
    rw [mul_pow, Real.sq_sqrt this, hr]; ring
  have hr2 : r ^ 2 = z.1 0 ^ 2 + z.1 1 ^ 2 := by
    rw [hrdef, planeLength_sq, bj_planeSq]
  obtain ⟨θ, hθ0, hθ1⟩ := bj_polar (z.1 0) (z.1 1)
  have hrθ : √(z.1 0 ^ 2 + z.1 1 ^ 2) = r := by rw [← hr2]; exact Real.sqrt_sq hr0.le
  rw [hrθ] at hθ0 hθ1
  refine ⟨((![θ, 0] : Fin 2 → ℝ), (![Λ, 0] : Fin 2 → ℝ)), ⟨hΛpos, ?_⟩, ?_⟩
  · simp [poincareGamma, hΛpos]
  rw [poincare_circular hm hκ hΛpos]
  have hA : Λ ^ 2 / (m ^ 2 * κ) = r := by field_simp; linarith
  have hs : m * √(κ / r) = Λ / r := by
    have : κ / r = (Λ / (m * r)) ^ 2 := by field_simp; linarith
    rw [this, Real.sqrt_sq (by positivity)]
    field_simp
  rw [hA]
  rw [hs]
  have hp0 : z.2 0 * r ^ 2 = -(z.1 1 * Λ) := by
    rw [hr2]; linear_combination z.1 0 * hd' - z.1 1 * hcr
  have hp1 : z.2 1 * r ^ 2 = z.1 0 * Λ := by
    rw [hr2]; linear_combination z.1 1 * hd' + z.1 0 * hcr
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i
  · simp [hθ0]
  · simp [hθ1]
  · simp only [Fin.zero_eta, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]
    rw [hθ1] at hp0
    rw [div_mul_eq_mul_div, div_eq_iff hr0.ne']
    exact mul_left_cancel₀ hr0.ne' (by linear_combination (-1 : ℝ) * hp0)
  · simp only [Fin.mk_one, Pi.smul_apply, Matrix.cons_val_one, smul_eq_mul]
    show Λ / r * Real.cos θ = z.2 1
    rw [hθ0] at hp1
    rw [div_mul_eq_mul_div, div_eq_iff hr0.ne']
    exact mul_left_cancel₀ hr0.ne' (by linear_combination (-1 : ℝ) * hp1)

private theorem bj_surj {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {z : Phase 2}
    (hz : z ∈ regionMK m κ) : ∃ w ∈ poincareDom, poincare m κ w = z := by
  rcases (cross_le_action hm hκ hz).lt_or_eq with h | h
  · exact bj_surj_lt hm hκ hz h
  · exact bj_surj_eq hm hκ hz h

theorem poincare_image {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) :
    poincare m κ '' poincareDom = regionMK m κ := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact (poincare_elements hm hκ hw).1
  · intro z hz
    obtain ⟨w, hw, hwz⟩ := bj_surj hm hκ hz
    exact ⟨w, hw, hwz⟩

end Surjective

section Inverse

/-- The explicit inverse: `Λ = m√(κ a)`, `Γ = Λ - cr`, `v` = rescaled LRL vector, `(ξ, η) = v/s`,
`c = (k Id + vvᵀ/(1+k))⁻¹ (q/a + v) = k⁻¹ (u - (v·u)/(1+k) v)` with `u = q/a + v`, `F = arg c`,
`λ = Φ(F, v)`. -/
def poincareInv (m κ : ℝ) (z : Phase 2) : Phase 2 :=
  let Λ := actionMK m κ z
  let Γ := Λ - planeCross z.1 z.2
  let v := κ⁻¹ • ((planeSq z.2 / m ^ 2 - κ / planeLength z.1) • z.1 -
    (planeDot z.1 z.2 / m ^ 2) • z.2)
  let s := √((1 - Γ / (2 * Λ)) / Λ)
  let k := 1 - Γ / Λ
  let u := ((m ^ 2 * κ) / Λ ^ 2) • z.1 + v
  let c := k⁻¹ • (u - (planeDot v u / (1 + k)) • v)
  let F := Complex.arg ⟨c 0, c 1⟩
  (![keplerPhi v F, s⁻¹ * v 0], ![Λ, s⁻¹ * v 1])

private theorem bj_phi_int (v : Fin 2 → ℝ) (F : ℝ) (k : ℤ) :
    keplerPhi v (F + 2 * π * k) = keplerPhi v F + 2 * π * k := by
  simp only [keplerPhi, bj_cos, bj_sin]; ring

/-- The algebra of `c`: `c = e` for `u = (K e - v + δ v) + v`, `δ = v·e/(1 + K)`,
`|v|² = 1 - K²`. -/
private theorem bj_c_eq (e v : Fin 2 → ℝ) {K : ℝ} (hK : 0 < K) (hv : planeSq v = 1 - K ^ 2) :
    K⁻¹ • (((K • e - v + (planeDot v e / (1 + K)) • v) + v) -
      (planeDot v ((K • e - v + (planeDot v e / (1 + K)) • v) + v) / (1 + K)) • v) = e := by
  have hv' : v 0 ^ 2 + v 1 ^ 2 = 1 - K ^ 2 := by rw [← bj_planeSq]; exact hv
  have h1K : (1 + K) ≠ 0 := by positivity
  ext i
  simp only [planeDot, Fin.sum_univ_two] at *
  fin_cases i
  · simp only [Fin.zero_eta, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    linear_combination (-(v 0 * (e 0 * v 0 + e 1 * v 1))) * hv'
  · simp only [Fin.mk_one, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    linear_combination (-(v 1 * (e 0 * v 0 + e 1 * v 1))) * hv'

theorem poincareInv_poincare {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {w : Phase 2}
    (hw : w ∈ poincareDom) :
    ∃ k : ℤ, poincareInv m κ (poincare m κ w) = (![w.1 0 + 2 * π * k, w.1 1], w.2) := by
  obtain ⟨-, -, -, hA, hC, hv⟩ := poincare_elements hm hκ hw
  obtain ⟨-, hK, -, hrad, hsq, hlen, -⟩ := poincare_facts hw
  have hΛ : 0 < w.2 0 := hw.1
  have hΓ2 : w.2 0 - (w.2 0 - poincareGamma w) = poincareGamma w := by ring
  have hu : (m ^ 2 * κ / w.2 0 ^ 2) • (poincare m κ w).1 + poincareV w =
      (poincareK w • orbitalUnit (poincareF w) - poincareV w
        + (planeDot (poincareV w) (orbitalUnit (poincareF w)) / (1 + poincareK w)) •
          poincareV w) + poincareV w := by
    show (m ^ 2 * κ / w.2 0 ^ 2) • ((w.2 0 ^ 2 / (m ^ 2 * κ)) • _) + _ = _
    have hone : (m ^ 2 * κ / w.2 0 ^ 2) * (w.2 0 ^ 2 / (m ^ 2 * κ)) = 1 := by
      have : m ^ 2 * κ ≠ 0 := by positivity
      field_simp
    rw [smul_smul, hone, one_smul]
  have hc := bj_c_eq (orbitalUnit (poincareF w)) (poincareV w) hK hsq
  have hKd : 1 - poincareGamma w / w.2 0 = poincareK w := rfl
  simp only [poincareInv]
  rw [hA, hC, hv, hΓ2, hKd, hu, hc]
  have hs : 0 < √((1 - poincareGamma w / (2 * w.2 0)) / w.2 0) := Real.sqrt_pos.2 hrad
  set F := poincareF w with hFdef
  have hn : ‖(⟨orbitalUnit F 0, orbitalUnit F 1⟩ : ℂ)‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk]
    simp only [orbitalUnit, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show Real.cos F * Real.cos F + Real.sin F * Real.sin F = 1 by
      nlinarith [Real.cos_sq_add_sin_sq F]]
    simp
  have hne : (⟨orbitalUnit F 0, orbitalUnit F 1⟩ : ℂ) ≠ 0 := by
    intro h; rw [h] at hn; simp at hn
  have hcos := Complex.cos_arg hne
  have hsin := Complex.sin_arg (⟨orbitalUnit F 0, orbitalUnit F 1⟩ : ℂ)
  rw [hn] at hcos hsin
  simp only [orbitalUnit, Matrix.cons_val_zero, Matrix.cons_val_one, div_one] at hcos hsin
  obtain ⟨j, hj⟩ := bj_exists_int (x := F) (y := Complex.arg ⟨orbitalUnit F 0, orbitalUnit F 1⟩)
    hcos.symm hsin.symm
  refine ⟨j, ?_⟩
  refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i
  · show keplerPhi (poincareV w) (Complex.arg ⟨orbitalUnit F 0, orbitalUnit F 1⟩) =
      w.1 0 + 2 * π * j
    rw [hj, bj_phi_int, hFdef, poincareF, keplerPhi_keplerLong hlen]
  · show _ * poincareV w 0 = w.1 1
    simp only [poincareV, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
    exact inv_mul_cancel_left₀ hs.ne' _
  · rfl
  · show _ * poincareV w 1 = w.2 1
    simp only [poincareV, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one]
    exact inv_mul_cancel_left₀ hs.ne' _

theorem poincare_poincareInv {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {z : Phase 2}
    (hz : z ∈ regionMK m κ) :
    poincareInv m κ z ∈ poincareDom ∧ poincare m κ (poincareInv m κ z) = z := by
  obtain ⟨w, hw, rfl⟩ := bj_surj hm hκ hz
  obtain ⟨k, hk⟩ := poincareInv_poincare hm hκ hw
  rw [hk]
  have hmem : ((![w.1 0 + 2 * π * k, w.1 1] : Fin 2 → ℝ), w.2) ∈ poincareDom := by
    refine ⟨hw.1, ?_⟩
    simpa [poincareGamma] using hw.2
  exact ⟨hmem, poincare_periodic hm hκ hw k⟩

end Inverse

end PoincareBijective

end KAM.Planetary

end
