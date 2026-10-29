/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarAssembly.Data
public import KAM.Planetary.PlanarAssembly.Boxes

/-!
# Planar assembly: literal exports of the cylinder norm and the fast inverse (GAP-PX)

Unsigned exports stating the literal conclusions of `bpP:p12:sec-set#data` (the cylinder
inequality `cylnorm`) and `stepP:p12:fd-inv` (the explicit analytic inverse of the Kepler
frequency map on a box of actions).
-/

public section

open Set Real

namespace KAM.Planetary

open KAM KAM.Kepler

/-- `bpP:p12:sec-set#data` (eq `cylnorm`): on the cylinder `C(V, r)` (`b = 2`) the squared
Euclidean length of the slow part is `< 2 r²`. -/
theorem cylnorm {V : Set (Fin 2 → ℝ)} {r : ℝ} {w : Phase (2 + 2)}
    (hw : w ∈ cylinder (b := 2) V r) : p11c_slowLength (p11cL_slow w) ^ 2 < 2 * r ^ 2 := by
  have h0 := hw.2 0
  have h1 := hw.2 1
  unfold p11c_slowLength
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity), Fin.sum_univ_two]
  simp only [slow, p11cL_slow] at h0 h1 ⊢
  nlinarith

namespace PlanarAssembly

private theorem cuberoot_inv {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    (c / (c / x ^ 3)) ^ ((3 : ℕ) : ℝ)⁻¹ = x := by
  rw [div_div_cancel₀ hc.ne']
  exact Real.pow_rpow_inv_natCast hx.le (by norm_num)

private theorem cube_cuberoot {c y : ℝ} (hc : 0 < c) (hy : 0 < y) :
    c / ((c / y) ^ ((3 : ℕ) : ℝ)⁻¹) ^ 3 = y := by
  rw [Real.rpow_inv_natCast_pow (div_pos hc hy).le (by norm_num)]
  exact div_div_cancel₀ hc.ne'

private theorem cuberoot_mem {c l u w : ℝ} (hc : 0 < c) (hl : 0 < l) (hlu : l < u)
    (h1 : c / u ^ 3 < w) (h2 : w < c / l ^ 3) :
    l < (c / w) ^ ((3 : ℕ) : ℝ)⁻¹ ∧ (c / w) ^ ((3 : ℕ) : ℝ)⁻¹ < u := by
  have hu : 0 < u := hl.trans hlu
  have hw : 0 < w := (div_pos hc (pow_pos hu 3)).trans h1
  have e1 : l ^ 3 < c / w := by
    rw [lt_div_iff₀ hw]; rw [lt_div_iff₀ (pow_pos hl 3)] at h2; linarith
  have e2 : c / w < u ^ 3 := by
    rw [div_lt_iff₀ hw]; rw [div_lt_iff₀ (pow_pos hu 3)] at h1; linarith
  have hp : (0 : ℝ) < ((3 : ℕ) : ℝ)⁻¹ := by norm_num
  constructor
  · calc l = (l ^ 3) ^ ((3 : ℕ) : ℝ)⁻¹ := (Real.pow_rpow_inv_natCast hl.le (by norm_num)).symm
      _ < _ := Real.rpow_lt_rpow (pow_nonneg hl.le 3) e1 hp
  · calc _ < (u ^ 3) ^ ((3 : ℕ) : ℝ)⁻¹ := Real.rpow_lt_rpow (div_pos hc hw).le e2 hp
      _ = u := Real.pow_rpow_inv_natCast hu.le (by norm_num)

private theorem analyticAt_cuberoot {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    AnalyticAt ℝ (fun y : ℝ => (c / y) ^ ((3 : ℕ) : ℝ)⁻¹) x := by
  have hq : 0 < c / x := div_pos hc hx
  have ha : AnalyticAt ℝ (fun y : ℝ => Real.log (c / y)) x :=
    AnalyticAt.log (analyticAt_const.div analyticAt_id hx.ne') hq
  have hb : AnalyticAt ℝ (fun y : ℝ => Real.exp (((3 : ℕ) : ℝ)⁻¹ * Real.log (c / y))) x :=
    (analyticAt_const.mul ha).rexp'
  refine hb.congr ?_
  have hev : ∀ᶠ y in nhds x, 0 < y := (isOpen_Ioi.mem_nhds hx)
  filter_upwards [hev] with y hy
  rw [Real.rpow_def_of_pos (div_pos hc hy), mul_comm]

/-- `stepP:p12:fd-inv`: on the image of the action box `W = ∏ (l'ᵢ, u'ᵢ)` under the Kepler
frequency map, `g(v)ᵢ = (κ² mᵢ³ / vᵢ)^{1/3}` is real analytic, inverts the frequency map on
`W`, and maps the image back into `W` with `ω_h (g v) = v`. -/
theorem fd_inv (κ : ℝ) (m l u : Fin 2 → ℝ) (hκ : 0 < κ) (hm : ∀ i, 0 < m i)
    (hl : ∀ i, 0 < l i) (hlu : ∀ i, l i < u i) :
    let W : Set (Fin 2 → ℝ) := pi univ (fun i => Ioo (l i) (u i))
    let g : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun v i => (κ ^ 2 * m i ^ 3 / v i) ^ (1 / 3 : ℝ)
    AnalyticOnNhd ℝ g (fastFrequency (kepler_h κ m) '' W) ∧
      (∀ Λ ∈ W, g (fastFrequency (kepler_h κ m) Λ) = Λ) ∧
      (∀ v ∈ fastFrequency (kepler_h κ m) '' W,
        g v ∈ W ∧ fastFrequency (kepler_h κ m) (g v) = v) := by
  intro W g
  have e3 : (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ := by norm_num
  have hg : g = fun v i => (κ ^ 2 * m i ^ 3 / v i) ^ ((3 : ℕ) : ℝ)⁻¹ := by
    funext v i; simp only [g, e3]
  have hc : ∀ i, 0 < κ ^ 2 * m i ^ 3 := fun i => by have := hm i; positivity
  have hpos : ∀ I ∈ W, ∀ i, 0 < I i := fun I hI i => (hl i).trans (hI i (mem_univ i)).1
  have hfreq : ∀ I ∈ W, fastFrequency (kepler_h κ m) I = fun i => κ ^ 2 * m i ^ 3 / I i ^ 3 :=
    fun I hI => (product_chart (n := 2) (by norm_num) κ m hκ hm).2.1 I (hpos I hI) |>.1
  have hback : ∀ w ∈ pi univ (fun i => Ioo (κ ^ 2 * m i ^ 3 / u i ^ 3) (κ ^ 2 * m i ^ 3 / l i ^ 3)),
      g w ∈ W ∧ fastFrequency (kepler_h κ m) (g w) = w := by
    intro w hw
    rw [hg]
    have hgm : (fun i => (κ ^ 2 * m i ^ 3 / w i) ^ ((3 : ℕ) : ℝ)⁻¹) ∈ W := fun i _ =>
      cuberoot_mem (hc i) (hl i) (hlu i) (hw i (mem_univ i)).1 (hw i (mem_univ i)).2
    refine ⟨hgm, ?_⟩
    rw [hfreq _ hgm]
    funext i
    have hwi : 0 < w i := (div_pos (hc i) (pow_pos ((hl i).trans (hlu i)) 3)).trans
      (hw i (mem_univ i)).1
    exact cube_cuberoot (hc i) hwi
  have himg : fastFrequency (kepler_h κ m) '' W =
      pi univ (fun i => Ioo (κ ^ 2 * m i ^ 3 / u i ^ 3) (κ ^ 2 * m i ^ 3 / l i ^ 3)) := by
    ext w
    constructor
    · rintro ⟨I, hI, rfl⟩ i _
      rw [hfreq I hI]
      have h1 := hI i (mem_univ i)
      constructor
      · exact div_lt_div_of_pos_left (hc i) (pow_pos (hpos I hI i) 3)
          (pow_lt_pow_left₀ h1.2 (hpos I hI i).le (by norm_num))
      · exact div_lt_div_of_pos_left (hc i) (pow_pos (hl i) 3)
          (pow_lt_pow_left₀ h1.1 (hl i).le (by norm_num))
    · intro hw
      exact ⟨g w, (hback w hw).1, (hback w hw).2⟩
  refine ⟨?_, ?_, fun v hv => hback v (himg ▸ hv)⟩
  · rw [himg, hg]
    intro w hw
    refine AnalyticAt.pi fun i => ?_
    have hwi : 0 < w i := (div_pos (hc i) (pow_pos ((hl i).trans (hlu i)) 3)).trans
      (hw i (mem_univ i)).1
    exact (analyticAt_cuberoot (hc i) hwi).comp (f := fun v : Fin 2 → ℝ => v i)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).analyticAt w)
  · intro Λ hΛ
    rw [hfreq Λ hΛ, hg]
    funext i
    exact cuberoot_inv (hc i) (hpos Λ hΛ i)

end PlanarAssembly

end KAM.Planetary
