/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Poincare.Product
public import KAM.Planetary.PlanarAssembly.Geometry
public import KAM.Frozen.Planetary.Defs.FastFrequency
public import KAM.Frozen.Planetary.Defs.HasFastDiffeomorphism
public import KAM.Frozen.Planetary.Defs.HasSecularBirkhoffForm

/-!
# Planar assembly: boxes, the Kepler frequency and radius arithmetic (Part 12)

Blueprint P, Part 12 (`bpP:p12:collar`, `bpP:p12:fast-diffeo`, `bpP:p12:f-mono`, the elementary
radius and threshold choices of `bpP:p12:data`, and the supplementary
`bpP:p7:product-chart` (b) completion):

* `collar`: the `t`-collar of the frontier of an open box in the plane has volume at most
  `4 t (L₀ + L₁)`, the exact difference of two box volumes;
* `product_chart`: analyticity of the action Hamiltonian `kepler_h` on positive actions, its
  gradient, frequency and diagonal Hessian, and the decoupling identity with `hProd`;
* `fast_diffeo`: the frozen `HasFastDiffeomorphism` for `kepler_h` on a positive open box, with
  the explicit inverse `(κ² mᵢ³ / vᵢ)^(1/3)`;
* `radius_choices`, `birkhoff_mono_radius`: the explicit radius and threshold arithmetic and the
  restriction of the frozen secular Birkhoff expansion to a smaller disc.
-/

@[expose] public noncomputable section

open Set Real MeasureTheory Function
open scoped BigOperators

namespace KAM.Planetary
open KAM KAM.Kepler

namespace PlanarAssembly

/-! ### The collar of a box -/

private theorem frontier_box (l u : Fin 2 → ℝ) (hlu : ∀ i, l i < u i) :
    frontier (pi univ (fun i => Ioo (l i) (u i))) =
      pi univ (fun i => Icc (l i) (u i)) \ pi univ (fun i => Ioo (l i) (u i)) := by
  rw [frontier, closure_pi_set, interior_pi_set Set.finite_univ]
  simp only [closure_Ioo (hlu _).ne, interior_Ioo]

private theorem collar_subset (l u : Fin 2 → ℝ) (hlu : ∀ i, l i < u i) (t : ℝ) (ht : 0 < t) :
    {I : Fin 2 → ℝ | ∃ J ∈ frontier (pi univ (fun i => Ioo (l i) (u i))), dist I J < t} ⊆
      pi univ (fun i => Ioo (l i - t) (u i + t)) \ Icc (fun i => l i + t) (fun i => u i - t) := by
  rintro I ⟨J, hJ, hd⟩
  rw [frontier_box l u hlu] at hJ
  obtain ⟨hJc, hJo⟩ := hJ
  have hd' : ∀ i, |I i - J i| < t := fun i => by
    have := (dist_pi_lt_iff ht).mp hd i
    rwa [Real.dist_eq] at this
  refine ⟨fun i _ => ?_, fun hI => hJo fun j _ => ?_⟩
  · have h1 := abs_lt.mp (hd' i)
    have h2 := hJc i (mem_univ i)
    constructor <;> linarith [h2.1, h2.2]
  · have h1 := abs_lt.mp (hd' j)
    have h2 := hI.1 j
    have h3 := hI.2 j
    constructor <;> linarith

theorem collar (l u : Fin 2 → ℝ) (hlu : ∀ i, l i < u i)
    (t : ℝ) (ht : 0 < t) (htl : ∀ i, t < (u i - l i) / 2) :
    volume {I : Fin 2 → ℝ | ∃ J ∈ frontier (pi univ (fun i => Ioo (l i) (u i))),
      dist I J < t} ≤ ENNReal.ofReal (4 * ((u 0 - l 0) + (u 1 - l 1)) * t) := by
  have hle : (fun i => l i + t) ≤ fun i => u i - t := fun i => by
    have := htl i; simp only; linarith
  have hsub : Icc (fun i => l i + t) (fun i => u i - t) ⊆
      pi univ (fun i => Ioo (l i - t) (u i + t)) := fun x hx i _ => by
    have h1 := hx.1 i
    have h2 := hx.2 i
    constructor <;> linarith
  have hfin : volume (Icc (fun i => l i + t) (fun i => u i - t)) ≠ ⊤ := by
    rw [Real.volume_Icc_pi]
    exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top
  refine (measure_mono (collar_subset l u hlu t ht)).trans ?_
  rw [measure_sdiff hsub measurableSet_Icc.nullMeasurableSet hfin, Real.volume_pi_Ioo,
    Real.volume_Icc_pi]
  simp only [Fin.prod_univ_two]
  have h0 : 0 ≤ ((u 0 - t) - (l 0 + t)) := by have := htl 0; linarith
  have h1 : 0 ≤ ((u 1 - t) - (l 1 + t)) := by have := htl 1; linarith
  have h0' : 0 ≤ ((u 0 + t) - (l 0 - t)) := by have := htl 0; linarith
  have h1' : 0 ≤ ((u 1 + t) - (l 1 - t)) := by have := htl 1; linarith
  rw [← ENNReal.ofReal_mul h0', ← ENNReal.ofReal_mul h0,
    ← ENNReal.ofReal_sub _ (mul_nonneg h0 h1)]
  refine le_of_eq (congrArg ENNReal.ofReal ?_)
  ring

/-! ### The Kepler action Hamiltonian -/

section KeplerH

variable {n : ℕ}

/-- The explicit formula for `kepler_h`. -/
private def kepEnergy (κ : ℝ) (m : Fin n → ℝ) (I : Fin n → ℝ) : ℝ :=
  -∑ i, κ ^ 2 * m i ^ 3 / (2 * I i ^ 2)

private theorem fast_assemble (I phi p q : Fin n → ℝ) :
    fast (assemble I phi p q).2 = I := by
  funext i
  simp [fast, assemble]

private theorem kepler_h_eq (κ : ℝ) (m : Fin n → ℝ) : kepler_h κ m = kepEnergy κ m := by
  funext I
  unfold kepler_h hProd kepEnergy
  rw [fast_assemble]

private theorem hProd_eq (κ : ℝ) (m : Fin n → ℝ) (w : Phase (n + n)) :
    hProd κ m w = kepler_h κ m (fast (a := n) (b := n) w.2) := by
  rw [kepler_h_eq]; rfl

private theorem hasDerivAt_inv_sq (c y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun y : ℝ => c / (2 * y ^ 2)) (-(c / y ^ 3)) y := by
  have h2 : HasDerivAt (fun y : ℝ => 2 * y ^ 2) (2 * (2 * y)) y := by
    simpa using (hasDerivAt_pow 2 y).const_mul 2
  have h3 := (h2.inv (mul_ne_zero two_ne_zero (pow_ne_zero 2 hy))).const_mul c
  simp only [div_eq_mul_inv]
  refine h3.congr_deriv ?_
  field_simp

private theorem hasDerivAt_div_cube (c y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun y : ℝ => c / y ^ 3) (-3 * c / y ^ 4) y := by
  have h3 := ((hasDerivAt_pow 3 y).inv (pow_ne_zero 3 hy)).const_mul c
  simp only [div_eq_mul_inv]
  refine h3.congr_deriv ?_
  field_simp
  ring

private theorem hasFDerivAt_kepEnergy (κ : ℝ) (m : Fin n → ℝ) {I : Fin n → ℝ}
    (hI : ∀ i, I i ≠ 0) :
    HasFDerivAt (kepEnergy κ m)
      (∑ i, (κ ^ 2 * m i ^ 3 / I i ^ 3) •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)) I := by
  have h : ∀ i ∈ Finset.univ, HasFDerivAt (fun J : Fin n → ℝ => κ ^ 2 * m i ^ 3 / (2 * J i ^ 2))
      (-((κ ^ 2 * m i ^ 3 / I i ^ 3) •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i))) I := by
    intro i _
    have := (hasDerivAt_inv_sq (κ ^ 2 * m i ^ 3) (I i) (hI i)).comp_hasFDerivAt I
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt
    rw [neg_smul] at this
    exact this
  have := (HasFDerivAt.fun_sum h).neg
  unfold kepEnergy
  convert this using 1
  simp [Finset.sum_neg_distrib]

private theorem fderiv_kepEnergy_single (κ : ℝ) (m : Fin n → ℝ) {I : Fin n → ℝ}
    (hI : ∀ i, I i ≠ 0) (i : Fin n) :
    fderiv ℝ (kepEnergy κ m) I (Pi.single i 1) = κ ^ 2 * m i ^ 3 / I i ^ 3 := by
  rw [(hasFDerivAt_kepEnergy κ m hI).fderiv]
  simp [Pi.single_apply]

private theorem analyticAt_kepEnergy (κ : ℝ) (m : Fin n → ℝ) {I : Fin n → ℝ}
    (hI : ∀ i, I i ≠ 0) : AnalyticAt ℝ (kepEnergy κ m) I := by
  unfold kepEnergy
  have h : AnalyticAt ℝ (fun I : Fin n → ℝ => ∑ i, κ ^ 2 * m i ^ 3 / (2 * I i ^ 2)) I := by
    refine Finset.analyticAt_fun_sum _ fun i _ => ?_
    have hp : AnalyticAt ℝ (fun I : Fin n → ℝ => I i) I :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).analyticAt I
    exact analyticAt_const.div (analyticAt_const.mul (hp.pow 2))
      (mul_ne_zero two_ne_zero (pow_ne_zero 2 (hI i)))
  exact h.neg

private theorem fastFrequency_kepler_h (κ : ℝ) (m : Fin n → ℝ) {I : Fin n → ℝ}
    (hI : ∀ i, I i ≠ 0) :
    fastFrequency (kepler_h κ m) I = fun i => κ ^ 2 * m i ^ 3 / I i ^ 3 := by
  funext i
  unfold fastFrequency
  rw [kepler_h_eq, fderiv_kepEnergy_single κ m hI]

end KeplerH

/-- bpP:p7:product-chart (b), p7 L197/L206: locally owned missing export. -/
theorem product_chart {n : ℕ} (hn : 0 < n) (κ : ℝ) (m : Fin n → ℝ)
    (hκ : 0 < κ) (hm : ∀ i, 0 < m i) :
    AnalyticOnNhd ℝ (kepler_h κ m) {I : Fin n → ℝ | ∀ i, 0 < I i} ∧
    (∀ I : Fin n → ℝ, (∀ i, 0 < I i) →
      (fastFrequency (kepler_h κ m) I = fun i => κ ^ 2 * m i ^ 3 / I i ^ 3) ∧
      (∀ i, fderiv ℝ (kepler_h κ m) I (Pi.single i 1) =
        κ ^ 2 * m i ^ 3 / I i ^ 3) ∧
      (∀ i j, fderiv ℝ (fastFrequency (kepler_h κ m)) I (Pi.single j 1) i =
        if i = j then -3 * κ ^ 2 * m i ^ 3 / I i ^ 4 else 0) ∧
      (∀ i, -3 * κ ^ 2 * m i ^ 3 / I i ^ 4 ≠ 0)) ∧
    (∀ w : Phase (n + n), hProd κ m w =
      kepler_h κ m (fast (a := n) (b := n) w.2)) ∧
    (∀ w ∈ poincareProdDom n, keplerPart κ m (poincareProd m κ w) =
      kepler_h κ m (fast (a := n) (b := n) w.2)) := by
  have _ := hn
  have hne : ∀ I : Fin n → ℝ, (∀ i, 0 < I i) → ∀ i, I i ≠ 0 := fun I hI i => (hI i).ne'
  refine ⟨?_, ?_, hProd_eq κ m, ?_⟩
  · intro I hI
    rw [kepler_h_eq]
    exact analyticAt_kepEnergy κ m (hne I hI)
  · intro I hI
    refine ⟨fastFrequency_kepler_h κ m (hne I hI), ?_, ?_, ?_⟩
    · intro i
      exact congrFun (fastFrequency_kepler_h κ m (hne I hI)) i
    · intro i j
      have hev : fastFrequency (kepler_h κ m) =ᶠ[nhds I]
          fun J i => κ ^ 2 * m i ^ 3 / J i ^ 3 := by
        have hopen : IsOpen {J : Fin n → ℝ | ∀ i, 0 < J i} :=
          by
            have : {J : Fin n → ℝ | ∀ i, 0 < J i} = pi univ fun _ => Ioi (0 : ℝ) := by
              ext J; simp
            rw [this]
            exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi
        filter_upwards [hopen.mem_nhds hI] with J hJ
        exact fastFrequency_kepler_h κ m (hne J hJ)
      have hd : HasFDerivAt (fun J : Fin n → ℝ => fun i => κ ^ 2 * m i ^ 3 / J i ^ 3)
          (ContinuousLinearMap.pi fun i =>
            (-3 * κ ^ 2 * m i ^ 3 / I i ^ 4) •
              (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)) I := by
        rw [hasFDerivAt_pi]
        intro i
        have := (hasDerivAt_div_cube (κ ^ 2 * m i ^ 3) (I i) (hne I hI i)).comp_hasFDerivAt I
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt
        have e : -3 * κ ^ 2 * m i ^ 3 / I i ^ 4 = -3 * (κ ^ 2 * m i ^ 3) / I i ^ 4 := by ring
        rw [e]
        exact this
      rw [hev.fderiv_eq, hd.fderiv]
      simp [Pi.single_apply]
    · intro i
      have := (hI i).ne'
      have := (hm i).ne'
      have := hκ.ne'
      positivity
  · intro w hw
    rw [keplerPart_poincareProd hm hκ hw, hProd_eq]

/-! ### The fast diffeomorphism -/

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

/-- bpP:p12:fast-diffeo. Positivity of kappa and masses is standing section data. -/
theorem fast_diffeo (κ : ℝ) (m l u : Fin 2 → ℝ) (hκ : 0 < κ)
    (hm : ∀ i, 0 < m i) (hl : ∀ i, 0 < l i) (hlu : ∀ i, l i < u i) :
    HasFastDiffeomorphism (kepler_h κ m) (pi univ (fun i => Ioo (l i) (u i))) := by
  set box : Set (Fin 2 → ℝ) := pi univ (fun i => Ioo (l i) (u i)) with hbox
  have hc : ∀ i, 0 < κ ^ 2 * m i ^ 3 := fun i => by have := hm i; positivity
  have hpos : ∀ I ∈ box, ∀ i, 0 < I i := fun I hI i => (hl i).trans (hI i (mem_univ i)).1
  have hfreq : ∀ I ∈ box, fastFrequency (kepler_h κ m) I = fun i => κ ^ 2 * m i ^ 3 / I i ^ 3 :=
    fun I hI => (product_chart (n := 2) (by norm_num) κ m hκ hm).2.1 I (hpos I hI) |>.1
  let g : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun w i => (κ ^ 2 * m i ^ 3 / w i) ^ ((3 : ℕ) : ℝ)⁻¹
  have hback : ∀ w ∈ pi univ (fun i => Ioo (κ ^ 2 * m i ^ 3 / u i ^ 3) (κ ^ 2 * m i ^ 3 / l i ^ 3)),
      g w ∈ box ∧ fastFrequency (kepler_h κ m) (g w) = w := by
    intro w hw
    have hgm : g w ∈ box := fun i _ => cuberoot_mem (hc i) (hl i) (hlu i) (hw i (mem_univ i)).1
      (hw i (mem_univ i)).2
    refine ⟨hgm, ?_⟩
    rw [hfreq _ hgm]
    funext i
    have hwi : 0 < w i := (div_pos (hc i) (pow_pos ((hl i).trans (hlu i)) 3)).trans
      (hw i (mem_univ i)).1
    exact cube_cuberoot (hc i) hwi
  have himg : fastFrequency (kepler_h κ m) '' box =
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
  refine ⟨?_, ?_, g, ?_, ?_, ?_⟩
  · refine (product_chart (n := 2) (by norm_num) κ m hκ hm).1.mono ?_
    exact fun I hI => hpos I hI
  · rw [himg]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
  · rw [himg]
    refine contDiffOn_pi.2 fun i => fun w hw => ContDiffAt.contDiffWithinAt ?_
    have hwi : 0 < w i := (div_pos (hc i) (pow_pos ((hl i).trans (hlu i)) 3)).trans
      (hw i (mem_univ i)).1
    refine ContDiffAt.rpow_const_of_ne ?_ (div_pos (hc i) hwi).ne'
    exact contDiffAt_const.div (contDiffAt_pi.1 contDiffAt_id i) hwi.ne'
  · intro I hI
    rw [hfreq I hI]
    funext i
    exact cuberoot_inv (hc i) (hpos I hI i)
  · intro w hw
    rw [himg] at hw
    exact hback w hw

/-! ### Radius arithmetic -/

/-- Elementary output of the P-G radius/threshold choices, not a P-G premise. -/
def secular_radius (rG δ : ℝ) : ℝ := min rG (√(δ / 2)) / 2

def coupling_threshold (r c : ℝ) : ℝ := min 1 (r ^ 6 / (log (1 / r)) ^ c)

theorem radius_choices (rG δ c : ℝ) (hrG : 0 < rG) (hrG1 : rG < 1)
    (hδ : 0 < δ) (hc : 0 < c) :
    let r := secular_radius rG δ
    0 < r ∧ r < rG ∧ r < 1 ∧ 2 * r ^ 2 ≤ δ / 2 ∧
    0 < coupling_threshold r c ∧ coupling_threshold r c ≤ 1 ∧
    ∀ μ, 0 < μ → μ < coupling_threshold r c → μ < r ^ 6 / (log (1 / r)) ^ c := by
  intro r
  have _ := hc
  have hsq : 0 < √(δ / 2) := Real.sqrt_pos.mpr (by positivity)
  have hmin : 0 < min rG (√(δ / 2)) := lt_min hrG hsq
  have hr : 0 < r := by unfold r secular_radius; positivity
  have hr1 : r < rG := by
    have : r ≤ rG / 2 := by
      unfold r secular_radius
      linarith [min_le_left rG (√(δ / 2))]
    linarith
  have hrs : r ≤ √(δ / 2) / 2 := by
    unfold r secular_radius
    linarith [min_le_right rG (√(δ / 2))]
  have hr2 : r < 1 := hr1.trans hrG1
  have hlog : 0 < log (1 / r) := by
    apply Real.log_pos
    rw [lt_one_div (by norm_num) hr]; simpa using hr2
  have hpos : 0 < r ^ 6 / (log (1 / r)) ^ c := by positivity
  refine ⟨hr, hr1, hr2, ?_, ?_, min_le_left _ _, ?_⟩
  · have h0 : 0 ≤ r := hr.le
    have h1 : r ^ 2 ≤ (√(δ / 2) / 2) ^ 2 := pow_le_pow_left₀ h0 hrs 2
    have h2 : (√(δ / 2) / 2) ^ 2 = δ / 8 := by
      rw [div_pow, Real.sq_sqrt (by positivity)]; ring
    nlinarith
  · exact lt_min one_pos hpos
  · intro μ _ hμ
    exact lt_of_lt_of_le hμ (min_le_right _ _)

/-! ### Restriction of the secular Birkhoff expansion -/

theorem birkhoff_mono_radius {a b : ℕ} {P : ℝ → Phase (a + b) → ℝ}
    {V : Set (Fin a → ℝ)} {r r0 μ0 : ℝ}
    {P0 : ℝ → (Fin a → ℝ) → ℝ}
    {Ω : ℝ → (Fin a → ℝ) → (Fin b → ℝ)}
    {β : ℝ → (Fin a → ℝ) → Matrix (Fin b) (Fin b) ℝ}
    (hr : 0 < r) (hrr0 : r ≤ r0)
    (h : HasSecularBirkhoffForm P V r0 μ0 P0 Ω β) :
    HasSecularBirkhoffForm P V r μ0 P0 Ω β := by
  intro μ hμ I hI
  obtain ⟨h1, h2⟩ := h μ hμ I hI
  refine ⟨fun p q hpq => h1 p q fun j => ?_, fun ε hε => ?_⟩
  · exact (hpq j).trans_le (pow_le_pow_left₀ hr.le hrr0 2)
  · obtain ⟨δ, hδ, hδr, hδ'⟩ := h2 ε hε
    refine ⟨min δ r, lt_min hδ hr, min_le_right _ _, fun p q hpq => hδ' p q fun j => ?_⟩
    have hm : min δ r ≤ δ := min_le_left _ _
    exact (hpq j).trans_le (pow_le_pow_left₀ (lt_min hδ hr).le hm 2)

end PlanarAssembly
end KAM.Planetary
end
