/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.HoloExt.Point
public import HD11964.CoverPlan

/-!
# HD 11964: `P_C` at real points; the per-slab strips; the cell-to-slab check (HD11964-HOLO)

Part 2 of `HD11964.HoloExt` (the facade keeps the public names).

* `planetChartC_ofReal`, `pertCC_realVar_ofReal` (1c-iii): at real points the complexified chart
  is LP's real chart and `P_C` is `P = μ fMov(Ψ)`.
* `chartOkAt_of_keplerData`, `chartPertExt_of`, `chartPertExt_HD` / `_A` / `_B`: (1c) in the
  drafted form on the uniform and the per-slab strips, with (1b) as the named premise
  `NoCollisionOn`.
* `Slab.cells`, `Slab.xiOk`, `fitPlan_xiOk`, `fitPlan_slabs_xi`: the decided cell-to-slab check.
-/

@[expose] public noncomputable section

open Set Filter KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.Application.LambdaDrift
open scoped Real Topology

namespace HD11964.Cover

/-! ### (1c-iii) Agreement at real points -/

theorem ofReal_cpow_half {r : ℝ} (hr : 0 ≤ r) : (r : ℂ) ^ (1 / 2 : ℂ) = ((√r : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hr]; norm_num

theorem ofReal_cpow_neg_half {r : ℝ} (hr : 0 ≤ r) :
    (r : ℂ) ^ (-(1 / 2 : ℂ)) = (((√r)⁻¹ : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hr, Complex.ofReal_cpow hr]; norm_num

/-- **One planet's complexified chart at a real point is LP's real chart** (`κ = 1`). -/
theorem planetChartC_ofReal {y₀ m lam Λ ξ η : ℝ} (hΛ : 0 < Λ) (hΓ : (ξ ^ 2 + η ^ 2) / 2 < Λ)
    (h : PlanetOk y₀ (lam : ℂ) (Λ : ℂ) (ξ : ℂ) (η : ℂ)) :
    planetChartC y₀ m lam Λ ξ η =
      (fun i => ((poincare m 1 (![lam, ξ], ![Λ, η])).1 i : ℂ),
        fun i => ((poincare m 1 (![lam, ξ], ![Λ, η])).2 i : ℂ)) := by
  set b : Phase 2 := (![lam, ξ], ![Λ, η]) with hbdef
  have hG : poincareGamma b = (ξ ^ 2 + η ^ 2) / 2 := by simp [poincareGamma, hbdef]
  have hr : 0 ≤ (1 - poincareGamma b / (2 * Λ)) / Λ := by
    apply div_nonneg _ hΛ.le
    rw [sub_nonneg, div_le_one (by linarith), hG]
    have : 0 ≤ (ξ ^ 2 + η ^ 2) / 2 := by positivity
    linarith
  have hrad : radC Λ ξ η = (((1 - poincareGamma b / (2 * Λ)) / Λ : ℝ) : ℂ) := by
    rw [hG]; simp only [radC]; push_cast; ring
  have hV : ∀ i, poincareV b i = √((1 - poincareGamma b / (2 * Λ)) / Λ) * ![ξ, η] i := by
    intro i; simp [poincareV, hbdef]
  have hv : eccC Λ ξ η = fun i => ((poincareV b i : ℝ) : ℂ) := by
    funext i
    rw [eccC, hrad, ofReal_cpow_half hr, hV]
    fin_cases i <;> simp
  have hpl : planeLength (poincareV b) < 1 := by
    have hc := h.contraction
    rw [hv] at hc
    simp only [Complex.norm_real, Real.norm_eq_abs] at hc
    have h1 : 1 ≤ Real.cosh y₀ := Real.one_le_cosh y₀
    have h2 : |poincareV b 0| + |poincareV b 1| < 1 := by
      nlinarith [abs_nonneg (poincareV b 0), abs_nonneg (poincareV b 1)]
    have hsq : planeSq (poincareV b) ≤ (|poincareV b 0| + |poincareV b 1|) ^ 2 := by
      simp only [planeSq, Fin.sum_univ_two, add_sq, sq_abs]
      nlinarith [abs_nonneg (poincareV b 0), abs_nonneg (poincareV b 1)]
    unfold planeLength
    rw [Real.sqrt_lt' one_pos]
    nlinarith [abs_nonneg (poincareV b 0), abs_nonneg (poincareV b 1)]
  have hF : eccLongC y₀ lam Λ ξ η = ((poincareF b : ℝ) : ℂ) := by
    symm
    refine (eccLongC_spec h).2.2 _ (by simpa using h.y_pos.le) ?_
    have h1 := KAM.Kepler.keplerPhi_keplerLong hpl (b.1 0)
    unfold KAM.Kepler.keplerPhi at h1
    have h2 := congrArg (fun r : ℝ => (r : ℂ)) h1
    simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_sin,
      Complex.ofReal_cos] at h2
    rw [hv]
    unfold KAM.Kepler.keplerOp poincareF
    simpa [hbdef] using h2
  have hk : kC Λ ξ η = ((poincareK b : ℝ) : ℂ) := by
    simp only [kC, poincareK, hG]; push_cast
    simp [hbdef]
  have hvc : vcC y₀ lam Λ ξ η = ((planeDot (poincareV b) (orbitalUnit (poincareF b)) : ℝ) : ℂ) := by
    unfold vcC
    rw [hv, hF]
    simp [planeDot, Fin.sum_univ_two, orbitalUnit]
  have hΛb : b.2 0 = Λ := by simp [hbdef]
  rw [planetChartC_eq, hvc, hk, hF, hv]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · fin_cases i <;>
      simp only [poincare, orbitalUnit, hΛb, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
        smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta,
        Fin.mk_one, Fin.isValue, mul_one] <;> push_cast <;> ring
  · fin_cases i <;>
      simp only [poincare, orbitalUnit, quarterTurn, KAM.Kepler.keplerJac, hΛb, Pi.smul_apply,
        Pi.sub_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
        Fin.zero_eta, Fin.mk_one, Fin.isValue, mul_one] <;> push_cast <;> ring

/-- `P = μ fMov(Ψ)` on the chart domain. -/
theorem chartPert_eq_fMov {w : Phase (2 + 2)} (hw : w ∈ poincareProdDom 2) :
    chartPert nu mu w = mu * fMov 1 1 nu (poincareProd nu 1 w) := by
  unfold chartPert liftChartHam
  rw [lpChart_hamiltonian nu_pos mu hw]; ring

/-- `fMov` for two planets. -/
theorem fMov_two (z : Phase (2 * 2)) :
    fMov 1 1 nu z = planeSq (bodyVector z.2 0 + bodyVector z.2 1) / 2 -
      nu 0 * nu 1 / planeLength (bodyVector z.1 0 - bodyVector z.1 1) := by
  have e0 : Finset.univ.filter (fun j : Fin 2 => (0 : Fin 2) < j) = {1} := by decide
  have e1 : Finset.univ.filter (fun j : Fin 2 => (1 : Fin 2) < j) = ∅ := by decide
  simp only [fMov, pairPotential, Fin.sum_univ_two, e0, e1, Finset.sum_singleton,
    Finset.sum_empty]
  ring

theorem withAngles_mem_dom {w : Phase (2 + 2)} (hw : w ∈ poincareProdDom 2) (lam : Fin 2 → ℝ) :
    withAngles w lam ∈ poincareProdDom 2 := by
  intro i
  have h := hw i
  simpa [poincareDom, poincareGamma, planetBlock, withAngles_fst_slow, withAngles_snd] using h

/-- **(1c-iii) At real points `P_C` is `P`.** -/
theorem pertCC_realVar_ofReal {y : Fin 2 → ℝ} {w : Phase (2 + 2)}
    (hw : w ∈ poincareProdDom 2) (t : Fin 2 → ℝ) (h : ChartOkAt y (realVar w fun j => (t j : ℂ))) :
    pertCC y (realVar w fun j => (t j : ℂ)) =
      (chartPert nu mu (withAngles w fun j => 2 * π * t j) : ℂ) := by
  set w' := withAngles w fun j => 2 * π * t j with hw'def
  have hw' : w' ∈ poincareProdDom 2 := withAngles_mem_dom hw _
  have hblk : ∀ j, qpCC y (realVar w fun j => (t j : ℂ)) j =
      (fun i => ((poincare (nu j) 1 (planetBlock w' j)).1 i : ℂ),
        fun i => ((poincare (nu j) 1 (planetBlock w' j)).2 i : ℂ)) := by
    intro j
    have hb := hw' j
    have hpb : planetBlock w' j = (![2 * π * t j, slow w.1 j], ![fast w.2 j, slow w.2 j]) := by
      simp [planetBlock, hw'def, withAngles_fst_fast, withAngles_fst_slow, withAngles_snd]
    rw [hpb] at hb ⊢
    obtain ⟨hΛ, hΓ⟩ := hb
    simp only [poincareGamma] at hΓ
    have hlam : ((2 * π * t j : ℝ) : ℂ) = 2 * π * (t j : ℂ) := by push_cast; ring
    have hj := h j
    simp only [realVar] at hj
    rw [← hlam] at hj
    have := planetChartC_ofReal (m := nu j) (by simpa using hΛ) (by simpa using hΓ) hj
    simp only [qpCC, realVar, ← hlam]
    simpa using this
  have hq := fun j => poincareProd_block nu 1 w' j
  rw [chartPert_eq_fMov hw', fMov_two]
  have hQ : ∀ j, bodyVector (poincareProd nu 1 w').1 j = (poincare (nu j) 1 (planetBlock w' j)).1 :=
    fun j => congrArg Prod.fst (hq j)
  have hP : ∀ j, bodyVector (poincareProd nu 1 w').2 j = (poincare (nu j) 1 (planetBlock w' j)).2 :=
    fun j => congrArg Prod.snd (hq j)
  rw [hQ, hQ, hP, hP]
  have hD : distSqCC y (realVar w fun j => (t j : ℂ)) = ((planeSq
      ((poincare (nu 0) 1 (planetBlock w' 0)).1 - (poincare (nu 1) 1 (planetBlock w' 1)).1) :
        ℝ) : ℂ) := by
    simp only [distSqCC, hblk]
    simp [planeSq, Fin.sum_univ_two]
  have hD0 : 0 ≤ planeSq ((poincare (nu 0) 1 (planetBlock w' 0)).1 -
      (poincare (nu 1) 1 (planetBlock w' 1)).1) := Finset.sum_nonneg fun k _ => sq_nonneg _
  simp only [pertCC, hD, ofReal_cpow_neg_half hD0, hblk]
  push_cast
  simp only [planeSq, planeLength, Fin.sum_univ_two, Pi.add_apply, Pi.sub_apply]
  push_cast
  ring

/-! ### (1c) on the per-slab strips, with (1b) as a named premise -/

/-- **(1b) as a named premise**: no complex collision on the strip `ρ` at the real state `w`
(to be discharged by the layer's certified enclosure of `d²`, e.g. `noCollision_of_enclosure`). -/
def NoCollisionOn (y ρ : Fin 2 → ℝ) (w : Phase (2 + 2)) : Prop :=
  ∀ θ ∈ stripA ρ, 0 < (distSqC y w θ).re

/-- (1c) in the drafted form: holomorphic and `1`-periodic on the strip, `P` at real angles. -/
def ChartPertExt (y ρ : Fin 2 → ℝ) (w : Phase (2 + 2)) : Prop :=
  DifferentiableOn ℂ (chartPertC y w) (stripA ρ) ∧
    (∀ (j : Fin 2) (θ : Fin 2 → ℂ), θ ∈ stripA ρ →
      chartPertC y w (θ + Pi.single j 1) = chartPertC y w θ) ∧
    ∀ t : Fin 2 → ℝ, chartPertC y w (fun j => (t j : ℂ)) =
      (chartPert nu mu (withAngles w fun j => 2 * π * t j) : ℂ)

theorem holoDomHD_subset_dom : holoDomHD ⊆ poincareProdDom 2 := fun _ hw =>
  openHD_subset_dom (region_subset_openHD (by norm_num) hw.1)

/-- The eccentricity vector at a real point is LP's `β (ξ, η)`. -/
theorem eccC_ofReal {Λ ξ η : ℝ} (hΛ : 0 < Λ) (hΓ : (ξ ^ 2 + η ^ 2) / 2 < Λ) :
    eccC Λ ξ η = ![((lpEccScale Λ ((ξ ^ 2 + η ^ 2) / 2) * ξ : ℝ) : ℂ),
      ((lpEccScale Λ ((ξ ^ 2 + η ^ 2) / 2) * η : ℝ) : ℂ)] := by
  have hr : 0 ≤ (1 - (ξ ^ 2 + η ^ 2) / 2 / (2 * Λ)) / Λ := by
    apply div_nonneg _ hΛ.le
    rw [sub_nonneg, div_le_one (by linarith)]
    have : 0 ≤ (ξ ^ 2 + η ^ 2) / 2 := by positivity
    linarith
  have hrad : radC Λ ξ η = (((1 - (ξ ^ 2 + η ^ 2) / 2 / (2 * Λ)) / Λ : ℝ) : ℂ) := by
    simp only [radC]; push_cast; ring
  funext i
  rw [eccC, hrad, ofReal_cpow_half hr]
  fin_cases i <;> simp [lpEccScale]

/-- **The chart conditions on the strip from (1a)** at a real state of the chart domain. -/
theorem chartOkAt_of_keplerData {y ρ κ : Fin 2 → ℝ} {w : Phase (2 + 2)}
    (hw : w ∈ poincareProdDom 2)
    (hK : ∀ j, KAM.Kepler.KeplerData {lam : ℂ | |lam.im| < 2 * π * ρ j}
      (fun _ => ((lpEccScale (fast w.2 j) (lpGamma w j) * slow w.1 j : ℝ) : ℂ))
      (fun _ => ((lpEccScale (fast w.2 j) (lpGamma w j) * slow w.2 j : ℝ) : ℂ))
      (fun lam => lam) (y j) (κ j))
    {θ : Fin 2 → ℂ} (hθ : θ ∈ stripA ρ) : ChartOkAt y (realVar w θ) := by
  intro j
  obtain ⟨hΛ, hΓ⟩ := hw j
  have hΛ' : 0 < fast w.2 j := by simpa [planetBlock] using hΛ
  have hΓ' : ((slow w.1 j) ^ 2 + (slow w.2 j) ^ 2) / 2 < fast w.2 j := by
    simpa [poincareGamma, planetBlock] using hΓ
  have hv := eccC_ofReal hΛ' hΓ'
  have hG : lpGamma w j = ((slow w.1 j) ^ 2 + (slow w.2 j) ^ 2) / 2 := rfl
  have hmem : 2 * π * θ j ∈ {lam : ℂ | |lam.im| < 2 * π * ρ j} := by
    have h1 := hθ j
    have hpi : (0 : ℝ) < 2 * π := by positivity
    simp only [Set.mem_ofPred_eq]
    have e : (2 * (π : ℂ) * θ j).im = 2 * π * (θ j).im := by simp
    rw [e, abs_mul, abs_of_pos hpi]
    exact mul_lt_mul_of_pos_left h1 hpi
  have hinv := (hK j).invariant _ hmem
  have hcon := (hK j).contraction _ hmem
  rw [hG] at hinv hcon
  simp only [realVar]
  refine ⟨by exact_mod_cast hΛ'.ne', ?_, ?_, (hK j).y₀_pos, ?_, ?_⟩
  · have hpos : 0 < (1 - ((slow w.1 j) ^ 2 + (slow w.2 j) ^ 2) / 2 / (2 * fast w.2 j)) /
        fast w.2 j := by
      apply div_pos _ hΛ'
      rw [sub_pos, div_lt_one (by linarith)]
      have : 0 ≤ ((slow w.1 j) ^ 2 + (slow w.2 j) ^ 2) / 2 := by positivity
      linarith
    have e : radC (fast w.2 j) (slow w.1 j) (slow w.2 j) = (((1 - ((slow w.1 j) ^ 2 +
        (slow w.2 j) ^ 2) / 2 / (2 * fast w.2 j)) / fast w.2 j : ℝ) : ℂ) := by
      simp only [radC]; push_cast; ring
    rw [e]
    exact Complex.ofReal_mem_slitPlane.2 hpos
  · have e : 1 + kC (fast w.2 j) (slow w.1 j) (slow w.2 j) = ((2 - ((slow w.1 j) ^ 2 +
        (slow w.2 j) ^ 2) / 2 / fast w.2 j : ℝ) : ℂ) := by
      simp only [kC]; push_cast; ring
    rw [e]
    have : ((slow w.1 j) ^ 2 + (slow w.2 j) ^ 2) / 2 / fast w.2 j < 1 := by
      rw [div_lt_one hΛ']; exact hΓ'
    exact_mod_cast (by linarith : (0 : ℝ) < 2 - ((slow w.1 j) ^ 2 + (slow w.2 j) ^ 2) / 2 /
      fast w.2 j).ne'
  · rw [hv]
    simpa using hinv
  · rw [hv]
    have := (hK j).κ_lt
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hcon ⊢
    linarith

/-- **(1c) on a strip from (1a) and (1b)**: holomorphic, periodic, `P` at real angles. -/
theorem chartPertExt_of {y ρ κ : Fin 2 → ℝ} {w : Phase (2 + 2)} (hw : w ∈ poincareProdDom 2)
    (hρ : ∀ j, 0 < ρ j)
    (hK : ∀ j, KAM.Kepler.KeplerData {lam : ℂ | |lam.im| < 2 * π * ρ j}
      (fun _ => ((lpEccScale (fast w.2 j) (lpGamma w j) * slow w.1 j : ℝ) : ℂ))
      (fun _ => ((lpEccScale (fast w.2 j) (lpGamma w j) * slow w.2 j : ℝ) : ℂ))
      (fun lam => lam) (y j) (κ j))
    (hcol : NoCollisionOn y ρ w) : ChartPertExt y ρ w := by
  have e : chartPertC y w = pertCC y ∘ fun θ => realVar w θ :=
    funext fun θ => chartPertC_eq_pertCC y w θ
  refine ⟨fun θ hθ => ?_, fun j θ hθ => ?_, fun t => ?_⟩
  · have ha := pertCC_analyticAt (chartOkAt_of_keplerData hw hK hθ) (hcol θ hθ)
    have hr : AnalyticAt ℂ (fun θ : Fin 2 → ℂ => realVar w θ) θ :=
      analyticAt_id.prod analyticAt_const
    rw [e]
    exact (ha.comp hr).differentiableAt.differentiableWithinAt
  · rw [chartPertC_eq_pertCC, chartPertC_eq_pertCC]
    exact pertCC_add_single (chartOkAt_of_keplerData hw hK hθ) j
  · rw [chartPertC_eq_pertCC]
    exact pertCC_realVar_ofReal hw t (chartOkAt_of_keplerData hw hK (ofReal_mem_stripA hρ t))

/-- **(1c), uniform strip** `ρ = (1/40, 3/20)` (slab 6, and all of `holoDomHD`). -/
theorem chartPertExt_HD {w : Phase (2 + 2)} (hw : w ∈ holoDomHD)
    (hcol : NoCollisionOn yHolo rhoHolo w) : ChartPertExt yHolo rhoHolo w :=
  chartPertExt_of (holoDomHD_subset_dom hw) (fun j => by fin_cases j <;> norm_num [rhoHolo])
    (fun j => keplerData_HD j hw) hcol

/-- **(1c), slabs 0–4** (`|ξ_c| ≤ 0.1431`): `ρ = (7/200, 3/20)`. -/
theorem chartPertExt_HD_A {w : Phase (2 + 2)} (hw : w ∈ holoDomHD)
    (hξ : |slow w.1 0| ≤ 1431 / 10000) (hcol : NoCollisionOn yHoloA rhoHoloA w) :
    ChartPertExt yHoloA rhoHoloA w :=
  chartPertExt_of (holoDomHD_subset_dom hw) (fun j => by fin_cases j <;> norm_num [rhoHoloA])
    (fun j => keplerData_HD_A j hw hξ) hcol

/-- **(1c), slab 5** (`|ξ_c| ≤ 0.1612`): `ρ = (3/100, 3/20)`. -/
theorem chartPertExt_HD_B {w : Phase (2 + 2)} (hw : w ∈ holoDomHD)
    (hξ : |slow w.1 0| ≤ 1612 / 10000) (hcol : NoCollisionOn yHoloB rhoHoloB w) :
    ChartPertExt yHoloB rhoHoloB w :=
  chartPertExt_of (holoDomHD_subset_dom hw) (fun j => by fin_cases j <;> norm_num [rhoHoloB])
    (fun j => keplerData_HD_B j hw hξ) hcol

/-! ### The cell-to-slab check -/

/-- The cells of one slab (in `CoverPlan.cells` order). -/
def Slab.cells (s : Slab) : List AffineCell := s.disc.toList ++ (s.upper ++ s.lower).map (·.cell)

/-- Decidable: every cell of the slab has `|c₂| + |h₂| ≤ X` (the `ξ_c` axis). -/
def Slab.xiOk (s : Slab) (X : ℚ) : Bool := s.cells.all fun k => decide (|k.c 2| + |k.h 2| ≤ X)

theorem abs_xi_le_of_mem_toSet {k : AffineCell} {w : Phase (2 + 2)} (hw : w ∈ k.toSet) :
    |slow w.1 0| ≤ |((k.c 2 : ℚ) : ℝ)| + |((k.h 2 : ℚ) : ℝ)| := by
  obtain ⟨u, hu, he⟩ := hw
  have h2 := congrFun he 2
  simp only [cellCoord, AffineCell.map] at h2
  simp only [Matrix.cons_val, Fin.isValue] at h2
  rw [h2]
  calc |((k.c 2 : ℚ) : ℝ) + ((k.h 2 : ℚ) : ℝ) * u 2| ≤
        |((k.c 2 : ℚ) : ℝ)| + |((k.h 2 : ℚ) : ℝ)| * |u 2| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ |((k.c 2 : ℚ) : ℝ)| + |((k.h 2 : ℚ) : ℝ)| * 1 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (hu 2) (abs_nonneg _))
    _ = _ := by ring

theorem abs_xi_le_of_xiOk {s : Slab} {X : ℚ} (hs : s.xiOk X = true) {k : AffineCell}
    (hk : k ∈ s.cells) {w : Phase (2 + 2)} (hw : w ∈ k.toSet) : |slow w.1 0| ≤ (X : ℝ) := by
  have h := List.all_eq_true.1 hs k hk
  have hq : |k.c 2| + |k.h 2| ≤ X := of_decide_eq_true h
  have hq' : ((|k.c 2| + |k.h 2| : ℚ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast hq
  push_cast at hq'
  exact (abs_xi_le_of_mem_toSet hw).trans hq'

/-- The decided check on `fitPlan`: slabs 0–4 within `0.1431`, slab 5 within `0.1612`. -/
theorem fitPlan_xiOk : ((fitPlan.slabs.take 5).all fun s => s.xiOk (1431 / 10000)) = true ∧
    (((fitPlan.slabs.drop 5).take 1).all fun s => s.xiOk (1612 / 10000)) = true :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- **The cell-to-slab statement**: every cell of slabs 0–4 of `fitPlan` lies in
`|ξ_c| ≤ 0.1431`, every cell of slab 5 in `|ξ_c| ≤ 0.1612`. -/
theorem fitPlan_slabs_xi :
    (∀ s ∈ fitPlan.slabs.take 5, ∀ k ∈ s.cells, ∀ w ∈ k.toSet, |slow w.1 0| ≤ 1431 / 10000) ∧
    (∀ s ∈ (fitPlan.slabs.drop 5).take 1, ∀ k ∈ s.cells, ∀ w ∈ k.toSet,
      |slow w.1 0| ≤ 1612 / 10000) := by
  refine ⟨fun s hs k hk w hw => ?_, fun s hs k hk w hw => ?_⟩
  · exact (abs_xi_le_of_xiOk (List.all_eq_true.1 fitPlan_xiOk.1 s hs) hk hw).trans
      (by norm_num)
  · exact (abs_xi_le_of_xiOk (List.all_eq_true.1 fitPlan_xiOk.2 s hs) hk hw).trans
      (by norm_num)

end HD11964.Cover

end
