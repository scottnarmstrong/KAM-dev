/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Poincare.Product
public import KAM.Planetary.Hamiltonian.Chart

/-!
# The oscillator polar chart and the full lattice

Blueprint P, Part 7 (`bpP:p7:lattice`): the polar chart `Θ_n` with `(ξ, η) = √(2R) (sin ψ, cos ψ)`
on the slow block, and the composite `Φ_n = Ψ^{(n)} ∘ Θ_n`.  Everything is blockwise: `polarMap`
is the one-planet polar map `polar1` on each `planetBlock`, so analyticity and symplecticity are
inherited from the explicit one-planet derivative.  The full lattice is `fullShift k = (2π k, 0)`,
`k : Fin (n + n) → ℤ`; `fullShift` and `angleScale` (`S_c`) are owned by Part 1
(`KAM.Planetary.Hamiltonian.Chart`).
-/

@[expose] public noncomputable section

open Set Metric Real
open scoped ContDiff

namespace KAM.Planetary

open KAM KAM.Kepler

section PolarChart

variable {n : ℕ}

/-- `bpP:p7:lattice`: the oscillator polar chart `Θ_n` and `Φ_n = Ψ^{(n)} ∘ Θ_n`
(coordinates `z = ((φ, ψ), (I, R))`). -/
def polarDom (n : ℕ) : Set (Phase (n + n)) :=
  {z | ∀ i, 0 < fast z.2 i ∧ 0 < slow z.2 i ∧ slow z.2 i < fast z.2 i}

def polarMap (z : Phase (n + n)) : Phase (n + n) :=
  assemble (fast z.2) (fast z.1) (fun i => √(2 * slow z.2 i) * Real.cos (slow z.1 i))
    (fun i => √(2 * slow z.2 i) * Real.sin (slow z.1 i))

/-! ### Block calculus -/

/-- The one-planet polar map `(ψ, R) ↦ √(2R) (sin ψ, cos ψ)` (with `(λ, Λ)` untouched). -/
def polar1 (w : Phase 2) : Phase 2 :=
  (![w.1 0, √(2 * w.2 1) * Real.sin (w.1 1)], ![w.2 0, √(2 * w.2 1) * Real.cos (w.1 1)])

/-- The one-planet polar domain. -/
def polarDom1 : Set (Phase 2) := {w | 0 < w.2 0 ∧ 0 < w.2 1 ∧ w.2 1 < w.2 0}

theorem planetBlock_polarMap (z : Phase (n + n)) (i : Fin n) :
    planetBlock (polarMap z) i = polar1 (planetBlock z i) := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> fin_cases k <;>
    simp [planetBlock, polarMap, polar1, assemble, fast, slow, Fin.append_left]

theorem mem_polarDom_iff {z : Phase (n + n)} : z ∈ polarDom n ↔ ∀ i, planetBlock z i ∈ polarDom1 := by
  simp [polarDom, polarDom1, planetBlock, fast, slow]

/-- Reassembling the blocks of a point gives the point back. -/
theorem unblock_planetBlock (z : Phase (n + n)) : unblock (fun i => planetBlock z i) = z := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp [unblock, planetBlock, fast, slow, Fin.append_left]

theorem polarMap_eq_unblock (z : Phase (n + n)) :
    polarMap z = unblock fun i => polar1 (planetBlock z i) := by
  conv_lhs => rw [← unblock_planetBlock (polarMap z)]
  congr 1
  funext i
  exact planetBlock_polarMap z i

/-- `unblock` as a linear map. -/
def unblockLin : (Fin n → Phase 2) →ₗ[ℝ] Phase (n + n) where
  toFun := unblock
  map_add' P Q := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [unblock, Fin.append_left]
  map_smul' c P := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [unblock, Fin.append_left]

/-- `unblock` as a continuous linear map. -/
def unblockCLM : (Fin n → Phase 2) →L[ℝ] Phase (n + n) :=
  LinearMap.toContinuousLinearMap unblockLin

theorem unblockCLM_apply (P : Fin n → Phase 2) : unblockCLM P = unblock P := rfl

/-! ### The one-planet polar map -/

private theorem hasFDerivAt_polar1 {w : Phase 2} (hR : 0 < w.2 1) :
    ∃ L : Phase 2 →L[ℝ] Phase 2, HasFDerivAt polar1 L w ∧ ∀ u : Phase 2,
      L u = (![u.1 0, (√(2 * w.2 1))⁻¹ * Real.sin (w.1 1) * u.2 1 +
                √(2 * w.2 1) * Real.cos (w.1 1) * u.1 1],
             ![u.2 0, (√(2 * w.2 1))⁻¹ * Real.cos (w.1 1) * u.2 1 -
                √(2 * w.2 1) * Real.sin (w.1 1) * u.1 1]) := by
  let c : Phase 2 →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).comp (ContinuousLinearMap.fst ℝ _ _)
  let r : Phase 2 →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).comp (ContinuousLinearMap.snd ℝ _ _)
  let a : Phase 2 →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).comp (ContinuousLinearMap.fst ℝ _ _)
  let b : Phase 2 →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).comp (ContinuousLinearMap.snd ℝ _ _)
  have h2R : (2 * w.2 1) ≠ 0 := by positivity
  have hs : HasFDerivAt (fun w : Phase 2 => √(2 * w.2 1))
      ((1 / (2 * √(2 * w.2 1))) • ((2 : ℝ) • r)) w :=
    HasFDerivAt.sqrt (f := fun w : Phase 2 => 2 * w.2 1) (r.hasFDerivAt.const_mul 2) h2R
  have hsin : HasFDerivAt (fun w : Phase 2 => Real.sin (w.1 1)) (Real.cos (w.1 1) • c) w :=
    c.hasFDerivAt.sin
  have hcos : HasFDerivAt (fun w : Phase 2 => Real.cos (w.1 1)) (-Real.sin (w.1 1) • c) w :=
    c.hasFDerivAt.cos
  have hg1 := hs.mul hsin
  have hg2 := hs.mul hcos
  let X1 : Phase 2 →L[ℝ] ℝ :=
    (√(2 * w.2 1) * Real.cos (w.1 1)) • c + (Real.sin (w.1 1) * (1 / (2 * √(2 * w.2 1)) * 2)) • r
  let X2 : Phase 2 →L[ℝ] ℝ :=
    (-(√(2 * w.2 1) * Real.sin (w.1 1))) • c + (Real.cos (w.1 1) * (1 / (2 * √(2 * w.2 1)) * 2)) • r
  let L : Phase 2 →L[ℝ] Phase 2 :=
    (ContinuousLinearMap.pi (![a, X1] : Fin 2 → Phase 2 →L[ℝ] ℝ)).prod
      (ContinuousLinearMap.pi (![b, X2] : Fin 2 → Phase 2 →L[ℝ] ℝ))
  refine ⟨L, ?_, fun u => ?_⟩
  · refine HasFDerivAt.prodMk ?_ ?_
    · refine hasFDerivAt_pi'.2 fun k => ?_
      fin_cases k
      · exact a.hasFDerivAt
      · refine hg1.congr_fderiv (ContinuousLinearMap.ext fun u => ?_)
        simp [X1, c, r]
        ring
    · refine hasFDerivAt_pi'.2 fun k => ?_
      fin_cases k
      · exact b.hasFDerivAt
      · refine hg2.congr_fderiv (ContinuousLinearMap.ext fun u => ?_)
        simp [X2, c, r]
        ring
  · refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> fin_cases k <;>
      simp [L, X1, X2, a, b, c, r] <;> field_simp <;> ring

private theorem fderiv_polar1_apply {w : Phase 2} (hR : 0 < w.2 1) (u : Phase 2) :
    fderiv ℝ polar1 w u =
      (![u.1 0, (√(2 * w.2 1))⁻¹ * Real.sin (w.1 1) * u.2 1 +
                √(2 * w.2 1) * Real.cos (w.1 1) * u.1 1],
       ![u.2 0, (√(2 * w.2 1))⁻¹ * Real.cos (w.1 1) * u.2 1 -
                √(2 * w.2 1) * Real.sin (w.1 1) * u.1 1]) := by
  obtain ⟨L, hL, hu⟩ := hasFDerivAt_polar1 hR
  rw [hL.fderiv, hu]

private theorem polar1_symplectic {w : Phase 2} (hw : w ∈ polarDom1) (u v : Phase 2) :
    symplecticForm (fderiv ℝ polar1 w u) (fderiv ℝ polar1 w v) = 1 * symplecticForm u v := by
  have hR : 0 < w.2 1 := hw.2.1
  rw [fderiv_polar1_apply hR, fderiv_polar1_apply hR]
  have hs : √(2 * w.2 1) * (√(2 * w.2 1))⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  have hsc := Real.sin_sq_add_cos_sq (w.1 1)
  simp only [symplecticForm, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (-(u.1 1 * v.2 1 - u.2 1 * v.1 1) * (Real.sin (w.1 1) ^ 2 + Real.cos (w.1 1) ^ 2)) * hs -
    (u.1 1 * v.2 1 - u.2 1 * v.1 1) * hsc

private theorem analyticAt_polar1 {w : Phase 2} (hR : 0 < w.2 1) : AnalyticAt ℝ polar1 w := by
  have hc : AnalyticAt ℝ (fun w : Phase 2 => w.1 1) w :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).comp
      (ContinuousLinearMap.fst ℝ _ _)).analyticAt w
  have hr : AnalyticAt ℝ (fun w : Phase 2 => w.2 1) w :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).comp
      (ContinuousLinearMap.snd ℝ _ _)).analyticAt w
  have ha : AnalyticAt ℝ (fun w : Phase 2 => w.1 0) w :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).comp
      (ContinuousLinearMap.fst ℝ _ _)).analyticAt w
  have hb : AnalyticAt ℝ (fun w : Phase 2 => w.2 0) w :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).comp
      (ContinuousLinearMap.snd ℝ _ _)).analyticAt w
  have hs : AnalyticAt ℝ (fun w : Phase 2 => √(2 * w.2 1)) w :=
    (((analyticAt_const.mul hr).contDiffAt (n := ω)).sqrt (by show 2 * w.2 1 ≠ 0; positivity)).analyticAt
  refine AnalyticAt.prod (AnalyticAt.pi fun k => ?_) (AnalyticAt.pi fun k => ?_)
  · fin_cases k
    · exact ha
    · exact hs.mul (Real.analyticAt_sin.comp hc)
  · fin_cases k
    · exact hb
    · exact hs.mul (Real.analyticAt_cos.comp hc)

theorem polarMap_eq_unblockCLM : (polarMap : Phase (n + n) → Phase (n + n)) =
    fun z => unblockCLM fun i => polar1 (blockCLM i z) := by
  funext z
  rw [polarMap_eq_unblock, unblockCLM_apply]
  simp [blockCLM_apply]

theorem analyticOnNhd_polarMap (n : ℕ) : AnalyticOnNhd ℝ (polarMap (n := n)) (polarDom n) := by
  intro z hz
  have h : AnalyticAt ℝ (fun z : Phase (n + n) => fun i => polar1 (blockCLM i z)) z :=
    analyticAt_pi_iff.2 fun i =>
      (analyticAt_polar1 (by simpa [blockCLM_apply] using (mem_polarDom_iff.1 hz i).2.1)).comp
        ((blockCLM i).analyticAt z)
  rw [polarMap_eq_unblockCLM]
  exact (unblockCLM.analyticAt _).comp h

theorem polarMap_mapsTo (n : ℕ) : MapsTo (polarMap (n := n)) (polarDom n) (poincareProdDom n) := by
  intro z hz i
  rw [planetBlock_polarMap]
  obtain ⟨h1, h2, h3⟩ := mem_polarDom_iff.1 hz i
  refine ⟨h1, ?_⟩
  simp only [polar1, poincareGamma]
  have hR : 0 ≤ 2 * (planetBlock z i).2 1 := by linarith
  have hsq := Real.sq_sqrt hR
  have hsc := Real.sin_sq_add_cos_sq ((planetBlock z i).1 1)
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  nlinarith [hsq, hsc]

theorem polarMap_symplectic (n : ℕ) : IsSymplecticOn 1 (polarMap (n := n)) (polarDom n) := by
  intro z hz u v
  have hd : ∀ i, HasFDerivAt polar1 (fderiv ℝ polar1 (planetBlock z i)) (blockCLM i z) := fun i => by
    rw [blockCLM_apply]
    exact (analyticAt_polar1 (mem_polarDom_iff.1 hz i).2.1).differentiableAt.hasFDerivAt
  have h1 : HasFDerivAt (fun z : Phase (n + n) => fun i => polar1 (blockCLM i z))
      (ContinuousLinearMap.pi fun i => (fderiv ℝ polar1 (planetBlock z i)).comp (blockCLM i)) z :=
    hasFDerivAt_pi'.2 fun i => by
      rw [ContinuousLinearMap.proj_pi]
      exact (hd i).comp z (blockCLM i).hasFDerivAt
  have h2 := unblockCLM.hasFDerivAt.comp z h1
  have h3 : HasFDerivAt (fun z : Phase (n + n) => unblockCLM fun i => polar1 (blockCLM i z)) _ z := h2
  rw [polarMap_eq_unblockCLM, h3.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply, unblockCLM_apply,
    blockCLM_apply, symplecticForm_blocks, planetBlock_unblock, one_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := polar1_symplectic (mem_polarDom_iff.1 hz i) (planetBlock u i) (planetBlock v i)
  rwa [one_mul] at this

/-! ### The full lattice -/

private theorem lat_sin (x : ℝ) (k : ℤ) : Real.sin (x + 2 * π * k) = Real.sin x := by
  rw [show x + 2 * π * k = x + k * (2 * π) by ring]
  exact Real.sin_add_int_mul_two_pi x k

private theorem lat_cos (x : ℝ) (k : ℤ) : Real.cos (x + 2 * π * k) = Real.cos x := by
  rw [show x + 2 * π * k = x + k * (2 * π) by ring]
  exact Real.cos_add_int_mul_two_pi x k

private theorem lat_exists_int {x y : ℝ} (hc : Real.cos x = Real.cos y)
    (hs : Real.sin x = Real.sin y) : ∃ k : ℤ, y = x + 2 * π * k := by
  have h : Real.cos (y - x) = 1 := by
    rw [Real.cos_sub, ← hc, ← hs]
    nlinarith [Real.cos_sq_add_sin_sq x]
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).1 h
  exact ⟨k, by linarith⟩

theorem polarDom_shift (k : Fin (n + n) → ℤ) {z : Phase (n + n)} (hz : z ∈ polarDom n) :
    z + fullShift k ∈ polarDom n := by
  intro i
  simpa [fullShift, fast, slow] using hz i

theorem polarMap_shift (k : Fin (n + n) → ℤ) (z : Phase (n + n)) :
    polarMap (z + fullShift k) =
      polarMap z + fastShift (a := n) (b := n) (fun i => k (Fin.castAdd n i)) := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp [polarMap, assemble, fullShift, fastShift, fast, slow, Fin.append_left,
      lat_sin, lat_cos]

private theorem polar_norm_sq {R : ℝ} (hR : 0 ≤ R) (ψ : ℝ) :
    (√(2 * R) * Real.cos ψ) ^ 2 + (√(2 * R) * Real.sin ψ) ^ 2 = 2 * R := by
  rw [mul_pow, mul_pow, ← mul_add, Real.sq_sqrt (by linarith), add_comm, Real.sin_sq_add_cos_sq,
    mul_one]

theorem polarMap_eq_shift {z z' : Phase (n + n)} (hz : z ∈ polarDom n) (hz' : z' ∈ polarDom n)
    {k' : Fin n → ℤ} (h : polarMap z' = polarMap z + fastShift (a := n) (b := n) k') :
    ∃ k : Fin (n + n) → ℤ, z' = z + fullShift k := by
  have hΛ : ∀ i, fast z'.2 i = fast z.2 i := fun i => by
    have := congrArg (fun y : Phase (n + n) => fast y.2 i) h
    simpa [polarMap, assemble, fast, fastShift, Fin.append_left] using this
  have hp : ∀ i, √(2 * slow z'.2 i) * Real.cos (slow z'.1 i) =
      √(2 * slow z.2 i) * Real.cos (slow z.1 i) := fun i => by
    have := congrArg (fun y : Phase (n + n) => slow y.2 i) h
    simpa [polarMap, assemble, slow, fastShift, Fin.append_right] using this
  have hq : ∀ i, √(2 * slow z'.2 i) * Real.sin (slow z'.1 i) =
      √(2 * slow z.2 i) * Real.sin (slow z.1 i) := fun i => by
    have := congrArg (fun y : Phase (n + n) => slow y.1 i) h
    simpa [polarMap, assemble, slow, fastShift, Fin.append_right] using this
  have hφ : ∀ i, fast z'.1 i = fast z.1 i + 2 * π * (k' i : ℝ) := fun i => by
    have := congrArg (fun y : Phase (n + n) => fast y.1 i) h
    simpa [polarMap, assemble, fast, fastShift, Fin.append_left] using this
  have hR : ∀ i, slow z'.2 i = slow z.2 i := fun i => by
    have h1 := polar_norm_sq (hz' i).2.1.le (slow z'.1 i)
    have h2 := polar_norm_sq (hz i).2.1.le (slow z.1 i)
    rw [hp i, hq i, h2] at h1
    linarith
  have hψ : ∀ i, ∃ j : ℤ, slow z'.1 i = slow z.1 i + 2 * π * j := fun i => by
    have hpos : 0 < √(2 * slow z.2 i) := Real.sqrt_pos.2 (by have := (hz i).2.1; linarith)
    have hc : Real.cos (slow z'.1 i) = Real.cos (slow z.1 i) := by
      have := hp i
      rw [hR i] at this
      exact mul_left_cancel₀ hpos.ne' this
    have hs : Real.sin (slow z'.1 i) = Real.sin (slow z.1 i) := by
      have := hq i
      rw [hR i] at this
      exact mul_left_cancel₀ hpos.ne' this
    exact lat_exists_int hc.symm hs.symm
  choose j hj using hψ
  refine ⟨Fin.append k' j, Prod.ext (funext fun idx => ?_) (funext fun idx => ?_)⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) idx
    · simpa [fast, fullShift, Fin.append_left] using hφ i
    · simpa [slow, fullShift, Fin.append_right] using hj i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) idx
    · simpa [fast, fullShift] using hΛ i
    · simpa [slow, fullShift] using hR i


/-! ### The composite chart `Φ_n = Ψ^{(n)} ∘ Θ_n` -/

theorem poincareProd_polar_symplectic {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i) (hκ : 0 < κ) :
    IsSymplecticOn 1 (poincareProd m κ ∘ polarMap) (polarDom n) := by
  have := (polarMap_symplectic n).comp (poincareProd_symplectic hm hκ)
    (fun z hz => (analyticOnNhd_polarMap n z hz).differentiableAt)
    (fun w hw => (analyticOnNhd_poincareProd hm hκ w hw).differentiableAt) (polarMap_mapsTo n)
  simpa using this

theorem analyticOnNhd_poincareProd_polar {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i)
    (hκ : 0 < κ) : AnalyticOnNhd ℝ (poincareProd m κ ∘ polarMap) (polarDom n) :=
  (analyticOnNhd_poincareProd hm hκ).comp (analyticOnNhd_polarMap n) (polarMap_mapsTo n)

theorem poincareProd_polar_lattice {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i) (hκ : 0 < κ)
    {z z' : Phase (n + n)} (hz : z ∈ polarDom n) (hz' : z' ∈ polarDom n) (k : Fin (n + n) → ℤ) :
    poincareProd m κ (polarMap (z + fullShift k)) = poincareProd m κ (polarMap z) ∧
    (poincareProd m κ (polarMap z') = poincareProd m κ (polarMap z) →
      ∃ k : Fin (n + n) → ℤ, z' = z + fullShift k) := by
  refine ⟨?_, fun h => ?_⟩
  · rw [polarMap_shift]
    exact (poincareProd_lattice hm hκ (polarMap_mapsTo n hz) _).2
  · obtain ⟨k', hk'⟩ := (poincareProd_eq_iff hm hκ (polarMap_mapsTo n hz)
      (polarMap_mapsTo n hz')).1 h.symm
    exact polarMap_eq_shift hz hz' hk'

/-- Period-one version: `Φ_n ∘ S_{2π}` is a `2π`-chart satisfying (Q1), (Q2) for the lattice `(k, 0)`. -/
theorem poincareProd_polar_periodOne_symplectic {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i)
    (hκ : 0 < κ) :
    IsSymplecticOn (2 * π) (poincareProd m κ ∘ polarMap ∘ angleScale (2 * π))
      (angleScale (2 * π) ⁻¹' polarDom n) := by
  have hc := isChart_angleScale (d := n + n) (c := 2 * π) (by positivity)
  have h1 : IsSymplecticOn (2 * π) (angleScale (2 * π)) (angleScale (2 * π) ⁻¹' polarDom n) :=
    fun z _ => hc.symplectic z (mem_univ z)
  have := h1.comp (poincareProd_polar_symplectic hm hκ)
    (fun z _ => (hc.analyticOnNhd z (mem_univ z)).differentiableAt)
    (fun w hw => (analyticOnNhd_poincareProd_polar hm hκ w hw).differentiableAt)
    (fun z hz => hz)
  simpa [Function.comp_assoc] using this

theorem poincareProd_polar_periodOne_lattice {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i)
    (hκ : 0 < κ) {z z' : Phase (n + n)} (hz : angleScale (2 * π) z ∈ polarDom n)
    (hz' : angleScale (2 * π) z' ∈ polarDom n) (k : Fin (n + n) → ℤ) :
    angleScale (2 * π) (z + ((fun i => (k i : ℝ)), 0)) ∈ polarDom n ∧
    poincareProd m κ (polarMap (angleScale (2 * π) (z + ((fun i => (k i : ℝ)), 0)))) =
      poincareProd m κ (polarMap (angleScale (2 * π) z)) ∧
    (poincareProd m κ (polarMap (angleScale (2 * π) z')) =
        poincareProd m κ (polarMap (angleScale (2 * π) z)) →
      ∃ k : Fin (n + n) → ℤ, z' = z + ((fun i => (k i : ℝ)), 0)) := by
  have hsh : angleScale (2 * π) (z + ((fun i => (k i : ℝ)), 0)) =
      angleScale (2 * π) z + fullShift k := by
    refine Prod.ext (funext fun i => ?_) (by simp [angleScale, fullShift])
    simp [angleScale, fullShift]
  refine ⟨?_, ?_, fun h => ?_⟩
  · rw [hsh]; exact polarDom_shift k hz
  · rw [hsh]; exact (poincareProd_polar_lattice hm hκ hz hz k).1
  · obtain ⟨k, hk⟩ := (poincareProd_polar_lattice hm hκ hz hz' 0).2 h
    refine ⟨k, Prod.ext (funext fun i => ?_) ?_⟩
    · have := congrArg (fun y : Phase (n + n) => y.1 i) hk
      simp [angleScale, fullShift] at this
      have h2π : (2 * π) ≠ 0 := by positivity
      refine mul_left_cancel₀ h2π ?_
      simp only [Prod.fst_add, Pi.add_apply]
      linarith
    · have := congrArg (fun y : Phase (n + n) => y.2) hk
      simpa [angleScale, fullShift] using this

theorem polar_hamiltonian_split {m : Fin n → ℝ} {G m0 μ : ℝ} (hm : ∀ i, 0 < m i)
    (hκ : 0 < G * m0) {z : Phase (n + n)} (hz : z ∈ polarDom n) :
    movingHamiltonian G m0 m μ (poincareProd m (G * m0) (polarMap z)) =
      hProd (G * m0) m (polarMap z) + μ * fMov G m0 m (poincareProd m (G * m0) (polarMap z)) :=
  movingHamiltonian_poincareProd hm hκ (polarMap_mapsTo n hz)

end PolarChart

end KAM.Planetary

end
