/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Averaging.Setting
public import KAM.Planetary.TwoScale.Constants

/-!
# Two-scale KAM: the two period conversions

`bpP:p3:period-dictionary`, `bpP:p2:use5`. Two distinct conversions between the `2π`-periodic
convention of CP and the period-one convention:

* the pure-angle conversion (`period_dictionary`, `period_dictionary_coeff`,
  `period_dictionary_field`): the chart `Q(θ, I) = (2πθ, I)` is conformal, the Hamiltonian is
  divided by `2π`, and the scale data transform with `c = 2π` leaving `constants` invariant;
* the conversion while Cartesian oscillators remain (`oscPeriodChart`, `use5`, `use5_constants`):
  only the fast angles/actions are rescaled (`θ ↦ 2πθ`, `I ↦ I/(2π)`), the Cartesian oscillator
  coordinates are untouched, so the chart is symplectic and the Hamiltonian is unchanged.

Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-08.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- Pure numerical invariant of the c=2pi period conversion. -/
theorem period_dictionary (p : ScaleData) :
    let c := 2 * π
    let p' := {p with
      E := p.E / c
      M := p.M / c
      Mhat := p.Mhat / c
      Mbar := c * p.Mbar
      Mbar₁ := c * p.Mbar₁
      Mbar₂ := c * p.Mbar₂
      L := c * p.L
      γ₁ := p.γ₁ / c
      γ₂ := p.γ₂ / c}
    constants p' = constants p := by
  intro c p'
  have hc : c ≠ 0 := by positivity
  have hx : p'.E * p'.M ^ 2 * p'.L / p'.γ₁ ^ 2 = p.E * p.M ^ 2 * p.L / p.γ₁ ^ 2 := by
    show p.E / c * (p.M / c) ^ 2 * (c * p.L) / (p.γ₁ / c) ^ 2 = _
    field_simp
  unfold constants
  simp only []
  rw [hx]
  generalize 6 / p.s * max 1 (log (1 / (p.E * p.M ^ 2 * p.L / p.γ₁ ^ 2))) = K
  have hA : p.γ₁ / c / (3 * (p.M / c) * K ^ (p.τ + 1)) = p.γ₁ / (3 * p.M * K ^ (p.τ + 1)) := by
    by_cases hM : p.M = 0
    · simp [hM]
    · field_simp
  have hB : p.γ₂ / c / (3 * (p.Mhat / c) * K ^ (p.τ + 1)) =
      p.γ₂ / (3 * p.Mhat * K ^ (p.τ + 1)) := by
    by_cases hM : p.Mhat = 0
    · simp [hM]
    · field_simp
  have hEL : p.E / c * (c * p.L) = p.E * p.L := by field_simp
  show (K, min (min (p.γ₁ / c / (3 * (p.M / c) * K ^ (p.τ + 1)))
      (p.γ₂ / c / (3 * (p.Mhat / c) * K ^ (p.τ + 1)))) p.ρ, _) = _
  rw [hA, hB]
  have hEL' : p'.E * p'.L = p.E * p.L := hEL
  rw [hEL']

/-- Remaining scalar invariants of use5, with the Hamiltonian and oscillator size unchanged. -/
theorem use5_constants (αcp rcp sc ε₀ K E b : ℝ) :
    let c := 2 * π
    let α := αcp / c
    let r := c * rcp
    let s := sc / c
    2 * π * α = αcp ∧ min (r * s) (ε₀ ^ 2) = min (rcp * sc) (ε₀ ^ 2) ∧
    K * s / α = K * sc / αcp ∧
    (2 ^ 12 * b * K * E * s ≤ α * min (r * s) (ε₀ ^ 2) ↔
      2 ^ 12 * b * K * E * sc ≤ αcp * min (rcp * sc) (ε₀ ^ 2)) := by
  intro c α r s
  have hc : (c : ℝ) ≠ 0 := by positivity
  have hcpos : 0 < c := by positivity
  have hrs : r * s = rcp * sc := by
    show c * rcp * (sc / c) = _
    field_simp
  have h1 : 2 * π * α = αcp := by
    show 2 * π * (αcp / (2 * π)) = _
    field_simp
  have h3 : K * s / α = K * sc / αcp := by
    show K * (sc / c) / (αcp / c) = _
    by_cases hα : αcp = 0
    · simp [hα]
    · field_simp
  refine ⟨h1, by rw [hrs], h3, ?_⟩
  rw [hrs]
  have : 2 ^ 12 * b * K * E * s = (2 ^ 12 * b * K * E * sc) / c := by
    show _ = _
    simp only [s]
    ring
  rw [this]
  show _ ≤ αcp / c * _ ↔ _
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hcpos]

/-- CP's coefficient functions are read at phi=2pi theta; normalizing the
Hamiltonian divides every coefficient and its norm bound by 2pi. -/
theorem period_dictionary_coeff {n : ℕ} {D : Set (Fin n → ℂ)} {r S E : ℝ}
    (H : CHam n) (hbound : WBound D r S (fun z => H ((2 * π : ℂ) • z.1, z.2)) E) :
    (∀ I k, coeff (fun z => H ((2 * π : ℂ) • z.1, z.2) / (2 * π : ℂ)) I k =
      coeff (fun z => H ((2 * π : ℂ) • z.1, z.2)) I k / (2 * π : ℂ)) ∧
    WBound D r S (fun z => H ((2 * π : ℂ) • z.1, z.2) / (2 * π : ℂ)) (E / (2 * π)) := by
  have hc : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  have hcn : ‖(2 * π : ℂ)‖ = 2 * π := by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have hcoeff : ∀ I k, coeff (fun z : CPhase n => H ((2 * π : ℂ) • z.1, z.2) / (2 * π : ℂ)) I k =
      coeff (fun z : CPhase n => H ((2 * π : ℂ) • z.1, z.2)) I k / (2 * π : ℂ) := by
    intro I k
    simp only [coeff, KAM.torusCoeffW, KAM.torusAverage, smul_eq_mul]
    rw [← MeasureTheory.integral_div]
    congr 1
    ext x
    ring
  refine ⟨hcoeff, fun I hI => ?_⟩
  obtain ⟨hs, hle⟩ := hbound I hI
  have hnorm : (fun k : Fin n → ℤ => ‖coeff (fun z : CPhase n =>
      H ((2 * π : ℂ) • z.1, z.2) / (2 * π : ℂ)) I k‖ * modeWeight S k) =
      fun k => (‖coeff (fun z : CPhase n => H ((2 * π : ℂ) • z.1, z.2)) I k‖ *
        modeWeight S k) / (2 * π) := by
    ext k
    rw [hcoeff, norm_div, hcn]
    ring
  refine ⟨?_, ?_⟩
  · unfold WSummable
    rw [hnorm]
    exact hs.div_const _
  · unfold wsum
    rw [hnorm, tsum_div_const]
    exact div_le_div_of_nonneg_right hle (by positivity)

/-! ## Diagonal charts -/

/-- The diagonal linear chart `(θ, I) ↦ (a θ, b I)` on `ℂⁿ × ℂⁿ`. -/
def diagChart {n : ℕ} (a b : Fin n → ℂ) : CPhase n →L[ℂ] CPhase n :=
  ((ContinuousLinearMap.pi fun i => a i • (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (Fin n → ℂ))).prod
    (ContinuousLinearMap.pi fun i => b i • (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin n → ℂ))))

theorem diagChart_apply {n : ℕ} (a b : Fin n → ℂ) (x : CPhase n) :
    diagChart a b x = (fun i => a i * x.1 i, fun i => b i * x.2 i) := rfl

/-- Pulling the Hamiltonian vector field back along a diagonal chart whose entries multiply to
the constant `κ`, with the Hamiltonian divided by `κ`. -/
theorem diagChart_field {n : ℕ} (a b : Fin n → ℂ) {κ : ℂ} (hκ : κ ≠ 0)
    (hab : ∀ i, a i * b i = κ) (H : CHam n) (z : CPhase n)
    (hH : DifferentiableAt ℂ H (diagChart a b z)) :
    diagChart a b (KAM.hamiltonianVectorFieldℂ (fun x => H (diagChart a b x) / κ) z) =
      KAM.hamiltonianVectorFieldℂ H (diagChart a b z) := by
  set L := diagChart a b with hL
  have hd : fderiv ℂ (fun x => H (L x) / κ) z = κ⁻¹ • (fderiv ℂ H (L z)).comp L := by
    have h1 : HasFDerivAt (fun x => H (L x)) ((fderiv ℂ H (L z)).comp L) z :=
      hH.hasFDerivAt.comp z L.hasFDerivAt
    have h2 : (fun x => H (L x) / κ) = fun x => κ⁻¹ • H (L x) := by
      funext x; simp [div_eq_inv_mul]
    rw [h2]
    exact (h1.const_smul κ⁻¹).fderiv
  have e1 : ∀ i, L (0, Pi.single i 1) = (0, Pi.single i (b i)) := by
    intro i
    ext j
    · simp [hL, diagChart_apply]
    · by_cases h : j = i <;> simp [hL, diagChart_apply, h]
  have e2 : ∀ i, L (Pi.single i 1, 0) = (Pi.single i (a i), 0) := by
    intro i
    ext j
    · by_cases h : j = i <;> simp [hL, diagChart_apply, h]
    · simp [hL, diagChart_apply]
  have e3 : ∀ (i : Fin n) (c : ℂ),
      ((0 : Fin n → ℂ), (Pi.single i c : Fin n → ℂ)) = c • ((0 : Fin n → ℂ), Pi.single i 1) := by
    intro i c; ext j <;> simp [Pi.single_apply]
  have e4 : ∀ (i : Fin n) (c : ℂ),
      ((Pi.single i c : Fin n → ℂ), (0 : Fin n → ℂ)) =
        c • ((Pi.single i 1 : Fin n → ℂ), (0 : Fin n → ℂ)) := by
    intro i c; ext j <;> simp [Pi.single_apply]
  have f1 : ∀ i, fderiv ℂ H (L z) (L (0, Pi.single i 1)) =
      b i * fderiv ℂ H (L z) (0, Pi.single i 1) := by
    intro i; rw [e1, e3, map_smul, smul_eq_mul]
  have f2 : ∀ i, fderiv ℂ H (L z) (L (Pi.single i 1, 0)) =
      a i * fderiv ℂ H (L z) (Pi.single i 1, 0) := by
    intro i; rw [e2, e4, map_smul, smul_eq_mul]
  have hLapp : ∀ x, L x = (fun i => a i * x.1 i, fun i => b i * x.2 i) := fun x => rfl
  ext i
  · simp only [KAM.hamiltonianVectorFieldℂ, hd, smul_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul, f1]
    simp only [hLapp]
    have := hab i
    field_simp
    rw [← this]
  · simp only [KAM.hamiltonianVectorFieldℂ, hd, smul_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul, f2]
    simp only [hLapp]
    have := hab i
    field_simp
    rw [← this]
    ring

/-- Pure-angle period dictionary, no Cartesian oscillator coordinates. -/
theorem period_dictionary_field {n : ℕ} (H : CHam n) (z : CPhase n)
    (hH : DifferentiableAt ℂ H ((2 * π : ℂ) • z.1, z.2)) :
    let c : ℂ := 2 * π
    let Q := fun x : CPhase n => (c • x.1, x.2)
    fderiv ℂ Q z (KAM.hamiltonianVectorFieldℂ (fun x => H (Q x) / c) z) =
      KAM.hamiltonianVectorFieldℂ H (Q z) := by
  intro c Q
  have hc : c ≠ 0 := by
    show (2 * π : ℂ) ≠ 0
    exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  have hQ : Q = diagChart (fun _ => c) (fun _ => 1) := by
    funext x; simp [Q, diagChart_apply, Prod.ext_iff, funext_iff]
  have hfd : fderiv ℂ Q z = diagChart (fun _ => c) (fun _ => 1) := by
    rw [hQ]; exact (diagChart _ _).fderiv
  rw [hfd, ← hQ]
  have := diagChart_field (fun _ : Fin n => c) (fun _ => (1 : ℂ)) hc (fun _ => mul_one c) H z
    (by rw [← hQ]; exact hH)
  rw [← hQ] at this
  exact this

/-- use5: the fast angle/action chart leaves Cartesian oscillators untouched. -/
def oscPeriodChart {n m : ℕ} (z : CPhase (n + m)) : CPhase (n + m) :=
  (Fin.append ((2 * π : ℂ) • firstBlock (b := m) z.1) (lastBlock (a := n) z.1),
    Fin.append ((2 * π : ℂ)⁻¹ • firstBlock (b := m) z.2) (lastBlock (a := n) z.2))

/-- The diagonal weights of `oscPeriodChart`: `2π` on the fast block, `1` on the oscillators. -/
def oscWeight (n m : ℕ) : Fin (n + m) → ℂ :=
  Fin.append (fun _ : Fin n => (2 * π : ℂ)) (fun _ : Fin m => 1)

theorem oscWeight_ne_zero (n m : ℕ) (i : Fin (n + m)) : oscWeight n m i ≠ 0 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [oscWeight]
  · simp [oscWeight]

theorem oscPeriodChart_eq_diag {n m : ℕ} (z : CPhase (n + m)) :
    oscPeriodChart z = diagChart (oscWeight n m) (fun i => (oscWeight n m i)⁻¹) z := by
  rw [diagChart_apply]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [oscPeriodChart, oscWeight, firstBlock, lastBlock]

theorem use5 {n m : ℕ} (H : CHam (n + m)) (z : CPhase (n + m))
    (hH : DifferentiableAt ℂ H (oscPeriodChart z)) :
    (∀ u v, symplFormC (fderiv ℂ (oscPeriodChart (n := n) (m := m)) z u)
      (fderiv ℂ (oscPeriodChart (n := n) (m := m)) z v) = symplFormC u v) ∧
    fderiv ℂ (oscPeriodChart (n := n) (m := m)) z
      (KAM.hamiltonianVectorFieldℂ (H ∘ oscPeriodChart) z) =
        KAM.hamiltonianVectorFieldℂ H (oscPeriodChart z) := by
  have hfun : (oscPeriodChart (n := n) (m := m)) =
      diagChart (oscWeight n m) (fun i => (oscWeight n m i)⁻¹) :=
    funext oscPeriodChart_eq_diag
  have hfd : fderiv ℂ (oscPeriodChart (n := n) (m := m)) z =
      diagChart (oscWeight n m) (fun i => (oscWeight n m i)⁻¹) := by
    rw [hfun]; exact (diagChart _ _).fderiv
  have hab : ∀ i, oscWeight n m i * (oscWeight n m i)⁻¹ = 1 :=
    fun i => mul_inv_cancel₀ (oscWeight_ne_zero n m i)
  refine ⟨fun u v => ?_, ?_⟩
  · rw [hfd]
    unfold symplFormC
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [diagChart_apply]
    have := hab i
    linear_combination (u.2 i * v.1 i - u.1 i * v.2 i) * this
  · rw [hfd]
    have key := diagChart_field (oscWeight n m) (fun i => (oscWeight n m i)⁻¹) one_ne_zero hab H z
      (by rw [← hfun]; exact hH)
    rw [← hfun] at key
    have hcomp : (H ∘ oscPeriodChart (n := n) (m := m)) =
        fun x => H (oscPeriodChart x) / 1 := by
      funext x; simp
    rw [hcomp, hfun]
    simpa only [← hfun] using key

end KAM.Planetary

end
