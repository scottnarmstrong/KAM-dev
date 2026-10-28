/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.FastBridge
public import KAM.Planetary.Preparation.FastParams

/-!
# Fast averaging (P11A-P5, `bpP:p11:avg-fast`, `bpP:p11:sec-C#data`)

The exact CP09 preparation parameters `p11K1, p11Alpha1, p11s1, p11d1, p11eta1` (`ν₁ = 3`), the
fast data `P11FastData` with its specification `P11FastSpec`, and the exported core theorem
`avg_fast_of_spec`: for an arbitrary `C : P11SecularData n` with `P11SecularSpec D C` the
conclusion of `avg_fast` holds. The signed `avg_fast` and `p11FastData` (which select
`C = p11SecularData D` through `holo_chart`) are one-line wrappers of it. The proof is the
application of `osc_averaging` (`af-apply`), the divisor bound (`af-o1`), the smallness (S1)
(`af-o2`, via `e4`) and the bookkeeping of the conclusion (`af-concl`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

/-- Exact CP09 preparation parameters; nu1 is fixed at 3. -/
def p11K1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) : ℝ :=
  6/(Real.pi*C.sigma)*Real.log (1/(eps*C.MF))
def p11Alpha1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) := C.gamma/2*p11K1 C eps^(-C.tau)
def p11s1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) :=
  min C.rC (C.gamma/(4*C.L*p11K1 C eps^(C.tau+1)))
def p11d1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) := min (p11s1 C eps*C.sigma) C.rz^2
def p11eta1 {n : ℕ} (C : P11SecularData n) (eps : ℝ) :=
  400*(1+n)*eps*C.MF^2/(2*Real.pi*p11Alpha1 C eps*p11d1 C eps)
structure P11FastData (n : ℕ) where
  map : P11Phase (n+n) → P11Phase (n+n)
  G : P11CVec n × P11Phase n → ℂ
  f1 : P11Phase (n+n) → ℂ
  deriving Inhabited
def P11FastSpec {n : ℕ} (C : P11SecularData n) (eps : ℝ) (A : P11FastData n) : Prop :=
  let U := p11WorkingDom n C.J0 (C.sigma/6) (p11s1 C eps/2) (C.rz/2)
  DifferentiableOn ℂ A.map U ∧ InjOn A.map U ∧
  DifferentiableOn ℂ A.f1 U ∧ KAM.Canonical.RealOn U A.f1 ∧
  DifferentiableOn ℂ A.G
    (Metric.ball (KAM.realInclusion n C.J0) (p11s1 C eps/2) ×ˢ Metric.ball 0 (C.rz/2)) ∧
  (∀ J : P11Vec n, ‖J-C.J0‖ < p11s1 C eps/2 → ∀ z : Phase n, ‖z‖ < C.rz/2 →
    (A.G (KAM.realInclusion n J,KAM.realInclusion₂ n z)).im=0) ∧
  (∀ z : Phase (n+n), KAM.realInclusion₂ (n+n) z ∈ U → ∀ i,
    ((A.map (KAM.realInclusion₂ (n+n) z)).1 i).im=0 ∧
    ((A.map (KAM.realInclusion₂ (n+n) z)).2 i).im=0) ∧
  (∀ z ∈ U, ∀ u v, KAM.Canonical.symplFormC (fderiv ℂ A.map z u) (fderiv ℂ A.map z v)=
    KAM.Canonical.symplFormC u v) ∧
  (∀ z ∈ U, ∀ k : Fin n → ℤ, A.map (z.1+Fin.append (fun i => (k i : ℂ)) 0,z.2)=
    A.map z+(Fin.append (fun i => (k i : ℂ)) 0,0)) ∧
  MapsTo A.map U (p11WorkingDom n C.J0 C.sigma (p11s1 C eps) C.rz) ∧
  (∀ z ∈ U, p11WorkingH C eps (A.map z)=
    C.h (fun i : Fin n => z.2 (Fin.castAdd n i))+
    eps*A.G ((fun i : Fin n => z.2 (Fin.castAdd n i)),
      ((fun i : Fin n => z.1 (Fin.natAdd n i)),fun i : Fin n => z.2 (Fin.natAdd n i)))+A.f1 z) ∧
  p11Bound U A.f1 ((eps*C.MF)^3) ∧
  (∀ z : P11Phase n, ‖z‖ < C.rz/2 → ∀ J, ‖J-KAM.realInclusion n C.J0‖ < p11s1 C eps/2 →
    let f := fun u : P11CVec n × P11CVec n => A.f1 (Fin.append u.1 z.1,Fin.append u.2 z.2)
    KAM.Weighted.WSummable f (C.sigma/6) J ∧ KAM.Weighted.wsum f (C.sigma/6) J ≤ (eps*C.MF)^3) ∧
  (∀ J, ‖J-KAM.realInclusion n C.J0‖ < p11s1 C eps/2 → ∀ z : P11Phase n, ‖z‖ < C.rz/2 →
    ‖A.G (J,z)-p11FastMean C.F J z‖ ≤ p11eta1 C eps) ∧
  ∀ z ∈ U,
    2*Real.pi*p11Alpha1 C eps*C.sigma*
      ‖(fun i : Fin n => (A.map z).2 (Fin.castAdd n i)-z.2 (Fin.castAdd n i))‖ ≤ 3*eps*C.MF ∧
    2*Real.pi*p11Alpha1 C eps*p11s1 C eps*
      ‖(fun i : Fin n => (A.map z).1 (Fin.castAdd n i)-z.1 (Fin.castAdd n i))‖ ≤ 9*eps*C.MF ∧
    2*Real.pi*p11Alpha1 C eps*C.rz*
      max (‖(fun i : Fin n => (A.map z).1 (Fin.natAdd n i)-z.1 (Fin.natAdd n i))‖)
        (‖(fun i : Fin n => (A.map z).2 (Fin.natAdd n i)-z.2 (Fin.natAdd n i))‖) ≤ 9*eps*C.MF

section Params

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- The positivity and size data of `P11SecularSpec` used by the fast averaging. -/
theorem fast_consts (hC : P11SecularSpec D C) :
    0 < C.gamma ∧ 0 < C.tau ∧ 1 ≤ C.L ∧ 0 < C.rC ∧ C.rC ≤ 1 ∧ 0 < C.sigma ∧ C.sigma ≤ 1 / 4 ∧
      0 < C.rz ∧ C.rz ≤ 1 ∧ 1 ≤ C.MF := by
  obtain ⟨-, -, -, hτ, -, -, -, -, hγ0, -, -, hrC0, hrC1, -, hσ0, hσ1, hrz0, hrz1, hMF, hL1, -⟩ := hC
  refine ⟨hγ0, ?_, hL1, hrC0, hrC1, hσ0, hσ1, hrz0, hrz1, hMF⟩
  rw [hτ]
  have : (2 : ℝ) ≤ n := by exact_mod_cast D.n_ge
  exact lt_max_of_lt_right (by linarith)

theorem p11K1_ge_one (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) : 1 ≤ p11K1 C eps := by
  obtain ⟨-, -, -, -, -, hσ0, hσ1, -, -, hMF⟩ := fast_consts hC
  have hℓ := log_inv_ge_one (mul_pos heps (by linarith)) hεM
  have hc : 1 ≤ 6 / (Real.pi * C.sigma) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  unfold p11K1
  nlinarith

theorem exp_p11K1 (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps) :
    Real.exp (-(2 * Real.pi * p11K1 C eps * C.sigma) / 6) = (eps * C.MF) ^ 2 := by
  obtain ⟨-, -, -, -, -, hσ0, -, -, -, hMF⟩ := fast_consts hC
  have hεM : 0 < eps * C.MF := mul_pos heps (by linarith)
  have h1 : -(2 * Real.pi * p11K1 C eps * C.sigma) / 6 = 2 * Real.log (eps * C.MF) := by
    unfold p11K1
    rw [one_div, Real.log_inv]
    field_simp
  rw [h1, show 2 * Real.log (eps * C.MF) = Real.log (eps * C.MF) + Real.log (eps * C.MF) by ring,
    Real.exp_add, Real.exp_log hεM, sq]

theorem p11s1_pos (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) : 0 < p11s1 C eps := by
  obtain ⟨hγ0, -, hL1, hrC0, -⟩ := fast_consts hC
  have hK := p11K1_ge_one hC heps hεM
  unfold p11s1
  refine lt_min hrC0 ?_
  have : 0 < p11K1 C eps ^ (C.tau + 1) := Real.rpow_pos_of_pos (by linarith) _
  positivity

theorem p11s1_le (C : P11SecularData n) (eps : ℝ) : p11s1 C eps ≤ C.rC := min_le_left _ _

theorem p11_budget (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) : 6 ≤ 2 * Real.pi * p11K1 C eps * C.sigma := by
  obtain ⟨-, -, -, -, -, hσ0, -, -, -, hMF⟩ := fast_consts hC
  have hℓ := log_inv_ge_one (mul_pos heps (by linarith)) hεM
  have : 2 * Real.pi * p11K1 C eps * C.sigma = 12 * Real.log (1 / (eps * C.MF)) := by
    unfold p11K1; field_simp; ring
  rw [this]; linarith

theorem p11_sK (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) :
    p11K1 C eps * C.L * p11s1 C eps ≤ C.gamma * p11K1 C eps ^ (-C.tau) / 4 := by
  obtain ⟨hγ0, hτ0, hL1, -⟩ := fast_consts hC
  have hK := p11K1_ge_one hC heps hεM
  have hK0 : 0 < p11K1 C eps := by linarith
  have hL0 : 0 < C.L := by linarith
  have h1 : p11s1 C eps ≤ C.gamma / (4 * C.L * p11K1 C eps ^ (C.tau + 1)) := min_le_right _ _
  calc p11K1 C eps * C.L * p11s1 C eps
      ≤ p11K1 C eps * C.L * (C.gamma / (4 * C.L * p11K1 C eps ^ (C.tau + 1))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = C.gamma * p11K1 C eps ^ (-C.tau) / 4 := by
        rw [Real.rpow_neg hK0.le, Real.rpow_add_one hK0.ne']
        have : 0 < p11K1 C eps ^ C.tau := Real.rpow_pos_of_pos hK0 _
        field_simp

theorem p11_alpha_le (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) :
    0 < p11Alpha1 C eps ∧ p11Alpha1 C eps ≤ 3 / 4 * C.gamma * p11K1 C eps ^ (-C.tau) := by
  obtain ⟨hγ0, -⟩ := fast_consts hC
  have hK0 : 0 < p11K1 C eps := by linarith [p11K1_ge_one hC heps hεM]
  have : 0 < p11K1 C eps ^ (-C.tau) := Real.rpow_pos_of_pos hK0 _
  unfold p11Alpha1
  constructor <;> nlinarith

/-- The signed `p11d1` parses as `(min (s₁σ) r_z)²`; it is bounded by the source `d₁`. -/
theorem p11d1_le (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) :
    0 < p11d1 C eps ∧ p11d1 C eps ≤ min (p11s1 C eps * C.sigma) (C.rz * C.rz) := by
  obtain ⟨-, -, -, hrC0, hrC1, hσ0, hσ1, hrz0, -⟩ := fast_consts hC
  have hs0 := p11s1_pos hC heps hεM
  have hs1 : p11s1 C eps ≤ 1 := (p11s1_le C eps).trans hrC1
  have ha0 : 0 < p11s1 C eps * C.sigma := mul_pos hs0 hσ0
  have ha1 : p11s1 C eps * C.sigma ≤ 1 := by nlinarith
  have hm0 : 0 < min (p11s1 C eps * C.sigma) C.rz := lt_min ha0 hrz0
  have hm1 : min (p11s1 C eps * C.sigma) C.rz ≤ 1 := (min_le_left _ _).trans ha1
  refine ⟨by unfold p11d1; positivity, ?_⟩
  unfold p11d1
  refine le_min ?_ ?_
  · calc min (p11s1 C eps * C.sigma) C.rz ^ 2 ≤ min (p11s1 C eps * C.sigma) C.rz * 1 := by
          nlinarith
      _ ≤ _ := by rw [mul_one]; exact min_le_left _ _
  · rw [sq]
    exact mul_le_mul (min_le_right _ _) (min_le_right _ _) hm0.le hrz0.le

/-- Reality of `h̃` at real points: the extra source premise of `osc_averaging`
(`OscHyp.real_h`) which `P11SecularSpec` does not record. -/
def P11SecularHReal {n : ℕ} (C : P11SecularData n) : Prop :=
  ∀ J : P11Vec n, KAM.realInclusion n J ∈ Metric.ball (KAM.realInclusion n C.J0) (2 * C.rC) →
    (C.h (KAM.realInclusion n J)).im = 0

/-- The point of the working domain with the angles set to zero. -/
theorem zero_angle_mem {s r rz : ℝ} (J0 : P11Vec n) (hs : 0 < s) {J x y : P11CVec n}
    (hJ : ‖J - KAM.realInclusion n J0‖ < r) (hx : ‖x‖ < rz) (hy : ‖y‖ < rz) :
    ((Fin.append (0 : P11CVec n) x, Fin.append J y) : P11Phase (n + n)) ∈
      p11WorkingDom n J0 s r rz := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; simpa [Fin.append_left] using hs
  · simpa [Fin.append_left] using hJ
  · simpa [Fin.append_right] using hx
  · simpa [Fin.append_right] using hy

end Params

section Core

open KAM.Weighted KAM.Canonical

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- Steps `af-apply`, `af-o1`, `af-concl` at a fixed `ε` for which (S1) holds. -/
theorem fast_spec_at (hC : P11SecularSpec D C) (hh : P11SecularHReal C) {eps : ℝ}
    (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1))
    (hS1 : 2 ^ 12 * (1 + (n : ℝ)) * p11K1 C eps * eps * C.MF * C.sigma ≤
      p11Alpha1 C eps * p11d1 C eps) : ∃ A, P11FastSpec C eps A := by
  have hC' := hC
  obtain ⟨hγ0, hτ0, hL1, hrC0, hrC1, hσ0, hσ1, hrz0, hrz1, hMF⟩ := fast_consts hC
  have hK1 := p11K1_ge_one hC heps hεM
  have hs0 := p11s1_pos hC heps hεM
  obtain ⟨hα0, hαK⟩ := p11_alpha_le hC heps hεM
  obtain ⟨hd0, hdle⟩ := p11d1_le hC heps hεM
  have hsmall : 2 ^ 12 * (1 + (n : ℝ)) * p11K1 C eps * (eps * C.MF) * C.sigma ≤
      p11Alpha1 C eps * min (p11s1 C eps * C.sigma) (C.rz ^ 2) := by
    calc _ = 2 ^ 12 * (1 + (n : ℝ)) * p11K1 C eps * eps * C.MF * C.sigma := by ring
      _ ≤ p11Alpha1 C eps * p11d1 C eps := hS1
      _ ≤ _ := by
        rw [← sq] at hdle
        exact mul_le_mul_of_nonneg_left (by simpa [sq] using hdle) hα0.le
  have hH := oscHyp_fast hC hh heps hs0 (p11s1_le C eps) (by linarith) hα0
    (p11_budget hC heps hεM) (p11_sK hC heps hεM) hαK hsmall
  obtain ⟨Ψ, g, fs, hV⟩ := osc_averaging hH
  dsimp only at hV
  simp only [zero_add, oscDom_eq_workingDom] at hV
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := hV
  refine ⟨⟨Ψ, fun p => (eps : ℂ)⁻¹ * g (Fin.append (0 : P11CVec n) p.2.1,
    Fin.append p.1 p.2.2), fs⟩, ?_⟩
  unfold P11FastSpec
  dsimp only
  trace_state
  sorry

end Core

end KAM.Planetary

end
