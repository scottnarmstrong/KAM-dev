/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Coefficients
public import KAM.Planetary.SecularForm.LaplaceCoeff
public import KAM.Planetary.SecularForm.LaplaceSeries
public import KAM.Planetary.SecularSpectrum.Norms

/-!
# Peeling the innermost planet

Blueprint P, Part 10 (`bpP:p10:laplace-bounds`, `bpP:p10:formula69`, `bpP:p10:peel`): the Laplace
coefficients `b_{3/2}^{(1)}, b_{3/2}^{(2)}` for small argument, the resulting two-sided bounds
(Formula 69 with remainders) on `pairA`, `pairB`, and the structure of the secular matrix when the
innermost axis tends to `0`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {n d m : ℕ}

/-- The ratio of consecutive terms of the `b_{3/2}^{(k)}` series, `k ≥ 1`, is at most `2 α²`. -/
theorem laplaceTerm_succ_le {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (hα : 0 ≤ α) (q : ℕ) :
    laplaceTerm (3/2) k (q+1) α ≤ 2 * α^2 * laplaceTerm (3/2) k q α := by
  have hT : 0 ≤ laplaceTerm (3/2) k q α := laplaceTerm_nonneg (by norm_num) hα k q
  have hq : (0:ℝ) ≤ q := Nat.cast_nonneg q
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have key : laplaceTerm (3/2) k (q+1) α =
      laplaceTerm (3/2) k q α * (((3/2 + (q+k)) * (3/2 + q)) / (((q:ℝ)+k+1) * (q+1)) * α^2) := by
    simp only [laplaceTerm, poch_succ, show q + 1 + k = (q + k) + 1 by ring, poch_succ,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      show 2 * (q + 1) + k = (2 * q + k) + 2 by ring, pow_add]
    have h1 : (0:ℝ) < (q + k).factorial := by exact_mod_cast Nat.factorial_pos _
    have h2 : (0:ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos _
    field_simp
  rw [key]
  have hr : ((3/2 + ((q:ℝ)+k)) * (3/2 + q)) / (((q:ℝ)+k+1) * (q+1)) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hq (by linarith : (0:ℝ) ≤ k - 1)]
  have : ((3/2 + ((q:ℝ)+k)) * (3/2 + q)) / (((q:ℝ)+k+1) * (q+1)) * α^2 ≤ 2 * α^2 :=
    mul_le_mul_of_nonneg_right hr (sq_nonneg α)
  nlinarith

theorem laplaceTerm_le_geom {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (hα : 0 ≤ α) (q : ℕ) :
    laplaceTerm (3/2) k q α ≤ laplaceTerm (3/2) k 0 α * (2 * α^2)^q := by
  induction q with
  | zero => simp
  | succ q ih =>
    calc laplaceTerm (3/2) k (q+1) α ≤ 2 * α^2 * laplaceTerm (3/2) k q α :=
          laplaceTerm_succ_le hk hα q
      _ ≤ 2 * α^2 * (laplaceTerm (3/2) k 0 α * (2 * α^2)^q) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ = laplaceTerm (3/2) k 0 α * (2 * α^2)^(q+1) := by ring

/-- The two-sided bounds for one index `k ∈ {1,2}`, with first term `c α^k`. -/
theorem laplace_bounds_aux {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1/2) :
    laplaceTerm (3/2) k 0 α ≤ laplace_def (3/2) k α ∧
    laplace_def (3/2) k α ≤ laplaceTerm (3/2) k 0 α * (1 + 4 * α^2) := by
  have hα1' : α < 1 := by linarith
  have hS := hasSum_laplaceTerm (by norm_num : (0:ℝ) < 3/2) hα hα1' k
  have hx : 2 * α^2 < 1 := by nlinarith
  refine ⟨?_, ?_⟩
  · exact le_hasSum hS 0 fun q _ => laplaceTerm_nonneg (by norm_num) hα k q
  · have hG : HasSum (fun q : ℕ => laplaceTerm (3/2) k 0 α * (2 * α^2)^q)
        (laplaceTerm (3/2) k 0 α * (1 - 2 * α^2)⁻¹) :=
      (hasSum_geometric_of_lt_one (by positivity) hx).mul_left _
    refine (hasSum_le (fun q => laplaceTerm_le_geom hk hα q) hS hG).trans ?_
    have hT : 0 ≤ laplaceTerm (3/2) k 0 α := laplaceTerm_nonneg (by norm_num) hα k 0
    refine mul_le_mul_of_nonneg_left ?_ hT
    rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
    have h4 : 0 ≤ 1 - 4 * α^2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg α) h4]

theorem laplace_bounds {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1/2) :
    (3/2)*α ≤ laplace_def (3/2) 1 α ∧
    laplace_def (3/2) 1 α ≤ (3/2)*α*(1+4*α^2) ∧
    (15/8)*α^2 ≤ laplace_def (3/2) 2 α ∧
    laplace_def (3/2) 2 α ≤ (15/8)*α^2*(1+4*α^2) := by
  have h1 := laplace_bounds_aux (k := 1) le_rfl hα hα1
  have h2 := laplace_bounds_aux (k := 2) (by norm_num) hα hα1
  have e1 : laplaceTerm (3/2) 1 0 α = (3/2) * α := by
    simp [laplaceTerm, poch]
  have e2 : laplaceTerm (3/2) 2 0 α = (15/8) * α^2 := by
    simp [laplaceTerm, poch, Finset.prod_range_succ]; norm_num
  rw [e1] at h1; rw [e2] at h2
  exact ⟨by simpa using h1.1, by simpa using h1.2, by simpa using h2.1, by simpa using h2.2⟩

theorem formula69 (D : Data n) {a : Vec n} (ha : a ∈ axes n) {i j : Fin n} (hij : i < j)
    (hα : a i/a j ≤ 1/2) :
    ∃ θ θ' : ℝ, θ ∈ Icc 0 (4*(a i/a j)^2) ∧ θ' ∈ Icc 0 (4*(a i/a j)^2) ∧
      pairA D a i j = (3/8)*D.G*D.m i*D.m j*(a i/a j)^2/a j*(1+θ) ∧
      pairB D a i j = (15/32)*D.G*D.m i*D.m j*(a i/a j)^3/a j*(1+θ') := by
  have hi := ha.1 i
  have hj := ha.1 j
  have hα0 : 0 < a i / a j := div_pos hi hj
  obtain ⟨b1, b2, b3, b4⟩ := laplace_bounds hα0.le hα
  set α := a i / a j with hαdef
  refine ⟨laplace_def (3/2) 1 α / ((3/2)*α) - 1, laplace_def (3/2) 2 α / ((15/8)*α^2) - 1,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [sub_nonneg, le_div_iff₀ (by positivity)]; linarith
  · rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]; nlinarith
  · rw [sub_nonneg, le_div_iff₀ (by positivity)]; linarith
  · rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]; nlinarith
  · simp only [pairA, min_eq_left hij.le, max_eq_right hij.le]
    rw [← hαdef]
    field_simp
    rw [hαdef]
    field_simp
    ring
  · simp only [pairB, min_eq_left hij.le, max_eq_right hij.le]
    rw [← hαdef]
    field_simp
    rw [hαdef]
    field_simp
    ring

def outerData (D : Data (n+1)) (hn : 0 < n) : Data n :=
  ⟨D.G,D.m0,(fun i => D.m i.succ),D.hG,D.hm0,(fun i => D.hm i.succ),hn⟩
def peelError (D : Data (n+1)) (hn : 0 < n) (a : Vec (n+1)) : Mat (n+1) :=
  fun i j => coeffs D a i j - Fin.cases 0
    (fun i' => Fin.cases 0 (fun j' => coeffs (outerData D hn) (fun k => a k.succ) i' j') j) i

theorem pairA_bounds (D : Data n) {a : Vec n} (ha : a ∈ axes n) {i j : Fin n} (hij : i < j)
    (hα : a i/a j ≤ 1/2) :
    0 ≤ pairA D a i j ∧ pairA D a i j ≤ (3/4)*D.G*D.m i*D.m j*a i^2/a j^3 := by
  obtain ⟨θ, θ', ⟨h1, h2⟩, -, hA, -⟩ := formula69 D ha hij hα
  have hi := ha.1 i
  have hj := ha.1 j
  have hα0 : 0 < a i / a j := div_pos hi hj
  have hG := D.hG
  have hmi := D.hm i
  have hmj := D.hm j
  have hsq : (a i / a j)^2 ≤ 1/4 := by nlinarith
  rw [hA]
  refine ⟨by positivity, ?_⟩
  have e : (3/8)*D.G*D.m i*D.m j*(a i/a j)^2/a j = (3/8) * (D.G*D.m i*D.m j*a i^2/a j^3) := by
    field_simp
  rw [e]
  have hP : 0 ≤ D.G*D.m i*D.m j*a i^2/a j^3 := by positivity
  have : (1 + θ) ≤ 2 := by nlinarith
  have e2 : (3/4)*D.G*D.m i*D.m j*a i^2/a j^3 = (3/4) * (D.G*D.m i*D.m j*a i^2/a j^3) := by ring
  rw [e2]
  nlinarith

theorem pairB_bounds (D : Data n) {a : Vec n} (ha : a ∈ axes n) {i j : Fin n} (hij : i < j)
    (hα : a i/a j ≤ 1/2) :
    0 ≤ pairB D a i j ∧ pairB D a i j ≤ (15/16)*D.G*D.m i*D.m j*a i^3/a j^4 := by
  obtain ⟨θ, θ', -, ⟨h1, h2⟩, -, hB⟩ := formula69 D ha hij hα
  have hi := ha.1 i
  have hj := ha.1 j
  have hα0 : 0 < a i / a j := div_pos hi hj
  have hG := D.hG
  have hmi := D.hm i
  have hmj := D.hm j
  have hsq : (a i / a j)^2 ≤ 1/4 := by nlinarith
  rw [hB]
  refine ⟨by positivity, ?_⟩
  have e : (15/32)*D.G*D.m i*D.m j*(a i/a j)^3/a j = (15/32) * (D.G*D.m i*D.m j*a i^3/a j^4) := by
    field_simp
  rw [e]
  have hP : 0 ≤ D.G*D.m i*D.m j*a i^3/a j^4 := by positivity
  have : (1 + θ') ≤ 2 := by nlinarith
  have e2 : (15/16)*D.G*D.m i*D.m j*a i^3/a j^4 = (15/16) * (D.G*D.m i*D.m j*a i^3/a j^4) := by
    ring
  rw [e2]
  nlinarith

theorem sqrt_action (D : Data n) {a : Vec n} {i : Fin n} (hi : 0 < a i) :
    √(action D a i) = √(D.m i) * (D.G*D.m0)^((1:ℝ)/4) * (a i)^((1:ℝ)/4) := by
  have hk : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  have h : 0 ≤ D.G * D.m0 * a i := by positivity
  unfold action
  rw [Real.sqrt_mul (D.hm i).le, Real.sqrt_eq_rpow (√(D.G * D.m0 * a i)),
    Real.sqrt_eq_rpow (D.G * D.m0 * a i), ← Real.rpow_mul h, Real.mul_rpow hk.le hi.le]
  norm_num
  ring

theorem action_pos (D : Data n) {a : Vec n} {i : Fin n} (hi : 0 < a i) : 0 < action D a i :=
  mul_pos (D.hm i) (Real.sqrt_pos.2 (by have := D.hG; have := D.hm0; positivity))

/-- Reindexing under `Fin.succ`: the outer system has the same coefficients. -/
theorem action_outer (D : Data (n+1)) (hn : 0 < n) (a : Vec (n+1)) (i : Fin n) :
    action (outerData D hn) (fun k => a k.succ) i = action D a i.succ := rfl

theorem pairA_outer (D : Data (n+1)) (hn : 0 < n) (a : Vec (n+1)) (i j : Fin n) :
    pairA (outerData D hn) (fun k => a k.succ) i j = pairA D a i.succ j.succ := by
  simp only [pairA, outerData, (Fin.strictMono_succ.monotone).map_min,
    (Fin.strictMono_succ.monotone).map_max]

theorem pairB_outer (D : Data (n+1)) (hn : 0 < n) (a : Vec (n+1)) (i j : Fin n) :
    pairB (outerData D hn) (fun k => a k.succ) i j = pairB D a i.succ j.succ := by
  simp only [pairB, outerData, (Fin.strictMono_succ.monotone).map_min,
    (Fin.strictMono_succ.monotone).map_max]

theorem pairA_comm (D : Data n) (a : Vec n) (i j : Fin n) : pairA D a i j = pairA D a j i := by
  simp only [pairA, min_comm i j, max_comm i j]

theorem sqrt_action_mul_self (D : Data n) {a : Vec n} {i : Fin n} (hi : 0 < a i) :
    √(action D a i) * √(action D a i) = action D a i :=
  Real.mul_self_sqrt (action_pos D hi).le

theorem coeffs_zero_zero (D : Data (n+1)) {a : Vec (n+1)} (h0 : 0 < a 0) :
    coeffs D a 0 0 = -(∑ j : Fin n, pairA D a 0 j.succ) / action D a 0 := by
  have h1 := Finset.add_sum_erase Finset.univ (fun k => pairA D a 0 k) (Finset.mem_univ 0)
  have h2 := Fin.sum_univ_succ (fun k => pairA D a 0 k)
  simp only [coeffs, qhat, ite_true, sqrt_action_mul_self D h0]
  congr 2
  linarith

theorem coeffs_zero_succ (D : Data (n+1)) (a : Vec (n+1)) (j : Fin n) :
    coeffs D a 0 j.succ =
      pairB D a 0 j.succ / (√(action D a 0) * √(action D a j.succ)) := by
  simp [coeffs, qhat, (Fin.succ_ne_zero j).symm]

theorem coeffs_succ_zero (D : Data (n+1)) (a : Vec (n+1)) (j : Fin n) :
    coeffs D a j.succ 0 = coeffs D a 0 j.succ := by
  simpa using (coeffs_hermitian D a).apply 0 j.succ

theorem coeffs_succ_succ_ne (D : Data (n+1)) (hn : 0 < n) (a : Vec (n+1)) {i j : Fin n}
    (h : i ≠ j) :
    coeffs D a i.succ j.succ = coeffs (outerData D hn) (fun k => a k.succ) i j := by
  simp [coeffs, qhat, Fin.succ_inj, h, pairB_outer, action_outer]

theorem coeffs_succ_succ_diag (D : Data (n+1)) (hn : 0 < n) {a : Vec (n+1)} (j : Fin n)
    (hj : 0 < a j.succ) :
    coeffs D a j.succ j.succ = coeffs (outerData D hn) (fun k => a k.succ) j j -
      pairA D a 0 j.succ / action D a j.succ := by
  have h1 := Finset.add_sum_erase Finset.univ (fun k => pairA D a j.succ k)
    (Finset.mem_univ j.succ)
  have h2 := Fin.sum_univ_succ (fun k => pairA D a j.succ k)
  have h3 := Finset.add_sum_erase Finset.univ (fun k => pairA (outerData D hn) (fun k => a k.succ) j k)
    (Finset.mem_univ j)
  have h4 : ∀ k : Fin n, pairA (outerData D hn) (fun k => a k.succ) j k = pairA D a j.succ k.succ :=
    fun k => by rw [pairA_outer]
  have hs : ∑ k ∈ Finset.univ.erase j.succ, pairA D a j.succ k =
      pairA D a j.succ 0 + ∑ k ∈ Finset.univ.erase j,
        pairA (outerData D hn) (fun k => a k.succ) j k := by
    simp only [h4] at h3 ⊢
    linarith
  have hm : √(action (outerData D hn) (fun k => a k.succ) j) *
      √(action (outerData D hn) (fun k => a k.succ) j) = action D a j.succ := by
    rw [action_outer]; exact sqrt_action_mul_self D hj
  simp only [coeffs, qhat, ite_true, hs, action_outer, sqrt_action_mul_self D hj]
  rw [pairA_comm D a j.succ 0]
  ring

theorem quart_pow (u : ℝ) (hu : 0 < u) : (u^4)^((1:ℝ)/4) = u := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]; norm_num

theorem quart_exists (x : ℝ) (hx : 0 < x) : ∃ u : ℝ, 0 < u ∧ x = u^4 :=
  ⟨x^((1:ℝ)/4), by positivity, by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num⟩

theorem cross_alg (G m0 mj κ t a : ℝ) (hG : 0 < G) (h0 : 0 < m0) (hj : 0 < mj) (hk : 0 < κ)
    (ht : 0 < t) (ha : 0 < a) :
    (15/16)*G*m0*mj*t^3/a^4 / ((√m0 * κ^((1:ℝ)/4) * t^((1:ℝ)/4)) * (√mj * κ^((1:ℝ)/4) * a^((1:ℝ)/4)))
      = 15*G*√(m0*mj)/(16*√κ) * t^((11:ℝ)/4) * a^(-(17:ℝ)/4) := by
  obtain ⟨u, hu, rfl⟩ := quart_exists t ht
  obtain ⟨v, hv, rfl⟩ := quart_exists a ha
  obtain ⟨w, hw, rfl⟩ := quart_exists κ hk
  obtain ⟨p, hp, rfl⟩ : ∃ p : ℝ, 0 < p ∧ m0 = p^2 := ⟨√m0, Real.sqrt_pos.2 h0, (Real.sq_sqrt h0.le).symm⟩
  obtain ⟨q, hq, rfl⟩ : ∃ q : ℝ, 0 < q ∧ mj = q^2 := ⟨√mj, Real.sqrt_pos.2 hj, (Real.sq_sqrt hj.le).symm⟩
  have e1 : √(p^2) = p := Real.sqrt_sq hp.le
  have e2 : √(q^2) = q := Real.sqrt_sq hq.le
  have e3 : √(p^2*q^2) = p*q := by rw [← mul_pow]; exact Real.sqrt_sq (by positivity)
  have e4 : √(w^4) = w^2 := by rw [show w^4 = (w^2)^2 by ring]; exact Real.sqrt_sq (by positivity)
  have e5 : (u^4)^((11:ℝ)/4) = u^11 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]; norm_num
  have e6 : (v^4)^(-(17:ℝ)/4) = (v^17)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv.le]; norm_num
  rw [e1, e2, e3, e4, e5, e6, quart_pow u hu, quart_pow v hv, quart_pow w hw]
  field_simp

theorem sq_exists (x : ℝ) (hx : 0 < x) : ∃ u : ℝ, 0 < u ∧ x = u^2 :=
  ⟨√x, Real.sqrt_pos.2 hx, (Real.sq_sqrt hx.le).symm⟩

theorem sqrt_mul_sq (k u : ℝ) (hk : 0 < k) (hu : 0 < u) : √(k * u^2) = √k * u := by
  rw [Real.sqrt_mul hk.le, Real.sqrt_sq hu.le]

theorem diag_alg (G m0 m' κ t a : ℝ) (hG : 0 < G) (h0 : 0 < m0) (hj : 0 < m') (hk : 0 < κ)
    (ht : 0 < t) (ha : 0 < a) :
    (3/4)*G*m0*m'*t^2/a^3/(m0*√(κ*t)) = 3*G/(4*√κ) * t^((3:ℝ)/2) * (m' * a^(-3:ℤ)) := by
  obtain ⟨s, hs, rfl⟩ := sq_exists t ht
  have e : (s^2)^((3:ℝ)/2) = s^3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]; norm_num
  have hk' := Real.sqrt_pos.2 hk
  rw [e, sqrt_mul_sq κ s hk hs, zpow_neg, zpow_ofNat]
  field_simp

theorem diag_alg2 (G m0 m' κ t a : ℝ) (hG : 0 < G) (h0 : 0 < m0) (hj : 0 < m') (hk : 0 < κ)
    (ht : 0 < t) (ha : 0 < a) :
    (3/4)*G*m0*m'*t^2/a^3/(m'*√(κ*a)) = 3*G*m0/(4*√κ) * t^2 * a^(-(7:ℝ)/2) := by
  obtain ⟨r, hr, rfl⟩ := sq_exists a ha
  have e : (r^2)^(-(7:ℝ)/2) = (r^7)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; norm_num
  have hk' := Real.sqrt_pos.2 hk
  rw [e, sqrt_mul_sq κ r hk hr]
  field_simp

theorem frobenius_le_sum_abs (M : Mat n) : frobenius M ≤ ∑ i, ∑ j, |M i j| := by
  unfold SecularSpectrum.frobenius
  rw [Real.sqrt_le_iff]
  refine ⟨Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _, ?_⟩
  have : ∀ i, (∑ j, M i j ^ 2) ≤ (∑ j, |M i j|) ^ 2 := fun i => by
    simp_rw [← sq_abs (M i _)]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => abs_nonneg _)
  calc ∑ i, ∑ j, M i j ^ 2 ≤ ∑ i, (∑ j, |M i j|) ^ 2 := Finset.sum_le_sum fun i _ => this i
    _ ≤ (∑ i, ∑ j, |M i j|) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _)

theorem op2_le_frobenius (M : Mat n) : op2 M ≤ frobenius M := by
  refine Real.sSup_le ?_ (Real.sqrt_nonneg _)
  rintro r ⟨x, hx, rfl⟩
  simpa [hx] using length2_mulVec_le M x

end Nondegeneracy
end KAM.Planetary
