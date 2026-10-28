/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.JetsPolar

/-!
# P Part 5: jets of the degree-four oscillator polynomial (`bpP:p5:be-coef`)

For real data `P0, Ω, β` and `y = (q, p)` let `s_k(y) = (p_k² + q_k²)/2` and
`oscPoly y = P0 + Σ Ω_k s_k + ½ Σ Σ β_ij s_i s_j`. Along a line, `oscPoly (τ y) =
P0 + τ² Q2 y + τ⁴ Q4 y`, so its second and fourth diagonal jets are `2 Q2` and `24 Q4`
(`iteratedFDeriv_two_oscPoly`, `iteratedFDeriv_four_oscPoly`). A symmetric 4-linear map with
diagonal `24 Q4` has the value `2 (Q4 (v + t u))''(0)` on `(u, u, v, v)` (`mixed_value`).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-JET.
-/

@[expose] public noncomputable section

open Set Function
open scoped BigOperators

namespace KAM.Planetary

theorem iteratedDeriv_quartic (c a q : ℝ) :
    iteratedDeriv 2 (fun τ : ℝ => c + a * τ ^ 2 + q * τ ^ 4) 0 = 2 * a ∧
    iteratedDeriv 4 (fun τ : ℝ => c + a * τ ^ 2 + q * τ ^ 4) 0 = 24 * q := by
  have d1 : deriv (fun τ : ℝ => c + a * τ ^ 2 + q * τ ^ 4) =
      fun τ => 2 * a * τ + 4 * q * τ ^ 3 := by
    funext τ
    have h : HasDerivAt (fun τ : ℝ => c + a * τ ^ 2 + q * τ ^ 4)
        (2 * a * τ + 4 * q * τ ^ 3) τ := by
      exact (((hasDerivAt_const τ c).add ((hasDerivAt_pow 2 τ).const_mul a)).add
        ((hasDerivAt_pow 4 τ).const_mul q)).congr_deriv (by simp; ring)
    exact h.deriv
  have d2 : deriv (fun τ : ℝ => 2 * a * τ + 4 * q * τ ^ 3) =
      fun τ => 2 * a + 12 * q * τ ^ 2 := by
    funext τ
    have h : HasDerivAt (fun τ : ℝ => 2 * a * τ + 4 * q * τ ^ 3)
        (2 * a + 12 * q * τ ^ 2) τ := by
      exact (((hasDerivAt_id τ).const_mul (2 * a)).add
        ((hasDerivAt_pow 3 τ).const_mul (4 * q))).congr_deriv (by simp; ring)
    exact h.deriv
  have d3 : deriv (fun τ : ℝ => 2 * a + 12 * q * τ ^ 2) = fun τ => 24 * q * τ := by
    funext τ
    have h : HasDerivAt (fun τ : ℝ => 2 * a + 12 * q * τ ^ 2) (24 * q * τ) τ := by
      exact ((hasDerivAt_const τ (2 * a)).add
        ((hasDerivAt_pow 2 τ).const_mul (12 * q))).congr_deriv (by simp; ring)
    exact h.deriv
  have d4 : deriv (fun τ : ℝ => 24 * q * τ) = fun _ => 24 * q := by
    funext τ
    have h : HasDerivAt (fun τ : ℝ => 24 * q * τ) (24 * q) τ := by
      simpa using (hasDerivAt_id τ).const_mul (24 * q)
    exact h.deriv
  constructor
  · rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_zero, d1, d2]
    simp
  · rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ',
      iteratedDeriv_zero, d1, d2, d3, d4]

variable {b : ℕ}

/-- Real jet carrier `(q, p)`. -/
abbrev RY (b : ℕ) := (Fin b → ℝ) × (Fin b → ℝ)

/-- Oscillator actions of `y = (q, p)` (matching `oscillatorAction p q`). -/
def oscS (y : RY b) (k : Fin b) : ℝ := (y.2 k ^ 2 + y.1 k ^ 2) / 2

def oscQ2 (Om : Fin b → ℝ) (y : RY b) : ℝ := ∑ k, Om k * oscS y k

def oscQ4 (be : Matrix (Fin b) (Fin b) ℝ) (y : RY b) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, be i j * oscS y i * oscS y j

def oscPoly (P0 : ℝ) (Om : Fin b → ℝ) (be : Matrix (Fin b) (Fin b) ℝ) (y : RY b) : ℝ :=
  P0 + oscQ2 Om y + oscQ4 be y

theorem oscS_smul (τ : ℝ) (y : RY b) (k : Fin b) : oscS (τ • y) k = τ ^ 2 * oscS y k := by
  simp only [oscS, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  ring

theorem oscPoly_smul (P0 : ℝ) (Om : Fin b → ℝ) (be : Matrix (Fin b) (Fin b) ℝ) (τ : ℝ)
    (y : RY b) :
    oscPoly P0 Om be (τ • y) = P0 + oscQ2 Om y * τ ^ 2 + oscQ4 be y * τ ^ 4 := by
  have h2 : oscQ2 Om (τ • y) = oscQ2 Om y * τ ^ 2 := by
    simp only [oscQ2, oscS_smul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h4 : oscQ4 be (τ • y) = oscQ4 be y * τ ^ 4 := by
    simp only [oscQ4, oscS_smul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [oscPoly, h2, h4]

theorem contDiff_oscPoly (P0 : ℝ) (Om : Fin b → ℝ) (be : Matrix (Fin b) (Fin b) ℝ) :
    ContDiff ℝ ⊤ (oscPoly P0 Om be) := by
  unfold oscPoly oscQ2 oscQ4 oscS
  fun_prop

theorem iteratedFDeriv_oscPoly_diag (P0 : ℝ) (Om : Fin b → ℝ) (be : Matrix (Fin b) (Fin b) ℝ)
    (n : ℕ) (y : RY b) :
    iteratedDeriv n (fun τ : ℝ => P0 + oscQ2 Om y * τ ^ 2 + oscQ4 be y * τ ^ 4) 0 =
      iteratedFDeriv ℝ n (oscPoly P0 Om be) 0 (fun _ => y) := by
  set L : ℝ →L[ℝ] RY b := (ContinuousLinearMap.id ℝ ℝ).smulRight y with hL
  have hLx : ∀ τ, L τ = τ • y := fun τ => by simp [hL]
  have hf : ContDiff ℝ (n : ℕ∞) (oscPoly P0 Om be) :=
    (contDiff_oscPoly P0 Om be).of_le (by exact_mod_cast le_top)
  have h := L.iteratedFDeriv_comp_right hf 0 (i := n) le_rfl
  have e : (fun τ : ℝ => P0 + oscQ2 Om y * τ ^ 2 + oscQ4 be y * τ ^ 4) =
      oscPoly P0 Om be ∘ L := by
    funext τ; simp [Function.comp, hLx, oscPoly_smul]
  rw [e, iteratedDeriv_eq_iteratedFDeriv, h]
  simp [hLx]

theorem iteratedFDeriv_two_oscPoly (P0 : ℝ) (Om : Fin b → ℝ) (be : Matrix (Fin b) (Fin b) ℝ)
    (y : RY b) :
    iteratedFDeriv ℝ 2 (oscPoly P0 Om be) 0 (fun _ => y) = 2 * oscQ2 Om y := by
  rw [← iteratedFDeriv_oscPoly_diag]
  exact (iteratedDeriv_quartic _ _ _).1

theorem iteratedFDeriv_four_oscPoly (P0 : ℝ) (Om : Fin b → ℝ) (be : Matrix (Fin b) (Fin b) ℝ)
    (y : RY b) :
    iteratedFDeriv ℝ 4 (oscPoly P0 Om be) 0 (fun _ => y) = 24 * oscQ4 be y := by
  rw [← iteratedFDeriv_oscPoly_diag]
  exact (iteratedDeriv_quartic _ _ _).2

/-- The mixed value of a symmetric 4-linear map whose diagonal is an even quartic along a line. -/
theorem mixed_value {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hM : ∀ (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → E), M (v ∘ σ) = M v) (u v : E)
    (e0 e2 e4 : ℝ) (hd : ∀ t : ℝ, M (fun _ => v + t • u) = e0 + e2 * t ^ 2 + e4 * t ^ 4) :
    M ![u, u, v, v] = e2 / 6 := by
  set N := M.curryLeft u with hN
  have hNs : ∀ (σ : Equiv.Perm (Fin 3)) (w : Fin 3 → E), N (w ∘ σ) = N w :=
    fun σ w => curryLeft_symm M hM u σ w
  set K := N.curryLeft u with hK
  have hKs : ∀ (σ : Equiv.Perm (Fin 2)) (w : Fin 2 → E), K (w ∘ σ) = K w :=
    fun σ w => curryLeft_symm N hNs u σ w
  have h1 : ∀ t : ℝ, 4 * N (fun _ => v + t • u) = 2 * e2 * t + 4 * e4 * t ^ 3 := by
    intro t
    have h := hasDerivAt_diag_line M hM v u t
    have h' : HasDerivAt (fun s : ℝ => M (fun _ => v + s • u))
        (2 * e2 * t + 4 * e4 * t ^ 3) t := by
      have e : (fun s : ℝ => M (fun _ => v + s • u)) = fun s => e0 + e2 * s ^ 2 + e4 * s ^ 4 :=
        funext hd
      rw [e]
      exact (((hasDerivAt_const t e0).add ((hasDerivAt_pow 2 t).const_mul e2)).add
        ((hasDerivAt_pow 4 t).const_mul e4)).congr_deriv (by simp; ring)
    have := h.unique h'
    rw [show ((3 + 1 : ℕ) : ℝ) = 4 by norm_num] at this
    exact this
  have h2 : HasDerivAt (fun s : ℝ => N (fun _ => v + s • u)) (3 * K (fun _ => v + (0 : ℝ) • u)) 0 := by
    have := hasDerivAt_diag_line N hNs v u 0
    rw [show ((2 + 1 : ℕ) : ℝ) = 3 by norm_num] at this
    exact this
  have h3 : HasDerivAt (fun s : ℝ => N (fun _ => v + s • u)) (2 * e2 / 4) 0 := by
    have e : (fun s : ℝ => N (fun _ => v + s • u)) = fun s => (2 * e2 * s + 4 * e4 * s ^ 3) / 4 :=
      funext fun s => by have := h1 s; linarith
    rw [e]
    exact (((hasDerivAt_id (0 : ℝ)).const_mul (2 * e2)).add
      ((hasDerivAt_pow 3 (0 : ℝ)).const_mul (4 * e4))).div_const 4 |>.congr_deriv (by simp)
  have h4 := h2.unique h3
  have hKv : K (fun _ => v) = M ![u, u, v, v] := by
    rw [hK, hN, ContinuousMultilinearMap.curryLeft_apply, ContinuousMultilinearMap.curryLeft_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  simp only [zero_smul, add_zero] at h4
  rw [← hKv]
  linarith

/-- The unit jet vector `(0, e_i)`. -/
def yvec (b : ℕ) (i : Fin b) : RY b := (0, Pi.single i 1)

theorem oscS_yvec (i k : Fin b) : oscS (yvec b i) k = (if k = i then 1 else 0) / 2 := by
  by_cases h : k = i <;> simp [oscS, yvec, h]

theorem oscQ2_yvec (Om : Fin b → ℝ) (j : Fin b) : oscQ2 Om (yvec b j) = Om j / 2 := by
  rw [oscQ2, Finset.sum_eq_single j (fun k _ hk => by simp [oscS_yvec, hk]) (by simp)]
  simp [oscS_yvec]
  ring

theorem oscQ4_line (be : Matrix (Fin b) (Fin b) ℝ) (i j : Fin b) (hij : i ≠ j) (t : ℝ) :
    oscQ4 be (yvec b j + t • yvec b i) =
      (be j j + t ^ 2 * (be j i + be i j) + t ^ 4 * be i i) / 8 := by
  have hS : ∀ k, oscS (yvec b j + t • yvec b i) k =
      ((if k = j then (1 : ℝ) else 0) + t ^ 2 * (if k = i then 1 else 0)) / 2 := by
    intro k
    have e1 : (yvec b j + t • yvec b i).2 k =
        (if k = j then (1 : ℝ) else 0) + t * (if k = i then 1 else 0) := by
      simp [yvec, Pi.single_apply]
    have e2 : (yvec b j + t • yvec b i).1 k = 0 := by simp [yvec]
    rw [oscS, e1, e2]
    by_cases hkj : k = j
    · have hki : k ≠ i := fun h => hij (h.symm.trans hkj)
      simp [hkj, hki, hij, Ne.symm hij]
    · by_cases hki : k = i
      · simp [hkj, hki, hij, Ne.symm hij]
      · simp [hkj, hki]
  have key : ∑ k, ∑ l, be k l * ((if k = j then (1:ℝ) else 0) + t ^ 2 * (if k = i then 1 else 0)) *
      ((if l = j then (1:ℝ) else 0) + t ^ 2 * (if l = i then 1 else 0)) =
      be j j + t ^ 2 * (be j i + be i j) + t ^ 4 * be i i := by
    simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul, mul_one, mul_zero,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  simp only [oscQ4, hS]
  have h4 : ∀ k l : Fin b, be k l * (((if k = j then (1 : ℝ) else 0) +
      t ^ 2 * (if k = i then 1 else 0)) / 2) * (((if l = j then (1 : ℝ) else 0) +
      t ^ 2 * (if l = i then 1 else 0)) / 2) =
      (be k l * ((if k = j then (1 : ℝ) else 0) + t ^ 2 * (if k = i then 1 else 0)) *
        ((if l = j then (1 : ℝ) else 0) + t ^ 2 * (if l = i then 1 else 0))) / 4 := by
    intro k l; ring
  simp only [h4, ← Finset.sum_div, key]
  ring

theorem oscQ4_yvec (be : Matrix (Fin b) (Fin b) ℝ) (i : Fin b) :
    oscQ4 be (yvec b i) = be i i / 8 := by
  have hS : ∀ k, oscS (yvec b i) k = (if k = i then (1 : ℝ) else 0) / 2 := oscS_yvec i
  simp only [oscQ4, hS]
  have h4 : ∀ k l : Fin b, be k l * ((if k = i then (1 : ℝ) else 0) / 2) *
      ((if l = i then (1 : ℝ) else 0) / 2) =
      (be k l * (if k = i then (1 : ℝ) else 0) * (if l = i then (1 : ℝ) else 0)) / 4 := by
    intro k l; ring
  simp only [h4, ← Finset.sum_div]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- The mixed jet entry of a symmetric 4-linear map with diagonal `24 Q4`. -/
theorem mixed_osc (be : Matrix (Fin b) (Fin b) ℝ) (hbe : be.IsSymm) (i j : Fin b) (hij : i ≠ j)
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => RY b) ℝ)
    (hM : ∀ (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → RY b), M (v ∘ σ) = M v)
    (hd : ∀ y, M (fun _ => y) = 24 * oscQ4 be y) :
    M ![yvec b i, yvec b i, yvec b j, yvec b j] = be i j := by
  have h := mixed_value M hM (yvec b i) (yvec b j) (3 * be j j) (3 * (be j i + be i j))
    (3 * be i i) (fun t => by rw [hd, oscQ4_line be i j hij]; ring)
  rw [h]
  have : be j i = be i j := by
    have := congrFun (congrFun hbe i) j
    simpa [Matrix.transpose_apply] using this
  rw [this]; ring

end KAM.Planetary

end
