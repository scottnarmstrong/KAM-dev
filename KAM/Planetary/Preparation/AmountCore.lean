/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakMeasure.ChartScaling

/-!
# Amount transfer helpers (P11A-P8c, `bpP:p11:amount`)

Parametric exported helpers for the steps of `bpP:p11:amount` (they are not the signed `amount`):

* `amount_norm` (`stepP:p11:am-norm`): `beta_{2,mu}(diag(1, eps) w, K) ≥ eps^2 beta_{2,mu}(w, K)`.
* `amount_dir` (`stepP:p11:am-dir`): the stability transfer in the action variable `J`.
* `amount_scale` (`stepP:p11:am-scale`): the `eps^nu` rescaling of the `J`-derivatives in the
  directions `(a, 0)`, giving `eps^mu b ≤` the full tensor norm at `(r, rho')`.
* `amount_transfer`: the combination, `(1/2) eps^(mu+2) beta_J ≤ index_def 2 mu (diag(1, eps) w) K`.

The prepared conclusions the signed `amount` consumes enter only as hypotheses of the shape
produced by `bpP:p11:prepared` (c) and `bpP:p11:holo-chart` (a).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

section Diag

variable {n : ℕ}

/-- The diagonal matrix `diag(1_n, eps 1_n)` applied to a `2n`-vector. -/
def p11DiagVec (eps : ℝ) (v : P11Vec (n+n)) : P11Vec (n+n) :=
  Fin.append (fun i : Fin n => v (Fin.castAdd n i)) (fun i : Fin n => eps * v (Fin.natAdd n i))

theorem p11dot_diagVec (eps : ℝ) (c v : P11Vec (n+n)) :
    p11dot c (p11DiagVec eps v) = p11dot (p11DiagVec eps c) v := by
  simp only [p11dot, p11DiagVec, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem p11euclid_sq {m : ℕ} (x : P11Vec m) : p11euclid x ^ 2 = ∑ i, x i ^ 2 := by
  simp only [p11euclid, KAM.Nekhoroshev.euclid, Real.norm_eq_abs, sq_abs]
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

theorem p11euclid_diagVec_sq (eps : ℝ) (c : P11Vec (n+n)) :
    p11euclid (p11DiagVec eps c) ^ 2 =
      (∑ i : Fin n, c (Fin.castAdd n i) ^ 2) + eps ^ 2 * ∑ i : Fin n, c (Fin.natAdd n i) ^ 2 := by
  rw [p11euclid_sq]
  simp only [p11DiagVec, Fin.sum_univ_add, Fin.append_left, Fin.append_right, mul_pow,
    Finset.mul_sum]

theorem p11euclid_diagVec_bounds {eps : ℝ} (he0 : 0 < eps) (he1 : eps ≤ 1) {c : P11Vec (n+n)}
    (hc : p11euclid c = 1) :
    eps ^ 2 ≤ p11euclid (p11DiagVec eps c) ^ 2 := by
  have h1 : (∑ i : Fin n, c (Fin.castAdd n i) ^ 2) + ∑ i : Fin n, c (Fin.natAdd n i) ^ 2 = 1 := by
    have := p11euclid_sq c
    rw [hc, Fin.sum_univ_add] at this
    linarith
  have hB : 0 ≤ ∑ i : Fin n, c (Fin.natAdd n i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hA : 0 ≤ ∑ i : Fin n, c (Fin.castAdd n i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [p11euclid_diagVec_sq]
  have : eps ^ 2 ≤ 1 := pow_le_one₀ he0.le he1
  nlinarith

theorem p11dot_smul_left {m : ℕ} (t : ℝ) (c v : P11Vec m) : p11dot (t • c) v = t * p11dot c v := by
  simp only [p11dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Scalar multiples can only increase the maximal jet by the factor, at points of smoothness. -/
theorem p11maxJet_smul_ge {d : ℕ} (hd : 1 ≤ d) {G : P11Vec d → P11Vec 1} {y : P11Vec d} {mu : ℕ}
    (hG : ∀ j ≤ mu, ContDiffAt ℝ j G y) {t : ℝ} (ht : 0 ≤ t) :
    t * p11maxJet mu G y ≤ p11maxJet mu (t • G) y := by
  obtain ⟨j, hj, e⟩ := p11maxJet_attained G y mu
  rw [e]
  obtain ⟨a, ha, h⟩ := p11dg_attained G j y hd
  have := le_p11dg (t • G) j y a ha
  rw [iteratedFDeriv_const_smul_apply (hG j hj)] at this
  have h2 : t * p11dg G j y ≤ p11dg (t • G) j y := by
    rw [h]
    simpa [p11_euclid_smul, abs_of_nonneg ht] using this
  exact h2.trans (le_p11maxJet (t • G) y mu hj)

/-- `stepP:p11:am-norm`: `g_2[D w](c, .) = |Dc|^2 g_2[w](c-hat, .)` with `eps ≤ |Dc| ≤ 1`, hence
`beta_{2,mu}(D w, K) ≥ eps^2 beta_{2,mu}(w, K)`. -/
theorem amount_norm {d n mu : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {V K : Set (P11Vec d)}
    (hV : IsOpen V) (hKV : K ⊆ V) (hne : K.Nonempty) {w : P11Vec d → P11Vec (n+n)}
    (hw : ContDiffOn ℝ mu w V) {eps : ℝ} (he0 : 0 < eps) (he1 : eps ≤ 1) :
    eps ^ 2 * index_def 2 mu w K ≤ index_def 2 mu (fun y => p11DiagVec eps (w y)) K := by
  refine le_index_def (by omega) 2 mu _ hne fun c hc y hy => ?_
  set s := p11euclid (p11DiagVec eps c) with hs
  have hs2 : eps ^ 2 ≤ s ^ 2 := p11euclid_diagVec_bounds he0 he1 hc
  have hs0 : 0 < s := by
    rcases (p11euclid_nonneg (p11DiagVec eps c)).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← hs] at h
      rw [← h] at hs2
      nlinarith [sq_pos_of_pos he0]
  set c' : P11Vec (n+n) := s⁻¹ • p11DiagVec eps c with hc'
  have hc'1 : p11euclid c' = 1 := by
    rw [hc', p11_euclid_smul, abs_of_pos (inv_pos.2 hs0), ← hs, inv_mul_cancel₀ hs0.ne']
  have hfun : p11scalar 2 (fun y => p11DiagVec eps (w y)) c = (s ^ 2) • p11scalar 2 w c' := by
    funext y i
    simp only [p11scalar, p11dot_diagVec, hc', p11dot_smul_left, Pi.smul_apply, smul_eq_mul]
    field_simp
  have hat : ∀ j ≤ mu, ContDiffAt ℝ j (p11scalar 2 w c') y := fun j hj =>
    ((contDiffOn_p11scalar hw 2 c').of_le (by exact_mod_cast hj)).contDiffAt
      (hV.mem_nhds (hKV hy))
  have h1 := index_def_le 2 mu w hc'1 hy
  have h2 := p11maxJet_smul_ge hd hat (sq_nonneg s)
  rw [hfun]
  have hnn := index_def_nonneg 2 mu w K
  calc eps ^ 2 * index_def 2 mu w K ≤ s ^ 2 * index_def 2 mu w K :=
        mul_le_mul_of_nonneg_right hs2 hnn
    _ ≤ s ^ 2 * p11maxJet mu (p11scalar 2 w c') y :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg s)
    _ ≤ _ := h2

end Diag

end KAM.Planetary

end
