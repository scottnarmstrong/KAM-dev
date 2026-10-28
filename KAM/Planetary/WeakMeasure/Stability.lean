/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakMeasure.Basic

/-!
# Stability of the amount and size bound for the scalar families (P11A-W1)

`stability` and `M_bound`: iterated Leibniz formulas (diagonal, via the line `t ↦ y + t a`, and the
operator-norm form on `EuclideanSpace`, used only as an internal bridge) and Cauchy-Schwarz.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

section Euclid

variable {n m : ℕ}

/-- The identification of `P11Vec n` with `EuclideanSpace` (internal bridge only). -/
def p11toE : P11Vec n ≃L[ℝ] EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (Fin n) ℝ).symm

theorem p11euclid_eq_norm (x : P11Vec n) : p11euclid x = ‖p11toE x‖ := by
  simp [p11toE, p11euclid, KAM.Nekhoroshev.euclid, EuclideanSpace.norm_eq]

theorem p11euclid_add_le (x y : P11Vec n) : p11euclid (x + y) ≤ p11euclid x + p11euclid y := by
  simp only [p11euclid_eq_norm, map_add]
  exact norm_add_le _ _

theorem p11euclid_sub_le (x y : P11Vec n) : p11euclid (x - y) ≤ p11euclid x + p11euclid y := by
  simp only [p11euclid_eq_norm, map_sub]
  exact (norm_sub_le _ _)

theorem p11euclid_one (r : ℝ) : p11euclid (fun _ : Fin 1 => r) = |r| := by
  simp [p11euclid, KAM.Nekhoroshev.euclid, Real.sqrt_sq_eq_abs]

theorem abs_p11dot_le (c v : P11Vec m) : |p11dot c v| ≤ p11euclid c * p11euclid v := by
  simp only [p11euclid_eq_norm]
  have := abs_real_inner_le_norm (p11toE c) (p11toE v)
  convert this using 2
  simp [p11dot, p11toE, PiLp.inner_apply, mul_comm]

end Euclid

section Jets

variable {n m : ℕ}

/-- The coefficient functional `v ↦ p11dot c v` as a continuous linear map. -/
def p11lin (c : P11Vec m) : P11Vec m →L[ℝ] ℝ :=
  ∑ i, c i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i

theorem p11lin_apply (c v : P11Vec m) : p11lin c v = p11dot c v := by
  simp [p11lin, p11dot]

/-- Embedding of scalars as `P11Vec 1`. -/
def p11const : ℝ →L[ℝ] P11Vec 1 :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ ℝ

theorem p11const_apply (r : ℝ) : p11const r = fun _ => r := rfl

theorem iteratedFDeriv_dot {w : P11Vec n → P11Vec m} {y : P11Vec n} {j : ℕ}
    (hw : ContDiffAt ℝ j w y) (c : P11Vec m) (a : Fin j → P11Vec n) :
    iteratedFDeriv ℝ j (fun x => p11dot c (w x)) y a = p11dot c (iteratedFDeriv ℝ j w y a) := by
  have := (p11lin c).iteratedFDeriv_comp_left hw (i := j) le_rfl
  have h2 : (fun x => p11dot c (w x)) = (p11lin c) ∘ w := by
    funext x; simp [p11lin_apply]
  rw [h2, this]
  simp [p11lin_apply]

theorem abs_iteratedFDeriv_dot_le {w : P11Vec n → P11Vec m} {y : P11Vec n} {j : ℕ}
    (hw : ContDiffAt ℝ j w y) (c : P11Vec m) (a : Fin j → P11Vec n) :
    |iteratedFDeriv ℝ j (fun x => p11dot c (w x)) y a| ≤
      p11euclid c * p11euclid (iteratedFDeriv ℝ j w y a) := by
  rw [iteratedFDeriv_dot hw]
  exact abs_p11dot_le _ _

theorem p11euclid_iteratedFDeriv_scalar {g : P11Vec n → ℝ} {y : P11Vec n} {j : ℕ}
    (hg : ContDiffAt ℝ j g y) (a : Fin j → P11Vec n) :
    p11euclid (iteratedFDeriv ℝ j (fun x => (fun _ : Fin 1 => g x)) y a) =
      |iteratedFDeriv ℝ j g y a| := by
  have h := p11const.iteratedFDeriv_comp_left hg (i := j) le_rfl
  have h2 : (fun x => (fun _ : Fin 1 => g x)) = p11const ∘ g := by
    funext x; rfl
  rw [h2, h]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  exact p11euclid_one _

/-- Diagonal gauge of a scalar function (as a `P11Vec 1`-valued one) from unit-direction bounds. -/
theorem p11dg_scalar_le {g : P11Vec n → ℝ} {y : P11Vec n} {j : ℕ}
    (hg : ContDiffAt ℝ j g y) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ a : P11Vec n, p11euclid a = 1 → |iteratedFDeriv ℝ j g y (fun _ => a)| ≤ B) :
    p11dg (fun x => (fun _ : Fin 1 => g x)) j y ≤ B := by
  unfold p11dg
  refine Real.sSup_le ?_ hB
  rintro v ⟨a, ha, rfl⟩
  rw [p11euclid_iteratedFDeriv_scalar hg]
  exact h a ha

theorem abs_jet_dot_le_of_p11dg {w : P11Vec n → P11Vec m} {y : P11Vec n} {j : ℕ}
    (hw : ContDiffAt ℝ j w y) {c : P11Vec m} (hc : p11euclid c = 1) {B : ℝ}
    (hB : p11dg w j y ≤ B) (a : P11Vec n) (ha : p11euclid a = 1) :
    |iteratedFDeriv ℝ j (fun x => p11dot c (w x)) y (fun _ => a)| ≤ B := by
  refine (abs_iteratedFDeriv_dot_le hw c _).trans ?_
  rw [hc, one_mul]
  exact (le_p11dg w j y a ha).trans hB

end Jets

section Leibniz

variable {n : ℕ}

private theorem p11line_isOpen {V : Set (P11Vec n)} (hV : IsOpen V) (y a : P11Vec n) :
    IsOpen ((ContinuousLinearMap.toSpanSingleton ℝ a) ⁻¹' ((fun z => y + z) ⁻¹' V)) :=
  (hV.preimage (continuous_const.add continuous_id)).preimage (ContinuousLinearMap.continuous _)

/-- The `j`-th derivative of `f` along the line `t ↦ y + t a` is the diagonal jet. -/
theorem p11line_iteratedDeriv {f : P11Vec n → ℝ} {V : Set (P11Vec n)} (hV : IsOpen V) {j : ℕ}
    (hf : ContDiffOn ℝ j f V) {y : P11Vec n} (hy : y ∈ V) (a : P11Vec n) :
    iteratedDeriv j (fun t : ℝ => f (y + t • a)) 0 = iteratedFDeriv ℝ j f y (fun _ => a) := by
  set g := ContinuousLinearMap.toSpanSingleton ℝ a with hg
  set V' : Set (P11Vec n) := (fun z => y + z) ⁻¹' V with hV'
  have hV'o : IsOpen V' := hV.preimage (continuous_const.add continuous_id)
  have hf' : ContDiffOn ℝ j (fun z => f (y + z)) V' :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun z hz => hz)
  have h0 : g 0 ∈ V' := by simpa [hV'] using hy
  have h1 := g.iteratedFDerivWithin_comp_right hf' hV'o.uniqueDiffOn
    (p11line_isOpen hV y a).uniqueDiffOn h0 (i := j) le_rfl
  have h0' : (0 : ℝ) ∈ (ContinuousLinearMap.toSpanSingleton ℝ a) ⁻¹' V' := by
    simpa [hg, hV'] using hy
  rw [iteratedFDerivWithin_of_isOpen _ (p11line_isOpen hV y a) h0',
    iteratedFDerivWithin_of_isOpen _ hV'o h0] at h1
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have e : (fun t : ℝ => f (y + t • a)) = (fun z => f (y + z)) ∘ g := by
    funext t; simp [hg]
  rw [e, h1, iteratedFDeriv_comp_add_left]
  simp [hg]

theorem p11line_contDiffAt {f : P11Vec n → ℝ} {V : Set (P11Vec n)} (hV : IsOpen V) {j : ℕ}
    (hf : ContDiffOn ℝ j f V) {y : P11Vec n} (hy : y ∈ V) (a : P11Vec n) :
    ContDiffAt ℝ j (fun t : ℝ => f (y + t • a)) 0 := by
  have h1 : ContDiffAt ℝ j f (y + (0 : ℝ) • a) := by
    simpa using hf.contDiffAt (hV.mem_nhds hy)
  exact h1.comp (0 : ℝ) (by fun_prop)

/-- Iterated Leibniz formula for equal arguments (`bpP:p11a:f-leib`, diagonal form). -/
theorem p11leibniz_diag {f h : P11Vec n → ℝ} {V : Set (P11Vec n)} (hV : IsOpen V) {j : ℕ}
    (hf : ContDiffOn ℝ j f V) (hh : ContDiffOn ℝ j h V) {y : P11Vec n} (hy : y ∈ V)
    (a : P11Vec n) :
    iteratedFDeriv ℝ j (fun x => f x * h x) y (fun _ => a) =
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        iteratedFDeriv ℝ i f y (fun _ => a) * iteratedFDeriv ℝ (j - i) h y (fun _ => a) := by
  have hfh : ContDiffOn ℝ j (fun x => f x * h x) V := hf.mul hh
  rw [← p11line_iteratedDeriv hV hfh hy a]
  have e : (fun t : ℝ => f (y + t • a) * h (y + t • a)) =
      (fun t : ℝ => f (y + t • a)) * (fun t : ℝ => h (y + t • a)) := rfl
  rw [e, iteratedDeriv_mul (p11line_contDiffAt hV hf hy a) (p11line_contDiffAt hV hh hy a)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [p11line_iteratedDeriv hV (hf.of_le (by exact_mod_cast hi')) hy a,
    p11line_iteratedDeriv hV (hh.of_le (by exact_mod_cast Nat.sub_le j i)) hy a]

end Leibniz

end KAM.Planetary
