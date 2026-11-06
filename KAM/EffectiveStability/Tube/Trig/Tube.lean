/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Trig.TubeClose
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Tube models: polynomials in the action deviations (T2-CONF, N3)

A tube model is a polynomial in `u : Fin 3 → ℝ` with coefficient functions of the angles,
indexed by a finite set `s` with monomial map `μ : ι → (Fin 3 → ℕ)`:
`tmEval s μ g u φ = Σ_{i ∈ s} u^{μ i} g_i(φ)`, `u^m = Π_j u_j^{m_j}` (`umon`), `|m| = Σ_j m_j`
(`mdeg`). The coefficients are trigonometric polynomials in the checker; here they are any
differentiable functions with sup bounds.

Main results:
* `abs_umon_le`: `|u^m| ≤ r^{|m|}` on the box; `upd_umon`: `∂_{u_j} u^m = m_j u^{m - e_j}`;
* `pderiv_tmEval`, `upd_tmEval`: the `φ`- and `u`-derivatives of a model are models
  (`∂_φ` acts on the coefficients; `∂_{u_j}` maps `u^m g` to `m_j u^{m - e_j} g`);
* `abs_tmEval_le`: the sup over the box is at most `Σ_i G_i r^{|μ i|}`;
* `tubeClose_tmEval_zero`: a model is `C¹`-close to `0` on the box with errors
  `Σ G_i r^{|μ i|}`, `Σ G'_i r^{|μ i|}`, `Σ |μ i| G_i r^{|μ i| - 1}`; this bounds every dropped
  part;
* `tmEval_mul`: the product of two models is the model over pairs, monomials added;
  `tmEval_split`: split by a predicate (the degree truncation `|m + n| ≤ L`);
* `tmEval_regroup`: regroup a model by its monomials (the coefficient of `u^p` is the sum of the
  coefficients with `μ i = p`);
* `sum_pairs_deg_eq`: the dropped bound by **degree profiles**:
  `Σ_{|m| + |n| > L} G_m H_n r^{|m| + |n|} = Σ_{d + e > L} A_d B_e r^{d + e}` with
  `A_d = Σ_{|m| = d} G_m`, `B_e = Σ_{|n| = e} H_n`.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset

/-! ### Monomials -/

/-- The monomial `u^m = Π_j u_j^{m_j}`. -/
def umon (m : Fin 3 → ℕ) (u : Fin 3 → ℝ) : ℝ := ∏ j, u j ^ m j

/-- The total degree `|m| = Σ_j m_j`. -/
def mdeg (m : Fin 3 → ℕ) : ℕ := ∑ j, m j

theorem mdeg_add (m n : Fin 3 → ℕ) : mdeg (m + n) = mdeg m + mdeg n := by
  simp [mdeg, sum_add_distrib]

theorem umon_add (m n : Fin 3 → ℕ) (u : Fin 3 → ℝ) : umon (m + n) u = umon m u * umon n u := by
  simp [umon, pow_add, prod_mul_distrib]

theorem InBox.nonneg {r : ℝ} {u : Fin 3 → ℝ} (hu : InBox r u) : 0 ≤ r :=
  (abs_nonneg _).trans (hu 0)

theorem abs_umon_le {r : ℝ} {u : Fin 3 → ℝ} (hu : InBox r u) (m : Fin 3 → ℕ) :
    |umon m u| ≤ r ^ mdeg m := by
  rw [umon, abs_prod, mdeg, ← prod_pow_eq_pow_sum]
  exact prod_le_prod₀ (fun j _ => by positivity) fun j _ => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hu j) _

theorem hasFDerivAt_umon (m : Fin 3 → ℕ) (u : Fin 3 → ℝ) :
    HasFDerivAt (umon m) (∑ i, (∏ k ∈ univ.erase i, u k ^ m k) •
      (((m i : ℝ) * u i ^ (m i - 1)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i))
      u := by
  have h : ∀ i ∈ (univ : Finset (Fin 3)), HasFDerivAt (fun v : Fin 3 → ℝ => v i ^ m i)
      (((m i : ℝ) * u i ^ (m i - 1)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i)
      u := fun i _ => HasDerivAt.comp_hasFDerivAt u (hasDerivAt_pow (m i) (u i))
        (hasFDerivAt_apply i u)
  exact HasFDerivAt.finsetProd h

theorem differentiable_umon (m : Fin 3 → ℕ) : Differentiable ℝ (umon m) :=
  fun u => (hasFDerivAt_umon m u).differentiableAt

/-- `∂_{u_j} u^m = m_j u^{m - e_j}`. -/
theorem fderiv_umon (m : Fin 3 → ℕ) (u : Fin 3 → ℝ) (j : Fin 3) :
    fderiv ℝ (umon m) u (Pi.single j 1) = (m j : ℝ) * umon (m - Pi.single j 1) u := by
  rw [(hasFDerivAt_umon m u).fderiv, _root_.sum_apply, sum_eq_single j]
  · simp only [smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      Pi.single_eq_same, mul_one]
    rw [umon, ← mul_prod_erase univ _ (mem_univ j)]
    have hj : (m - Pi.single j 1 : Fin 3 → ℕ) j = m j - 1 := by simp
    have hk : ∀ k ∈ univ.erase j, u k ^ (m - Pi.single j 1 : Fin 3 → ℕ) k = u k ^ m k :=
      fun k hk => by simp [ne_of_mem_erase hk]
    rw [hj, prod_congr rfl hk]
    ring
  · intro i _ hij
    simp [Pi.single_apply, hij]
  · simp

theorem abs_fderiv_umon_le {r : ℝ} {u : Fin 3 → ℝ} (hu : InBox r u) (m : Fin 3 → ℕ)
    (j : Fin 3) :
    |fderiv ℝ (umon m) u (Pi.single j 1)| ≤ (mdeg m : ℝ) * r ^ (mdeg m - 1) := by
  have hr := hu.nonneg
  rw [fderiv_umon, abs_mul, Nat.abs_cast]
  by_cases h0 : m j = 0
  · rw [h0, Nat.cast_zero, zero_mul]; positivity
  have hdeg : mdeg (m - Pi.single j 1) = mdeg m - 1 := by
    have : m = (m - Pi.single j 1) + Pi.single j 1 := by
      funext k
      by_cases hk : k = j
      · subst hk; simp; omega
      · simp [Pi.single_apply, hk]
    conv_rhs => rw [this, mdeg_add]
    simp [mdeg]
  have hmj : (m j : ℝ) ≤ mdeg m := by
    have : m j ≤ mdeg m := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)
    exact_mod_cast this
  calc (m j : ℝ) * |umon (m - Pi.single j 1) u| ≤ (mdeg m : ℝ) * r ^ (mdeg m - 1) := by
        rw [← hdeg]
        exact mul_le_mul hmj (abs_umon_le hu _) (abs_nonneg _) (Nat.cast_nonneg _)

/-! ### Models -/

/-- A tube model `Σ_{i ∈ s} u^{μ i} g_i(φ)`. -/
noncomputable def tmEval {ι : Type*} (s : Finset ι) (μ : ι → Fin 3 → ℕ)
    (g : ι → (Fin 2 → ℝ) → ℝ) (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) : ℝ :=
  ∑ i ∈ s, umon (μ i) u * g i φ

variable {ι κ : Type*}

theorem tubeDiff_tmEval (s : Finset ι) (μ : ι → Fin 3 → ℕ) {g : ι → (Fin 2 → ℝ) → ℝ}
    (hg : ∀ i ∈ s, Differentiable ℝ (g i)) (r : ℝ) : TubeDiff (tmEval s μ g) r := by
  refine ⟨fun u _ => ?_, fun u _ φ => ?_⟩
  · have : tmEval s μ g u = fun φ => ∑ i ∈ s, umon (μ i) u * g i φ := rfl
    rw [this]
    exact Differentiable.fun_sum fun i hi => (hg i hi).const_mul _
  · have : (fun v => tmEval s μ g v φ) = fun v => ∑ i ∈ s, umon (μ i) v * g i φ := rfl
    rw [this]
    exact (Differentiable.fun_sum fun i _ => (differentiable_umon (μ i)).mul_const _) u

/-- The `φ`-derivative of a model acts on the coefficients. -/
theorem pderiv_tmEval (s : Finset ι) (μ : ι → Fin 3 → ℕ) {g : ι → (Fin 2 → ℝ) → ℝ}
    (hg : ∀ i ∈ s, Differentiable ℝ (g i)) (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (a : Fin 2) :
    pderiv (tmEval s μ g u) φ a = tmEval s μ (fun i ψ => pderiv (g i) ψ a) u φ := by
  have h : ∀ i ∈ s, HasFDerivAt (fun ψ => umon (μ i) u * g i ψ)
      (umon (μ i) u • fderiv ℝ (g i) φ) φ := fun i hi =>
    ((hg i hi) φ).hasFDerivAt.const_mul _
  have hs := HasFDerivAt.fun_sum h
  rw [pderiv, show tmEval s μ g u = fun ψ => ∑ i ∈ s, umon (μ i) u * g i ψ from rfl, hs.fderiv,
    _root_.sum_apply, tmEval]
  rfl

/-- The `u`-derivative of a model: `∂_{u_j} (u^m g) = m_j u^{m - e_j} g`. -/
theorem upd_tmEval (s : Finset ι) (μ : ι → Fin 3 → ℕ) (g : ι → (Fin 2 → ℝ) → ℝ)
    (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (j : Fin 3) :
    upd (tmEval s μ g) u φ j =
      ∑ i ∈ s, ((μ i j : ℝ) * umon (μ i - Pi.single j 1) u) * g i φ := by
  have h : ∀ i ∈ s, HasFDerivAt (fun v => umon (μ i) v * g i φ)
      (g i φ • fderiv ℝ (umon (μ i)) u) u := fun i _ =>
    (differentiable_umon (μ i) u).hasFDerivAt.mul_const _
  have hs := HasFDerivAt.fun_sum h
  rw [upd, show (fun v => tmEval s μ g v φ) = fun v => ∑ i ∈ s, umon (μ i) v * g i φ from rfl,
    hs.fderiv, _root_.sum_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [smul_apply, fderiv_umon, smul_eq_mul]
  ring

/-! ### Sup bounds on the box -/

theorem abs_tmEval_le (s : Finset ι) (μ : ι → Fin 3 → ℕ) (g : ι → (Fin 2 → ℝ) → ℝ)
    {G : ι → ℝ} (hG : ∀ i ∈ s, ∀ φ, |g i φ| ≤ G i) {r : ℝ} {u : Fin 3 → ℝ} (hu : InBox r u)
    (φ : Fin 2 → ℝ) : |tmEval s μ g u φ| ≤ ∑ i ∈ s, G i * r ^ mdeg (μ i) := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
  rw [abs_mul, mul_comm]
  exact mul_le_mul (hG i hi φ) (abs_umon_le hu _) (abs_nonneg _)
    ((abs_nonneg _).trans (hG i hi φ))

theorem abs_pderiv_tmEval_le (s : Finset ι) (μ : ι → Fin 3 → ℕ) {g : ι → (Fin 2 → ℝ) → ℝ}
    (hg : ∀ i ∈ s, Differentiable ℝ (g i)) {G₁ : ι → ℝ}
    (hG : ∀ i ∈ s, ∀ φ a, |pderiv (g i) φ a| ≤ G₁ i) {r : ℝ} {u : Fin 3 → ℝ} (hu : InBox r u)
    (φ : Fin 2 → ℝ) (a : Fin 2) :
    |pderiv (tmEval s μ g u) φ a| ≤ ∑ i ∈ s, G₁ i * r ^ mdeg (μ i) := by
  rw [pderiv_tmEval s μ hg]
  exact abs_tmEval_le s μ _ (fun i hi φ => hG i hi φ a) hu φ

theorem abs_upd_tmEval_le (s : Finset ι) (μ : ι → Fin 3 → ℕ) (g : ι → (Fin 2 → ℝ) → ℝ)
    {G : ι → ℝ} (hG : ∀ i ∈ s, ∀ φ, |g i φ| ≤ G i) {r : ℝ} {u : Fin 3 → ℝ} (hu : InBox r u)
    (φ : Fin 2 → ℝ) (j : Fin 3) :
    |upd (tmEval s μ g) u φ j| ≤ ∑ i ∈ s, (mdeg (μ i) : ℝ) * G i * r ^ (mdeg (μ i) - 1) := by
  rw [upd_tmEval]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
  rw [abs_mul, ← fderiv_umon]
  have h1 := abs_fderiv_umon_le hu (μ i) j
  have h2 := hG i hi φ
  calc |fderiv ℝ (umon (μ i)) u (Pi.single j 1)| * |g i φ|
      ≤ ((mdeg (μ i) : ℝ) * r ^ (mdeg (μ i) - 1)) * G i :=
        mul_le_mul h1 h2 (abs_nonneg _) (by have := hu.nonneg; positivity)
    _ = _ := by ring

/-- **A model is `C¹`-close to zero on the box** with its sup bounds: the form in which every
dropped part (dropped degrees, dropped modes) enters the error. -/
theorem tubeClose_tmEval_zero (s : Finset ι) (μ : ι → Fin 3 → ℕ) {g : ι → (Fin 2 → ℝ) → ℝ}
    (hg : ∀ i ∈ s, Differentiable ℝ (g i)) {G G₁ : ι → ℝ} (hG : ∀ i ∈ s, ∀ φ, |g i φ| ≤ G i)
    (hG₁ : ∀ i ∈ s, ∀ φ a, |pderiv (g i) φ a| ≤ G₁ i) (r : ℝ) :
    TubeClose (tmEval s μ g) (fun _ _ => 0) r (∑ i ∈ s, G i * r ^ mdeg (μ i))
      (∑ i ∈ s, G₁ i * r ^ mdeg (μ i))
      (∑ i ∈ s, (mdeg (μ i) : ℝ) * G i * r ^ (mdeg (μ i) - 1)) := by
  have hd := tubeDiff_tmEval s μ hg r
  refine ⟨hd.φ, fun _ _ => differentiable_const 0, hd.u, fun _ _ _ => differentiableAt_const 0,
    fun u hu φ => ?_, fun u hu φ a => ?_, fun u hu φ j => ?_⟩
  · rw [sub_zero]; exact abs_tmEval_le s μ g hG hu φ
  · rw [show pderiv (fun _ : Fin 2 → ℝ => (0 : ℝ)) φ a = 0 by simp [pderiv], sub_zero]
    exact abs_pderiv_tmEval_le s μ hg hG₁ hu φ a
  · rw [show upd (fun _ _ => (0 : ℝ)) u φ j = 0 by simp [upd], sub_zero]
    exact abs_upd_tmEval_le s μ g hG hu φ j

/-! ### Products, truncation and regrouping -/

/-- **The product of two models** is the model over pairs, with added monomials and multiplied
coefficients. -/
theorem tmEval_mul (s : Finset ι) (t : Finset κ) (μ : ι → Fin 3 → ℕ) (ν : κ → Fin 3 → ℕ)
    (g : ι → (Fin 2 → ℝ) → ℝ) (h : κ → (Fin 2 → ℝ) → ℝ) (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) :
    tmEval s μ g u φ * tmEval t ν h u φ =
      tmEval (s ×ˢ t) (fun x => μ x.1 + ν x.2) (fun x ψ => g x.1 ψ * h x.2 ψ) u φ := by
  rw [tmEval, tmEval, tmEval, sum_mul_sum, sum_product]
  refine sum_congr rfl fun i _ => sum_congr rfl fun k _ => ?_
  rw [umon_add]
  ring

/-- Split a model by a predicate on its indices (e.g. the degree truncation). -/
theorem tmEval_split (s : Finset ι) (μ : ι → Fin 3 → ℕ) (g : ι → (Fin 2 → ℝ) → ℝ)
    (P : ι → Prop) [DecidablePred P] (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) :
    tmEval s μ g u φ = tmEval (s.filter P) μ g u φ + tmEval (s.filter fun i => ¬ P i) μ g u φ :=
  (sum_filter_add_sum_filter_not s P _).symm

/-- Regroup a model by its monomials: the coefficient of `u^p` is the sum of the coefficients of
the indices with `μ i = p`. -/
theorem tmEval_regroup [DecidableEq (Fin 3 → ℕ)] (s : Finset ι) (μ : ι → Fin 3 → ℕ)
    (g : ι → (Fin 2 → ℝ) → ℝ) (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) :
    tmEval s μ g u φ =
      tmEval (s.image μ) id (fun p ψ => ∑ i ∈ s.filter (fun i => μ i = p), g i ψ) u φ := by
  rw [tmEval, tmEval, ← sum_fiberwise_of_maps_to (g := μ) (t := s.image μ)
    (fun i hi => mem_image_of_mem μ hi)]
  refine sum_congr rfl fun p _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [(mem_filter.mp hi).2]
  rfl

/-! ### Degree profiles -/

/-- **Degree profiles.** A sum over pairs of a weight depending only on the two degrees is the
sum over degree pairs of the profiles `A_d = Σ_{|μ i| = d} G_i`, `B_e = Σ_{|ν k| = e} H_k`. -/
theorem sum_pairs_deg_eq (s : Finset ι) (t : Finset κ) (μ : ι → Fin 3 → ℕ) (ν : κ → Fin 3 → ℕ)
    (G : ι → ℝ) (H : κ → ℝ) (w : ℕ → ℕ → ℝ) (Ds Dt : ℕ)
    (hs : ∀ i ∈ s, mdeg (μ i) ≤ Ds) (ht : ∀ k ∈ t, mdeg (ν k) ≤ Dt) :
    ∑ x ∈ s ×ˢ t, G x.1 * H x.2 * w (mdeg (μ x.1)) (mdeg (ν x.2)) =
      ∑ d ∈ range (Ds + 1), ∑ e ∈ range (Dt + 1),
        (∑ i ∈ s.filter (fun i => mdeg (μ i) = d), G i) *
          (∑ k ∈ t.filter (fun k => mdeg (ν k) = e), H k) * w d e := by
  rw [sum_product, ← sum_fiberwise_of_maps_to (g := fun i => mdeg (μ i)) (t := range (Ds + 1))
    (fun i hi => mem_range.mpr (Nat.lt_succ_of_le (hs i hi)))]
  refine sum_congr rfl fun d _ => ?_
  calc ∑ i ∈ s.filter (fun i => mdeg (μ i) = d), ∑ k ∈ t, G i * H k * w (mdeg (μ i)) (mdeg (ν k))
      = ∑ i ∈ s.filter (fun i => mdeg (μ i) = d), ∑ e ∈ range (Dt + 1),
          ∑ k ∈ t.filter (fun k => mdeg (ν k) = e), G i * H k * w d e := by
        refine sum_congr rfl fun i hi => ?_
        rw [← sum_fiberwise_of_maps_to (s := t) (g := fun k => mdeg (ν k)) (t := range (Dt + 1))
          (fun k hk => mem_range.mpr (Nat.lt_succ_of_le (ht k hk)))]
        refine sum_congr rfl fun e _ => sum_congr rfl fun k hk => ?_
        rw [(mem_filter.mp hi).2, (mem_filter.mp hk).2]
    _ = ∑ e ∈ range (Dt + 1), ∑ i ∈ s.filter (fun i => mdeg (μ i) = d),
          ∑ k ∈ t.filter (fun k => mdeg (ν k) = e), G i * H k * w d e := sum_comm
    _ = _ := by
        refine sum_congr rfl fun e _ => ?_
        rw [sum_mul_sum, sum_mul]
        refine sum_congr rfl fun i _ => ?_
        rw [sum_mul]

/-- **The dropped degrees of a product**, bounded by degree profiles: the part of degree `> L`
of the product of two models (coefficient sup bounds `G`, `H`) is at most
`Σ_{d + e > L} A_d B_e r^{d + e}` on the box. -/
theorem abs_dropped_le (s : Finset ι) (t : Finset κ) (μ : ι → Fin 3 → ℕ) (ν : κ → Fin 3 → ℕ)
    (g : ι → (Fin 2 → ℝ) → ℝ) (h : κ → (Fin 2 → ℝ) → ℝ) {G : ι → ℝ} {H : κ → ℝ}
    (hG : ∀ i ∈ s, ∀ φ, |g i φ| ≤ G i) (hH : ∀ k ∈ t, ∀ φ, |h k φ| ≤ H k) (L Ds Dt : ℕ)
    (hs : ∀ i ∈ s, mdeg (μ i) ≤ Ds) (ht : ∀ k ∈ t, mdeg (ν k) ≤ Dt) {r : ℝ} {u : Fin 3 → ℝ}
    (hu : InBox r u) (φ : Fin 2 → ℝ) :
    |tmEval ((s ×ˢ t).filter fun x => L < mdeg (μ x.1 + ν x.2)) (fun x => μ x.1 + ν x.2)
        (fun x ψ => g x.1 ψ * h x.2 ψ) u φ| ≤
      ∑ d ∈ range (Ds + 1), ∑ e ∈ range (Dt + 1),
        (∑ i ∈ s.filter (fun i => mdeg (μ i) = d), G i) *
          (∑ k ∈ t.filter (fun k => mdeg (ν k) = e), H k) *
            (if L < d + e then r ^ (d + e) else 0) := by
  have hr := hu.nonneg
  have hG0 : ∀ i ∈ s, 0 ≤ G i := fun i hi => (abs_nonneg _).trans (hG i hi 0)
  have hH0 : ∀ k ∈ t, 0 ≤ H k := fun k hk => (abs_nonneg _).trans (hH k hk 0)
  refine (abs_tmEval_le _ _ _ (G := fun x => G x.1 * H x.2) (fun x hx φ => ?_) hu φ).trans ?_
  · have hx' := (mem_filter.mp hx).1
    rw [mem_product] at hx'
    rw [abs_mul]
    exact mul_le_mul (hG _ hx'.1 φ) (hH _ hx'.2 φ) (abs_nonneg _) (hG0 _ hx'.1)
  rw [← sum_pairs_deg_eq s t μ ν G H (fun d e => if L < d + e then r ^ (d + e) else 0) Ds Dt hs ht,
    sum_filter]
  refine sum_le_sum fun x hx => ?_
  rw [mdeg_add]
  split_ifs <;> simp

end KAM.EffectiveStability.Tube

end
