/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Trig.Tube
public import KAM.EffectiveStability.Tube.Trig.Model

/-!
# Partial derivatives of tube observables from coefficient norms (T2-CONF, N5c)

For an observable of N3's model form `f(u, φ) = Σ_{i ∈ s} u^{μ_i} g_i(φ)` (`tmEval`), read as a
function of the pair `p = (u, φ)` (the form of the tube checker,
`KAM/EffectiveStability/Tube/Check/TubeChart.lean`):

* `differentiable_tmEvalPair`: `f` is differentiable when every `g_i` is;
* `fderiv_tmEvalPair_u`, `fderiv_tmEvalPair_φ`: the joint derivative in the directions
  `(e_l, 0)` and `(0, e_b)`;
* `abs_fderiv_tmEvalPair_u_le`, `abs_fderiv_tmEvalPair_φ_le`: on the box `|u| ≤ ρ`, from coefficient
  norms `|g_i| ≤ G_i` and `|∂_b g_i| ≤ G'_i` (N3's `l1`/`wl1`),
  `|∂_{u_l} f| ≤ Σ_i μ_{i,l} ρ^{|μ_i - e_l|} G_i` and `|∂_{φ_b} f| ≤ Σ_i ρ^{|μ_i|} G'_i`.
  These are the `Fu`, `Fφ` hypotheses of the tube checker.
* `tmEvalPair_add_two_pi`, `evalK_add_two_pi`, `TP.eval_add_two_pi`: `2π`-periodicity in `φ` (the
  checker's `ObsPeriodic`, unfolded).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open Finset

variable {ι : Type*}

/-- A model observable as a function of the pair `(u, φ)`. -/
def tmEvalPair (s : Finset ι) (μ : ι → Fin 3 → ℕ) (g : ι → (Fin 2 → ℝ) → ℝ)
    (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  tmEval s μ g p.1 p.2

theorem hasFDerivAt_tmEvalPair_term (m : Fin 3 → ℕ) {g : (Fin 2 → ℝ) → ℝ}
    (hg : Differentiable ℝ g) (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) :
    HasFDerivAt (fun p : (Fin 3 → ℝ) × (Fin 2 → ℝ) => umon m p.1 * g p.2)
      (umon m p.1 • (fderiv ℝ g p.2).comp (ContinuousLinearMap.snd ℝ (Fin 3 → ℝ) (Fin 2 → ℝ)) +
        g p.2 • (fderiv ℝ (umon m) p.1).comp
          (ContinuousLinearMap.fst ℝ (Fin 3 → ℝ) (Fin 2 → ℝ))) p := by
  have hu : HasFDerivAt (fun p : (Fin 3 → ℝ) × (Fin 2 → ℝ) => umon m p.1)
      ((fderiv ℝ (umon m) p.1).comp (ContinuousLinearMap.fst ℝ (Fin 3 → ℝ) (Fin 2 → ℝ))) p :=
    ((hasFDerivAt_umon m p.1).differentiableAt.hasFDerivAt).comp p hasFDerivAt_fst
  have hgp : HasFDerivAt (fun p : (Fin 3 → ℝ) × (Fin 2 → ℝ) => g p.2)
      ((fderiv ℝ g p.2).comp (ContinuousLinearMap.snd ℝ (Fin 3 → ℝ) (Fin 2 → ℝ))) p :=
    ((hg p.2).hasFDerivAt).comp p hasFDerivAt_snd
  exact hu.mul hgp

theorem hasFDerivAt_tmEvalPair (s : Finset ι) (μ : ι → Fin 3 → ℕ) {g : ι → (Fin 2 → ℝ) → ℝ}
    (hg : ∀ i ∈ s, Differentiable ℝ (g i)) (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) :
    HasFDerivAt (tmEvalPair s μ g)
      (∑ i ∈ s, (umon (μ i) p.1 •
        (fderiv ℝ (g i) p.2).comp (ContinuousLinearMap.snd ℝ (Fin 3 → ℝ) (Fin 2 → ℝ)) +
        g i p.2 • (fderiv ℝ (umon (μ i)) p.1).comp
          (ContinuousLinearMap.fst ℝ (Fin 3 → ℝ) (Fin 2 → ℝ)))) p := by
  have h := HasFDerivAt.fun_sum (u := s) (fun i hi => hasFDerivAt_tmEvalPair_term (μ i) (hg i hi) p)
  have e : tmEvalPair s μ g = fun p => ∑ i ∈ s, umon (μ i) p.1 * g i p.2 := by
    funext p; rfl
  rw [e]
  exact h

theorem differentiable_tmEvalPair (s : Finset ι) (μ : ι → Fin 3 → ℕ) {g : ι → (Fin 2 → ℝ) → ℝ}
    (hg : ∀ i ∈ s, Differentiable ℝ (g i)) : Differentiable ℝ (tmEvalPair s μ g) :=
  fun p => (hasFDerivAt_tmEvalPair s μ hg p).differentiableAt

theorem fderiv_tmEvalPair_u (s : Finset ι) (μ : ι → Fin 3 → ℕ) {g : ι → (Fin 2 → ℝ) → ℝ}
    (hg : ∀ i ∈ s, Differentiable ℝ (g i)) (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) (l : Fin 3) :
    fderiv ℝ (tmEvalPair s μ g) p (Pi.single l 1, 0) =
      ∑ i ∈ s, (μ i l : ℝ) * umon (μ i - Pi.single l 1) p.1 * g i p.2 := by
  rw [(hasFDerivAt_tmEvalPair s μ hg p).fderiv, _root_.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst',
    map_zero, smul_eq_mul, mul_zero, zero_add, fderiv_umon]
  ring

theorem fderiv_tmEvalPair_φ (s : Finset ι) (μ : ι → Fin 3 → ℕ) {g : ι → (Fin 2 → ℝ) → ℝ}
    (hg : ∀ i ∈ s, Differentiable ℝ (g i)) (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) (b : Fin 2) :
    fderiv ℝ (tmEvalPair s μ g) p (0, Pi.single b 1) =
      ∑ i ∈ s, umon (μ i) p.1 * fderiv ℝ (g i) p.2 (Pi.single b 1) := by
  rw [(hasFDerivAt_tmEvalPair s μ hg p).fderiv, _root_.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst',
    map_zero, smul_eq_mul, mul_zero, add_zero]

/-- `|∂_{u_l} f| ≤ Σ_i μ_{i,l} ρ^{|μ_i - e_l|} G_i` on the box `|u| ≤ ρ`. -/
theorem abs_fderiv_tmEvalPair_u_le (s : Finset ι) (μ : ι → Fin 3 → ℕ) {g : ι → (Fin 2 → ℝ) → ℝ}
    (hg : ∀ i ∈ s, Differentiable ℝ (g i)) {G : ι → ℝ} (hG : ∀ i ∈ s, ∀ φ, |g i φ| ≤ G i)
    {ρ : ℝ} {u : Fin 3 → ℝ} (hu : ∀ l, |u l| ≤ ρ) (φ : Fin 2 → ℝ) (l : Fin 3) :
    |fderiv ℝ (tmEvalPair s μ g) (u, φ) (Pi.single l 1, 0)| ≤
      ∑ i ∈ s, (μ i l : ℝ) * ρ ^ mdeg (μ i - Pi.single l 1) * G i := by
  rw [fderiv_tmEvalPair_u s μ hg]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_mul, Nat.abs_cast]
  have h1 := abs_umon_le (r := ρ) hu (μ i - Pi.single l 1)
  have h2 := hG i hi φ
  have h0 : (0 : ℝ) ≤ μ i l := Nat.cast_nonneg _
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 h0) h2 (abs_nonneg _)
    (mul_nonneg h0 ((abs_nonneg _).trans h1))

/-- `|∂_{φ_b} f| ≤ Σ_i ρ^{|μ_i|} G'_i` on the box `|u| ≤ ρ`. -/
theorem abs_fderiv_tmEvalPair_φ_le (s : Finset ι) (μ : ι → Fin 3 → ℕ) {g : ι → (Fin 2 → ℝ) → ℝ}
    (hg : ∀ i ∈ s, Differentiable ℝ (g i)) {b : Fin 2} {G' : ι → ℝ}
    (hG' : ∀ i ∈ s, ∀ φ, |fderiv ℝ (g i) φ (Pi.single b 1)| ≤ G' i)
    {ρ : ℝ} {u : Fin 3 → ℝ} (hu : ∀ l, |u l| ≤ ρ) (φ : Fin 2 → ℝ) :
    |fderiv ℝ (tmEvalPair s μ g) (u, φ) (0, Pi.single b 1)| ≤
      ∑ i ∈ s, ρ ^ mdeg (μ i) * G' i := by
  rw [fderiv_tmEvalPair_φ s μ hg]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
  rw [abs_mul]
  exact mul_le_mul (abs_umon_le hu (μ i)) (hG' i hi φ) (abs_nonneg _)
    ((abs_nonneg _).trans (abs_umon_le hu (μ i)))

/-! ### Periodicity -/

theorem trig_add_int_mul_two_pi (p : Bool) (x : ℝ) (n : ℤ) :
    trig p (x + n * (2 * Real.pi)) = trig p x := by
  cases p <;> simp [trig, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

theorem kdot_add_two_pi (k : ℤ × ℤ) (φ : Fin 2 → ℝ) (m : Fin 2 → ℤ) :
    kdot k (φ + fun a => 2 * Real.pi * m a) =
      kdot k φ + ((k.1 * m 0 + k.2 * m 1 : ℤ) : ℝ) * (2 * Real.pi) := by
  simp only [kdot, Pi.add_apply]; push_cast; ring

theorem evalK_add_two_pi (κ : ℕ → ℤ × ℤ) (p : Bool) (d : List ℤ) (φ : Fin 2 → ℝ)
    (m : Fin 2 → ℤ) : evalK κ p d (φ + fun a => 2 * Real.pi * m a) = evalK κ p d φ := by
  unfold evalK
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kdot_add_two_pi, trig_add_int_mul_two_pi]

theorem TP.eval_add_two_pi (S : ℕ) (x : TP) (φ : Fin 2 → ℝ) (m : Fin 2 → ℤ) :
    x.eval S (φ + fun a => 2 * Real.pi * m a) = x.eval S φ := by
  simp only [TP.eval, evalK_add_two_pi]

/-- `2π`-periodicity of a model observable from that of its coefficients (the tube checker's
`ObsPeriodic`, unfolded). -/
theorem tmEvalPair_add_two_pi (s : Finset ι) (μ : ι → Fin 3 → ℕ) {g : ι → (Fin 2 → ℝ) → ℝ}
    (hg : ∀ i ∈ s, ∀ (φ : Fin 2 → ℝ) (m : Fin 2 → ℤ),
      g i (φ + fun a => 2 * Real.pi * m a) = g i φ) :
    ∀ (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (m : Fin 2 → ℤ),
      tmEvalPair s μ g (u, φ + fun a => 2 * Real.pi * m a) = tmEvalPair s μ g (u, φ) := by
  intro u φ m
  simp only [tmEvalPair, tmEval]
  exact Finset.sum_congr rfl fun i hi => by rw [hg i hi]

end KAM.EffectiveStability.Tube

end
