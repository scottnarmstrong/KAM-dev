/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# Planar quartic torsion: vanishing order and iterated derivatives (P11C, package T4)

A real function `f` *vanishes to order `m`* at `0` when it is locally `a ^ m * h a` with `h`
analytic at `0`. Then every iterated derivative of order `< m` vanishes, so two analytic
functions whose difference vanishes to order `m` have the same jet through order `m - 1`.
Also the elementary power-series facts used for the Laplace coefficients.
-/

@[expose] public noncomputable section
open Set Filter Topology
namespace KAM.Planetary

/-- `f` is locally `a ^ m` times a function analytic at `0`. -/
def p11cVanishes (m : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ h : ℝ → ℝ, AnalyticAt ℝ h 0 ∧ f =ᶠ[𝓝 0] fun a => a ^ m * h a

theorem p11cVanishes.mono {m n : ℕ} (hmn : n ≤ m) {f : ℝ → ℝ} (hf : p11cVanishes m f) :
    p11cVanishes n f := by
  obtain ⟨h, hh, hfh⟩ := hf
  refine ⟨fun a => a ^ (m - n) * h a, by fun_prop, hfh.mono fun a ha => ?_⟩
  simp only [ha, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hmn]

theorem p11cVanishes.add {m : ℕ} {f g : ℝ → ℝ} (hf : p11cVanishes m f) (hg : p11cVanishes m g) :
    p11cVanishes m (fun a => f a + g a) := by
  obtain ⟨h, hh, hfh⟩ := hf
  obtain ⟨k, hk, hgk⟩ := hg
  exact ⟨fun a => h a + k a, hh.add hk, (hfh.and hgk).mono fun a ha => by
    simp only [ha.1, ha.2]; ring⟩

theorem p11cVanishes.mul_left {m : ℕ} {f : ℝ → ℝ} (g : ℝ → ℝ) (hg : AnalyticAt ℝ g 0)
    (hf : p11cVanishes m f) : p11cVanishes m (fun a => g a * f a) := by
  obtain ⟨h, hh, hfh⟩ := hf
  exact ⟨fun a => g a * h a, hg.mul hh, hfh.mono fun a ha => by simp only [ha]; ring⟩

theorem p11cVanishes_pow_mul (m : ℕ) {h : ℝ → ℝ} (hh : AnalyticAt ℝ h 0) :
    p11cVanishes m (fun a => a ^ m * h a) :=
  ⟨h, hh, Eventually.of_forall fun _ => rfl⟩

theorem p11c_iteratedDeriv_pow_mul : ∀ (j m : ℕ) {h : ℝ → ℝ}, AnalyticAt ℝ h 0 → j < m →
    iteratedDeriv j (fun a => a ^ m * h a) 0 = 0 := by
  intro j
  induction j with
  | zero =>
    intro m h _ hm
    simp [zero_pow hm.ne']
  | succ j ih =>
    intro m h hh hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hd : deriv (fun a => a ^ (m + 1) * h a) =ᶠ[𝓝 0]
        fun a => a ^ m * (((m : ℝ) + 1) * h a + a * deriv h a) := by
      filter_upwards [hh.eventually_analyticAt] with x hx
      have h1 : HasDerivAt (fun a : ℝ => a ^ (m + 1)) (((m + 1 : ℕ) : ℝ) * x ^ m) x := by
        simpa using hasDerivAt_pow (m + 1) x
      have := (h1.mul hx.differentiableAt.hasDerivAt).deriv
      change deriv (fun a => a ^ (m + 1) * h a) x = _ at this
      rw [this]; push_cast; ring
    rw [iteratedDeriv_succ', (Filter.EventuallyEq.iteratedDeriv_eq j hd)]
    exact ih m (by fun_prop) (by omega)

theorem p11c_iteratedDeriv_eq_of_vanishes {m : ℕ} {f g : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (hg : AnalyticAt ℝ g 0) (hv : p11cVanishes m (fun a => f a - g a)) :
    ∀ j < m, iteratedDeriv j f 0 = iteratedDeriv j g 0 := by
  intro j hj
  obtain ⟨h, hh, hfh⟩ := hv
  have h0 : iteratedDeriv j (fun a => f a - g a) 0 = 0 := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq j hfh]
    exact p11c_iteratedDeriv_pow_mul j m hh hj
  rw [iteratedDeriv_fun_sub (hf.contDiffAt) (hg.contDiffAt)] at h0
  linarith

theorem p11c_iteratedFDeriv_eq_of_vanishes {n m : ℕ} {F G : ℝ → Fin n → ℝ}
    (hF : ∀ i, AnalyticAt ℝ (fun a => F a i) 0) (hG : ∀ i, AnalyticAt ℝ (fun a => G a i) 0)
    (hv : ∀ i, p11cVanishes m (fun a => F a i - G a i)) :
    ∀ j < m, iteratedFDeriv ℝ j F 0 = iteratedFDeriv ℝ j G 0 := by
  intro j hj
  have key : ∀ (H : ℝ → Fin n → ℝ), (∀ i, AnalyticAt ℝ (fun a => H a i) 0) → ∀ i,
      iteratedFDeriv ℝ j (fun a => H a i) 0 (fun _ => 1) = iteratedFDeriv ℝ j H 0 (fun _ => 1) i
          := by
    intro H hH i
    have hc : ContDiffAt ℝ j H 0 := contDiffAt_pi.2 fun i => (hH i).contDiffAt
    have := congrArg (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℝ) ℝ => L (fun _ => (1
        : ℝ)))
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).iteratedFDeriv_comp_left
        (n := j) hc (i := j) le_rfl)
    exact this
  refine ContinuousMultilinearMap.ext_ring (funext fun i => ?_)
  rw [← key F hF i, ← key G hG i, ← iteratedDeriv_eq_iteratedFDeriv,
    ← iteratedDeriv_eq_iteratedFDeriv]
  exact p11c_iteratedDeriv_eq_of_vanishes (hF i) (hG i) (hv i) j hj

end KAM.Planetary
