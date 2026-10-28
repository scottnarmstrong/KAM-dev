/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# Divided differences (blueprint `bpP:p11a:divided-difference`)

For `f` of class `C^q` on `[a,b]` and strictly increasing nodes `t₀ < ⋯ < t_q` in `[a,b]`, the
divided difference `∑ᵢ f(tᵢ) / ∏_{j≠i}(tᵢ - tⱼ)` equals `f^{(q)}(ξ) / q!` for some `ξ ∈ (t₀, t_q)`
(`KAM.Planetary.divided_difference`).

The proof interpolates `f` at the nodes by `Lagrange.interpolate` (the interpolation coefficient is
the `q`-th derivative of the interpolant divided by `q!`; step `stepP:p11a:dd-interp`) and applies
Rolle's theorem `q` times to the difference `f - P` (step `stepP:p11a:dd-rolle`, `p11Rolle_step`).
-/

@[expose] public noncomputable section

open Set Polynomial

namespace KAM.Planetary

/-- Iterated Rolle at level `k`: a `C^k` function vanishing at `k+1` increasing nodes in `[a,b]`
has a vanishing `k`-th derivative in the closed hull of the nodes. -/
def P11RolleIcc (k : ℕ) : Prop :=
  ∀ (a b : ℝ) (g : ℝ → ℝ), ContDiffOn ℝ k g (Icc a b) → ∀ t : Fin (k + 1) → ℝ, StrictMono t →
    (∀ i, a ≤ t i) → (∀ i, t i ≤ b) → (∀ i, g (t i) = 0) →
    ∃ ξ ∈ Icc (t 0) (t (Fin.last k)), iteratedDeriv k g ξ = 0

/-- One Rolle step: level `k` gives level `k+1`, with a zero in the open hull of the nodes. -/
theorem p11Rolle_step {k : ℕ} (IH : P11RolleIcc k) {a b : ℝ} {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ (k + 1) g (Icc a b)) (t : Fin (k + 2) → ℝ) (ht : StrictMono t)
    (ha : ∀ i, a ≤ t i) (hb : ∀ i, t i ≤ b) (h0 : ∀ i, g (t i) = 0) :
    ∃ ξ ∈ Ioo (t 0) (t (Fin.last (k + 1))), iteratedDeriv (k + 1) g ξ = 0 := by
  have hcont : ContinuousOn g (Icc a b) := hg.continuousOn
  have hr : ∀ i : Fin (k + 1), ∃ s ∈ Ioo (t i.castSucc) (t i.succ), deriv g s = 0 := fun i =>
    exists_deriv_eq_zero (ht (Fin.castSucc_lt_succ))
      (hcont.mono (Icc_subset_Icc (ha _) (hb _))) (by rw [h0, h0])
  choose s hs hs0 using hr
  have hsm : StrictMono s := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    calc s i.castSucc < t i.castSucc.succ := (hs _).2
      _ = t i.succ.castSucc := by rw [Fin.succ_castSucc]
      _ < s i.succ := (hs _).1
  have hsub : Icc (s 0) (s (Fin.last k)) ⊆ Ioo a b := fun x hx =>
    ⟨lt_of_lt_of_le (lt_of_le_of_lt (ha _) (hs 0).1) hx.1,
      lt_of_le_of_lt hx.2 (lt_of_lt_of_le (hs _).2 (hb _))⟩
  have hd : ContDiffOn ℝ k (deriv g) (Ioo a b) :=
    ((contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo).1 (hg.mono Ioo_subset_Icc_self)).2.2
  obtain ⟨ξ, hξ, hξ0⟩ := IH (s 0) (s (Fin.last k)) (deriv g) (hd.mono hsub) s hsm
    (fun i => hsm.monotone (Fin.zero_le i)) (fun i => hsm.monotone (Fin.le_last i)) hs0
  refine ⟨ξ, ⟨?_, ?_⟩, by rw [iteratedDeriv_succ']; exact hξ0⟩
  · have h1 : t 0 < s 0 := by simpa using (hs 0).1
    exact lt_of_lt_of_le h1 hξ.1
  · have h1 : s (Fin.last k) < t (Fin.last (k + 1)) := by simpa using (hs (Fin.last k)).2
    exact lt_of_le_of_lt hξ.2 h1

/-- Iterated Rolle at every level. -/
theorem p11Rolle_Icc : ∀ k, P11RolleIcc k
  | 0 => by
    intro a b g _ t _ _ _ h0
    exact ⟨t 0, ⟨le_rfl, le_rfl⟩, by simpa using h0 0⟩
  | k + 1 => fun a b g hg t ht ha hb h0 => by
    obtain ⟨ξ, hξ, h⟩ := p11Rolle_step (p11Rolle_Icc k) hg t ht ha hb h0
    exact ⟨ξ, Ioo_subset_Icc_self hξ, h⟩

/-- Derivatives of the real evaluation of a polynomial. -/
theorem p11_iteratedDeriv_eval (P : ℝ[X]) (n : ℕ) :
    iteratedDeriv n (fun x => P.eval x) = fun x => (derivative^[n] P).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    funext x
    exact Polynomial.deriv _

/-- Interpolation coefficient: the `q`-th derivative of the Lagrange interpolant at `q+1` distinct
nodes is the constant `q!` times the divided difference. -/
theorem p11_iterate_derivative_interpolate {q : ℕ} (t : Fin (q + 1) → ℝ) (ht : StrictMono t)
    (r : Fin (q + 1) → ℝ) :
    derivative^[q] (Lagrange.interpolate Finset.univ t r) =
      C ((q.factorial : ℝ) * ∑ i, r i / ∏ j ∈ Finset.univ.erase i, (t i - t j)) := by
  have hinj : Set.InjOn t (↑(Finset.univ : Finset (Fin (q + 1)))) := ht.injective.injOn
  rw [Lagrange.iterate_derivative_interpolate _ hinj (by simp)]
  simp [Finset.mul_sum, map_sum]

theorem divided_difference {q : ℕ} (hq : 1 ≤ q) {a b : ℝ} (hab : a < b)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ q f (Icc a b)) (t : Fin (q+1) → ℝ)
    (ht : StrictMono t) (ha : ∀ i, a ≤ t i) (hb : ∀ i, t i ≤ b) :
    ∃ xi ∈ Ioo (t 0) (t (Fin.last q)),
      (∑ i, f (t i) / ∏ j ∈ Finset.univ.erase i, (t i-t j)) =
        iteratedDeriv q f xi / q.factorial := by
  classical
  have hinj : Set.InjOn t (↑(Finset.univ : Finset (Fin (q + 1)))) := ht.injective.injOn
  set P := Lagrange.interpolate Finset.univ t (fun i => f (t i)) with hP
  have hPeval : ∀ i, P.eval (t i) = f (t i) := fun i =>
    Lagrange.eval_interpolate_at_node _ hinj (Finset.mem_univ i)
  have hPder := p11_iterate_derivative_interpolate t ht (fun i => f (t i))
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  simp only [Nat.succ_eq_add_one] at hPder hf ⊢
  have hPc : ∀ n : WithTop ℕ∞, ContDiff ℝ n (fun x => P.eval x) := fun n => by
    simpa using Polynomial.contDiff_aeval (𝕜 := ℝ) P n
  have hu : ContDiffOn ℝ (k + 1) (fun x => f x - P.eval x) (Icc a b) :=
    hf.sub ((hPc _).contDiffOn)
  obtain ⟨ξ, hξ, hξ0⟩ := p11Rolle_step (p11Rolle_Icc k) hu t ht ha hb
    (fun i => by simp [hPeval])
  refine ⟨ξ, hξ, ?_⟩
  have hξab : ξ ∈ Ioo a b := ⟨lt_of_le_of_lt (ha 0) hξ.1, lt_of_lt_of_le hξ.2 (hb _)⟩
  have hfat : ContDiffAt ℝ (k + 1) f ξ := hf.contDiffAt (Icc_mem_nhds hξab.1 hξab.2)
  rw [iteratedDeriv_fun_sub hfat (hPc _).contDiffAt, p11_iteratedDeriv_eval, hP, hPder] at hξ0
  simp only [eval_C] at hξ0
  have hfac : ((k + 1).factorial : ℝ) ≠ 0 := by positivity
  rw [eq_div_iff hfac]
  linarith

end KAM.Planetary
