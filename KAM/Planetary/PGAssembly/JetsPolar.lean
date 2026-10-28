/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# P Part 5: calculus helpers for the jets (`bpP:p5:be-coef`)

* `iteratedFDeriv_comp_clm_of_isOpen`: the iterated derivative of `f ∘ g` for a continuous linear
  `g` and `f` smooth on an open set (no global smoothness).
* `eq_zero_of_diag_of_symm`: a symmetric multilinear map vanishing on the diagonal is zero
  (polarization, by induction on the arity).

Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-JET.
-/

@[expose] public noncomputable section

open Set Function

namespace KAM.Planetary

section Comp

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Local chain rule for the iterated derivative along a continuous linear map. -/
theorem iteratedFDeriv_comp_clm_of_isOpen {U : Set E} (hU : IsOpen U) {f : E → F} {n : ℕ}
    (hf : ContDiffOn 𝕜 n f U) (g : G →L[𝕜] E) {x : G} (hx : g x ∈ U) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv 𝕜 i (f ∘ g) x =
      (iteratedFDeriv 𝕜 i f (g x)).compContinuousLinearMap fun _ => g := by
  have hV : IsOpen (g ⁻¹' U) := hU.preimage g.continuous
  have h := g.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hV.uniqueDiffOn hx
    (by exact_mod_cast hi)
  rwa [iteratedFDerivWithin_of_isOpen i hV hx, iteratedFDerivWithin_of_isOpen i hU hx] at h

end Comp

section Polar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem curryLeft_symm {k : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) ℝ)
    (hM : ∀ (σ : Equiv.Perm (Fin (k + 1))) (v : Fin (k + 1) → E), M (v ∘ σ) = M v)
    (v : E) (σ : Equiv.Perm (Fin k)) (w : Fin k → E) :
    M.curryLeft v (w ∘ σ) = M.curryLeft v w := by
  rw [ContinuousMultilinearMap.curryLeft_apply, ContinuousMultilinearMap.curryLeft_apply]
  have := hM (Equiv.Perm.decomposeFin.symm (0, σ)) (Fin.cons v w)
  convert this using 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

/-- The derivative of the diagonal of a symmetric multilinear map along a line. -/
theorem hasDerivAt_diag_line {k : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) ℝ)
    (hM : ∀ (σ : Equiv.Perm (Fin (k + 1))) (v : Fin (k + 1) → E), M (v ∘ σ) = M v)
    (v u : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => M (fun _ => v + s • u))
      (((k + 1 : ℕ) : ℝ) * M.curryLeft u (fun _ => v + t • u)) t := by
  classical
  have h1 : HasDerivAt (fun s : ℝ => (fun _ : Fin (k + 1) => v + s • u)) (fun _ => u) t := by
    refine hasDerivAt_pi.2 fun _ => ?_
    simpa using ((hasDerivAt_id t).smul_const u).const_add v
  have h2 := (M.hasFDerivAt (fun _ : Fin (k + 1) => v + t • u)).comp_hasDerivAt t h1
  have hterm : ∀ i : Fin (k + 1),
      M (Function.update (fun _ => v + t • u) i u) = M.curryLeft u (fun _ => v + t • u) := by
    intro i
    rw [ContinuousMultilinearMap.curryLeft_apply, ← hM (Equiv.swap 0 i)
      (Fin.cons u (fun _ : Fin k => v + t • u))]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · by_cases hj0 : j = 0
      · subst hj0
        obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 (Ne.symm hj)
        simp [Function.update_of_ne hj]
      · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj0
        simp [Equiv.swap_apply_of_ne_of_ne hj0 hj, Function.update_of_ne hj]
  have h3 : (M.linearDeriv (fun _ => v + t • u)) (fun _ => u) =
      ((k + 1 : ℕ) : ℝ) * M.curryLeft u (fun _ => v + t • u) := by
    rw [ContinuousMultilinearMap.linearDeriv_apply]
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← h3]
  exact h2

theorem diag_curryLeft {k : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) ℝ)
    (hM : ∀ (σ : Equiv.Perm (Fin (k + 1))) (v : Fin (k + 1) → E), M (v ∘ σ) = M v)
    (hd : ∀ y, M (fun _ => y) = 0) (v y : E) :
    M.curryLeft v (fun _ => y) = 0 := by
  have h := hasDerivAt_diag_line M hM y v 0
  have h0 : HasDerivAt (fun s : ℝ => M (fun _ : Fin (k + 1) => y + s • v)) 0 0 := by
    have : (fun s : ℝ => M (fun _ : Fin (k + 1) => y + s • v)) = fun _ => 0 :=
      funext fun _ => hd _
    rw [this]; exact hasDerivAt_const _ _
  have hz := h.unique h0
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [zero_smul, add_zero] at hz
  exact (mul_eq_zero.1 hz).resolve_left hk

/-- Polarization: a symmetric multilinear map vanishing on the diagonal vanishes. -/
theorem eq_zero_of_diag_of_symm : ∀ (k : ℕ)
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ),
    (∀ (σ : Equiv.Perm (Fin k)) (v : Fin k → E), M (v ∘ σ) = M v) →
    (∀ y, M (fun _ => y) = 0) → M = 0
  | 0, M, _, hd => by
    ext v
    have h := hd 0
    obtain rfl : v = fun _ => (0 : E) := funext fun i => i.elim0
    simpa using h
  | k + 1, M, hM, hd => by
    ext m
    have h := eq_zero_of_diag_of_symm k (M.curryLeft (m 0))
      (fun σ w => curryLeft_symm M hM _ σ w) (fun y => diag_curryLeft M hM hd _ y)
    have : M m = M.curryLeft (m 0) (Fin.tail m) := by
      rw [ContinuousMultilinearMap.curryLeft_apply, Fin.cons_self_tail]
    rw [this, h]; rfl

end Polar

end KAM.Planetary

end
