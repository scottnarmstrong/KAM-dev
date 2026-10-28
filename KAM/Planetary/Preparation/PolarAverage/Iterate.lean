/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PolarAverage.Torus
public import KAM.Planetary.Preparation.PolarAverage.EvenDescent

/-!
# Descent of the radial polar average through all squares (P11A-P6 helper)

`p11PolarW G (J, w)` is even in each coordinate of `w`. Replacing the coordinates of `w` one at a
time by the principal square roots of new variables `u_k = w_k²` preserves holomorphy
(`p11_even_descent`): `Φ_j (J, u) = p11PolarW G (J, v)` with `v_k = √u_k` for `k < j` and
`v_k = u_k` for `k ≥ j` is holomorphic on `W_j`, where the first `j` coordinates of `u` lie in
`D(0, r²)` and the others in `D(0, r)`. After `n` steps `u ↦ p11PolarW G (J, √u)` is holomorphic on
`D × B(0, r²)`.
-/

@[expose] public noncomputable section

open Set MeasureTheory Metric Filter
open scoped Topology Real

namespace KAM.Planetary

variable {n : ℕ}

/-- The first `j` coordinates replaced by principal square roots. -/
def p11Vj (j : ℕ) (u : P11CVec n) : P11CVec n :=
  fun k => if k.val < j then Complex.sqrt (u k) else u k

/-- Domain of the `j`-th stage. -/
def p11Wj (D : Set (P11CVec n)) (r : ℝ) (j : ℕ) : Set (P11CVec n × P11CVec n) :=
  {p | p.1 ∈ D ∧ ∀ k : Fin n, ‖p.2 k‖ < if k.val < j then r ^ 2 else r}

/-- Parameter set for the `j`-th descent step; the `j`-th coordinate is free. -/
def p11Oj (D : Set (P11CVec n)) (r : ℝ) (j : Fin n) : Set (P11CVec n × P11CVec n) :=
  {p | p.1 ∈ D ∧ ∀ k : Fin n, k ≠ j → ‖p.2 k‖ < if k.val < j.val then r ^ 2 else r}

theorem p11_isOpen_Wj {D : Set (P11CVec n)} (hD : IsOpen D) (r : ℝ) (j : ℕ) :
    IsOpen (p11Wj D r j) := by
  have : p11Wj D r j = (Prod.fst ⁻¹' D) ∩ ⋂ k : Fin n,
      {p : P11CVec n × P11CVec n | ‖p.2 k‖ < if k.val < j then r ^ 2 else r} := by
    ext p; simp [p11Wj]
  rw [this]
  refine (hD.preimage continuous_fst).inter (isOpen_iInter_of_finite fun k => ?_)
  exact isOpen_lt (by fun_prop) continuous_const

theorem p11_isOpen_Oj {D : Set (P11CVec n)} (hD : IsOpen D) (r : ℝ) (j : Fin n) :
    IsOpen (p11Oj D r j) := by
  have : p11Oj D r j = (Prod.fst ⁻¹' D) ∩ ⋂ k : Fin n,
      {p : P11CVec n × P11CVec n | k ≠ j → ‖p.2 k‖ < if k.val < j.val then r ^ 2 else r} := by
    ext p; simp [p11Oj]
  rw [this]
  refine (hD.preimage continuous_fst).inter (isOpen_iInter_of_finite fun k => ?_)
  by_cases hk : k = j
  · simp [hk]
  · simp only [ne_eq, hk, not_false_eq_true, forall_true_left]
    exact isOpen_lt (by fun_prop) continuous_const

theorem p11_norm_sqrt_lt {a : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : ‖a‖ < r ^ 2) :
    ‖Complex.sqrt a‖ < r :=
  lt_of_pow_lt_pow_left₀ 2 hr (by rwa [p11_norm_sqrt_sq])

theorem p11_norm_Vj_lt {D : Set (P11CVec n)} {r : ℝ} (hr : 0 < r) {j : ℕ}
    {p : P11CVec n × P11CVec n}
    (hp : p ∈ p11Wj D r j) : ‖p11Vj j p.2‖ < r := by
  refine (pi_norm_lt_iff hr).2 fun k => ?_
  have h := hp.2 k
  unfold p11Vj
  split_ifs at h ⊢ with hk
  · exact p11_norm_sqrt_lt hr.le h
  · exact h

theorem p11Vj_update (j : Fin n) (u : P11CVec n) (s : ℂ) :
    p11Vj j.val (Function.update u j s) = Function.update (p11Vj j.val u) j s := by
  funext k
  by_cases hk : k = j
  · subst hk; simp [p11Vj]
  · simp [p11Vj, Function.update_of_ne hk]

theorem p11Vj_succ (j : Fin n) (u : P11CVec n) :
    p11Vj (j.val + 1) u = p11Vj j.val (Function.update u j (Complex.sqrt (u j))) := by
  funext k
  by_cases hk : k = j
  · subst hk; simp [p11Vj]
  · have hkv : k.val ≠ j.val := fun h => hk (Fin.ext h)
    have : k.val < j.val + 1 ↔ k.val < j.val := by omega
    simp [p11Vj, Function.update_of_ne hk, this]

/-- The descent through all squares: `(J, u) ↦ p11PolarW G (J, √u)` is holomorphic on
`D × B(0, r²)`. -/
theorem p11PolarW_sqrt_differentiableOn {D : Set (P11CVec n)} (hD : IsOpen D) {r : ℝ} (hr : 0 < r)
    {G : P11CVec n × P11Phase n → ℂ} (hG : DifferentiableOn ℂ G (D ×ˢ ball 0 r)) :
    DifferentiableOn ℂ (fun p : P11CVec n × P11CVec n =>
      p11PolarW G (p.1, fun k => Complex.sqrt (p.2 k))) (D ×ˢ ball (0 : P11CVec n) (r ^ 2)) := by
  let Φ : ℕ → P11CVec n × P11CVec n → ℂ := fun j p => p11PolarW G (p.1, p11Vj j p.2)
  have hstep : ∀ j : ℕ, j ≤ n → DifferentiableOn ℂ (Φ j) (p11Wj D r j) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hset : p11Wj D r 0 = D ×ˢ ball (0 : P11CVec n) r := by
        ext p
        simp only [p11Wj, Nat.not_lt_zero, ite_false, mem_prod, mem_ball_zero_iff,
          Set.mem_ofPred_eq]
        rw [pi_norm_lt_iff hr]
      have hΦ0 : Φ 0 = p11PolarW G := by
        funext p
        simp only [Φ]
        congr 1
      rw [hset, hΦ0]
      exact p11PolarW_differentiableOn hD hG
    | succ j ih =>
      intro hj
      have hjn : j < n := hj
      set jj : Fin n := ⟨j, hjn⟩ with hjjdef
      have hjv : jj.val = j := rfl
      have ih' := ih (Nat.le_succ j |>.trans hj)
      set Ω := p11Oj D r jj with hΩdef
      have hΩ : IsOpen Ω := p11_isOpen_Oj hD r jj
      let h : ℂ × (P11CVec n × P11CVec n) → ℂ :=
        fun x => Φ j (x.2.1, Function.update x.2.2 jj x.1)
      have hupd : Differentiable ℂ (fun x : ℂ × (P11CVec n × P11CVec n) =>
          (x.2.1, Function.update x.2.2 jj x.1)) := by
        refine Differentiable.prodMk (by fun_prop) (differentiable_pi.2 fun k => ?_)
        by_cases hk : k = jj
        · subst hk; simp only [Function.update_self]; fun_prop
        · simp only [Function.update_of_ne hk]; fun_prop
      have hmaps : ∀ x ∈ ball (0 : ℂ) r ×ˢ Ω,
          (x.2.1, Function.update x.2.2 jj x.1) ∈ p11Wj D r j := by
        intro x hx
        refine ⟨hx.2.1, fun k => ?_⟩
        by_cases hk : k = jj
        · subst hk
          simp only [Function.update_self, hjv, lt_self_iff_false, ite_false]
          exact mem_ball_zero_iff.mp hx.1
        · show ‖Function.update x.2.2 jj x.1 k‖ < _
          rw [Function.update_of_ne hk]
          have := hx.2.2 k hk
          have hkv : k.val < j + 1 ↔ k.val < j := by
            have : k.val ≠ j := fun h => hk (Fin.ext h)
            omega
          simpa [hjv, hkv] using this
      have hd : DifferentiableOn ℂ h (ball (0 : ℂ) r ×ˢ Ω) :=
        ih'.comp hupd.differentiableOn hmaps
      have hev : ∀ s ∈ ball (0 : ℂ) r, ∀ p ∈ Ω, h (-s, p) = h (s, p) := by
        intro s hs p hp
        have hmem := hmaps (s, p) ⟨hs, hp⟩
        have hw := p11_norm_Vj_lt hr hmem
        have heven := p11PolarW_even hG hmem.1 hw jj
        simp only [h, Φ]
        rw [← heven]
        have e1 : p11Vj j (Function.update p.2 jj (-s)) =
            Function.update (p11Vj j (Function.update p.2 jj s)) jj
              (-(p11Vj j (Function.update p.2 jj s) jj)) := by
          rw [← hjv, p11Vj_update, p11Vj_update]
          simp [Function.update_idem]
        simp only [e1]
      have hdesc := p11_even_descent hΩ hr hd hev
      have hmaps2 : ∀ p ∈ p11Wj D r (j + 1),
          (p.2 jj, p) ∈ ball (0 : ℂ) (r ^ 2) ×ˢ Ω := by
        intro p hp
        refine ⟨?_, hp.1, fun k hk => ?_⟩
        · have := hp.2 jj
          simp only [hjv, Nat.lt_succ_self, ite_true] at this
          exact mem_ball_zero_iff.mpr this
        · have := hp.2 k
          have hkv : k.val < j + 1 ↔ k.val < j := by
            have : k.val ≠ j := fun h => hk (Fin.ext h)
            omega
          simpa [hjv, hkv] using this
      have hcomp := hdesc.comp (f := fun p : P11CVec n × P11CVec n => (p.2 jj, p))
        (by fun_prop) (fun p hp => hmaps2 p hp)
      refine hcomp.congr fun p hp => ?_
      simp only [Φ, h, Function.comp]
      rw [← p11Vj_succ jj p.2, hjv]
  have hset : p11Wj D r n = D ×ˢ ball (0 : P11CVec n) (r ^ 2) := by
    ext p
    have hk : ∀ k : Fin n, k.val < n := fun k => k.isLt
    simp [p11Wj, hk, pi_norm_lt_iff (show (0 : ℝ) < r ^ 2 by positivity)]
  have hfun : (fun p : P11CVec n × P11CVec n => p11PolarW G (p.1, fun k => Complex.sqrt (p.2 k))) =
      Φ n := by
    funext p
    show p11PolarW G (p.1, _) = p11PolarW G (p.1, p11Vj n p.2)
    congr 2
    funext k
    simp [p11Vj, k.isLt]
  rw [hfun, ← hset]
  exact hstep n le_rfl

end KAM.Planetary
