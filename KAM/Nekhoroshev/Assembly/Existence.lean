/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Assembly.Confinement
public import KAM.Nekhoroshev.ODE.Specialization

/-!
# Part 10 assembly: existence and uniqueness (`bpN:p10:existence`, `bpN:p10:uniqueness`)

`existence` feeds `confinement` into `ODE.confinement_glue` on the open ball `actionBall n p.R`;
`uniqueness` restricts the solution in time (`head_solution_restrict`) and applies
`ODE.uniqueness_closed`, using only the analytic ODE data.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Nekhoroshev

variable {n : ℕ}

/-- ex-ball: closed max-norm action ball, strictly inside the solution domain. -/
theorem ex_ball (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos) {ε : ℝ}
    (hε : 0 < ε) (hε0 : ε ≤ p.eps0) {I₀ : Fin n → ℝ}
    (hI : I₀ ∈ actionBall n (p.R / 2)) : closedBall I₀ (p.rho ε) ⊆ actionBall n p.R := by
  obtain ⟨-, hρ, -⟩ := cp_size hn p hp hε hε0
  have hR := hp.hR
  intro x hx
  have h1 : ‖I₀‖ < p.R / 2 := by simpa [actionBall] using hI
  have h2 : ‖x - I₀‖ ≤ p.rho ε := by simpa [dist_eq_norm] using hx
  have h3 : ‖x‖ ≤ ‖x - I₀‖ + ‖I₀‖ := by simpa using norm_add_le (x - I₀) I₀
  simp only [actionBall, mem_ball, dist_zero_right]
  linarith

theorem existence (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos)
    {h : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hh : HeadHyp p h) (hf : IsAnalyticPerturbation p.R p.s ε f)
    (hε : 0 < ε) (hε0 : ε ≤ p.eps0) (θ₀ I₀ : Fin n → ℝ)
    (hI : I₀ ∈ actionBall n (p.R / 2)) :
    ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = (θ₀, I₀) ∧
      IsSolutionOn (KAM.realHamiltonian h f) (actionBall n p.R) (Icc (-p.tau ε) (p.tau ε)) z ∧
      ∀ t : ℝ, |t| ≤ p.tau ε → ‖(z t).2 - I₀‖ ≤ p.rho ε := by
  obtain ⟨hρ, -, hτ⟩ := cp_size hn p hp hε hε0
  have hd : Data n p.R p.s ε h f := ⟨hp.hR, hp.hs, hh.1, hf⟩
  have hUs : actionBall n p.R ⊆ ball (0 : Fin n → ℝ) (p.R + p.s) :=
    ball_subset_ball (by linarith [hp.hs])
  obtain ⟨z, hz0, hz, hzc, -⟩ := ODE.confinement_glue hd (U := actionBall n p.R) isOpen_ball hUs
    hτ hρ (ex_ball hn p hp hε hε0 hI) (fun J y _ hJc h0 hy0 hy =>
      confinement hn p hp hh hf hε hε0 hI hJc h0 hy0 hy)
  exact ⟨z, hz0, hz, hzc⟩

/-- un-restrict: restriction only in time; the derivative stays two-sided. -/
theorem head_solution_restrict {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {U : Set (Fin n → ℝ)} {τ L : ℝ} (hL : L ≤ τ)
    {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} (hz : IsSolutionOn H U (Icc (-τ) τ) z) :
    IsSolutionOn H U (Icc (-L) L) z :=
  fun t ht => hz t ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- Stronger than the blueprint: uniqueness uses just the analytic ODE data, any tau and L. -/
theorem uniqueness {R s ε τ : ℝ} {h : (Fin n → ℂ) → ℂ}
    {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hd : Data n R s ε h f)
    {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hz : IsSolutionOn (KAM.realHamiltonian h f) (actionBall n R) (Icc (-τ) τ) z)
    {L : ℝ} (hL : 0 ≤ L) (hLτ : L ≤ τ)
    {y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)} (hy0 : y 0 = z 0)
    (hy : IsSolutionOn (KAM.realHamiltonian h f) (actionBall n R) (Icc (-L) L) y) :
    EqOn y z (Icc (-L) L) :=
  ODE.uniqueness_closed hd isOpen_ball (ball_subset_ball (by linarith [hd.hs])) hy
    (head_solution_restrict hLτ hz) hy0

end KAM.Nekhoroshev

end
