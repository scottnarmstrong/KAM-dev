/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Sound.Static

/-!
# Soundness of the Hamiltonian sub-check

`TorusCertificate.ham_structural`: `D` is open and translation invariant, and `H` is holomorphic,
periodic and real on `D` once its denominators are certified (`HamExpr.contDiffOn_eval`,
`eval_add_int`, `eval_real`). `checkHamBounds_sound`: a successful `Slp.balls` certifies every
denominator (`HamExpr.nonvanishingOn_of_balls`); the jet bridges `jet_d1/d2/d3` identify the
slot values with the partials along `phaseBasis`; each slot lies in its ball, hence is bounded by
`slotMagQ`; the `NormBridge` forms turn sums of partials into the five operator-norm bounds.
-/

public section

namespace KAM.Certificate

open KAM KAM.Torus CertArith

variable {n : ℕ} {α : Type} [CertArith α]

/-- `sumRangeQ` is the `Finset.range` sum. -/
theorem sumRangeQ_eq (k : ℕ) (f : ℕ → ℚ) : sumRangeQ k f = ∑ i ∈ Finset.range k, f i := by
  induction k with
  | zero => simp [sumRangeQ]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp [sumRangeQ, List.range_succ]

/-- A sum over the phase indices is the `sumRangeQ` over their natural numbering. -/
theorem sum_phaseNat_eq_sumRangeQ (f : ℕ → ℚ) :
    ∑ a : Fin n ⊕ Fin n, f (phaseNat a) = sumRangeQ (n + n) f := by
  rw [sumRangeQ_eq, ← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv finSumFinEquiv _ _ fun a => by
    rw [← phaseNat_finSumFinEquiv_symm, Equiv.symm_apply_apply]

/-- Double sums over the phase indices. -/
theorem sum_sum_phaseNat_eq_sumRangeQ (f : ℕ → ℕ → ℚ) :
    ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n, f (phaseNat a) (phaseNat b) =
      sumRangeQ (n + n) (fun i => sumRangeQ (n + n) (f i)) := by
  rw [Finset.sum_congr rfl fun a _ => sum_phaseNat_eq_sumRangeQ (f (phaseNat a))]
  exact sum_phaseNat_eq_sumRangeQ (fun i => sumRangeQ (n + n) (f i))

/-- A slot in its ball is bounded by the ball's magnitude. -/
theorem norm_le_ballMagQ_of_mem {z : ℂ} {b : CC ℚ × ℚ} (h : ‖z - b.1.toC‖ ≤ (b.2 : ℝ)) :
    ‖z‖ ≤ (ballMagQ b : ℝ) := by
  have h1 : ‖b.1.toC‖ ≤ |(b.1.re : ℝ)| + |(b.1.im : ℝ)| := Complex.norm_le_abs_re_add_abs_im _
  have h2 : ‖z‖ ≤ ‖z - b.1.toC‖ + ‖b.1.toC‖ := norm_le_norm_sub_add z _
  simp only [ballMagQ, Rat.cast_add, Rat.cast_abs]
  linarith

/-- Every slot of a ball-evaluated program is bounded by its slot magnitude. -/
theorem Slp.norm_val_le_slotMagQ {p : Slp} {WH : CertWeight} {s N : ℕ}
    (hW : checkWeight WH s N = true) {centre radius : List ℚ} {taylorN : ℕ}
    {bs : List (CC ℚ × ℚ)} (h : p.balls n WH centre radius taylorN = some bs)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ certDomain n WH.rho centre radius) (i : ℕ) :
    ‖p.val n z i‖ ≤ (slotMagQ bs i : ℝ) :=
  norm_le_ballMagQ_of_mem ((ballsAux_sound hW hz p.ops [] [] bs BallRel.ballRel_nil h).2 i)

/-- Structural facts of `H` on `D`, given the certified denominators. -/
theorem TorusCertificate.ham_structural (c : TorusCertificate n α)
    (hnv : c.ham.NonvanishingOn c.D) :
    IsOpen c.D ∧ (∀ z ∈ c.D, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ c.D) ∧
      DifferentiableOn ℂ c.H c.D ∧
      (∀ z ∈ c.D, ∀ k : Fin n → ℤ, c.H (z.1 + (fun i => (k i : ℂ)), z.2) = c.H z) ∧
      ∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ c.D →
        (c.H ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0 :=
  ⟨isOpen_certDomain _ _ _ _, fun _ hz k => certDomain_add_int hz k,
    (c.ham.contDiffOn_eval (isOpen_certDomain _ _ _ _) hnv).differentiableOn (by simp),
    fun z _ k => c.ham.eval_add_int z k, fun θ I _ => c.ham.eval_real θ I⟩

variable [LawfulCertArith α]

theorem checkHamBounds_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (h : checkHamBounds c = true) :
    c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M := by
  have hS := checkStatic_sound hs
  have hn : 1 ≤ n := by have := hS.hn; omega
  unfold checkHamBounds at h
  cases hb : c.ham.jet.prog.balls n c.weightH c.centre c.radius c.expOrder with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some bs =>
  rw [hb] at h
  simp only [hamBoundsOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨hDH, hXH⟩, hDX⟩, hD2X⟩, hD2H⟩ := h
  have hnv : c.ham.NonvanishingOn c.D := c.ham.nonvanishingOn_of_balls hS.hWH hb
  have hD : IsOpen c.D := isOpen_certDomain _ _ _ _
  refine ⟨hnv, fun z hz => ?_⟩
  -- slot bounds
  have hmag (i : ℕ) : ‖c.ham.jet.prog.val n z i‖ ≤ (slotMagQ bs i : ℝ) :=
    Slp.norm_val_le_slotMagQ hS.hWH hb hz i
  have hd1 (a : Fin n ⊕ Fin n) :
      ‖fderiv ℂ c.H z (phaseBasis a)‖ ≤ (slotMagQ bs (c.ham.jet.d1.getD (phaseNat a) 0) : ℝ) := by
    have := hmag (c.ham.jet.d1.getD (phaseNat a) 0); rwa [c.ham.jet_d1 hD hnv hz a] at this
  have hd2 (a b : Fin n ⊕ Fin n) :
      ‖iteratedFDeriv ℂ 2 c.H z ![phaseBasis a, phaseBasis b]‖ ≤
        (slotMagQ bs ((c.ham.jet.d2.getD (phaseNat a) []).getD (phaseNat b) 0) : ℝ) := by
    have := hmag ((c.ham.jet.d2.getD (phaseNat a) []).getD (phaseNat b) 0)
    rwa [c.ham.jet_d2 hD hnv hz a b] at this
  have hd3 (a b e : Fin n ⊕ Fin n) :
      ‖iteratedFDeriv ℂ 3 c.H z ![phaseBasis a, phaseBasis b, phaseBasis e]‖ ≤
        (slotMagQ bs (((c.ham.jet.d3.getD (phaseNat a) []).getD (phaseNat b) []).getD
          (phaseNat e) 0) : ℝ) := by
    have := hmag (((c.ham.jet.d3.getD (phaseNat a) []).getD (phaseNat b) []).getD (phaseNat e) 0)
    rwa [c.ham.jet_d3 hD hnv hz a b e] at this
  have hcd : ContDiffAt ℂ ⊤ c.H z :=
    (c.ham.contDiffOn_eval hD hnv).contDiffAt (hD.mem_nhds hz)
  have hM0 : (0 : ℝ) ≤ c.params.M := hS.hM.le
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `‖DH‖`
    refine (norm_fderiv_le_sum_partials z).trans ((Finset.sum_le_sum fun a _ => hd1 a).trans ?_)
    rw [← Rat.cast_sum, sum_phaseNat_eq_sumRangeQ (fun i => slotMagQ bs (c.ham.jet.d1.getD i 0))]
    exact_mod_cast hDH
  · -- `‖X_H‖`
    rw [← norm_sumVec]
    refine (pi_norm_le_iff_of_nonneg hM0).2 fun a => ?_
    rw [hamiltonianVectorFieldℂ_sumVec]
    have key (b : Fin n ⊕ Fin n) : ‖fderiv ℂ c.H z (phaseBasis b)‖ ≤ c.params.M :=
      (hd1 b).trans (by exact_mod_cast hXH _ (phaseNat_lt_add b))
    rcases a with i | i
    · exact key _
    · rw [Sum.elim_inr, norm_neg]; exact key _
  · -- `‖DX_H‖`
    refine norm_fderiv_hamiltonianVectorFieldℂ_le hn (hcd.of_le (by simp)) fun a => ?_
    refine (Finset.sum_le_sum fun b _ => hd2 a.swap b).trans ?_
    rw [← Rat.cast_sum, sum_phaseNat_eq_sumRangeQ
      (fun i => slotMagQ bs ((c.ham.jet.d2.getD (phaseNat a.swap) []).getD i 0))]
    exact_mod_cast hDX _ (phaseNat_lt_add a.swap)
  · -- `‖D²X_H‖`
    refine norm_iteratedFDeriv_two_hamiltonianVectorFieldℂ_le hn (hcd.of_le (by simp))
      fun a => ?_
    refine (Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun e _ => hd3 a.swap b e).trans ?_
    have := hD2X _ (phaseNat_lt_add a.swap)
    rw [← sum_sum_phaseNat_eq_sumRangeQ
      (fun i j => slotMagQ bs (((c.ham.jet.d3.getD (phaseNat a.swap) []).getD i []).getD j 0))]
      at this
    exact_mod_cast this
  · -- `‖D²H‖`
    refine (norm_iteratedFDeriv_two_le_sum_partials z).trans
      ((Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hd2 a b).trans ?_)
    have := hD2H
    rw [← sum_sum_phaseNat_eq_sumRangeQ
      (fun i j => slotMagQ bs ((c.ham.jet.d2.getD i []).getD j 0))] at this
    exact_mod_cast this

end KAM.Certificate
