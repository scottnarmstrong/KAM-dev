/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.OscillatorFiniteChain

/-!
# P Part 2: the accumulated oscillator normal form (`stepP:p2:oa-concl`)

`OSched.G` is the sum of the zero-mode increments of the successive remainders. This module shows
it depends on the phase only through the flat parameter `(oscPack z).2` (so it is independent of
the fast angles), and that `g - f̂₀` is the finite sum of the later zero-mode increments, which
gives its weighted bound. Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, Revision 3,
package P23-15.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

section Gen

variable {n m : ℕ} {D : Set (Fin n → ℝ)} {c : OSched} {K α : ℝ} {h : (Fin n → ℂ) → ℂ}
  {f : CHam (n + m)} {ε : ℕ → ℝ} {M : ℕ}

theorem oscBound_zero {r rp rq S : ℝ} :
    oscBound D r rp rq S (fun _ : CPhase (n + m) => (0 : ℂ)) 0 := by
  intro x _
  have h0 : ∀ k : Fin n → ℤ,
      coeff (oscFunction fun _ : CPhase (n + m) => (0 : ℂ)) x k = 0 := fun k => by
    simp [oscFunction, coeff, KAM.torusCoeffW, KAM.torusAverage]
  simp [WSummable, wsum, h0]

/-- The accumulated normal form only depends on the flat parameter. -/
theorem OSched.G_indep (c : OSched) (D : Set (Fin n → ℝ)) (K : ℝ) (h : (Fin n → ℂ) → ℂ)
    (f : CHam (n + m)) (i : ℕ) {z z' : CPhase (n + m)} (hz : (oscPack z).2 = (oscPack z').2) :
    c.G D K h f i z = c.G D K h f i z' := by
  rw [OSched.G_eq_sum]
  simp only [OSched.inc, hz]

theorem OIter.S_final_pos (hS : OIter D c K α h f ε M) : 0 < c.x.S (M + 1) := by
  obtain ⟨-, -, -, -, -, -, -, h8⟩ := hS.widths M le_rfl
  rw [Sched.S_succ]; linarith

theorem OIter.tail_sum (hS : OIter D c K α h f ε M) :
    ∀ l ≤ M, oscClass D (c.x.R (M + 1)) (c.p.R (M + 1)) (c.q.R (M + 1)) (c.x.S (M + 1))
        (fun z => ∑ j ∈ Finset.range l, c.inc D K h f (j + 1) z) ∧
      oscBound D (c.x.R (M + 1)) (c.p.R (M + 1)) (c.q.R (M + 1)) (c.x.S (M + 1))
        (fun z => ∑ j ∈ Finset.range l, c.inc D K h f (j + 1) z)
        (∑ j ∈ Finset.range l, ε (j + 1)) := by
  intro l
  induction l with
  | zero =>
    intro _
    simp only [Finset.sum_range_zero]
    exact ⟨oscClass.zero, oscBound_zero⟩
  | succ l ih =>
    intro hl
    obtain ⟨i1, i2⟩ := ih (by omega)
    have hsc := hS.stage (i := l + 1) hl
    obtain ⟨a, b, d, e⟩ := hS.R_anti (i := l + 1) (j := M + 1) (by omega) le_rfl
    have hc := hsc.inc_cls.mono a b d e
    have hb := hsc.inc_bound.mono_gen (E' := ε (l + 1)) a b d e le_rfl
    simp only [Finset.sum_range_succ]
    exact ⟨i1.add hc, osc_bound_add hS.S_final_pos i1 hc i2 hb⟩

/-- `g - f̂₀` is the finite sum of the later zero-mode increments. -/
theorem OIter.gen_tail (hS : OIter D c K α h f ε M) :
    oscClass D (c.x.R (M + 1)) (c.p.R (M + 1)) (c.q.R (M + 1)) (c.x.S (M + 1))
      (fun z => c.G D K h f (M + 1) z - coeff (oscFunction f) (oscPack z).2 0) ∧
    oscBound D (c.x.R (M + 1)) (c.p.R (M + 1)) (c.q.R (M + 1)) (c.x.S (M + 1))
      (fun z => c.G D K h f (M + 1) z - coeff (oscFunction f) (oscPack z).2 0)
      (∑ j ∈ Finset.range M, ε (j + 1)) := by
  obtain ⟨t1, t2⟩ := hS.tail_sum M le_rfl
  have e : (fun z : CPhase (n + m) =>
      c.G D K h f (M + 1) z - coeff (oscFunction f) (oscPack z).2 0) =
      fun z => ∑ j ∈ Finset.range M, c.inc D K h f (j + 1) z := by
    funext z
    rw [OSched.G_eq_sum]
    beta_reduce
    rw [Fin.sum_univ_eq_sum_range (fun j => c.inc D K h f j z) (M + 1),
      Finset.sum_range_succ' (fun j => c.inc D K h f j z) M]
    simp [OSched.inc, OSched.F_zero]
  rw [e]
  exact ⟨t1, t2⟩

end Gen

end KAM.Planetary

end
