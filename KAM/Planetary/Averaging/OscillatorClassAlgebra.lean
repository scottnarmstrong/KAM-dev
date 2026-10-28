/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Averaging.OscillatorGen
public import KAM.Planetary.Averaging.OscillatorFlowMap
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# P Part 2: algebra of the oscillator class

Sums, congruence on the domain, and the pointwise-defined pieces of the step
(`bpP:p2:osc-iter`): the accumulated `g = ∑ⱼ gⱼ` and `gp = g + ⟨f⟩`.
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-13.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

section Algebra

variable {n m : ℕ} {D : Set (Fin n → ℝ)} {r rp rq S : ℝ}

theorem oscClass.add {u v : CHam (n + m)} (hu : oscClass D r rp rq S u)
    (hv : oscClass D r rp rq S v) : oscClass D r rp rq S (fun z => u z + v z) :=
  ⟨hu.1.add hv.1, fun j z hz => by simp only [hu.2 j z hz, hv.2 j z hz]⟩

theorem oscClass.sub {u v : CHam (n + m)} (hu : oscClass D r rp rq S u)
    (hv : oscClass D r rp rq S v) : oscClass D r rp rq S (fun z => u z - v z) :=
  ⟨hu.1.sub hv.1, fun j z hz => by simp only [hu.2 j z hz, hv.2 j z hz]⟩

theorem oscClass.zero : oscClass D r rp rq S (fun _ : CPhase (n + m) => (0 : ℂ)) :=
  ⟨differentiableOn_const 0, fun _ _ _ => rfl⟩

theorem oscClass.sum {J : ℕ} {g : Fin J → CHam (n + m)} (hg : ∀ j, oscClass D r rp rq S (g j)) :
    oscClass D r rp rq S (fun z => ∑ j, g j z) := by
  induction J with
  | zero => simpa using (oscClass.zero (D := D) (r := r) (rp := rp) (rq := rq) (S := S))
  | succ J ih =>
    have e : (fun z : CPhase (n + m) => ∑ j, g j z) =
        fun z => g 0 z + ∑ j : Fin J, g j.succ z := by
      funext z; rw [Fin.sum_univ_succ]
    rw [e]
    exact (hg 0).add (ih fun j => hg j.succ)

/-- The weighted bound only depends on the values on the domain. -/
theorem oscBound.congr {u v : CHam (n + m)} {M : ℝ} (hS : 0 < S)
    (h : ∀ z ∈ oscDom (m := m) D r rp rq S, u z = v z) (hb : oscBound D r rp rq S u M) :
    oscBound D r rp rq S v M := by
  intro x hx
  have hc : ∀ k, coeff (oscFunction v) x k = coeff (oscFunction u) x k := fun k =>
    coeff_congr_real (fun θ => (h _ (oscUnpack_mem_oscDom.2
      ⟨KAM.ofReal_mem_complexStrip hS θ, hx⟩)).symm) k
  obtain ⟨h1, h2⟩ := hb x hx
  refine ⟨?_, ?_⟩
  · unfold WSummable; simp only [hc]; exact h1
  · unfold wsum; simp only [hc]; exact h2

theorem oscClass.congr {u v : CHam (n + m)} (hu : oscClass D r rp rq S u)
    (h : ∀ z ∈ oscDom (m := m) D r rp rq S, u z = v z) : oscClass D r rp rq S v :=
  ⟨hu.1.congr fun z hz => (h z hz).symm, fun j z hz => by
    have hmem : ((z.1 + Pi.single (Fin.castAdd m j) 1, z.2) : CPhase (n + m)) ∈
        oscDom (m := m) D r rp rq S := by
      have e : ((z.1 + Pi.single (Fin.castAdd m j) 1, z.2) : CPhase (n + m)) =
          z + oscFastShift (m := m) (Pi.single j 1) := by
        rw [oscFastShift_single]; ext <;> simp
      rw [e]
      exact oscDom_add_shift (fun i => by by_cases hi : i = j <;> simp [hi]) hz
    rw [← h _ hmem, ← h _ hz]
    exact hu.2 j z hz⟩

end Algebra

end KAM.Planetary

end
