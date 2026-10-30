/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Normal.Analysis.Gradient
public import KAM.Frozen.Wave.Defs.IsClassicalSolution

/-!
# Definitions for the equivalence of the PDE and the coefficient system
(blueprint `bpW:w0n:pde-equiv`)

Infrastructure used by several nodes; the dependency graph is still being built.

* `KAM.Wave.waveV`: the velocity reconstruction `V_m(p)(x) = Σ_j √λ_j p_j φ_j(x)` of a real
  sequence (agrees with the frozen `reconV` on `coeff y`);
* `KAM.Wave.waveEllToLp a p c`: the weighted `ℓ²` coordinates `(ω_{a,p}(j) c_j)_j` of a sequence
  `c ∈ ℓ^{a,p}` (and `0` for other sequences); this is the Banach space structure in which
  continuity and differentiability "into `ℓ^{a,p}`" are expressed;
* `KAM.Wave.IsClassicalSolutionWith`: classical solution of the cubic wave equation on an open
  set `I` of times, with explicit witnesses for `u_t, u_x, u_tt, u_xx`
  (blueprint `bpW:w0:nlw`); `KAM.Wave.isClassicalSolution_iff_with_univ` shows that for `I = ℝ`
  it is the frozen `KAM.Wave.IsClassicalSolution`.
-/

@[expose] public noncomputable section

open Real
open scoped ENNReal

namespace KAM.Wave

/-- `V_m(p)(x) = Σ_j √λ_j p_j φ_j(x)` for a real sequence `p` (blueprint
`bpW:w0:reconstruction`). -/
def waveV (m : ℝ) (hm : 0 < m) (c : ℕ+ → ℝ) (x : ℝ) : ℝ :=
  ∑' j : ℕ+, Real.sqrt (lam m hm j) * c j * sineMode j x

lemma reconV_eq_waveV (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) :
    reconV m hm y = waveV m hm (coeff y) := rfl

open scoped Classical in
/-- The weighted `ℓ²` coordinates of a sequence of `ℓ^{a,p}` (zero for other sequences). -/
def waveEllToLp (a p : ℝ) (c : ℕ+ → ℝ) : lp (fun _ : ℕ+ => ℝ) 2 :=
  if h : WaveEll a p c then ⟨fun j => ellWeight a p j * c j, memℓp_two_of_waveEll h⟩ else 0

lemma waveEllToLp_apply {a p : ℝ} {c : ℕ+ → ℝ} (h : WaveEll a p c) (j : ℕ+) :
    waveEllToLp a p c j = ellWeight a p j * c j := by
  simp [waveEllToLp, h]

lemma waveEllToLp_apply_div {a p : ℝ} {c : ℕ+ → ℝ} (h : WaveEll a p c) (j : ℕ+) :
    waveEllToLp a p c j / ellWeight a p j = c j := by
  rw [waveEllToLp_apply h]
  have := (waveEllWeight_pos a p j).ne'
  field_simp

/-- A classical solution of `u_tt = u_xx - m u - u³` on the open set `I` of times, with explicit
witnesses for the partial derivatives (blueprint `bpW:w0:nlw`, with `I` in place of `ℝ`). -/
def IsClassicalSolutionWith (m : ℝ) (u ut ux utt uxx : ℝ → ℝ → ℝ) (I : Set ℝ) : Prop :=
  (∀ v ∈ ({Function.uncurry u, Function.uncurry ut, Function.uncurry ux,
      Function.uncurry utt, Function.uncurry uxx} : Set (ℝ × ℝ → ℝ)),
    ContinuousOn v (I ×ˢ Set.Icc 0 π)) ∧
  (∀ t ∈ I, ∀ x ∈ Set.Icc 0 π,
    HasDerivAt (fun s => u s x) (ut t x) t ∧
    HasDerivAt (fun s => ut s x) (utt t x) t ∧
    HasDerivWithinAt (u t) (ux t x) (Set.Icc 0 π) x ∧
    HasDerivWithinAt (ux t) (uxx t x) (Set.Icc 0 π) x ∧
    utt t x = uxx t x - m * u t x - u t x ^ 3) ∧
  ∀ t ∈ I, u t 0 = 0 ∧ u t π = 0

/-- For `I = ℝ` this is the frozen `IsClassicalSolution`. -/
theorem isClassicalSolution_iff_with_univ (m : ℝ) (hm : 0 < m) (u : ℝ → ℝ → ℝ) :
    IsClassicalSolution m hm u ↔
      ∃ ut ux utt uxx : ℝ → ℝ → ℝ, IsClassicalSolutionWith m u ut ux utt uxx Set.univ := by
  unfold IsClassicalSolution IsClassicalSolutionWith
  simp only [Set.mem_univ, true_imp_iff]

end KAM.Wave

end
