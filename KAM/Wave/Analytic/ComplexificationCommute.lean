/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Analytic.ComplexificationLp
public import KAM.Wave.Seq.Multiplier

/-!
# Complexification commutes with `τ_{a,p}`, `κ_{a,p}` and real multipliers

Blueprint-W `bpW:w1:complexification-lemma` (i), the clause "all three commute with `τ_{a,p}`,
`κ_{a,p}` and every real multiplier `D_μ`" (package W1-ANALYTIC). This is source-faithful
infrastructure used by several nodes; the dependency graph is still being built.

The transports are the `RCLike`-generic `KAM.Wave.coeffW`, `KAM.Wave.tauLp` and
`KAM.Wave.weightedDiagCLM`, instantiated at `ℝ` and at `ℂ`; a real multiplier `μ` acts on `ℓ²_ℂ`
as the multiplier `fun j => (μ j : ℂ)`.
-/

@[expose] public noncomputable section

open ENNReal

namespace KAM.Wave

/-! ### `κ_{a,p}` -/

theorem coeffW_complexifyLp (a p : ℝ) (y : lp (fun _ : ℕ+ => ℝ) 2) (j : ℕ+) :
    coeffW (K := ℂ) a p (complexifyLp y) j = ((coeffW (K := ℝ) a p y j : ℝ) : ℂ) := by
  simp [coeffW]

theorem coeffW_reLp (a p : ℝ) (z : lp (fun _ : ℕ+ => ℂ) 2) (j : ℕ+) :
    coeffW (K := ℝ) a p (reLp z) j = (coeffW (K := ℂ) a p z j).re := by
  simp [coeffW, Complex.div_ofReal_re]

theorem coeffW_conjLp (a p : ℝ) (z : lp (fun _ : ℕ+ => ℂ) 2) (j : ℕ+) :
    coeffW (K := ℂ) a p (conjLp z) j = starRingEnd ℂ (coeffW (K := ℂ) a p z j) := by
  simp [coeffW]

/-! ### `τ_{a,p}` -/

theorem isEll_complexify_of_isEll (a p : ℝ) {w : ℕ+ → ℝ} (h : IsEll a p w) :
    IsEll a p (fun j => (w j : ℂ)) := by
  have e : ⇑(complexifyLp ⟨fun j => (ellWeight a p j : ℝ) * w j, h⟩) =
      fun j => (ellWeight a p j : ℂ) * (w j : ℂ) := by
    funext j; simp
  unfold IsEll
  exact e ▸ lp.memℓp _

theorem isEll_re_of_isEll (a p : ℝ) {w : ℕ+ → ℂ} (h : IsEll a p w) :
    IsEll a p (fun j => (w j).re) := by
  have e : ⇑(reLp ⟨fun j => (ellWeight a p j : ℂ) * w j, h⟩) =
      fun j => (ellWeight a p j : ℝ) * (w j).re := by
    funext j; simp
  unfold IsEll
  exact e ▸ lp.memℓp _

theorem isEll_conj_of_isEll (a p : ℝ) {w : ℕ+ → ℂ} (h : IsEll a p w) :
    IsEll a p (fun j => starRingEnd ℂ (w j)) := by
  have e : ⇑(conjLp ⟨fun j => (ellWeight a p j : ℂ) * w j, h⟩) =
      fun j => (ellWeight a p j : ℂ) * starRingEnd ℂ (w j) := by
    funext j; simp
  unfold IsEll
  exact e ▸ lp.memℓp _

theorem complexifyLp_tauLp (a p : ℝ) (w : ℕ+ → ℝ) (h : IsEll a p w) :
    complexifyLp (tauLp a p w h) =
      tauLp a p (fun j => (w j : ℂ)) (isEll_complexify_of_isEll a p h) := by
  ext j; simp

theorem reLp_tauLp (a p : ℝ) (w : ℕ+ → ℂ) (h : IsEll a p w) :
    reLp (tauLp a p w h) = tauLp a p (fun j => (w j).re) (isEll_re_of_isEll a p h) := by
  ext j; simp

theorem conjLp_tauLp (a p : ℝ) (w : ℕ+ → ℂ) (h : IsEll a p w) :
    conjLp (tauLp a p w h) =
      tauLp a p (fun j => starRingEnd ℂ (w j)) (isEll_conj_of_isEll a p h) := by
  ext j; simp

/-! ### Real diagonal multipliers `D_μ` -/

theorem norm_ofReal_le_of_norm_le {μ : ℕ+ → ℝ} {M : ℝ} (hM : ∀ j, ‖μ j‖ ≤ M) (j : ℕ+) :
    ‖(μ j : ℂ)‖ ≤ M := by simpa using hM j

theorem weightedDiagCLM_complexifyLp {μ : ℕ+ → ℝ} {M : ℝ} (hM : ∀ j, ‖μ j‖ ≤ M)
    (y : lp (fun _ : ℕ+ => ℝ) 2) :
    weightedDiagCLM (fun j => (μ j : ℂ)) (norm_ofReal_le_of_norm_le hM) (complexifyLp y) =
      complexifyLp (weightedDiagCLM μ hM y) := by
  ext j; simp

theorem weightedDiagCLM_reLp {μ : ℕ+ → ℝ} {M : ℝ} (hM : ∀ j, ‖μ j‖ ≤ M)
    (z : lp (fun _ : ℕ+ => ℂ) 2) :
    reLp (weightedDiagCLM (fun j => (μ j : ℂ)) (norm_ofReal_le_of_norm_le hM) z) =
      weightedDiagCLM μ hM (reLp z) := by
  ext j; simp

theorem weightedDiagCLM_conjLp {μ : ℕ+ → ℝ} {M : ℝ} (hM : ∀ j, ‖μ j‖ ≤ M)
    (z : lp (fun _ : ℕ+ => ℂ) 2) :
    conjLp (weightedDiagCLM (fun j => (μ j : ℂ)) (norm_ofReal_le_of_norm_le hM) z) =
      weightedDiagCLM (fun j => (μ j : ℂ)) (norm_ofReal_le_of_norm_le hM) (conjLp z) := by
  ext j; simp

/-- `D_μ` commutes with `κ_{a,p}`: `κ (D_μ y) = μ · κ y`, so multipliers also commute with `τ`. -/
theorem coeffW_weightedDiagCLM {K : Type*} [RCLike K] (a p : ℝ) (μ : ℕ+ → K) {M : ℝ}
    (hM : ∀ j, ‖μ j‖ ≤ M) (y : lp (fun _ : ℕ+ => K) 2) (j : ℕ+) :
    coeffW a p (weightedDiagCLM μ hM y) j = μ j * coeffW a p y j := by
  simp [coeffW, mul_div_assoc]

end KAM.Wave
