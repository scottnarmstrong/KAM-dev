/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.HamClass

/-!
# Smoothing symmetric forms (blueprint-W `bpW:w3:forms`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-SETTING, blueprint label `bpW:w3:forms`.

A continuous symmetric `(n+1)`-linear form `𝔓` on `𝔚` is *smoothing with constant `c`*
(`IsBirkSmoothing`, `d = n + 1`, `n ≥ 1`) if there is a continuous `n`-linear `N = ∇𝔓 : 𝔚ⁿ → 𝔚^+`
(a map into `BirkSpace` read at weight `p + 1`) with
`𝔓(w¹, …, wⁿ, v) = Ω(∇𝔓(w¹, …, wⁿ), v)` and `‖∇𝔓(w)‖₊ ≤ c ∏ ‖wⁱ‖`. For its diagonal
`P(w) = 𝔓(w,…,w)`:

* `birkDiag_field`: `X_P(w) = d ∇𝔓(w,…,w)` is the Hamiltonian field (`IsBirkHamFieldPlus` on all of
  `𝔚`);
* `norm_birkDiag_le`, `norm_birkDiagField_le`, `norm_birkDiagField_sub_le`:
  `|P(w)| ≤ c ‖w‖^d`, `‖X_P(w)‖₊ ≤ d c ‖w‖^{d-1}`,
  `‖X_P(y) - X_P(w)‖₊ ≤ d(d-1) c max(‖y‖,‖w‖)^{d-2} ‖y - w‖`;
* `birkDiag_analyticOnNhd`, `birkDiagField_analyticOnNhd`, `birkDiag_isClassA`: analyticity of `P`
  and
  `X_P`, hence `P ∈ 𝒜(𝔚)` when `P` is real.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open scoped ComplexConjugate

variable {a p : ℝ} {ha : 0 ≤ a} {hp : 0 ≤ p} {n : ℕ}

/-- (`bpW:w3:forms`) `𝔓` (`d = n + 1`) is a smoothing symmetric form with constant `c`, `N = ∇𝔓`. -/
structure IsBirkSmoothing (a p : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p) (n : ℕ) (c : ℝ)
    (𝔓 : ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => BirkSpace) ℂ)
    (N : ContinuousMultilinearMap ℂ (fun _ : Fin n => BirkSpace) BirkSpace) : Prop where
  nonneg : 0 ≤ c
  symm : ∀ (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → BirkSpace),
    𝔓 (fun i => w (σ i)) = 𝔓 w
  pairing : ∀ (w : Fin n → BirkSpace) (v : BirkSpace),
    𝔓 (Fin.snoc (α := fun _ => BirkSpace) w v) = birkOmegaPlus a p ha hp (N w) v
  bound : ∀ w : Fin n → BirkSpace, ‖N w‖ ≤ c * ∏ i, ‖w i‖

/-- The diagonal `P(w) = 𝔓(w, …, w)`. -/
def birkDiag (𝔓 : ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => BirkSpace) ℂ)
    (w : BirkSpace) : ℂ := 𝔓 (fun _ => w)

/-- The field `X_P(w) = d ∇𝔓(w, …, w)`, `d = n + 1`. -/
def birkDiagField (N : ContinuousMultilinearMap ℂ (fun _ : Fin n => BirkSpace) BirkSpace)
    (w : BirkSpace) : BirkSpace := ((n + 1 : ℕ) : ℂ) • N (fun _ => w)

section

variable {c : ℝ} {𝔓 : ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => BirkSpace) ℂ}
  {N : ContinuousMultilinearMap ℂ (fun _ : Fin n => BirkSpace) BirkSpace}

theorem birkDiag_analyticOnNhd (𝔓 : ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => BirkSpace) ℂ)
    :
    AnalyticOnNhd ℂ (birkDiag 𝔓) Set.univ := by
  intro w _
  have hdiag : AnalyticAt ℂ (fun w : BirkSpace => fun _ : Fin (n + 1) => w) w :=
    (ContinuousLinearMap.pi fun _ : Fin (n + 1) => ContinuousLinearMap.id ℂ BirkSpace).analyticAt w
  exact (𝔓.cpolynomialAt (x := fun _ => w)).analyticAt.comp hdiag

theorem birkDiagField_analyticOnNhd
    (N : ContinuousMultilinearMap ℂ (fun _ : Fin n => BirkSpace) BirkSpace) :
    AnalyticOnNhd ℂ (birkDiagField N) Set.univ := by
  intro w _
  have hdiag : AnalyticAt ℂ (fun w : BirkSpace => fun _ : Fin n => w) w :=
    (ContinuousLinearMap.pi fun _ : Fin n => ContinuousLinearMap.id ℂ BirkSpace).analyticAt w
  exact ((N.cpolynomialAt (x := fun _ => w)).analyticAt.comp hdiag).const_smul (c := ((n + 1 : ℕ) :
      ℂ))

theorem snoc_const_apply (w v : BirkSpace) (j : Fin (n + 1)) :
    (Fin.snoc (α := fun _ => BirkSpace) (fun _ : Fin n => w) v) j =
      if j = Fin.last n then v else w := by
  induction j using Fin.lastCases with
  | last => simp
  | cast j => simp [(Fin.castSucc_lt_last j).ne]

theorem update_const_eq_snoc_comp (w v : BirkSpace) (i : Fin (n + 1)) :
    Function.update (fun _ : Fin (n + 1) => w) i v =
      fun j => (Fin.snoc (α := fun _ => BirkSpace) (fun _ : Fin n => w) v)
        (Equiv.swap i (Fin.last n) j) := by
  ext j
  rw [Function.update_apply, snoc_const_apply, Equiv.swap_apply_def]
  by_cases hj : j = i <;> by_cases hl : j = Fin.last n <;> by_cases hi : i = Fin.last n <;>
    simp_all

variable (hS : IsBirkSmoothing a p ha hp n c 𝔓 N)

omit hS in
/-- (`bpW:w3:forms`) The derivative of the diagonal of a multilinear form. -/
theorem hasFDerivAt_birkDiag (w : BirkSpace) :
    HasFDerivAt (birkDiag 𝔓)
      (∑ i : Fin (n + 1), 𝔓.toContinuousLinearMap (fun _ => w) i) w := by
  classical
  have h := HasFDerivAt.multilinear_comp (f := 𝔓) (g := fun (_ : Fin (n + 1)) (x : BirkSpace) => x)
    (g' := fun _ => ContinuousLinearMap.id ℂ BirkSpace) (x := w) (fun _ => hasFDerivAt_id w)
  exact h.congr_fderiv (by simp)

include hS in
/-- (`bpW:w3:forms`) `DP(w) v = d 𝔓(w, …, w, v)` for the diagonal of a symmetric form. -/
theorem fderiv_birkDiag_apply (w v : BirkSpace) :
    fderiv ℂ (birkDiag 𝔓) w v = ((n + 1 : ℕ) : ℂ) * 𝔓 (Fin.snoc (α := fun _ => BirkSpace)
      (fun _ : Fin n => w) v) := by
  classical
  rw [(hasFDerivAt_birkDiag (𝔓 := 𝔓) w).fderiv, sum_apply]
  have : ∀ i : Fin (n + 1), 𝔓.toContinuousLinearMap (fun _ => w) i v =
      𝔓 (Fin.snoc (α := fun _ => BirkSpace) (fun _ : Fin n => w) v) := fun i => by
    rw [ContinuousMultilinearMap.toContinuousLinearMap_apply, update_const_eq_snoc_comp]
    exact hS.symm _ _
  simp [this]

theorem birkOmegaPlus_smul (ha : 0 ≤ a) (hp : 0 ≤ p) (z : ℂ) (X v : BirkSpace) :
    birkOmegaPlus a p ha hp (z • X) v = z * birkOmegaPlus a p ha hp X v := by
  simp [birkOmegaPlus]

include hS in
/-- (`bpW:w3:forms`) `X_P(w) = d ∇𝔓(w, …, w)` is the Hamiltonian field of `P`, on all of `𝔚`. -/
theorem birkDiag_field : IsBirkHamFieldPlus a p ha hp Set.univ (birkDiag 𝔓) (birkDiagField N) where
  differentiableOn := (birkDiag_analyticOnNhd 𝔓).differentiableOn
  deriv_eq w _ v := by
    rw [fderiv_birkDiag_apply hS, hS.pairing, birkDiagField, birkOmegaPlus_smul]

theorem snoc_const_self (w : BirkSpace) :
    (Fin.snoc (α := fun _ => BirkSpace) (fun _ : Fin n => w) w) = fun _ => w := by
  ext j
  rw [snoc_const_apply]
  split_ifs <;> simp_all

include hS in
/-- (`bpW:w3:forms`) `|P(w)| ≤ c ‖w‖^d`. -/
theorem norm_birkDiag_le (w : BirkSpace) : ‖birkDiag 𝔓 w‖ ≤ c * ‖w‖ ^ (n + 1) := by
  have h1 : birkDiag 𝔓 w = birkOmegaPlus a p ha hp (N fun _ => w) w := by
    rw [← hS.pairing, snoc_const_self]; rfl
  rw [h1]
  refine (norm_birkOmega_le ha hp _ _).trans ?_
  have h2 : ‖birkEmbed a (p + 1) p (by linarith) (N fun _ => w)‖ ≤ ‖N fun _ => w‖ := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    calc _ ≤ 1 * ‖N fun _ => w‖ := by gcongr; exact norm_birkEmbed_le _ _ _ _
      _ = _ := one_mul _
  have h3 := hS.bound fun _ => w
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h3
  calc ‖birkEmbed a (p + 1) p (by linarith) (N fun _ => w)‖ * ‖w‖ ≤ (c * ‖w‖ ^ n) * ‖w‖ := by
        gcongr; exact h2.trans h3
    _ = c * ‖w‖ ^ (n + 1) := by ring

include hS in
/-- (`bpW:w3:forms`) `‖X_P(w)‖₊ ≤ d c ‖w‖^{d-1}`. -/
theorem norm_birkDiagField_le (w : BirkSpace) :
    ‖birkDiagField N w‖ ≤ (n + 1) * c * ‖w‖ ^ n := by
  have h3 := hS.bound fun _ => w
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h3
  rw [birkDiagField, norm_smul]
  simp only [Complex.norm_natCast]
  push_cast
  calc ((n : ℝ) + 1) * ‖N fun _ => w‖ ≤ ((n : ℝ) + 1) * (c * ‖w‖ ^ n) := by gcongr
    _ = _ := by ring

include hS in
/-- (`bpW:w3:forms`) `‖X_P(y) - X_P(w)‖₊ ≤ d(d-1) c max(‖y‖,‖w‖)^{d-2} ‖y - w‖` (`n ≥ 1`). -/
theorem norm_birkDiagField_sub_le (hn : 1 ≤ n) (y w : BirkSpace) :
    ‖birkDiagField N y - birkDiagField N w‖ ≤
      (n + 1) * n * c * max ‖y‖ ‖w‖ ^ (n - 1) * ‖y - w‖ := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hN : ‖N‖ ≤ c := ContinuousMultilinearMap.opNorm_le_bound hS.nonneg hS.bound
  have h := N.norm_image_sub_le (fun _ : Fin n => y) (fun _ : Fin n => w)
  simp only [Fintype.card_fin, pi_norm_const] at h
  have e : (fun _ : Fin n => y) - (fun _ : Fin n => w) = fun _ => y - w := by ext; rfl
  rw [e, pi_norm_const] at h
  rw [birkDiagField, birkDiagField, ← smul_sub, norm_smul]
  simp only [Complex.norm_natCast]
  push_cast
  calc ((n : ℝ) + 1) * ‖(N fun _ => y) - N fun _ => w‖
      ≤ ((n : ℝ) + 1) * (‖N‖ * n * max ‖y‖ ‖w‖ ^ (n - 1) * ‖y - w‖) := by gcongr
    _ ≤ ((n : ℝ) + 1) * (c * n * max ‖y‖ ‖w‖ ^ (n - 1) * ‖y - w‖) := by gcongr
    _ = _ := by ring

theorem birkDiag_isClassA (hS : IsBirkSmoothing a p ha hp n c 𝔓 N)
    (hreal : ∀ w : Fin (n + 1) → BirkSpace, 𝔓 (fun i => birkRho (w i)) = conj (𝔓 w)) :
    IsBirkClassA a p ha hp Set.univ (birkDiag 𝔓) (birkDiagField N) where
  isOpen := isOpen_univ
  rho_mem _ _ := trivial
  real w _ := hreal fun _ => w
  analytic := birkDiag_analyticOnNhd 𝔓
  field w hw v := (birkDiag_field hS).deriv_eq w hw v
  analytic_field := birkDiagField_analyticOnNhd N

end

end KAM.Wave

end
