/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Data.Fintype.Perm

/-!
# Block composition of multilinear maps and symmetrization (blueprint-W `bpW:w3:Yseries`)

Package W3-MAIN, blueprint label `bpW:w3:Yseries`.

`blockMap R sz P n h`: for `R : E^r → G` continuous multilinear and `P l : E^{sz l} → E`, the
continuous multilinear map `E^n → G`, `v ↦ R(P_0(v|₀), …, P_{r-1}(v|_{r-1}))`
(`n = Σ_l sz l`), with `‖blockMap R sz P n h‖ ≤ ‖R‖ ∏‖P l‖`. `symmMulti`: the symmetrization of a
continuous multilinear map (same diagonal, norm `≤`), and the derivative of the diagonal of a
symmetric multilinear map (`hasFDerivAt_diag_symm`).
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The index equivalence `(Σ l, Fin (sz l)) ≃ Fin n`. -/
def blockEquiv {r : ℕ} (sz : Fin r → ℕ) (n : ℕ) (h : ∑ l, sz l = n) :
    (Σ l : Fin r, Fin (sz l)) ≃ Fin n :=
  (finSigmaFinEquiv (n := sz)).trans (finCongr h)

/-- `v ↦ R(P_0(v|₀), …)`. -/
def blockMap {r : ℕ} (R : ContinuousMultilinearMap ℂ (fun _ : Fin r => E) G) (sz : Fin r → ℕ)
    (P : (l : Fin r) → ContinuousMultilinearMap ℂ (fun _ : Fin (sz l) => E) E) (n : ℕ)
    (h : ∑ l, sz l = n) : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) G where
  toMultilinearMap :=
    (R.toMultilinearMap.compMultilinearMap (fun l => (P l).toMultilinearMap)).domDomCongr
      (blockEquiv sz n h)
  cont := by
    show Continuous fun v : Fin n → E =>
      R fun l => P l (fun b => v (blockEquiv sz n h ⟨l, b⟩))
    refine R.cont.comp (continuous_pi fun l => (P l).cont.comp (continuous_pi fun b => ?_))
    exact continuous_apply _

theorem blockMap_apply {r : ℕ} (R : ContinuousMultilinearMap ℂ (fun _ : Fin r => E) G)
    (sz : Fin r → ℕ) (P : (l : Fin r) → ContinuousMultilinearMap ℂ (fun _ : Fin (sz l) => E) E)
    (n : ℕ) (h : ∑ l, sz l = n) (v : Fin n → E) :
    blockMap R sz P n h v = R fun l => P l (fun b => v (blockEquiv sz n h ⟨l, b⟩)) := rfl

theorem blockMap_const {r : ℕ} (R : ContinuousMultilinearMap ℂ (fun _ : Fin r => E) G)
    (sz : Fin r → ℕ) (P : (l : Fin r) → ContinuousMultilinearMap ℂ (fun _ : Fin (sz l) => E) E)
    (n : ℕ) (h : ∑ l, sz l = n) (w : E) :
    blockMap R sz P n h (fun _ => w) = R fun l => P l (fun _ => w) := rfl

theorem norm_blockMap_le {r : ℕ} (R : ContinuousMultilinearMap ℂ (fun _ : Fin r => E) G)
    (sz : Fin r → ℕ) (P : (l : Fin r) → ContinuousMultilinearMap ℂ (fun _ : Fin (sz l) => E) E)
    (n : ℕ) (h : ∑ l, sz l = n) :
    ‖blockMap R sz P n h‖ ≤ ‖R‖ * ∏ l, ‖P l‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  rw [blockMap_apply]
  refine (R.le_opNorm _).trans ?_
  have hb : ∀ l : Fin r, ‖P l (fun b => v (blockEquiv sz n h ⟨l, b⟩))‖ ≤
      ‖P l‖ * ∏ b, ‖v (blockEquiv sz n h ⟨l, b⟩)‖ := fun l => (P l).le_opNorm _
  have hprod : ∏ l : Fin r, ‖P l (fun b => v (blockEquiv sz n h ⟨l, b⟩))‖ ≤
      ∏ l : Fin r, (‖P l‖ * ∏ b, ‖v (blockEquiv sz n h ⟨l, b⟩)‖) := by
    gcongr with l hl; exact hb l
  have hsig : ∏ l : Fin r, ∏ b, ‖v (blockEquiv sz n h ⟨l, b⟩)‖ = ∏ i : Fin n, ‖v i‖ := by
    rw [← Fintype.prod_sigma' (fun l b => ‖v (blockEquiv sz n h ⟨l, b⟩)‖)]
    exact Equiv.prod_comp (blockEquiv sz n h) (fun i => ‖v i‖)
  calc ‖R‖ * ∏ l : Fin r, ‖P l (fun b => v (blockEquiv sz n h ⟨l, b⟩))‖
      ≤ ‖R‖ * ∏ l : Fin r, (‖P l‖ * ∏ b, ‖v (blockEquiv sz n h ⟨l, b⟩)‖) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖R‖ * (∏ l, ‖P l‖) * ∏ i : Fin n, ‖v i‖ := by
        rw [Finset.prod_mul_distrib, hsig]; ring

/-! ### Symmetrization -/

/-- The symmetrization `(1/n!) Σ_σ Φ ∘ σ`. -/
def symmMulti {n : ℕ} (Φ : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) G) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => E) G :=
  ((1 : ℂ) / (n.factorial : ℂ)) •
    ∑ σ : Equiv.Perm (Fin n), ContinuousMultilinearMap.domDomCongr σ Φ

theorem symmMulti_apply {n : ℕ} (Φ : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) G)
    (v : Fin n → E) :
    symmMulti Φ v =
      ((1 : ℂ) / (n.factorial : ℂ)) • ∑ σ : Equiv.Perm (Fin n), Φ (fun i => v (σ i)) := by
  unfold symmMulti
  simp [ContinuousMultilinearMap.sum_apply]

theorem symmMulti_perm {n : ℕ} (Φ : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) G)
    (τ : Equiv.Perm (Fin n)) (v : Fin n → E) :
    symmMulti Φ (fun i => v (τ i)) = symmMulti Φ v := by
  rw [symmMulti_apply, symmMulti_apply]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => Φ (fun i => v (σ i)))

theorem symmMulti_const {n : ℕ} (Φ : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) G) (w : E) :
    symmMulti Φ (fun _ => w) = Φ (fun _ => w) := by
  rw [symmMulti_apply]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [one_div, inv_mul_cancel₀ this, one_smul]

theorem norm_symmMulti_le {n : ℕ} (Φ : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) G) :
    ‖symmMulti Φ‖ ≤ ‖Φ‖ := by
  unfold symmMulti
  rw [norm_smul]
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h1 : ‖(1 : ℂ) / (n.factorial : ℂ)‖ = 1 / (n.factorial : ℝ) := by
    rw [norm_div, norm_one]; simp
  rw [h1]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
  have : ∑ σ : Equiv.Perm (Fin n), ‖ContinuousMultilinearMap.domDomCongr σ Φ‖ ≤
      ∑ σ : Equiv.Perm (Fin n), ‖Φ‖ :=
    Finset.sum_le_sum fun σ _ => by
      rw [ContinuousMultilinearMap.norm_domDomCongr]
  refine (mul_le_mul_of_nonneg_left this (by positivity)).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The derivative of the diagonal `w ↦ Φ(w,…,w)` of a symmetric multilinear map is
`u ↦ (k+1) Φ(u, w, …, w)`. -/
theorem hasFDerivAt_diag_symm {k : ℕ} (Φ : ContinuousMultilinearMap ℂ (fun _ : Fin (k + 1) => E) G)
    (hs : ∀ (τ : Equiv.Perm (Fin (k + 1))) (v : Fin (k + 1) → E), Φ (fun i => v (τ i)) = Φ v)
    (w : E) :
    HasFDerivAt (fun w : E => Φ (fun _ => w))
      (((k + 1 : ℕ) : ℂ) • ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => E) G
        (fun _ => w)).comp Φ.curryLeft)) w := by
  classical
  have hd : HasFDerivAt (fun w : E => fun _ : Fin (k + 1) => w)
      (ContinuousLinearMap.pi fun _ : Fin (k + 1) => ContinuousLinearMap.id ℂ E) w :=
    hasFDerivAt_pi'.2 fun _ => hasFDerivAt_id w
  have h := (Φ.hasFDerivAt (x := fun _ : Fin (k + 1) => w)).comp w hd
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun u => ?_
  have hc : ∀ (j : Fin (k + 1)), j ≠ 0 →
      (Fin.cons u (fun _ : Fin k => w) : Fin (k + 1) → E) j = w := fun j hj => by
    obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj
    simp
  have e : ∀ i : Fin (k + 1), Φ (Function.update (fun _ : Fin (k + 1) => w) i u) =
      Φ (Fin.cons u (fun _ : Fin k => w)) := fun i => by
    rw [← hs (Equiv.swap 0 i) (Fin.cons u (fun _ : Fin k => w))]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp [Function.update]
    · by_cases hj0 : j = 0
      · subst hj0
        have : i ≠ 0 := fun h => hj h.symm
        rw [Function.update_of_ne hj, Equiv.swap_apply_left, hc i this]
      · rw [Function.update_of_ne hj, Equiv.swap_apply_of_ne_of_ne hj0 hj, hc j hj0]
  show _ = ((k + 1 : ℕ) : ℂ) • Φ.curryLeft u (fun _ => w)
  rw [ContinuousLinearMap.comp_apply]
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  calc _ = ∑ i : Fin (k + 1), Φ (Fin.cons u (fun _ : Fin k => w)) :=
        Finset.sum_congr rfl fun i _ => e i
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [← Nat.cast_smul_eq_nsmul ℂ]
      rfl

end KAM.Wave

end
