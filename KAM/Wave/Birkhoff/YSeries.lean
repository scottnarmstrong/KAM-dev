/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieAnalyticPlus
public import KAM.Wave.Birkhoff.BlockMap

/-!
# The power series of the integrand `Y` (blueprint-W `bpW:w3:Yseries`), coefficients

Package W3-MAIN, blueprint label `bpW:w3:Yseries`.

In the two-space setting of `LiePlus` (`ι : F → E`, `S : E³ → F`, `T = ι ∘ S`) and a cubic
`N : E³ → F`: `lieNsum n = Σ_{a+b+c=n} N(Φ_a,Φ_b,Φ_c)` (the `n`-th coefficient of
`N(Γ_t,Γ_t,Γ_t)`) and `lieV n : E^{2n+3} → F` is defined by the triangular recursion
`V_n = Nsum_n - Σ_{j<n} (2j+3) Ψ^F_j(ι V_{n-1-j}, ·)`, where `Ψ^F_j` is the symmetrization of
`Φ^F_j` and `Ψ(V, ·)` puts `V` in the first slot (`slotMap`). Then
`Σ_n t^n V_n(w,…,w)` solves `DΓ_t(w) (ι V) = ι N(Γ_t(w))` (`bpW:w3:Yseries`, Steps inverse and
integrand).
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- `Ψ(V(g), h)` as a multilinear map in `(g, h)`: `V` in the first slot of `Ψ`. -/
def slotMap {k a : ℕ} (Ψ : ContinuousMultilinearMap ℂ (fun _ : Fin (k + 1) => E) F)
    (V : ContinuousMultilinearMap ℂ (fun _ : Fin a => E) E) (n : ℕ) (h : a + k = n) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => E) F :=
  ContinuousMultilinearMap.domDomCongr (finSumFinEquiv.trans (finCongr h))
    (ContinuousMultilinearMap.uncurrySum (Ψ.curryLeft.compContinuousMultilinearMap V))

theorem slotMap_const {k a : ℕ} (Ψ : ContinuousMultilinearMap ℂ (fun _ : Fin (k + 1) => E) F)
    (V : ContinuousMultilinearMap ℂ (fun _ : Fin a => E) E) (n : ℕ) (h : a + k = n) (w : E) :
    slotMap Ψ V n h (fun _ => w) = Ψ (Fin.cons (V (fun _ => w)) (fun _ : Fin k => w)) := rfl

theorem norm_slotMap_le {k a : ℕ} (Ψ : ContinuousMultilinearMap ℂ (fun _ : Fin (k + 1) => E) F)
    (V : ContinuousMultilinearMap ℂ (fun _ : Fin a => E) E) (n : ℕ) (h : a + k = n) :
    ‖slotMap Ψ V n h‖ ≤ ‖Ψ‖ * ‖V‖ := by
  unfold slotMap
  rw [ContinuousMultilinearMap.norm_domDomCongr]
  have h1 : ‖ContinuousMultilinearMap.uncurrySum (Ψ.curryLeft.compContinuousMultilinearMap V)‖ =
      ‖Ψ.curryLeft.compContinuousMultilinearMap V‖ :=
    ((ContinuousMultilinearMap.currySumEquiv ℂ (Fin a) (Fin k) E F).symm).norm_map _
  rw [h1]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  rw [ContinuousMultilinearMap.curryLeft_norm]

variable (ι : F →L[ℂ] E) (S N : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) F)

/-- `Ψ^F_j`, the symmetrization of `Φ^F_j`. -/
def lieSymF (j : ℕ) : ContinuousMultilinearMap ℂ (fun _ : Fin (2 * (j + 1) + 1) => E) F :=
  symmMulti (lieMultiF ι S j)

/-- `Nsum_n = Σ_{a+b+c=n} N(Φ_a, Φ_b, Φ_c)`. -/
def lieNsum (n : ℕ) : ContinuousMultilinearMap ℂ (fun _ : Fin (2 * n + 3) => E) F :=
  ∑ x ∈ Finset.Nat.antidiagonalTuple 3 n,
    lieBlockT N x (fun j => lieMulti (lieT ι S) (x j)) (2 * n + 3)

/-- The coefficients `V_n : E^{2n+3} → F`. -/
def lieV : (n : ℕ) → ContinuousMultilinearMap ℂ (fun _ : Fin (2 * n + 3) => E) F
  | n => lieNsum ι S N n - ∑ j ∈ (Finset.range n).attach,
      ((2 * (j.1 : ℂ) + 3)) • slotMap (lieSymF ι S j.1)
        (ι.compContinuousMultilinearMap (lieV (n - 1 - j.1))) (2 * n + 3)
        (by have := Finset.mem_range.1 j.2; omega)
decreasing_by
  have := Finset.mem_range.1 j.2
  omega

theorem lieV_eq (n : ℕ) :
    lieV ι S N n = lieNsum ι S N n - ∑ j ∈ Finset.range n,
      if h : j < n then ((2 * (j : ℂ) + 3)) • slotMap (lieSymF ι S j)
        (ι.compContinuousMultilinearMap (lieV ι S N (n - 1 - j))) (2 * n + 3)
        (by omega) else 0 := by
  rw [lieV]
  congr 1
  rw [← Finset.sum_attach (Finset.range n)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := Finset.mem_range.1 j.2
  simp [this]

theorem lieV_eval (w : E) (n : ℕ) :
    lieV ι S N n (fun _ => w) = lieNsum ι S N n (fun _ => w) - ∑ j ∈ Finset.range n,
      if j < n then ((2 * (j : ℂ) + 3)) • lieSymF ι S j
        (Fin.cons (ι (lieV ι S N (n - 1 - j) (fun _ => w))) (fun _ : Fin (2 * (j + 1)) => w))
      else 0 := by
  rw [lieV_eq]
  simp only [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j < n := Finset.mem_range.1 hj
  simp only [hjn, dite_true, if_true]
  rw [ContinuousMultilinearMap.smul_apply, slotMap_const]
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
theorem comp_lieBlockT (R : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) F) (f : Fin 3 → ℕ)
    (P : (j : Fin 3) → ContinuousMultilinearMap ℂ (fun _ : Fin (2 * f j + 1) => E) E) (n : ℕ) :
    lieBlockT (ι.compContinuousMultilinearMap R) f P n =
      ι.compContinuousMultilinearMap (lieBlockT R f P n) := by
  unfold lieBlockT
  by_cases h : ∑ j, (2 * f j + 1) = n
  · simp only [h, dite_true]
    rfl
  · simp only [h, dite_false]
    ext v
    simp

theorem comp_lieMultiF (j : ℕ) :
    ι.compContinuousMultilinearMap (lieMultiF ι S j) = lieMulti (lieT ι S) (j + 1) := by
  rw [lieMulti_succ]
  unfold lieMultiF
  refine ContinuousMultilinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.sum_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [lieT, comp_lieBlockT]
  rfl

theorem comp_lieSymF (j : ℕ) :
    ι.compContinuousMultilinearMap (lieSymF ι S j) =
      symmMulti (lieMulti (lieT ι S) (j + 1)) := by
  rw [← comp_lieMultiF]
  unfold lieSymF
  refine ContinuousMultilinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    symmMulti_apply, map_smul, map_sum]

theorem lieDer_eq_symm (T : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) E) (j : ℕ) (w u : E) :
    lieDer T w (j + 1) u =
      ((2 * (j + 1) + 1 : ℕ) : ℂ) • symmMulti (lieMulti T (j + 1)) (Fin.cons u (fun _ => w)) := by
  have h1 := hasFDerivAt_lieSeq T (j + 1) w
  have h2 := hasFDerivAt_diag_symm (symmMulti (lieMulti T (j + 1)))
    (symmMulti_perm (lieMulti T (j + 1))) w
  have e : (fun w' : E => lieSeq T w' (j + 1)) =
      fun w' : E => symmMulti (lieMulti T (j + 1)) (fun _ => w') := by
    funext w'; rw [symmMulti_const, lieMulti_const]
  rw [e] at h1
  have := DFunLike.congr_fun (h1.unique h2) u
  rw [this]
  rfl

theorem map_lieSymF_cons (j : ℕ) (w u : E) :
    ι (((2 * (j : ℂ) + 3)) • lieSymF ι S j (Fin.cons u (fun _ : Fin (2 * (j + 1)) => w))) =
      lieDer (lieT ι S) w (j + 1) u := by
  rw [lieDer_eq_symm, ← comp_lieSymF, map_smul]
  have : ((2 * (j + 1) + 1 : ℕ) : ℂ) = 2 * (j : ℂ) + 3 := by push_cast; ring
  rw [this]
  rfl

end KAM.Wave

end
