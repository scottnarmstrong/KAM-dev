/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Witness.BinomialProd

/-!
# Derivatives of binomial product remainders (T2-CONF, N4)

The first derivatives of `binomProdRem s L B u` (`Witness/BinomialProd.lean`):

* in `u` (`fderiv` on `ι → ℝ` in the direction `Pi.single i 1`): the slot sum with the `i`-th slots
  replaced by their `u`-derivatives `binomSlotDu`; bound
  `tailSum (update (boxMaj s L bmin bmax r) i (slotMajDu s_i L bmin_i bmax_i r)) L`
  (`abs_fderiv_binomProdRem_u_le_box`);
* in the angles `φ`, for base points `B_j = Bf j φ` depending on `φ : Fin 2 → ℝ` and `u` fixed: by
  the chain rule `∂_{φ_a} = Σ_i ∂_a(Bf i) · ∂_{B_i}`, where `∂_{B_i}` replaces the `i`-th slots by
  `s_i · binomSlot (s_i - 1)`; with `|∂_a Bf i| ≤ β_i` the bound is
  `Σ_i β_i · tailSum (update (boxMaj s L bmin bmax r) i (|s_i| · slotMaj (s_i - 1) L …)) L`
  (`abs_fderiv_binomProdRem_phi_le_box`).

Both come with differentiability (`differentiableAt_binomProdRem_u`,
`differentiableAt_binomProdRem_phi`).
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A bound of a slot sum with the `i`-th slot family replaced. -/
theorem abs_tail_update_le {g G : ι → ℕ → ℝ} {gi Gi : ℕ → ℝ} {L : ℕ} (i : ι)
    (hg : ∀ j m, m < L + 2 → |g j m| ≤ G j m) (hgi : ∀ m, m < L + 2 → |gi m| ≤ Gi m) :
    |∑ p ∈ tailSet ι L, gi (p i) * ∏ j ∈ univ.erase i, g j (p j)| ≤
      tailSum (Function.update G i Gi) L := by
  have h : ∑ p ∈ tailSet ι L, gi (p i) * ∏ j ∈ univ.erase i, g j (p j) =
      ∑ p ∈ tailSet ι L, ∏ j, Function.update g i gi j (p j) :=
    sum_congr rfl fun p _ => (prod_update_slot g i gi p).symm
  rw [h]
  refine abs_tail_le fun j m hm => ?_
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self]
    exact hgi m hm
  · simp only [Function.update_of_ne hj]
    exact hg j m hm

/-! ### `u`-derivatives -/

/-- The derivative in `u` of one product of slots. -/
theorem hasFDerivAt_slotProd_u (s : ι → ℝ) (L : ℕ) (B u : ι → ℝ) (p : ι → ℕ)
    (hBu : ∀ j, 0 < B j + u j) :
    HasFDerivAt (fun v : ι → ℝ => ∏ j, binomSlot (s j) L (B j) (v j) (p j))
      (∑ i, (∏ j ∈ univ.erase i, binomSlot (s j) L (B j) (u j) (p j)) •
        (binomSlotDu (s i) L (B i) (u i) (p i) • ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : ι => ℝ) i)) u := by
  have hj : ∀ j ∈ (univ : Finset ι), HasFDerivAt
      (fun v : ι → ℝ => binomSlot (s j) L (B j) (v j) (p j))
      (binomSlotDu (s j) L (B j) (u j) (p j) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j) u := fun j _ =>
    HasDerivAt.comp_hasFDerivAt (h₂ := fun t => binomSlot (s j) L (B j) t (p j)) u
      (hasDerivAt_binomSlot_u (s j) L (hBu j) (p j)) (hasFDerivAt_apply (𝕜 := ℝ) j u)
  exact HasFDerivAt.finsetProd hj

/-- The function `v ↦ binomProdRem s L B v` as a slot sum. -/
theorem binomProdRem_fun_u_eq (s : ι → ℝ) (L : ℕ) (B : ι → ℝ) :
    (fun v => binomProdRem s L B v) =
      fun v => ∑ p ∈ tailSet ι L, ∏ j, binomSlot (s j) L (B j) (v j) (p j) :=
  funext fun v => binomProdRem_eq s L B v

theorem hasFDerivAt_binomProdRem_u (s : ι → ℝ) (L : ℕ) (B u : ι → ℝ)
    (hBu : ∀ j, 0 < B j + u j) :
    HasFDerivAt (fun v => binomProdRem s L B v)
      (∑ p ∈ tailSet ι L, ∑ i, (∏ j ∈ univ.erase i, binomSlot (s j) L (B j) (u j) (p j)) •
        (binomSlotDu (s i) L (B i) (u i) (p i) • ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : ι => ℝ) i)) u := by
  rw [binomProdRem_fun_u_eq]
  exact HasFDerivAt.fun_sum fun p _ => hasFDerivAt_slotProd_u s L B u p hBu

theorem differentiableAt_binomProdRem_u (s : ι → ℝ) (L : ℕ) (B u : ι → ℝ)
    (hBu : ∀ j, 0 < B j + u j) : DifferentiableAt ℝ (fun v => binomProdRem s L B v) u :=
  (hasFDerivAt_binomProdRem_u s L B u hBu).differentiableAt

/-- The partial derivative in `u_i`, as a slot sum. -/
theorem fderiv_binomProdRem_u (s : ι → ℝ) (L : ℕ) (B u : ι → ℝ) (hBu : ∀ j, 0 < B j + u j)
    (i : ι) :
    fderiv ℝ (fun v => binomProdRem s L B v) u (Pi.single i 1) =
      ∑ p ∈ tailSet ι L, binomSlotDu (s i) L (B i) (u i) (p i) *
        ∏ j ∈ univ.erase i, binomSlot (s j) L (B j) (u j) (p j) := by
  rw [(hasFDerivAt_binomProdRem_u s L B u hBu).fderiv]
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul,
    ContinuousLinearMap.proj_apply]
  refine sum_congr rfl fun p _ => ?_
  rw [sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
  simp [mul_comm]

/-- **`u`-derivative bound.** On the box, `|∂_{u_i} binomProdRem s L B u|` is at most the tail sum
with the `i`-th slot majorants replaced by `slotMajDu`. -/
theorem abs_fderiv_binomProdRem_u_le_box (s : ι → ℝ) (L : ℕ) {bmin bmax B u : ι → ℝ} {r : ℝ}
    (hr : ∀ j, r < bmin j) (h1 : ∀ j, bmin j ≤ B j) (h2 : ∀ j, B j ≤ bmax j)
    (hu : ∀ j, |u j| ≤ r) (i : ι) :
    |fderiv ℝ (fun v => binomProdRem s L B v) u (Pi.single i 1)| ≤
      tailSum (Function.update (boxMaj s L bmin bmax r) i
        (slotMajDu (s i) L (bmin i) (bmax i) r)) L := by
  have hBu : ∀ j, 0 < B j + u j := fun j => by
    linarith [hr j, h1 j, hu j, neg_abs_le (u j)]
  rw [fderiv_binomProdRem_u s L B u hBu i]
  exact abs_tail_update_le i (fun j m _ => abs_binomSlot_le m (h1 j) (h2 j) (hr j) (hu j))
    fun m _ => abs_binomSlotDu_le m (h1 i) (h2 i) (hr i) (hu i)

/-! ### Angle derivatives through `B(φ)` -/

/-- The derivative in `φ` of one product of slots, with base points `Bf j φ`. -/
theorem hasFDerivAt_slotProd_phi (s : ι → ℝ) (L : ℕ) (Bf : ι → (Fin 2 → ℝ) → ℝ) (u : ι → ℝ)
    (p : ι → ℕ) {φ : Fin 2 → ℝ} (hBd : ∀ j, DifferentiableAt ℝ (Bf j) φ)
    (hB : ∀ j, 0 < Bf j φ) (hBu : ∀ j, 0 < Bf j φ + u j) :
    HasFDerivAt (fun φ => ∏ j, binomSlot (s j) L (Bf j φ) (u j) (p j))
      (∑ i, (∏ j ∈ univ.erase i, binomSlot (s j) L (Bf j φ) (u j) (p j)) •
        ((s i * binomSlot (s i - 1) L (Bf i φ) (u i) (p i)) • fderiv ℝ (Bf i) φ)) φ :=
  HasFDerivAt.finsetProd (u := univ) (g := fun j φ => binomSlot (s j) L (Bf j φ) (u j) (p j))
    fun j _ => (hasDerivAt_binomSlot_B (s j) L (hB j) (hBu j) (p j)).comp_hasFDerivAt φ
      (hBd j).hasFDerivAt

theorem hasFDerivAt_binomProdRem_phi (s : ι → ℝ) (L : ℕ) (Bf : ι → (Fin 2 → ℝ) → ℝ)
    (u : ι → ℝ) {φ : Fin 2 → ℝ} (hBd : ∀ j, DifferentiableAt ℝ (Bf j) φ)
    (hB : ∀ j, 0 < Bf j φ) (hBu : ∀ j, 0 < Bf j φ + u j) :
    HasFDerivAt (fun φ => binomProdRem s L (fun j => Bf j φ) u)
      (∑ p ∈ tailSet ι L, ∑ i, (∏ j ∈ univ.erase i, binomSlot (s j) L (Bf j φ) (u j) (p j)) •
        ((s i * binomSlot (s i - 1) L (Bf i φ) (u i) (p i)) • fderiv ℝ (Bf i) φ)) φ := by
  have hfun : (fun φ => binomProdRem s L (fun j => Bf j φ) u) =
      fun φ => ∑ p ∈ tailSet ι L, ∏ j, binomSlot (s j) L (Bf j φ) (u j) (p j) :=
    funext fun φ => binomProdRem_eq s L (fun j => Bf j φ) u
  rw [hfun]
  exact HasFDerivAt.fun_sum fun p _ => hasFDerivAt_slotProd_phi s L Bf u p hBd hB hBu

theorem differentiableAt_binomProdRem_phi (s : ι → ℝ) (L : ℕ) (Bf : ι → (Fin 2 → ℝ) → ℝ)
    (u : ι → ℝ) {φ : Fin 2 → ℝ} (hBd : ∀ j, DifferentiableAt ℝ (Bf j) φ)
    (hB : ∀ j, 0 < Bf j φ) (hBu : ∀ j, 0 < Bf j φ + u j) :
    DifferentiableAt ℝ (fun φ => binomProdRem s L (fun j => Bf j φ) u) φ :=
  (hasFDerivAt_binomProdRem_phi s L Bf u hBd hB hBu).differentiableAt

/-- The partial derivative in `φ_a`, by the chain rule through the base points. -/
theorem fderiv_binomProdRem_phi (s : ι → ℝ) (L : ℕ) (Bf : ι → (Fin 2 → ℝ) → ℝ) (u : ι → ℝ)
    {φ : Fin 2 → ℝ} (hBd : ∀ j, DifferentiableAt ℝ (Bf j) φ) (hB : ∀ j, 0 < Bf j φ)
    (hBu : ∀ j, 0 < Bf j φ + u j) (a : Fin 2) :
    fderiv ℝ (fun φ => binomProdRem s L (fun j => Bf j φ) u) φ (Pi.single a 1) =
      ∑ i, fderiv ℝ (Bf i) φ (Pi.single a 1) *
        ∑ p ∈ tailSet ι L, s i * binomSlot (s i - 1) L (Bf i φ) (u i) (p i) *
          ∏ j ∈ univ.erase i, binomSlot (s j) L (Bf j φ) (u j) (p j) := by
  rw [(hasFDerivAt_binomProdRem_phi s L Bf u hBd hB hBu).fderiv]
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun p _ => ?_
  ring

/-- **Angle-derivative bound.** For base points `Bf j φ ∈ [b_min_j, b_max_j]`, `|u_j| ≤ r < b_min_j`
and `|∂_a Bf j φ| ≤ β_j`:
`|∂_{φ_a} binomProdRem s L (Bf · φ) u|`
`  ≤ Σ_i β_i · tailSum (update G i (|s_i| · slotMaj (s_i - 1) …)) L`
with `G = boxMaj s L bmin bmax r`. -/
theorem abs_fderiv_binomProdRem_phi_le_box (s : ι → ℝ) (L : ℕ) (Bf : ι → (Fin 2 → ℝ) → ℝ)
    {bmin bmax u β : ι → ℝ} {r : ℝ} {φ : Fin 2 → ℝ} (hBd : ∀ j, DifferentiableAt ℝ (Bf j) φ)
    (hr : ∀ j, r < bmin j) (h1 : ∀ j, bmin j ≤ Bf j φ) (h2 : ∀ j, Bf j φ ≤ bmax j)
    (hu : ∀ j, |u j| ≤ r) (a : Fin 2) (hβ : ∀ j, |fderiv ℝ (Bf j) φ (Pi.single a 1)| ≤ β j) :
    |fderiv ℝ (fun φ => binomProdRem s L (fun j => Bf j φ) u) φ (Pi.single a 1)| ≤
      ∑ i, β i * tailSum (Function.update (boxMaj s L bmin bmax r) i
        (fun m => |s i| * slotMaj (s i - 1) L (bmin i) (bmax i) r m)) L := by
  have hB : ∀ j, 0 < Bf j φ := fun j => by linarith [hr j, h1 j, hu j, abs_nonneg (u j)]
  have hBu : ∀ j, 0 < Bf j φ + u j := fun j => by
    linarith [hr j, h1 j, hu j, neg_abs_le (u j)]
  rw [fderiv_binomProdRem_phi s L Bf u hBd hB hBu a]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  have hS := abs_tail_update_le (L := L) (G := boxMaj s L bmin bmax r)
    (g := fun j m => binomSlot (s j) L (Bf j φ) (u j) m)
    (gi := fun m => s i * binomSlot (s i - 1) L (Bf i φ) (u i) m)
    (Gi := fun m => |s i| * slotMaj (s i - 1) L (bmin i) (bmax i) r m) i
    (fun j m _ => abs_binomSlot_le m (h1 j) (h2 j) (hr j) (hu j))
    (fun m _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_binomSlot_le m (h1 i) (h2 i) (hr i) (hu i))
        (abs_nonneg _))
  rw [abs_mul]
  exact mul_le_mul (hβ i) hS (abs_nonneg _) ((abs_nonneg _).trans (hβ i))

/-! ### The packaged tube statement -/

/-- The value bound of the remainder on the box. -/
noncomputable def remBound₀ (s : ι → ℝ) (L : ℕ) (bmin bmax : ι → ℝ) (r : ℝ) : ℝ :=
  tailSum (boxMaj s L bmin bmax r) L

/-- The bound of the `u_i`-derivative of the remainder on the box. -/
noncomputable def remBoundU (s : ι → ℝ) (L : ℕ) (bmin bmax : ι → ℝ) (r : ℝ) (i : ι) : ℝ :=
  tailSum (Function.update (boxMaj s L bmin bmax r) i (slotMajDu (s i) L (bmin i) (bmax i) r)) L

/-- The bound of the `φ_a`-derivative of the remainder on the box, given `|∂_a B_i| ≤ β_i`. -/
noncomputable def remBoundPhi (s : ι → ℝ) (L : ℕ) (bmin bmax : ι → ℝ) (r : ℝ) (β : ι → ℝ) : ℝ :=
  ∑ i, β i * tailSum (Function.update (boxMaj s L bmin bmax r) i
    (fun m => |s i| * slotMaj (s i - 1) L (bmin i) (bmax i) r m)) L

/-- **Binomial products on the tube.** Let `Bf j : (Fin 2 → ℝ) → ℝ` be differentiable with
`b_min_j ≤ Bf j φ ≤ b_max_j` and `|∂_a Bf j φ| ≤ β_j` everywhere, and `r < b_min_j`. Then for every
`φ` and every `u` with `|u_j| ≤ r`, `Π_j (Bf j φ + u_j)^{s_j}` is its truncation at total degree
`≤ L` plus a remainder which is differentiable in `u` and in `φ`, with
`|R| ≤ remBound₀`, `|∂_{u_i} R| ≤ remBoundU i`, `|∂_{φ_a} R| ≤ remBoundPhi`. -/
theorem binomProd_tube (s : ι → ℝ) (L : ℕ) (Bf : ι → (Fin 2 → ℝ) → ℝ) {bmin bmax β : ι → ℝ}
    {r : ℝ} (hBd : ∀ j, Differentiable ℝ (Bf j)) (hr : ∀ j, r < bmin j)
    (h1 : ∀ j φ, bmin j ≤ Bf j φ) (h2 : ∀ j φ, Bf j φ ≤ bmax j)
    (hβ : ∀ j φ a, |fderiv ℝ (Bf j) φ (Pi.single a 1)| ≤ β j)
    (φ : Fin 2 → ℝ) (u : ι → ℝ) (hu : ∀ j, |u j| ≤ r) :
    binomProd s (fun j => Bf j φ) u =
        binomTrunc s L (fun j => Bf j φ) u + binomProdRem s L (fun j => Bf j φ) u ∧
      |binomProdRem s L (fun j => Bf j φ) u| ≤ remBound₀ s L bmin bmax r ∧
      DifferentiableAt ℝ (fun v => binomProdRem s L (fun j => Bf j φ) v) u ∧
      (∀ i, |fderiv ℝ (fun v => binomProdRem s L (fun j => Bf j φ) v) u (Pi.single i 1)| ≤
        remBoundU s L bmin bmax r i) ∧
      DifferentiableAt ℝ (fun φ => binomProdRem s L (fun j => Bf j φ) u) φ ∧
      (∀ a, |fderiv ℝ (fun φ => binomProdRem s L (fun j => Bf j φ) u) φ (Pi.single a 1)| ≤
        remBoundPhi s L bmin bmax r β) := by
  have hB : ∀ j, 0 < Bf j φ := fun j => by linarith [hr j, h1 j φ, hu j, abs_nonneg (u j)]
  have hBu : ∀ j, 0 < Bf j φ + u j := fun j => by
    linarith [hr j, h1 j φ, hu j, neg_abs_le (u j)]
  refine ⟨by rw [binomProdRem]; ring,
    abs_binomProdRem_le_box s L hr (fun j => h1 j φ) (fun j => h2 j φ) hu,
    differentiableAt_binomProdRem_u s L _ u hBu,
    fun i => abs_fderiv_binomProdRem_u_le_box s L hr (fun j => h1 j φ) (fun j => h2 j φ) hu i,
    differentiableAt_binomProdRem_phi s L Bf u (fun j => hBd j φ) hB hBu,
    fun a => abs_fderiv_binomProdRem_phi_le_box s L Bf (fun j => hBd j φ) hr (fun j => h1 j φ)
      (fun j => h2 j φ) hu a fun j => hβ j φ a⟩

end KAM.EffectiveStability.Tube

end
