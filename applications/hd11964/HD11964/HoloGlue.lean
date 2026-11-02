/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.HoloExt

/-!
# HD 11964: the consumer glue of the complex extension (HD11964-HOLO-FIX)

The two glue lemmas AUDIT-HD11964-HOLO-1 recommended (R1, R2):

* `noCollisionOn_of_enclosure` (R2): (1b) on any strip `stripA ρ` with any Kepler strips `y`,
  in the exact form of the named premise `NoCollisionOn y ρ w`, from a certified enclosure
  `‖d² − D‖ ≤ r < Re D` (the layer's data). It generalises `noCollision_of_enclosure`
  (`rhoHolo`, `yHolo` only) to the per-slab strips `rhoHoloA`/`yHoloA` and `rhoHoloB`/`yHoloB`.
* `AffineCell.etaOk`, `fitPlan_etaOk`, `abs_eta_le_of_mem_toSet`, `repSet_subset_holoDomHD`
  (R1): the representatives of the cover lie in `holoDomHD`. The `η_c` axis of every cell of
  `fitPlan` is decided within `1/500`. This is the auditor's probe (`AuditCheck.lean`), adopted.
-/

@[expose] public noncomputable section

open Set KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.Application.LambdaDrift
open scoped Real

namespace HD11964.Cover

/-! ### (1b) on any strip from an enclosure (R2) -/

/-- **(1b) on any strip from a certified enclosure of `d²`** (the layer's data): if
`‖d² − D‖ ≤ r < Re D` on `stripA ρ`, then the named premise `NoCollisionOn y ρ w` holds. -/
theorem noCollisionOn_of_enclosure {y ρ : Fin 2 → ℝ} {w : Phase (2 + 2)}
    {D : (Fin 2 → ℂ) → ℂ} {r : (Fin 2 → ℂ) → ℝ}
    (hD : ∀ θ ∈ stripA ρ, ‖distSqC y w θ - D θ‖ ≤ r θ)
    (hr : ∀ θ ∈ stripA ρ, r θ < (D θ).re) : NoCollisionOn y ρ w := by
  intro θ hθ
  have h1 := (Complex.abs_re_le_norm _).trans (hD θ hθ)
  rw [Complex.sub_re, abs_le] at h1
  linarith [hr θ hθ, h1.1]

/-! ### The representatives lie in `holoDomHD` (R1) -/

/-- Decidable: the cell has `|c₃| + |h₃| ≤ 1/500` (the `η_c` axis). -/
def AffineCell.etaOk (k : AffineCell) : Bool := decide (|k.c 3| + |k.h 3| ≤ 1 / 500)

/-- The decided check on `fitPlan`: every cell has `|η_c| ≤ 1/500`. -/
theorem fitPlan_etaOk : fitPlan.cells.all AffineCell.etaOk = true := by decide +kernel

theorem abs_eta_le_of_mem_toSet {k : AffineCell} {w : Phase (2 + 2)} (hw : w ∈ k.toSet) :
    |slow w.2 0| ≤ |((k.c 3 : ℚ) : ℝ)| + |((k.h 3 : ℚ) : ℝ)| := by
  obtain ⟨u, hu, he⟩ := hw
  have h3 := congrFun he 3
  simp only [cellCoord, AffineCell.map] at h3
  simp only [Matrix.cons_val, Fin.isValue] at h3
  rw [h3]
  calc |((k.c 3 : ℚ) : ℝ) + ((k.h 3 : ℚ) : ℝ) * u 3| ≤
        |((k.c 3 : ℚ) : ℝ)| + |((k.h 3 : ℚ) : ℝ)| * |u 3| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ |((k.c 3 : ℚ) : ℝ)| + |((k.h 3 : ℚ) : ℝ)| * 1 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (hu 3) (abs_nonneg _))
    _ = _ := by ring

/-- **The representatives of the cover lie in `holoDomHD`** (the consumer's glue: every (1a),
(1c) and (1d) theorem assumes `w ∈ holoDomHD`). -/
theorem repSet_subset_holoDomHD : repSet fitPlan.cells (1 / 500) ⊆ holoDomHD := by
  rintro w ⟨hR, k, hk, hw⟩
  refine ⟨hR, ?_⟩
  have h := List.all_eq_true.1 fitPlan_etaOk k hk
  have hq : |k.c 3| + |k.h 3| ≤ 1 / 500 := of_decide_eq_true h
  have hq' : ((|k.c 3| + |k.h 3| : ℚ) : ℝ) ≤ ((1 / 500 : ℚ) : ℝ) := by exact_mod_cast hq
  push_cast at hq'
  exact (abs_eta_le_of_mem_toSet hw).trans hq'

end HD11964.Cover

end
