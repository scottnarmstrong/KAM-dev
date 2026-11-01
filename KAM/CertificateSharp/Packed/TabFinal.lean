/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.TorsSound

/-!
# The averaged torsion test on tables

`tabFinal n cfg P C R S σ`: the landed averaged test (`avgBoundsOk` with the landed `avgInvRows`)
for exact centres `C i j` (complex rationals) and radii `R i j` (rationals) of an
`(n+1) × (n+1)` matrix, the defect `I - S C` computed exactly from the decoded witness.
`tabFinal_sound`: if every entry of a matrix `A` is within `R` of `C`, a passing test gives the
landed conclusion (`IsUnit A.det`, row sums of `A⁻¹` below `σ`). The tables are small, so the test
is cheap; the entries are checked elsewhere (one process per entry).
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith
open scoped Matrix Matrix.Norms.Operator

section Defs

variable {α : Type} [CertArith α] (n : ℕ) (cfg : ModelConfig α) (P : ℕ)

/-- The exact value of a witness entry at mantissa scale `P` (`(0, 0)` if it does not decode). -/
def tabSq (S : List (List (CC α))) (i l : ℕ) : ℚ × ℚ :=
  match certMantPair cfg.toMant P (ccEntry S i l) with
  | some z => ((z.1 : ℚ) / 2 ^ P, (z.2 : ℚ) / 2 ^ P)
  | none => (0, 0)

/-- Every witness entry decodes. -/
def tabSOk (S : List (List (CC α))) : Bool :=
  (List.range (n + 1)).all fun i => (List.range (n + 1)).all fun l =>
    (certMantPair cfg.toMant P (ccEntry S i l)).isSome

/-- The entry `(i, j)` of `I - S C` (exact). -/
def tabDef (C : ℕ → ℕ → ℚ × ℚ) (S : List (List (CC α))) (i j : ℕ) : ℚ × ℚ :=
  ((if i = j then 1 else 0) - ∑ l ∈ Finset.range (n + 1),
      ((tabSq cfg P S i l).1 * (C l j).1 - (tabSq cfg P S i l).2 * (C l j).2),
    -∑ l ∈ Finset.range (n + 1),
      ((tabSq cfg P S i l).1 * (C l j).2 + (tabSq cfg P S i l).2 * (C l j).1))

/-- **The final test on tables.** -/
def tabFinal (C : ℕ → ℕ → ℚ × ℚ) (R : ℕ → ℕ → ℚ) (S : List (List (CC α))) (σ : ℚ) : Bool :=
  listShapeOk (n + 1) S && tabSOk n cfg P S &&
    avgBoundsOk
      (List.ofFn fun i : Fin (n + 1) =>
        (ofRatUp (∑ j ∈ Finset.range (n + 1), qAbs1 (tabDef n cfg P C S i.val j)) : α))
      (avgInvRows n S)
      (List.ofFn fun i : Fin (n + 1) => (ofRatUp (∑ j ∈ Finset.range (n + 1), R i.val j) : α)) σ

end Defs

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}

omit [LawfulCertArith α] in
theorem tabDef_eq {cfg : ModelConfig α} {P : ℕ} (C : ℕ → ℕ → ℚ × ℚ) (S : List (List (CC α)))
    (i j : ℕ) :
    qC (tabDef n cfg P C S i j) = (if i = j then (1 : ℂ) else 0) -
      ∑ l ∈ Finset.range (n + 1), qC (tabSq cfg P S i l) * qC (C l j) := by
  have hI : ∀ x y u v : ℂ, (x + Complex.I * y) * (u + Complex.I * v) =
      (x * u - y * v) + Complex.I * (x * v + y * u) := by
    intro x y u v
    ring_nf
    rw [Complex.I_sq]
    ring
  unfold tabDef qC
  simp only [hI, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  push_cast
  split_ifs <;> push_cast <;> ring

theorem tab_ccEntry_toC_eq {cfg : ModelConfig α} {P : ℕ} {S : List (List (CC α))}
    (hS : tabSOk n cfg P S = true) {i l : ℕ} (hi : i < n + 1) (hl : l < n + 1) :
    (ccEntry S i l).toC = qC (tabSq cfg P S i l) := by
  simp only [tabSOk, List.all_eq_true, List.mem_range] at hS
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (hS i hi l hl)
  rw [certMantPair_sound hz]
  unfold tabSq qC
  rw [hz]
  push_cast
  ring

/-- **The final test on tables**: the landed averaged conclusion for any bordered matrix `A`
whose entries are within the radius table of the centre table. -/
theorem tabFinal_sound {cfg : ModelConfig α} {P : ℕ} {C : ℕ → ℕ → ℚ × ℚ} {R : ℕ → ℕ → ℚ}
    {S : List (List (CC α))} {σ : ℚ} {A : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ}
    (hent : ∀ x y, ‖A x y - qC (C (torsionIdx n x) (torsionIdx n y))‖ ≤
      (R (torsionIdx n x) (torsionIdx n y) : ℝ))
    (h : tabFinal n cfg P C R S σ = true) :
    IsUnit A.det ∧ ∀ i, ∑ j, ‖A⁻¹ i j‖ ≤ σ := by
  simp only [tabFinal, Bool.and_eq_true] at h
  obtain ⟨⟨-, hSok⟩, hb⟩ := h
  obtain ⟨hd, hr, hr0, hbr, hδ1, hδ0, hfin⟩ := avgBoundsOk_spec hb
  set a := maxCandidate (List.ofFn fun i : Fin (n + 1) =>
    (ofRatUp (∑ j ∈ Finset.range (n + 1), qAbs1 (tabDef n cfg P C S i.val j)) : α))
  set b := maxCandidate (avgInvRows n S)
  set r := maxCandidate (List.ofFn fun i : Fin (n + 1) =>
    (ofRatUp (∑ j ∈ Finset.range (n + 1), R i.val j) : α))
  set ι := torsionIdx n
  let Cm : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ := fun x y => qC (C (ι x) (ι y))
  let Sm : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ := fun x y => (ccEntry S (ι x) (ι y)).toC
  have hrow : ∀ x : Fin n ⊕ Unit, ∃ i : Fin (n + 1), i.val = ι x :=
    fun x => ⟨⟨ι x, torsionIdx_lt n x⟩, rfl⟩
  -- the radius matrix
  have hR : ‖A - Cm‖ ≤ val r := by
    rw [norm_le_iff_forall_rowSum hr0]
    intro x
    obtain ⟨i, hi⟩ := hrow x
    have hrw := hr _ ((List.mem_ofFn' _ _).mpr ⟨i, rfl⟩)
    refine le_trans ?_ ((LawfulCertArith.ofRatUp_ge _).trans hrw)
    rw [hi]
    push_cast
    rw [Finset.sum_range (fun j => ((R (ι x) j : ℚ) : ℝ)),
      ← sum_torsionIdx n (fun j => ((R (ι x) j : ℚ) : ℝ))]
    exact Finset.sum_le_sum fun y _ => by rw [Matrix.sub_apply]; exact hent x y
  -- the witness
  have hb0 : 0 ≤ val b := by
    refine le_trans ?_ (hbr _ ((List.mem_ofFn' _ _).mpr ⟨0, rfl⟩))
    exact sumUp_nonneg (fun _ => CC.normUp_nonneg _) _
  have hS : ‖Sm‖ ≤ val b := by
    rw [norm_le_iff_forall_rowSum hb0]
    intro x
    obtain ⟨i, hi⟩ := hrow x
    have hrw := hbr _ ((List.mem_ofFn' _ _).mpr ⟨i, rfl⟩)
    refine le_trans ?_ ((sumUp_ge _ _).trans hrw)
    rw [← Fin.sum_univ_def, hi]
    rw [← sum_torsionIdx n (fun j => val (ccEntry S (ι x) j).normUp)]
    exact Finset.sum_le_sum fun y _ => CC.norm_le_normUp _
  -- the centre defect, exact
  have hSm : ∀ x l, Sm x l = qC (tabSq cfg P S (ι x) (ι l)) := fun x l =>
    tab_ccEntry_toC_eq hSok (torsionIdx_lt n x) (torsionIdx_lt n l)
  have ha0 : 0 ≤ val a := by
    refine le_trans ?_ (hd _ ((List.mem_ofFn' _ _).mpr ⟨0, rfl⟩))
    refine le_trans ?_ (LawfulCertArith.ofRatUp_ge _)
    push_cast
    exact Finset.sum_nonneg fun j _ => by unfold qAbs1; positivity
  have hDf : ‖1 - Sm * Cm‖ ≤ val a := by
    rw [norm_le_iff_forall_rowSum ha0]
    intro x
    obtain ⟨i, hi⟩ := hrow x
    have hrw := hd _ ((List.mem_ofFn' _ _).mpr ⟨i, rfl⟩)
    refine le_trans ?_ ((LawfulCertArith.ofRatUp_ge _).trans hrw)
    rw [hi]
    push_cast
    rw [Finset.sum_range (fun j => ((qAbs1 (tabDef n cfg P C S (ι x) j) : ℚ) : ℝ)),
      ← sum_torsionIdx n (fun j => ((qAbs1 (tabDef n cfg P C S (ι x) j) : ℚ) : ℝ))]
    refine Finset.sum_le_sum fun y _ => ?_
    have he : (1 - Sm * Cm) x y = qC (tabDef n cfg P C S (ι x) (ι y)) := by
      rw [tabDef_eq, Finset.sum_range (fun l => qC (tabSq cfg P S (ι x) l) * qC (C l (ι y))),
        ← sum_torsionIdx n (fun l => qC (tabSq cfg P S (ι x) l) * qC (C l (ι y))),
        Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply]
      congr 1
      · by_cases hxy : x = y
        · simp [hxy]
        · have hne : ι x ≠ ι y := (torsionIdx_injective n).ne hxy
          simp [hxy, hne]
      · exact Finset.sum_congr rfl fun l _ => by rw [hSm]
    rw [he]
    exact norm_qC_le _
  -- the defect of `S` against `A`
  have hE : ‖1 - Sm * A‖ ≤ val (upAdd a (upMul b r)) := by
    have e1 : 1 - Sm * A = (1 - Sm * Cm) + Sm * (Cm - A) := by
      rw [Matrix.mul_sub]
      abel
    have hm := LawfulCertArith.upMul_ge b r hb0 hr0
    have hu := LawfulCertArith.upAdd_ge a (upMul b r)
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖Sm * (Cm - A)‖ ≤ val b * val r := by
      refine (Matrix.linfty_opNorm_mul _ _).trans ?_
      rw [norm_sub_rev]
      exact mul_le_mul hS hR (norm_nonneg _) hb0
    linarith
  obtain ⟨hU, hInv, -⟩ := matrix_inv_of_approx_inverse hE hδ1 hS
  refine ⟨hU, fun i => (rowSum_le_norm _ i).trans (hInv.trans ?_)⟩
  rw [div_le_iff₀ (by linarith)]
  nlinarith

end Sound

end KAM.CertificateSharp.Packed
