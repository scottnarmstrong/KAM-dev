/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakMeasure.PowerLaw
public import KAM.Planetary.WeakMeasure.Stability
public import KAM.Planetary.WeakKAM.Admissible
public import KAM.Planetary.WeakKAM.FiniteDivisor

/-! # P11B finite measure: bridge to the P11A weak-measure interface

Dictionary between the selection carriers (`selectionLength`, `selectionDG`, `selectionThick`,
`SelectionData`) and the P11A weak-measure interface (`p11euclid`, `p11dg`, `p11thick`,
`P11Patch`, `P11DioHyp`), used by `finite_measure`:

* `selectionPatch` is the patch `K ⊂ V` with `V` the real points of the `2ϑ` action collar;
* `selectionThick` is compact and `selectionM₀` bounds the jets of the frequency map there;
* `selectionDioHyp` packages the hypotheses `D1`-`D3` of `diophantine-measure` for a family of
  mode-dependent smooth frequency maps that stays `θ_max`-close to `ω`.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology Pointwise
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ}

theorem selectionLength_eq_p11euclid (x : SelectionR n) : selectionLength x = p11euclid x := by
  unfold selectionLength p11euclid KAM.Nekhoroshev.euclid
  simp [Real.norm_eq_abs, sq_abs]

theorem selectionLength_fun_eq : (selectionLength : SelectionR n → ℝ) = p11euclid :=
  funext selectionLength_eq_p11euclid

theorem continuous_selectionReal : Continuous (selectionReal : SelectionR n → SelectionC n) :=
  (selectionRealLI n).continuous

/-- The real points of the `2ϑ` action collar. -/
def selectionV (d : SelectionData n) : Set (SelectionR n) :=
  {y | selectionReal y ∈ actionNbhd d.K (2 * d.ϑ)}

theorem isOpen_selectionV (d : SelectionData n) : IsOpen (selectionV d) :=
  (p11_isOpen_actionNbhd d.K (2 * d.ϑ)).preimage continuous_selectionReal

theorem selectionThick_eq_p11thick (K : Set (SelectionR n)) (v : ℝ) :
    selectionThick K v = p11thick K v := by
  unfold selectionThick p11thick
  simp only [selectionLength_fun_eq]

theorem selectionThick_subset_V (d : SelectionData n) : selectionThick d.K d.ϑ ⊆ selectionV d := by
  rintro y ⟨x, hx, hxy⟩
  refine ⟨x, hx, ?_⟩
  have h1 : selectionReal y - (fun i => (x i : ℂ)) = selectionReal (y - x) := by
    funext i; simp [selectionReal]
  rw [h1, norm_selectionReal]
  have := d.theta_pos
  exact lt_of_le_of_lt (norm_le_selectionLength _ |>.trans hxy) (by linarith)

theorem K_subset_selectionThick (K : Set (SelectionR n)) {v : ℝ} (hv : 0 ≤ v) :
    K ⊆ selectionThick K v := fun x hx => ⟨x, hx, by simpa [selectionLength] using hv⟩

/-- The patch `K ⊂ V` of the selection data, with thickness `ϑ`. -/
def selectionPatch (d : SelectionData n) : P11Patch n where
  K := d.K
  V := selectionV d
  v := d.ϑ
  n_pos := d.n_pos
  nonempty := nonempty_of_measure_ne_zero d.positive_measure.ne'
  compact := d.compact
  openV := isOpen_selectionV d
  diameter_pos := selectionAdm_diam_pos d
  v_pos := d.theta_pos
  thick_sub := by
    rw [← selectionThick_eq_p11thick]
    exact selectionThick_subset_V d

theorem isCompact_selectionThick (K : Set (SelectionR n)) (hK : IsCompact K) (v : ℝ) :
    IsCompact (selectionThick K v) := by
  have hB : IsCompact {z : SelectionR n | selectionLength z ≤ v} := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · simp only [selectionLength_fun_eq]
      exact isClosed_le p11euclid_continuous continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : SelectionR n)) (r := v)).subset fun a ha => ?_
      rw [mem_closedBall_zero_iff]
      exact (norm_le_selectionLength a).trans ha
  have : selectionThick K v = K + {z : SelectionR n | selectionLength z ≤ v} := by
    ext x
    simp only [selectionThick, Set.mem_add, mem_ofPred_eq]
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨y, hy, x - y, h, by abel⟩
    · rintro ⟨y, hy, z, hz, rfl⟩
      exact ⟨y, hy, by simpa using hz⟩
  rw [this]
  exact hK.add hB

theorem p11dg_eq_selectionDGVector (f : SelectionR n → SelectionR n) (j : ℕ) (y : SelectionR n) :
    p11dg f j y = selectionDGVector j f y := by
  unfold p11dg selectionDGVector
  simp only [selectionLength_fun_eq]

theorem p11dg_scalar_eq_selectionDG {j : ℕ} {y : SelectionR n}
    (g : SelectionR n → ℝ) (hg : ContDiffAt ℝ j g y) :
    p11dg (fun x => (fun _ : Fin 1 => g x)) j y = selectionDG j g y := by
  unfold p11dg selectionDG
  simp only [selectionLength_fun_eq]
  congr 1
  ext v
  simp only [mem_ofPred_eq]
  refine exists_congr fun a => and_congr_right fun _ => ?_
  rw [p11euclid_iteratedFDeriv_scalar hg]

end KAM.Planetary
