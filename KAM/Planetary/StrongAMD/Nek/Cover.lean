/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.AnalyticDomain.Containment
public import KAM.Planetary.Exponential.Stopped

/-!
# The finite sharp cover of the action set

Source: `LP:MAIN L8 (244–271)` and `LP:MAIN L14 (468–500)` as
planned in `docs/tracks/LP/lp3/LP3-PLAN.md` §2.2–§2.3 (fixed data (F3)–(F7)), track LP,
non-frozen.

Everything here is chosen before the small parameter `μ`. From the shared-tube radius `r_g` and the
tube width `R` (of `exists_strongTube`):

* `nekWidth`, `nekEta`, `nekRho`: `rs = min (4 r_g) (R/4)`, `η = rs/4`, `ρ = rs/8`;
* `exists_isNekCover`: a finite set of centres `c_j ∈ 𝓛_δ` with `𝓛_δ ⊆ ⋃ ball c_j (η/2)`;
* cells `nekCellInner c = ball c η` (`G_j`), `nekCellOuter c = ball c (2η)` (`G′_j`) and
  `nekCellSlow c = slowBall n (B(c) − 5δ/16)` (`D_j`), with openness, convexity and the collar
  `nekCell_collar`;
* `nekCell_threshold_bound`: `|B(I⁰) − B(c_j)| ≤ δ/16`;
* `nekCell_containment`: `partialComplexDomain G′_j D_j ρ ⊆ complexTube (strongCore) (R/2)`;
* `exists_nekSlowGap`: `ε_D > 0` for the slow erosion (`stopped_slow_erosion`);
* `IsNekCover.mem_innerCore`: the fast erosion premise of the frozen theorem.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary Set Metric

variable {n : ℕ}

/-! ### Widths (F3) -/

/-- `rs := min (4 r_g) (R/4)` (`LP3-PLAN` (F3)). -/
def nekWidth (rg R : ℝ) : ℝ := min (4 * rg) (R / 4)

/-- `η := rs/4`, the radius of the cells `G_j`. -/
def nekEta (rg R : ℝ) : ℝ := nekWidth rg R / 4

/-- `ρ := rs/8`, the imaginary width. -/
def nekRho (rg R : ℝ) : ℝ := nekWidth rg R / 8

theorem nekWidth_pos {rg R : ℝ} (hrg : 0 < rg) (hR : 0 < R) : 0 < nekWidth rg R :=
  lt_min (by linarith) (by linarith)

theorem nekWidth_le_four_mul (rg R : ℝ) : nekWidth rg R ≤ 4 * rg := min_le_left _ _

theorem nekWidth_lt_half {rg R : ℝ} (hR : 0 < R) : nekWidth rg R < R / 2 :=
  (min_le_right _ _).trans_lt (by linarith)

theorem nekEta_pos {rg R : ℝ} (hrg : 0 < rg) (hR : 0 < R) : 0 < nekEta rg R := by
  have := nekWidth_pos hrg hR
  unfold nekEta
  linarith

theorem nekRho_pos {rg R : ℝ} (hrg : 0 < rg) (hR : 0 < R) : 0 < nekRho rg R := by
  have := nekWidth_pos hrg hR
  unfold nekRho
  linarith

theorem nekRho_le_eta {rg R : ℝ} (hrg : 0 < rg) (hR : 0 < R) : nekRho rg R ≤ nekEta rg R := by
  have := nekWidth_pos hrg hR
  unfold nekRho nekEta
  linarith

theorem four_mul_nekEta (rg R : ℝ) : 4 * nekEta rg R = nekWidth rg R := by
  unfold nekEta
  ring

/-- `η ≤ r_g`. -/
theorem nekEta_le {rg R : ℝ} : nekEta rg R ≤ rg := by
  have := nekWidth_le_four_mul rg R
  unfold nekEta
  linarith

/-! ### Cells (F5) -/

/-- `G_j = ball (c_j, η)`. -/
def nekCellInner (rg R : ℝ) (c : Fin n → ℝ) : Set (Fin n → ℝ) := ball c (nekEta rg R)

/-- `G′_j = ball (c_j, 2η)`. -/
def nekCellOuter (rg R : ℝ) (c : Fin n → ℝ) : Set (Fin n → ℝ) := ball c (2 * nekEta rg R)

/-- The local sharp slow level `A_j = B(c_j) − 5δ/16`. -/
def nekCellLevel (ν : Fin n → ℝ) (δ : ℝ) (c : Fin n → ℝ) : ℝ :=
  strongThreshold ν c - 5 * δ / 16

/-- `D_j = {y : ∑ (y₁² + y₂²)/2 < A_j}`. -/
def nekCellSlow (ν : Fin n → ℝ) (δ : ℝ) (c : Fin n → ℝ) : Set (Phase n) :=
  slowBall n (nekCellLevel ν δ c)

theorem isOpen_nekCellInner (rg R : ℝ) (c : Fin n → ℝ) : IsOpen (nekCellInner rg R c) :=
  isOpen_ball

theorem convex_nekCellInner (rg R : ℝ) (c : Fin n → ℝ) : Convex ℝ (nekCellInner rg R c) :=
  convex_ball _ _

theorem isOpen_nekCellOuter (rg R : ℝ) (c : Fin n → ℝ) : IsOpen (nekCellOuter rg R c) :=
  isOpen_ball

theorem convex_nekCellOuter (rg R : ℝ) (c : Fin n → ℝ) : Convex ℝ (nekCellOuter rg R c) :=
  convex_ball _ _

theorem isOpen_nekCellSlow (ν : Fin n → ℝ) (δ : ℝ) (c : Fin n → ℝ) :
    IsOpen (nekCellSlow ν δ c) :=
  isOpen_slowBall n _

theorem nekCellInner_subset_outer (rg R : ℝ) (hrg : 0 < rg) (hR : 0 < R) (c : Fin n → ℝ) :
    nekCellInner rg R c ⊆ nekCellOuter rg R c :=
  ball_subset_ball (by linarith [nekEta_pos hrg hR])

/-- The collar: `I ∈ G_j → closedBall I ρ ⊆ G′_j`. -/
theorem nekCell_collar {rg R : ℝ} (hrg : 0 < rg) (hR : 0 < R) {c : Fin n → ℝ}
    {I : Fin n → ℝ} (hI : I ∈ nekCellInner rg R c) :
    closedBall I (nekRho rg R) ⊆ nekCellOuter rg R c := by
  intro x hx
  rw [mem_closedBall] at hx
  rw [nekCellInner, mem_ball] at hI
  rw [nekCellOuter, mem_ball]
  have := dist_triangle x I c
  have := nekRho_le_eta hrg hR
  linarith

theorem nekCell_level_le (ν : Fin n → ℝ) {δ : ℝ} (hδ : 0 < δ) (c : Fin n → ℝ) :
    nekCellLevel ν δ c ≤ strongThreshold ν c - δ / 4 := by
  unfold nekCellLevel
  linarith

/-! ### Finite cover (F4) -/

/-- A finite cover of `𝓛_δ` by centres in `𝓛_δ` and balls of radius `η/2`. -/
structure IsNekCover (ν : Fin n → ℝ) (L : Set (Fin n → ℝ)) (δ rg R : ℝ)
    (s : Finset (Fin n → ℝ)) : Prop where
  mem_levelSet : ∀ c ∈ s, c ∈ strongLevelSet ν L δ
  covers : ∀ I0 ∈ strongLevelSet ν L δ, ∃ c ∈ s, ‖I0 - c‖ < nekEta rg R / 2

/-- (F4) A finite sharp cover exists (compactness of `𝓛_δ`). -/
theorem exists_isNekCover {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) {L : Set (Fin n → ℝ)}
    (hL : IsCompact L) (hLch : L ⊆ chamber ν) {δ rg R : ℝ} (hrg : 0 < rg) (hR : 0 < R) :
    ∃ s : Finset (Fin n → ℝ), IsNekCover ν L δ rg R s := by
  have hc := isCompact_strongLevelSet hν hn hL hLch δ
  have he : 0 < nekEta rg R / 2 := by linarith [nekEta_pos hrg hR]
  obtain ⟨t, hts, htf, hcov⟩ := finite_cover_balls_of_compact hc he
  refine ⟨htf.toFinset, fun c hcm => hts (htf.mem_toFinset.1 hcm), fun I0 hI0 => ?_⟩
  have := hcov hI0
  simp only [mem_iUnion, mem_ball, exists_prop] at this
  obtain ⟨c, hct, hd⟩ := this
  exact ⟨c, htf.mem_toFinset.2 hct, by rwa [← dist_eq_norm]⟩

/-! ### Fast erosion -/

section Fast

variable {rg R : ℝ} {c I0 : Fin n → ℝ}

/-- Stopped fast actions stay in `G_j`: if `‖I0 − c‖ < η/2`, `r ≤ η/4` and `‖x − I0‖ ≤ r` then
`x ∈ G_j`. -/
theorem nekCell_mem_of_close {r : ℝ} (hI : ‖I0 - c‖ < nekEta rg R / 2) (hr : r ≤ nekEta rg R / 4)
    {x : Fin n → ℝ} (hx : ‖x - I0‖ ≤ r) (hη : 0 < nekEta rg R) : x ∈ nekCellInner rg R c := by
  rw [nekCellInner, mem_ball, dist_eq_norm]
  have h2 : ‖x - c‖ ≤ ‖x - I0‖ + ‖I0 - c‖ := by
    have := norm_add_le (x - I0) (I0 - c)
    simpa using this
  linarith

/-- The fast erosion premise: `I0 ∈ innerCore G_j r` for `r ≤ η/4`. -/
theorem nekCell_mem_innerCore {r : ℝ} (hI : ‖I0 - c‖ < nekEta rg R / 2)
    (hr : r ≤ nekEta rg R / 4) (hη : 0 < nekEta rg R) (hr0 : 0 ≤ r) :
    I0 ∈ KAM.Nekhoroshev.innerCore (nekCellInner rg R c) r := by
  have hball : closedBall I0 r ⊆ nekCellInner rg R c := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    exact nekCell_mem_of_close hI hr hx hη
  exact ⟨hball (mem_closedBall_self hr0), hball⟩

/-- Every point of `𝓛_δ` lies in `innerCore G_j r` of some cell of the cover. -/
theorem IsNekCover.mem_innerCore {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ : ℝ}
    {s : Finset (Fin n → ℝ)} (hs : IsNekCover ν L δ rg R s) (hη : 0 < nekEta rg R)
    {I0 : Fin n → ℝ} (hI0 : I0 ∈ strongLevelSet ν L δ) {r : ℝ} (hr : r ≤ nekEta rg R / 4)
    (hr0 : 0 ≤ r) :
    ∃ c ∈ s, ‖I0 - c‖ < nekEta rg R / 2 ∧
      I0 ∈ KAM.Nekhoroshev.innerCore (nekCellInner rg R c) r := by
  obtain ⟨c, hcs, hd⟩ := hs.covers I0 hI0
  exact ⟨c, hcs, hd, nekCell_mem_innerCore hd hr hη hr0⟩

end Fast

/-! ### The threshold bound -/

/-- `|B(I⁰) − B(c)| ≤ δ/16` for `I⁰, c ∈ 𝓛_δ` with `‖I⁰ − c‖ ≤ 4 r_g`. -/
theorem nekCell_threshold_bound {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ rg : ℝ}
    (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hg : IsSharedTube ν L δ rg)
    {I0 c : Fin n → ℝ} (hI0 : I0 ∈ strongLevelSet ν L δ) (hc : c ∈ strongLevelSet ν L δ)
    (hd : ‖I0 - c‖ ≤ 4 * rg) :
    |strongThreshold ν I0 - strongThreshold ν c| ≤ δ / 16 :=
  (abs_strongThreshold_sub_le_modulus hν hn hg.compact hg.subset_chamber
    (self_subset_cthickening _ hI0) (self_subset_cthickening _ hc) hd).trans hg.modulus

/-- The cover form: `‖I⁰ − c‖ < η/2` suffices. -/
theorem nekCell_threshold_bound_of_close {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ rg R : ℝ}
    (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hg : IsSharedTube ν L δ rg)
    {I0 c : Fin n → ℝ} (hI0 : I0 ∈ strongLevelSet ν L δ) (hc : c ∈ strongLevelSet ν L δ)
    (hd : ‖I0 - c‖ < nekEta rg R / 2) :
    |strongThreshold ν I0 - strongThreshold ν c| ≤ δ / 16 :=
  nekCell_threshold_bound hν hn hg hI0 hc
    (hd.le.trans (by linarith [nekEta_le (rg := rg) (R := R), hg.pos]))

/-! ### Containment -/

theorem norm_sub_ofReal_re_eq (w : ℂ) : ‖w - ((w.re : ℝ) : ℂ)‖ = |w.im| := by
  have : w - ((w.re : ℝ) : ℂ) = (w.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- The cell's complex domain lies in the `R/2`-tube of the sharp core (`strongCore_containment`
with centre `c_j`). -/
theorem nekCell_containment {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ rg R : ℝ}
    (hrg : 0 < rg) (hR : 0 < R) (hδ : 0 < δ) {c : Fin n → ℝ} (hc : c ∈ strongLevelSet ν L δ) :
    KAM.Nekhoroshev.partialComplexDomain (nekCellOuter rg R c) (nekCellSlow ν δ c)
        (nekRho rg R) ⊆ complexTube (strongCore ν L δ rg) (R / 2) := by
  intro z hz
  obtain ⟨hf, hs, hz1, hz2⟩ := hz
  have hrs := nekWidth_pos hrg hR
  have h4 := four_mul_nekEta rg R
  have hρη := nekRho_le_eta hrg hR
  have hρpos := nekRho_pos hrg hR
  have hηpos := nekEta_pos hrg hR
  have hρ4 : nekRho rg R ≤ 4 * nekEta rg R := by linarith
  refine strongCore_containment (s := nekEta rg R) (b := nekEta rg R) (rs := nekWidth rg R)
    hrs (nekWidth_le_four_mul rg R) ?_ hc ?_ ?_ ?_
  · rw [h4, max_self, max_self]
    exact nekWidth_lt_half hR
  · rw [pi_norm_lt_iff hrs]
    intro i
    have hf' : ‖fast (fun j => (z.2 j).re) - c‖ < 2 * nekEta rg R := by
      have := hf
      rwa [nekCellOuter, mem_ball, dist_eq_norm] at this
    have h1 : |(z.2 (Fin.castAdd n i)).re - c i| < 2 * nekEta rg R := by
      have := norm_le_pi_norm (fast (fun j => (z.2 j).re) - c) i
      simp only [Pi.sub_apply, Real.norm_eq_abs, fast] at this
      exact lt_of_le_of_lt this hf'
    have h3 : |(z.2 (Fin.castAdd n i)).im| < nekRho rg R := hz2 _
    have h5 := Complex.norm_le_abs_re_add_abs_im (z.2 (Fin.castAdd n i) - ((c i : ℝ) : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
      sub_zero] at h5
    simp only [Pi.sub_apply]
    linarith
  · rw [h4, pi_norm_lt_iff hrs]
    intro i
    have h3 : |(z.1 (Fin.castAdd n i)).im| < nekRho rg R := hz1 _
    rw [Real.norm_eq_abs]
    linarith
  · refine ⟨(slow fun i => (z.1 i).re, slow fun i => (z.2 i).re), ?_, ?_, ?_⟩
    · have := hs
      simp only [nekCellSlow, slowBall, mem_ofPred_eq] at this
      have hle := nekCell_level_le ν hδ c
      simp only [secularBall, mem_ofPred_eq]
      linarith
    · rw [h4, pi_norm_lt_iff hrs]
      intro i
      have h3 : |(z.1 (Fin.natAdd n i)).im| < nekRho rg R := hz1 _
      simp only [Pi.sub_apply, slow]
      rw [norm_sub_ofReal_re_eq]
      linarith
    · rw [h4, pi_norm_lt_iff hrs]
      intro i
      have h3 : |(z.2 (Fin.natAdd n i)).im| < nekRho rg R := hz2 _
      simp only [Pi.sub_apply, slow]
      rw [norm_sub_ofReal_re_eq]
      linarith

/-! ### The slow erosion gap (F7) -/

/-- The per-cell gap `(√(2A_j) − √(2A′_j))/√(2n)` is positive (`A′_j = B(c_j) − 3δ/8`). -/
theorem nekCell_slowGap_pos {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ : ℝ} (hn : 2 ≤ n)
    (hδ : 0 < δ) {c : Fin n → ℝ} (hc : c ∈ strongLevelSet ν L δ) :
    0 < (Real.sqrt (2 * nekCellLevel ν δ c) - Real.sqrt (2 * (strongThreshold ν c - 3 * δ / 8))) /
      Real.sqrt (2 * n) := by
  have hB : δ ≤ strongThreshold ν c := hc.2
  have hn' : (0 : ℝ) < n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine div_pos (sub_pos.2 (Real.sqrt_lt_sqrt ?_ ?_)) (Real.sqrt_pos.2 (by positivity))
  · linarith
  · unfold nekCellLevel
    linarith

/-- (F7) `ε_D > 0`, uniform over a finite set of cells: for `ε < ε_D`,
`√(2A′_j) + √(2n) ε < √(2A_j)` for every centre `c_j ∈ s` (the hypothesis of
`stopped_slow_erosion`). -/
theorem exists_nekSlowGap {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ : ℝ} (hn : 2 ≤ n)
    (hδ : 0 < δ) (s : Finset (Fin n → ℝ)) (hs : ∀ c ∈ s, c ∈ strongLevelSet ν L δ) :
    ∃ εD : ℝ, 0 < εD ∧ ∀ c ∈ s, ∀ ε : ℝ, 0 ≤ ε → ε < εD →
      Real.sqrt (2 * (strongThreshold ν c - 3 * δ / 8)) + Real.sqrt (2 * n) * ε <
        Real.sqrt (2 * nekCellLevel ν δ c) := by
  classical
  have hn' : (0 : ℝ) < n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hsq : 0 < Real.sqrt (2 * n) := Real.sqrt_pos.2 (by positivity)
  set f : (Fin n → ℝ) → ℝ := fun c =>
    (Real.sqrt (2 * nekCellLevel ν δ c) - Real.sqrt (2 * (strongThreshold ν c - 3 * δ / 8))) /
      Real.sqrt (2 * n) with hf
  have key : ∃ εD : ℝ, 0 < εD ∧ ∀ c ∈ s, εD ≤ f c := by
    rcases s.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · refine ⟨s.inf' h f, (Finset.lt_inf'_iff h).2 fun c hc => nekCell_slowGap_pos hn hδ (hs c hc),
        fun c hc => Finset.inf'_le _ hc⟩
  obtain ⟨εD, hεD, hle⟩ := key
  refine ⟨εD, hεD, fun c hc ε hε0 hεlt => ?_⟩
  have h1 := hle c hc
  have h2 : ε < f c := lt_of_lt_of_le hεlt h1
  rw [hf] at h2
  simp only at h2
  rw [lt_div_iff₀ hsq] at h2
  linarith

end KAM.Planetary.StrongAMD

end
