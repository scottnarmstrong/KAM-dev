/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.NoCrossing

/-!
# The cover lemma for affine cells (HD11964-COVERLEMMA)

The order-2 cover of the region `R(d)` (HD11964-CELLS) by **affine cells** `x = c + M u`,
`‖u‖_∞ ≤ 1`, in the cell coordinates `x = (Λ_c, Λ_b, ξ_c, η_c, ξ_b, η_b)` (`cellCoord`), with
`M = diag (h₀, h₁, h₂, h₃) ⊕ Rot (a, b) · diag (h₄, h₅)` and an exact rational rotation
`a² + b² = 1` in the `(ξ_b, η_b)` plane (`AffineCell`; `toMx` is kamx-hd-layer's matrix form,
`cellMap c Mx`).

* `CoversReps cells d`: every rotation representative (`η_c = 0`, `ξ_c ≥ 0`) of `R(d)` lies in a
  cell of the list.
* `CoverPlan`, `CoverPlan.ok`: a plan (slabs in `ξ_c`; per slab one disc cell or two chains of
  wedges in `(ξ_b, η_b)`) and its decidable check. `coversReps_of_ok`: a checked plan covers.
* `existsRep`, `hRS_of_coversReps`: every state rotates to a representative, so the cover gives the
  hypothesis `hRS` of `bracket_bound_of_rotation` and `range_bound_of_rotation`.

Status: committed unbuilt (not imported by the package root) before the 2 November 05:00 reboot;
every declaration was checked in a scratch elaboration (`lake env lean`, exit 0, no proof
escape). It lands after the reboot with narrower imports (orchestrator ruling). The fitted plan
and its check are in `HD11964.CoverPlan`.
-/

@[expose] public noncomputable section

open Set KAM KAM.Planetary KAM.Application.LambdaDrift

namespace HD11964.Cover

/-! ### Affine cells -/

/-- The six cell coordinates `(Λ_c, Λ_b, ξ_c, η_c, ξ_b, η_b)` of a chart state, with
`ξ_i = slow w.1 i` and `η_i = slow w.2 i` (CP10's `(φ, q; I, p)` order, `assemble`). The angles
`fast w.1` are free: a cell contains every angle. -/
def cellCoord (w : Phase (2 + 2)) : Fin 6 → ℝ :=
  ![fast w.2 0, fast w.2 1, slow w.1 0, slow w.2 0, slow w.1 1, slow w.2 1]

/-- An affine cell with rational data: centre `c`, half-widths `h` (four axes, then radial and
tangential), and the frame `(a, b) = (cos φ, sin φ)` of the `(ξ_b, η_b)` plane. -/
structure AffineCell where
  /-- The centre, in `cellCoord` order. -/
  c : Fin 6 → ℚ
  /-- The half-widths: `Λ_c, Λ_b, ξ_c, η_c`, then radial and tangential. -/
  h : Fin 6 → ℚ
  /-- The frame's cosine. -/
  a : ℚ
  /-- The frame's sine. -/
  b : ℚ

namespace AffineCell

/-- The cell map `u ↦ c + M u`, `M = diag (h₀, h₁, h₂, h₃) ⊕ Rot (a, b) · diag (h₄, h₅)`. -/
def map (k : AffineCell) (u : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![k.c 0 + k.h 0 * u 0, k.c 1 + k.h 1 * u 1, k.c 2 + k.h 2 * u 2, k.c 3 + k.h 3 * u 3,
    k.c 4 + k.a * k.h 4 * u 4 - k.b * k.h 5 * u 5,
    k.c 5 + k.b * k.h 4 * u 4 + k.a * k.h 5 * u 5]

/-- The matrix of the cell map (kamx-hd-layer's `cellMap c Mx`, `PackedTF/Assembly.lean`):
`diag (h₀, h₁, h₂, h₃)` and the block `Rot (a, b) · diag (h₄, h₅)` on `(ξ_b, η_b)`. -/
def toMx (k : AffineCell) : Fin 6 → Fin 6 → ℚ :=
  ![![k.h 0, 0, 0, 0, 0, 0], ![0, k.h 1, 0, 0, 0, 0], ![0, 0, k.h 2, 0, 0, 0],
    ![0, 0, 0, k.h 3, 0, 0], ![0, 0, 0, 0, k.a * k.h 4, -k.b * k.h 5],
    ![0, 0, 0, 0, k.b * k.h 4, k.a * k.h 5]]

/-- The cell map in matrix form, `k.map u = c + toMx u` (over `ℝ`; kamx-hd-layer's `cellMap`
is its cast to `ℂ`). -/
theorem map_eq_cellMap (k : AffineCell) (u : Fin 6 → ℝ) :
    k.map u = fun i => (k.c i : ℝ) + ∑ j, (k.toMx i j : ℝ) * u j := by
  funext i
  fin_cases i <;> simp [map, toMx, Fin.sum_univ_six] <;> ring

/-- **The cell**: the chart states whose cell coordinates are `c + M u` with `‖u‖_∞ ≤ 1` (every
angle). The kernel's cell check bounds `F` on this set. -/
def toSet (k : AffineCell) : Set (Phase (2 + 2)) :=
  {w | ∃ u : Fin 6 → ℝ, (∀ j, |u j| ≤ 1) ∧ cellCoord w = k.map u}

/-- Rational well-formedness: positive half-widths and an exact rotation. -/
def wf (k : AffineCell) : Bool :=
  (List.finRange 6).all (fun j => decide (0 < k.h j)) && decide (k.a ^ 2 + k.b ^ 2 = 1)

/-- The radial coordinate `⟨p, e_r⟩`, `e_r = (a, b)`. -/
def rad (k : AffineCell) (p : Fin 2 → ℚ) : ℚ := k.a * p 0 + k.b * p 1

/-- The tangential coordinate `⟨p, e_t⟩`, `e_t = (-b, a)`. -/
def tng (k : AffineCell) (p : Fin 2 → ℚ) : ℚ := -k.b * p 0 + k.a * p 1

/-- The centre's `(ξ_b, η_b)` part. -/
def cb (k : AffineCell) : Fin 2 → ℚ := ![k.c 4, k.c 5]

/-- Membership in inequality form (the planned `mem_toSet_iff`, for `wf k`). -/
def MemIneq (k : AffineCell) (x : Fin 6 → ℝ) : Prop :=
  |x 0 - k.c 0| ≤ k.h 0 ∧ |x 1 - k.c 1| ≤ k.h 1 ∧ |x 2 - k.c 2| ≤ k.h 2 ∧
    |x 3 - k.c 3| ≤ k.h 3 ∧
    |k.a * (x 4 - k.c 4) + k.b * (x 5 - k.c 5)| ≤ k.h 4 ∧
    |-k.b * (x 4 - k.c 4) + k.a * (x 5 - k.c 5)| ≤ k.h 5

end AffineCell

/-! ### The cover statement -/

/-- **The cover statement** (the cell-format agreement): every rotation representative of `R(d)`
(`η_c = 0`, `ξ_c ≥ 0`) lies in some cell of the list. -/
def CoversReps (cells : List AffineCell) (d : ℝ) : Prop :=
  ∀ w ∈ region d, slow w.2 0 = 0 → 0 ≤ slow w.1 0 → ∃ k ∈ cells, w ∈ k.toSet

/-- The set `S` of the rotation lemmas: the representatives of `R(d)` inside the cells. -/
def repSet (cells : List AffineCell) (d : ℝ) : Set (Phase (2 + 2)) :=
  {w | w ∈ region d ∧ ∃ k ∈ cells, w ∈ k.toSet}

/-! ### Cover plans -/

/-- The rational box `[Λlo, Λhi]` and `Cbar` (`lamLo`, `lamHi`, `cBar` of `HD11964.Threshold`). -/
def lamLoQ : Fin 2 → ℚ := ![116621 / 2000000, 4454241 / 2500000]

/-- See `lamLoQ`. -/
def lamHiQ : Fin 2 → ℚ := ![292553 / 5000000, 3575393 / 2000000]

/-- See `lamLoQ`. -/
def cBarQ : ℚ := 1 / 100

/-- The planar cross product `v × p = v₀ p₁ - v₁ p₀`. -/
def crossQ (v p : Fin 2 → ℚ) : ℚ := v 0 * p 1 - v 1 * p 0

/-- A wedge: the cone from the ray `v` counterclockwise to the ray `w`, assigned to a cell, with a
slope bound `τ` of both rays in the cell frame. -/
structure Wedge where
  /-- The first ray. -/
  v : Fin 2 → ℚ
  /-- The second ray. -/
  w : Fin 2 → ℚ
  /-- The cell carrying the wedge. -/
  cell : AffineCell
  /-- `|⟨v, e_t⟩| ≤ τ ⟨v, e_r⟩` for both rays. -/
  τ : ℚ

/-- A slab `ξ_c ∈ [lo, hi]` with b's disc radius `R` (`R² ≥ 2 Cmax - lo²`), covered by one cell
(`disc`) or by two chains of wedges: `upper` from `(1, 0)` to `(-1, 0)`, `lower` from `(-1, 0)`
to `(1, 0)`. A wedge of the fan that straddles `(±1, 0)` appears in both chains. -/
structure Slab where
  /-- The lower end of the slab. -/
  lo : ℚ
  /-- The upper end of the slab. -/
  hi : ℚ
  /-- The radius of b's disc on the slab. -/
  R : ℚ
  /-- A single cell containing the whole disc, if any. -/
  disc : Option AffineCell
  /-- The chain of the upper half-plane `η_b ≥ 0`. -/
  upper : List Wedge
  /-- The chain of the lower half-plane `η_b < 0`. -/
  lower : List Wedge

/-- A cover plan: `d` and the slabs from `ξ_c = 0` up. -/
structure CoverPlan where
  /-- The drift `d` (`D.d`). -/
  d : ℚ
  /-- The slabs, consecutive, from `0`. -/
  slabs : List Slab

namespace CoverPlan

/-- `Cmax = Cbar + 2d`. -/
def cmax (P : CoverPlan) : ℚ := cBarQ + 2 * P.d

/-- The cells of the plan. -/
def cells (P : CoverPlan) : List AffineCell :=
  P.slabs.flatMap fun s => s.disc.toList ++ (s.upper ++ s.lower).map (·.cell)

/-- The non-b conditions of a cell on a slab: `Λ` covers `[Λlo - d, Λhi + d]`, `ξ_c` covers
`[lo, hi]`, `η_c = 0` is inside. -/
def axesOk (P : CoverPlan) (s : Slab) (k : AffineCell) : Bool :=
  k.wf && decide (k.c 0 - k.h 0 ≤ lamLoQ 0 - P.d) && decide (lamHiQ 0 + P.d ≤ k.c 0 + k.h 0) &&
    decide (k.c 1 - k.h 1 ≤ lamLoQ 1 - P.d) && decide (lamHiQ 1 + P.d ≤ k.c 1 + k.h 1) &&
    decide (k.c 2 - k.h 2 ≤ s.lo) && decide (s.hi ≤ k.c 2 + k.h 2) && decide (|k.c 3| ≤ k.h 3)

/-- A disc cell: the disc of radius `R` lies in the cell's `(ξ_b, η_b)` box. -/
def discOk (P : CoverPlan) (s : Slab) (k : AffineCell) : Bool :=
  P.axesOk s k && decide (s.R + |k.rad k.cb| ≤ k.h 4) && decide (s.R + |k.tng k.cb| ≤ k.h 5)

/-- A wedge: the cone `v → w` (less than a half-turn) intersected with the disc of radius `R`
lies in the cell's rotated box. -/
def wedgeOk (P : CoverPlan) (s : Slab) (x : Wedge) : Bool :=
  let k := x.cell
  P.axesOk s k && decide (0 < crossQ x.v x.w) && decide (0 ≤ x.τ) &&
    decide (0 ≤ k.rad x.v) && decide (0 ≤ k.rad x.w) &&
    decide (|k.tng x.v| ≤ x.τ * k.rad x.v) && decide (|k.tng x.w| ≤ x.τ * k.rad x.w) &&
    decide (k.rad k.cb - k.h 4 ≤ 0) && decide (s.R ≤ k.rad k.cb + k.h 4) &&
    decide (|k.tng k.cb| ≤ k.h 5) &&
    decide (x.τ ^ 2 * s.R ^ 2 ≤ (1 + x.τ ^ 2) * (k.h 5 - |k.tng k.cb|) ^ 2)

/-- A chain of wedges from the ray `start` to the ray `stop`, consecutive rays equal. -/
def chainOk (start stop : Fin 2 → ℚ) : List Wedge → Bool
  | [] => false
  | [x] => decide (x.v = start) && decide (x.w = stop)
  | x :: y :: rest => decide (x.v = start) && chainOk x.w stop (y :: rest)

/-- A slab: `0 ≤ lo ≤ hi`, `0 ≤ R`, `R² ≥ 2 Cmax - lo²`, and either a disc cell or two chains. -/
def slabOk (P : CoverPlan) (s : Slab) : Bool :=
  decide (0 ≤ s.lo) && decide (s.lo ≤ s.hi) && decide (0 ≤ s.R) &&
    decide (2 * P.cmax - s.lo ^ 2 ≤ s.R ^ 2) &&
    (match s.disc with
      | some k => P.discOk s k
      | none => chainOk ![1, 0] ![-1, 0] s.upper && chainOk ![-1, 0] ![1, 0] s.lower &&
          (s.upper ++ s.lower).all (P.wedgeOk s))

/-- Consecutive slabs from `ξ_c = 0` to `ξ_c ≥ √(2 Cmax)`. -/
def slabsChainOk (cm : ℚ) : ℚ → List Slab → Bool
  | _, [] => false
  | a, [s] => decide (s.lo = a) && decide (0 ≤ s.hi) && decide (2 * cm ≤ s.hi ^ 2)
  | a, s :: t :: rest => decide (s.lo = a) && slabsChainOk cm s.hi (t :: rest)

/-- **The decidable check of a cover plan** (to be run by `decide +kernel`). -/
def ok (P : CoverPlan) : Bool :=
  decide (0 < P.d) && slabsChainOk P.cmax 0 P.slabs && P.slabs.all P.slabOk

end CoverPlan

/-! ### The planned lemmas (statements only) -/

/-- **The planned theorem** `coversReps_of_ok`: a checked plan covers the representatives. -/
def CoverTheorem : Prop :=
  ∀ P : CoverPlan, P.ok = true → CoversReps P.cells (P.d : ℝ)

/-- Step 0 (`exists_chartRot_rep`): every chart state rotates to a representative. -/
def ExistsRep : Prop :=
  ∀ w : Phase (2 + 2), ∃ θ : ℝ, slow (chartRot θ w).2 0 = 0 ∧ 0 ≤ slow (chartRot θ w).1 0

/-- The consumer (`hRS_of_coversReps`): the cover statement gives the hypothesis `hRS` of
`bracket_bound_of_rotation` and `range_bound_of_rotation`, with `R = region d` and
`S = repSet cells d`. -/
def HRSOfCovers : Prop :=
  ∀ (cells : List AffineCell) (d : ℝ), CoversReps cells d →
    ∀ w ∈ region d, ∃ θ : ℝ, chartRot θ w ∈ repSet cells d

/-- `mem_toSet_iff`: membership in inequality form, for a well-formed cell. -/
def MemToSetIff : Prop :=
  ∀ k : AffineCell, k.wf = true → ∀ w : Phase (2 + 2), w ∈ k.toSet ↔ k.MemIneq (cellCoord w)

/-- Step 1 (`exists_slab`): a representative of `R(d)` lies in a slab of a checked chain. -/
def ExistsSlab : Prop :=
  ∀ (cm : ℚ) (S : List Slab), CoverPlan.slabsChainOk cm 0 S = true →
    ∀ x : ℝ, 0 ≤ x → x ^ 2 ≤ 2 * (cm : ℝ) → ∃ s ∈ S, (s.lo : ℝ) ≤ x ∧ x ≤ s.hi

/-- Step 2 (`disc_of_region`): on a slab, b's eccentricity vector lies in the disc of radius `R`. -/
def DiscOfRegion : Prop :=
  ∀ (d : ℝ) (w : Phase (2 + 2)), w ∈ region d → slow w.2 0 = 0 → ∀ lo R : ℝ, 0 ≤ lo →
    lo ≤ slow w.1 0 → 0 ≤ R → 2 * (cBar + 2 * d) - lo ^ 2 ≤ R ^ 2 →
    slow w.1 1 ^ 2 + slow w.2 1 ^ 2 ≤ R ^ 2

/-- Step 3 (`exists_wedge_of_chain`, a discrete intermediate-value argument on the list): if
`start × p ≥ 0` and `p × stop ≥ 0`, some wedge of a checked chain has `v × p ≥ 0 ≤ p × w`. -/
def ExistsWedge : Prop :=
  ∀ (start stop : Fin 2 → ℚ) (L : List Wedge), CoverPlan.chainOk start stop L = true →
    ∀ p : Fin 2 → ℝ, 0 ≤ (start 0 : ℝ) * p 1 - start 1 * p 0 →
      0 ≤ p 0 * (stop 1 : ℝ) - p 1 * stop 0 →
      ∃ x ∈ L, 0 ≤ (x.v 0 : ℝ) * p 1 - x.v 1 * p 0 ∧ 0 ≤ p 0 * (x.w 1 : ℝ) - p 1 * x.w 0

/-- Step 4 (`memIneq_of_wedge`): a point of a checked wedge's cone inside the disc of radius `R`,
with the slab's `ξ_c`, `η_c = 0` and `Λ` in the region's box, satisfies the cell's inequalities. -/
def MemOfWedge : Prop :=
  ∀ (P : CoverPlan) (s : Slab) (x : Wedge), P.wedgeOk s x = true →
    ∀ y : Fin 6 → ℝ,
      ((lamLoQ 0 : ℝ) - P.d ≤ y 0 ∧ y 0 ≤ (lamHiQ 0 : ℝ) + P.d) →
      ((lamLoQ 1 : ℝ) - P.d ≤ y 1 ∧ y 1 ≤ (lamHiQ 1 : ℝ) + P.d) →
      (s.lo : ℝ) ≤ y 2 → y 2 ≤ s.hi → y 3 = 0 → 0 ≤ (s.R : ℝ) → y 4 ^ 2 + y 5 ^ 2 ≤ (s.R : ℝ) ^ 2 →
      0 ≤ (x.v 0 : ℝ) * y 5 - x.v 1 * y 4 → 0 ≤ y 4 * (x.w 1 : ℝ) - y 5 * x.w 0 →
      x.cell.MemIneq y


/-! ### Scratch proofs of steps 2 and 3 -/

/-- Step 2. -/
theorem discOfRegion : DiscOfRegion := by
  intro d w hw hη lo R hlo hξ hR hR2
  obtain ⟨-, -, hA⟩ := hw
  unfold chartAMD at hA
  simp only [Fin.sum_univ_two, hη] at hA
  nlinarith [mul_le_mul hξ hξ hlo (hlo.trans hξ)]

/-- Step 3. -/
theorem existsWedge : ExistsWedge := by
  intro start stop L
  induction L generalizing start with
  | nil => intro h; simp [CoverPlan.chainOk] at h
  | cons x rest ih =>
    intro h p h0 hm
    cases rest with
    | nil =>
      simp only [CoverPlan.chainOk, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨x, by simp, h0, hm⟩
    | cons y rest' =>
      simp only [CoverPlan.chainOk, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, h'⟩ := h
      by_cases hw : 0 ≤ p 0 * (x.w 1 : ℝ) - p 1 * x.w 0
      · exact ⟨x, by simp, h0, hw⟩
      · have e : (x.w 0 : ℝ) * p 1 - x.w 1 * p 0 = -(p 0 * x.w 1 - p 1 * x.w 0) := by ring
        obtain ⟨z, hz, hz1, hz2⟩ := ih x.w h' p (by rw [e]; linarith) hm
        exact ⟨z, List.mem_cons_of_mem _ hz, hz1, hz2⟩

/-- Step 1, from any start `a`. -/
theorem existsSlab_aux (cm : ℚ) : ∀ (S : List Slab) (a : ℚ), CoverPlan.slabsChainOk cm a S = true →
    ∀ x : ℝ, (a : ℝ) ≤ x → x ^ 2 ≤ 2 * (cm : ℝ) → ∃ s ∈ S, (s.lo : ℝ) ≤ x ∧ x ≤ s.hi := by
  intro S
  induction S with
  | nil => intro a h; simp [CoverPlan.slabsChainOk] at h
  | cons s rest ih =>
    intro a h x hx hx2
    cases rest with
    | nil =>
      simp only [CoverPlan.slabsChainOk, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hlo, hhi⟩, hcm⟩ := h
      refine ⟨s, by simp, by rw [hlo]; exact hx, ?_⟩
      have h1 : 2 * (cm : ℝ) ≤ (s.hi : ℝ) ^ 2 := by exact_mod_cast hcm
      have h2 : (0 : ℝ) ≤ s.hi := by exact_mod_cast hhi
      by_contra hc
      rw [not_le] at hc
      nlinarith [mul_self_lt_mul_self h2 hc]
    | cons t rest' =>
      simp only [CoverPlan.slabsChainOk, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hlo, h'⟩ := h
      by_cases hxs : x ≤ s.hi
      · exact ⟨s, by simp, by rw [hlo]; exact hx, hxs⟩
      · obtain ⟨z, hz, h1, h2⟩ := ih s.hi h' x (le_of_lt (not_le.mp hxs)) hx2
        exact ⟨z, List.mem_cons_of_mem _ hz, h1, h2⟩

/-- Step 1. -/
theorem existsSlab : ExistsSlab := fun cm S h x hx hx2 =>
  existsSlab_aux cm S 0 h x (by simpa using hx) hx2

/-- `MemToSetIff`, the direction used by the cover (inequalities ⇒ membership). -/
theorem mem_toSet_of_memIneq (k : AffineCell) (hk : k.wf = true) (w : Phase (2 + 2))
    (h : k.MemIneq (cellCoord w)) : w ∈ k.toSet := by
  simp only [AffineCell.wf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hk
  obtain ⟨hpos, hrot⟩ := hk
  have hp : ∀ j, (0 : ℝ) < k.h j := fun j => by exact_mod_cast hpos j (List.mem_finRange j)
  have hr : (k.a : ℝ) ^ 2 + (k.b : ℝ) ^ 2 = 1 := by exact_mod_cast hrot
  set x := cellCoord w with hx
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  set A : ℝ := k.a * (x 4 - k.c 4) + k.b * (x 5 - k.c 5) with hA
  set B : ℝ := -k.b * (x 4 - k.c 4) + k.a * (x 5 - k.c 5) with hB
  set u : Fin 6 → ℝ := ![(x 0 - k.c 0) / k.h 0, (x 1 - k.c 1) / k.h 1, (x 2 - k.c 2) / k.h 2,
    (x 3 - k.c 3) / k.h 3, A / k.h 4, B / k.h 5] with hu_def
  have key : ∀ (t s : ℝ), 0 < s → |t| ≤ s → |t / s| ≤ 1 := fun t s hs ht => by
    rw [abs_div, abs_of_pos hs, div_le_one hs]
    exact ht
  have hm : ∀ (t s : ℝ), 0 < s → s * (t / s) = t := fun t s hs => by
    field_simp
  have hu : ∀ j, |u j| ≤ 1 := by
    intro j
    fin_cases j
    · exact key _ _ (hp 0) h0
    · exact key _ _ (hp 1) h1
    · exact key _ _ (hp 2) h2
    · exact key _ _ (hp 3) h3
    · exact key _ _ (hp 4) h4
    · exact key _ _ (hp 5) h5
  refine ⟨u, hu, ?_⟩
  have e0 : (k.h 0 : ℝ) * u 0 = x 0 - k.c 0 := hm _ _ (hp 0)
  have e1 : (k.h 1 : ℝ) * u 1 = x 1 - k.c 1 := hm _ _ (hp 1)
  have e2 : (k.h 2 : ℝ) * u 2 = x 2 - k.c 2 := hm _ _ (hp 2)
  have e3 : (k.h 3 : ℝ) * u 3 = x 3 - k.c 3 := hm _ _ (hp 3)
  have e4 : (k.h 4 : ℝ) * u 4 = A := hm _ _ (hp 4)
  have e5 : (k.h 5 : ℝ) * u 5 = B := hm _ _ (hp 5)
  funext j
  fin_cases j
  · show x 0 = k.c 0 + k.h 0 * u 0
    linear_combination -e0
  · show x 1 = k.c 1 + k.h 1 * u 1
    linear_combination -e1
  · show x 2 = k.c 2 + k.h 2 * u 2
    linear_combination -e2
  · show x 3 = k.c 3 + k.h 3 * u 3
    linear_combination -e3
  · show x 4 = k.c 4 + k.a * k.h 4 * u 4 - k.b * k.h 5 * u 5
    linear_combination (-(k.a : ℝ)) * e4 + (k.b : ℝ) * e5 + (-(x 4 - k.c 4)) * hr
  · show x 5 = k.c 5 + k.b * k.h 4 * u 4 + k.a * k.h 5 * u 5
    linear_combination (-(k.b : ℝ)) * e4 + (-(k.a : ℝ)) * e5 + (-(x 5 - k.c 5)) * hr

/-- Step 4. -/
theorem memOfWedge : MemOfWedge := by
  intro P s x hx y hΛ0 hΛ1 hlo hhi hy3 hR0 hdisc hv hw
  simp only [CoverPlan.wedgeOk, CoverPlan.axesOk, AffineCell.wf, AffineCell.rad, AffineCell.tng,
    AffineCell.cb, crossQ, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hx
  obtain ⟨-, hrot, hl0, hh0, hl1, hh1, hl2, hh2, hc3, hD, hτ, hrv, hrw, htv, htw, hc4, hR4, htc,
    hfin⟩ := hx
  have hr : (x.cell.a : ℝ) ^ 2 + (x.cell.b : ℝ) ^ 2 = 1 := by exact_mod_cast hrot
  have hl0' : (x.cell.c 0 : ℝ) - x.cell.h 0 ≤ lamLoQ 0 - P.d := by exact_mod_cast hl0
  have hh0' : (lamHiQ 0 : ℝ) + P.d ≤ x.cell.c 0 + x.cell.h 0 := by exact_mod_cast hh0
  have hl1' : (x.cell.c 1 : ℝ) - x.cell.h 1 ≤ lamLoQ 1 - P.d := by exact_mod_cast hl1
  have hh1' : (lamHiQ 1 : ℝ) + P.d ≤ x.cell.c 1 + x.cell.h 1 := by exact_mod_cast hh1
  have hl2' : (x.cell.c 2 : ℝ) - x.cell.h 2 ≤ s.lo := by exact_mod_cast hl2
  have hh2' : (s.hi : ℝ) ≤ x.cell.c 2 + x.cell.h 2 := by exact_mod_cast hh2
  have hc3' : |(x.cell.c 3 : ℝ)| ≤ x.cell.h 3 := by exact_mod_cast hc3
  have hD' : (0 : ℝ) < x.v 0 * x.w 1 - x.v 1 * x.w 0 := by exact_mod_cast hD
  have hτ' : (0 : ℝ) ≤ x.τ := by exact_mod_cast hτ
  have hrv' : (0 : ℝ) ≤ x.cell.a * x.v 0 + x.cell.b * x.v 1 := by
    exact_mod_cast of_decide_eq_true hrv
  have hrw' : (0 : ℝ) ≤ x.cell.a * x.w 0 + x.cell.b * x.w 1 := by
    exact_mod_cast of_decide_eq_true hrw
  have htv' : |-(x.cell.b : ℝ) * x.v 0 + x.cell.a * x.v 1| ≤
      x.τ * (x.cell.a * x.v 0 + x.cell.b * x.v 1) := by exact_mod_cast of_decide_eq_true htv
  have htw' : |-(x.cell.b : ℝ) * x.w 0 + x.cell.a * x.w 1| ≤
      x.τ * (x.cell.a * x.w 0 + x.cell.b * x.w 1) := by exact_mod_cast of_decide_eq_true htw
  have hc4' : (x.cell.a : ℝ) * x.cell.c 4 + x.cell.b * x.cell.c 5 - x.cell.h 4 ≤ 0 := by
    exact_mod_cast of_decide_eq_true hc4
  have hR4' : (s.R : ℝ) ≤ x.cell.a * x.cell.c 4 + x.cell.b * x.cell.c 5 + x.cell.h 4 := by
    exact_mod_cast of_decide_eq_true hR4
  have htc' : |-(x.cell.b : ℝ) * x.cell.c 4 + x.cell.a * x.cell.c 5| ≤ x.cell.h 5 := by
    exact_mod_cast of_decide_eq_true htc
  have hfin' : (x.τ : ℝ) ^ 2 * s.R ^ 2 ≤ (1 + (x.τ : ℝ) ^ 2) *
      (x.cell.h 5 - |-(x.cell.b : ℝ) * x.cell.c 4 + x.cell.a * x.cell.c 5|) ^ 2 := by
    exact_mod_cast of_decide_eq_true hfin
  -- the radial and tangential coordinates of `p = (y 4, y 5)`
  set a : ℝ := ((x.cell.a : ℚ) : ℝ)
  set b : ℝ := ((x.cell.b : ℚ) : ℝ)
  set τ : ℝ := ((x.τ : ℚ) : ℝ)
  set r : ℝ := a * y 4 + b * y 5 with hr_def
  set t : ℝ := -b * y 4 + a * y 5 with ht_def
  set rc : ℝ := a * x.cell.c 4 + b * x.cell.c 5 with hrc_def
  set tc : ℝ := -b * x.cell.c 4 + a * x.cell.c 5 with htc_def
  have hcs : r ^ 2 + t ^ 2 = y 4 ^ 2 + y 5 ^ 2 := by
    simp only [hr_def, ht_def]; linear_combination (y 4 ^ 2 + y 5 ^ 2) * hr
  set D : ℝ := x.v 0 * x.w 1 - x.v 1 * x.w 0 with hD_def
  have id1 : D * r = (y 4 * x.w 1 - y 5 * x.w 0) * (a * x.v 0 + b * x.v 1) +
      (x.v 0 * y 5 - x.v 1 * y 4) * (a * x.w 0 + b * x.w 1) := by
    simp only [hD_def, hr_def]; ring
  have id2 : D * t = (y 4 * x.w 1 - y 5 * x.w 0) * (-b * x.v 0 + a * x.v 1) +
      (x.v 0 * y 5 - x.v 1 * y 4) * (-b * x.w 0 + a * x.w 1) := by
    simp only [hD_def, ht_def]; ring
  have hw' : (0 : ℝ) ≤ y 4 * x.w 1 - y 5 * x.w 0 := hw
  have hv' : (0 : ℝ) ≤ x.v 0 * y 5 - x.v 1 * y 4 := hv
  have hrad : 0 ≤ r := by
    have h1 : D * 0 ≤ D * r := by
      rw [mul_zero, id1]
      exact add_nonneg (mul_nonneg hw' hrv') (mul_nonneg hv' hrw')
    exact le_of_mul_le_mul_left h1 hD'
  have hradR : r ≤ s.R := by
    have h1 : r ^ 2 ≤ (s.R : ℝ) ^ 2 := by linarith [sq_nonneg t]
    have h2 := sq_le_sq.mp h1
    rw [abs_of_nonneg hR0] at h2
    exact (le_abs_self r).trans h2
  obtain ⟨htv1, htv2⟩ := abs_le.mp htv'
  obtain ⟨htw1, htw2⟩ := abs_le.mp htw'
  have htng1 : t ≤ τ * r := by
    have h1 : D * 0 ≤ D * (τ * r - t) := by
      have e : D * (τ * r - t) = (y 4 * x.w 1 - y 5 * x.w 0) *
          (τ * (a * x.v 0 + b * x.v 1) - (-b * x.v 0 + a * x.v 1)) +
          (x.v 0 * y 5 - x.v 1 * y 4) *
            (τ * (a * x.w 0 + b * x.w 1) - (-b * x.w 0 + a * x.w 1)) := by
        linear_combination τ * id1 - id2
      rw [mul_zero, e]
      exact add_nonneg (mul_nonneg hw' (sub_nonneg.mpr htv2)) (mul_nonneg hv' (sub_nonneg.mpr htw2))
    linarith [le_of_mul_le_mul_left h1 hD']
  have htng2 : -(τ * r) ≤ t := by
    have h1 : D * 0 ≤ D * (τ * r + t) := by
      have e : D * (τ * r + t) = (y 4 * x.w 1 - y 5 * x.w 0) *
          (τ * (a * x.v 0 + b * x.v 1) + (-b * x.v 0 + a * x.v 1)) +
          (x.v 0 * y 5 - x.v 1 * y 4) *
            (τ * (a * x.w 0 + b * x.w 1) + (-b * x.w 0 + a * x.w 1)) := by
        linear_combination τ * id1 + id2
      rw [mul_zero, e]
      exact add_nonneg (mul_nonneg hw' (by linarith)) (mul_nonneg hv' (by linarith))
    linarith [le_of_mul_le_mul_left h1 hD']
  have hm0 : 0 ≤ (x.cell.h 5 : ℝ) - |tc| := sub_nonneg.mpr htc'
  have ht2 : t ^ 2 ≤ (τ * r) ^ 2 := sq_le_sq' htng2 htng1
  have ht3 : (1 + τ ^ 2) * t ^ 2 ≤ (1 + τ ^ 2) * (x.cell.h 5 - |tc|) ^ 2 :=
    calc (1 + τ ^ 2) * t ^ 2 = t ^ 2 + τ ^ 2 * t ^ 2 := by ring
      _ ≤ (τ * r) ^ 2 + τ ^ 2 * t ^ 2 := by linarith
      _ = τ ^ 2 * (r ^ 2 + t ^ 2) := by ring
      _ = τ ^ 2 * (y 4 ^ 2 + y 5 ^ 2) := by rw [hcs]
      _ ≤ τ ^ 2 * (s.R : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hdisc (sq_nonneg τ)
      _ ≤ (1 + τ ^ 2) * (x.cell.h 5 - |tc|) ^ 2 := hfin'
  have ht4 : t ^ 2 ≤ (x.cell.h 5 - |tc|) ^ 2 := le_of_mul_le_mul_left ht3 (by positivity)
  have ht5 : |t| ≤ x.cell.h 5 - |tc| := by
    have h2 := sq_le_sq.mp ht4
    rwa [abs_of_nonneg hm0] at h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact abs_le.mpr ⟨by linarith [hΛ0.1], by linarith [hΛ0.2]⟩
  · exact abs_le.mpr ⟨by linarith [hΛ1.1], by linarith [hΛ1.2]⟩
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [hy3, zero_sub, abs_neg]; exact hc3'
  · have e : a * (y 4 - x.cell.c 4) + b * (y 5 - x.cell.c 5) = r - rc := by
      simp only [hr_def, hrc_def]; ring
    rw [e]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have e : -b * (y 4 - x.cell.c 4) + a * (y 5 - x.cell.c 5) = t - tc := by
      simp only [ht_def, htc_def]; ring
    rw [e]
    linarith [abs_sub t tc]

/-- The disc case of step 4. -/
theorem memOfDisc (P : CoverPlan) (s : Slab) (k : AffineCell) (hk : P.discOk s k = true)
    (y : Fin 6 → ℝ)
    (hΛ0 : (lamLoQ 0 : ℝ) - P.d ≤ y 0 ∧ y 0 ≤ (lamHiQ 0 : ℝ) + P.d)
    (hΛ1 : (lamLoQ 1 : ℝ) - P.d ≤ y 1 ∧ y 1 ≤ (lamHiQ 1 : ℝ) + P.d)
    (hlo : (s.lo : ℝ) ≤ y 2) (hhi : y 2 ≤ s.hi) (hy3 : y 3 = 0) (hR0 : 0 ≤ (s.R : ℝ))
    (hdisc : y 4 ^ 2 + y 5 ^ 2 ≤ (s.R : ℝ) ^ 2) : k.MemIneq y := by
  simp only [CoverPlan.discOk, CoverPlan.axesOk, AffineCell.wf, AffineCell.rad, AffineCell.tng,
    AffineCell.cb, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hk
  obtain ⟨-, hrot, hl0, hh0, hl1, hh1, hl2, hh2, hc3, hd4, hd5⟩ := hk
  have hr : (k.a : ℝ) ^ 2 + (k.b : ℝ) ^ 2 = 1 := by exact_mod_cast hrot
  have hl0' : (k.c 0 : ℝ) - k.h 0 ≤ lamLoQ 0 - P.d := by exact_mod_cast hl0
  have hh0' : (lamHiQ 0 : ℝ) + P.d ≤ k.c 0 + k.h 0 := by exact_mod_cast hh0
  have hl1' : (k.c 1 : ℝ) - k.h 1 ≤ lamLoQ 1 - P.d := by exact_mod_cast hl1
  have hh1' : (lamHiQ 1 : ℝ) + P.d ≤ k.c 1 + k.h 1 := by exact_mod_cast hh1
  have hl2' : (k.c 2 : ℝ) - k.h 2 ≤ s.lo := by exact_mod_cast hl2
  have hh2' : (s.hi : ℝ) ≤ k.c 2 + k.h 2 := by exact_mod_cast hh2
  have hc3' : |(k.c 3 : ℝ)| ≤ k.h 3 := by exact_mod_cast hc3
  have hd4' : (s.R : ℝ) + |(k.a : ℝ) * k.c 4 + k.b * k.c 5| ≤ k.h 4 := by
    exact_mod_cast of_decide_eq_true hd4
  have hd5' : (s.R : ℝ) + |-(k.b : ℝ) * k.c 4 + k.a * k.c 5| ≤ k.h 5 := by
    exact_mod_cast of_decide_eq_true hd5
  set a : ℝ := ((k.a : ℚ) : ℝ)
  set b : ℝ := ((k.b : ℚ) : ℝ)
  have hcs : (a * y 4 + b * y 5) ^ 2 + (-b * y 4 + a * y 5) ^ 2 = y 4 ^ 2 + y 5 ^ 2 := by
    linear_combination (y 4 ^ 2 + y 5 ^ 2) * hr
  have hb1 : |a * y 4 + b * y 5| ≤ s.R := by
    have h1 : (a * y 4 + b * y 5) ^ 2 ≤ (s.R : ℝ) ^ 2 := by
      linarith [sq_nonneg (-b * y 4 + a * y 5)]
    have h2 := sq_le_sq.mp h1
    rwa [abs_of_nonneg hR0] at h2
  have hb2 : |-b * y 4 + a * y 5| ≤ s.R := by
    have h1 : (-b * y 4 + a * y 5) ^ 2 ≤ (s.R : ℝ) ^ 2 := by
      linarith [sq_nonneg (a * y 4 + b * y 5)]
    have h2 := sq_le_sq.mp h1
    rwa [abs_of_nonneg hR0] at h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact abs_le.mpr ⟨by linarith [hΛ0.1], by linarith [hΛ0.2]⟩
  · exact abs_le.mpr ⟨by linarith [hΛ1.1], by linarith [hΛ1.2]⟩
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [hy3, zero_sub, abs_neg]; exact hc3'
  · have e : a * (y 4 - k.c 4) + b * (y 5 - k.c 5) =
        (a * y 4 + b * y 5) - (a * k.c 4 + b * k.c 5) := by ring
    rw [e]
    linarith [abs_sub (a * y 4 + b * y 5) (a * k.c 4 + b * k.c 5)]
  · have e : -b * (y 4 - k.c 4) + a * (y 5 - k.c 5) =
        (-b * y 4 + a * y 5) - (-b * k.c 4 + a * k.c 5) := by ring
    rw [e]
    linarith [abs_sub (-b * y 4 + a * y 5) (-b * k.c 4 + a * k.c 5)]

theorem wf_of_axesOk {P : CoverPlan} {s : Slab} {k : AffineCell} (h : P.axesOk s k = true) :
    k.wf = true := by
  simp only [CoverPlan.axesOk, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1

theorem lamLoQ_cast (i : Fin 2) : ((lamLoQ i : ℚ) : ℝ) = lamLo i := by
  fin_cases i <;> simp [lamLoQ, lamLo]

theorem lamHiQ_cast (i : Fin 2) : ((lamHiQ i : ℚ) : ℝ) = lamHi i := by
  fin_cases i <;> simp [lamHiQ, lamHi]

theorem cmax_cast (P : CoverPlan) : ((P.cmax : ℚ) : ℝ) = cBar + 2 * (P.d : ℝ) := by
  simp [CoverPlan.cmax, cBarQ, cBar]

/-- **The main theorem** (`CoverTheorem`). -/
theorem coversReps_of_ok : CoverTheorem := by
  intro P hP w hw hη hξ
  simp only [CoverPlan.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hP
  obtain ⟨⟨-, hchain⟩, hslabs⟩ := hP
  obtain ⟨hsafe, hΛ, hA⟩ := hw
  have hx2 : slow w.1 0 ^ 2 ≤ 2 * ((P.cmax : ℚ) : ℝ) := by
    rw [cmax_cast]
    unfold chartAMD at hA
    simp only [Fin.sum_univ_two, hη] at hA
    nlinarith [sq_nonneg (slow w.1 1), sq_nonneg (slow w.2 1)]
  obtain ⟨s, hs, hslo, hshi⟩ := existsSlab P.cmax P.slabs hchain _ hξ hx2
  have hsok := hslabs s hs
  simp only [CoverPlan.slabOk, Bool.and_eq_true, decide_eq_true_eq] at hsok
  obtain ⟨⟨⟨⟨hlo0, -⟩, hR0⟩, hR2⟩, hrest⟩ := hsok
  have hR0' : (0 : ℝ) ≤ s.R := by exact_mod_cast hR0
  have hR2' : 2 * (cBar + 2 * (P.d : ℝ)) - (s.lo : ℝ) ^ 2 ≤ (s.R : ℝ) ^ 2 := by
    rw [← cmax_cast]; exact_mod_cast hR2
  have hdisc : slow w.1 1 ^ 2 + slow w.2 1 ^ 2 ≤ (s.R : ℝ) ^ 2 :=
    discOfRegion _ w ⟨hsafe, hΛ, hA⟩ hη s.lo s.R (by exact_mod_cast hlo0) hslo hR0' hR2'
  have hΛ0 : (lamLoQ 0 : ℝ) - P.d ≤ cellCoord w 0 ∧ cellCoord w 0 ≤ (lamHiQ 0 : ℝ) + P.d := by
    rw [lamLoQ_cast, lamHiQ_cast]; exact hΛ 0
  have hΛ1 : (lamLoQ 1 : ℝ) - P.d ≤ cellCoord w 1 ∧ cellCoord w 1 ≤ (lamHiQ 1 : ℝ) + P.d := by
    rw [lamLoQ_cast, lamHiQ_cast]; exact hΛ 1
  have hmem : ∀ k, (k ∈ s.disc.toList ∨ k ∈ (s.upper ++ s.lower).map (·.cell)) → k ∈ P.cells := by
    intro k hk
    simp only [CoverPlan.cells, List.mem_flatMap, List.mem_append]
    exact ⟨s, hs, hk⟩
  cases hdk : s.disc with
  | some k =>
    rw [hdk] at hrest
    have hm := memOfDisc P s k hrest (cellCoord w) hΛ0 hΛ1 hslo hshi hη hR0' hdisc
    refine ⟨k, hmem k (Or.inl (by simp [hdk])), mem_toSet_of_memIneq k ?_ w hm⟩
    simp only [CoverPlan.discOk, Bool.and_eq_true] at hrest
    exact wf_of_axesOk hrest.1.1
  | none =>
    rw [hdk] at hrest
    simp only [Bool.and_eq_true, List.all_eq_true] at hrest
    obtain ⟨⟨hup, hlow⟩, hall⟩ := hrest
    have key : ∀ x ∈ s.upper ++ s.lower,
        0 ≤ (x.v 0 : ℝ) * slow w.2 1 - x.v 1 * slow w.1 1 →
        0 ≤ slow w.1 1 * (x.w 1 : ℝ) - slow w.2 1 * x.w 0 → ∃ k ∈ P.cells, w ∈ k.toSet := by
      intro x hx h1 h2
      have hxok := hall x hx
      have hm := memOfWedge P s x hxok (cellCoord w) hΛ0 hΛ1 hslo hshi hη hR0' hdisc h1 h2
      have hwf : x.cell.wf = true := by
        simp only [CoverPlan.wedgeOk, Bool.and_eq_true] at hxok
        exact wf_of_axesOk hxok.1.1.1.1.1.1.1.1.1.1
      exact ⟨x.cell, hmem _ (Or.inr (List.mem_map.mpr ⟨x, hx, rfl⟩)),
        mem_toSet_of_memIneq _ hwf w hm⟩
    by_cases hηb : 0 ≤ slow w.2 1
    · obtain ⟨x, hx, h1, h2⟩ := existsWedge _ _ s.upper hup ![slow w.1 1, slow w.2 1]
        (by simpa using hηb) (by simpa using hηb)
      exact key x (List.mem_append_left _ hx) (by simpa using h1) (by simpa using h2)
    · have hn : 0 ≤ -slow w.2 1 := by linarith [not_le.mp hηb]
      obtain ⟨x, hx, h1, h2⟩ := existsWedge _ _ s.lower hlow ![slow w.1 1, slow w.2 1]
        (by simpa using hn) (by simpa using hn)
      exact key x (List.mem_append_right _ hx) (by simpa using h1) (by simpa using h2)

theorem slow_append' {a b : ℕ} (u : Fin a → ℝ) (v : Fin b → ℝ) : slow (Fin.append u v) = v := by
  funext i
  simp only [slow, Fin.append_right]

theorem slow_chartRot_fst (θ : ℝ) (w : Phase (2 + 2)) (i : Fin 2) :
    slow (chartRot θ w).1 i = Real.cos θ * slow w.1 i - Real.sin θ * slow w.2 i := by
  simp only [chartRot, assemble, slow_append']

theorem slow_chartRot_snd (θ : ℝ) (w : Phase (2 + 2)) (i : Fin 2) :
    slow (chartRot θ w).2 i = Real.sin θ * slow w.1 i + Real.cos θ * slow w.2 i := by
  simp only [chartRot, assemble, slow_append']

/-- Step 0. -/
theorem existsRep : ExistsRep := by
  intro w
  by_cases h0 : slow w.1 0 = 0 ∧ slow w.2 0 = 0
  · refine ⟨0, ?_, ?_⟩
    · rw [slow_chartRot_snd, h0.1, h0.2]; ring
    · rw [slow_chartRot_fst, h0.1, h0.2]; simp
  · set z : ℂ := ⟨slow w.1 0, -slow w.2 0⟩ with hz_def
    have hz : z ≠ 0 := by
      intro h
      apply h0
      have h1 := congrArg Complex.re h
      have h2 := congrArg Complex.im h
      simp only [hz_def, Complex.zero_re, Complex.zero_im] at h1 h2
      exact ⟨h1, by linarith⟩
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    refine ⟨Complex.arg z, ?_, ?_⟩
    · rw [slow_chartRot_snd, Complex.sin_arg, Complex.cos_arg hz]
      simp only [hz_def]
      field_simp
      ring
    · rw [slow_chartRot_fst, Complex.sin_arg, Complex.cos_arg hz]
      simp only [hz_def]
      have e : slow w.1 0 / ‖z‖ * slow w.1 0 - -slow w.2 0 / ‖z‖ * slow w.2 0 =
          (slow w.1 0 ^ 2 + slow w.2 0 ^ 2) / ‖z‖ := by ring
      rw [e]
      positivity

/-- The consumer: the cover statement gives `hRS` of the rotation lemmas. -/
theorem hRS_of_coversReps : HRSOfCovers := by
  intro cells d hc w hw
  obtain ⟨θ, h1, h2⟩ := existsRep w
  have hr := chartRot_mem_region θ hw
  obtain ⟨k, hk, hkw⟩ := hc _ hr h1 h2
  exact ⟨θ, hr, k, hk, hkw⟩


end HD11964.Cover

end
