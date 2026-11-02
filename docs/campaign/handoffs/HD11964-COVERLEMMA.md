# Handoff HD11964-COVERLEMMA (phase 2: the cover lemma for affine cells, statement and proof plan)

Worker kamx-hd11964, branch `hd11964-p2`. Task from the orchestrator (2 November 2026):
- the ruling makes the fitted cover (`κ = 0.2`) the kernel target;
- kamx-hd-layer is being asked to accept the rotated affine cell map;
- until 04:30 UTC:
  - draft the Lean cover lemma's exact statement (generic: a finite list of affine cells `w = c + M u`,
    `|u| ≤ 1`, with `M` diagonal except a rational rotation block, covering `R(d)`);
  - plan its proof in the four steps of HD11964-CELLS;
  - put the statement in this handoff for the cell-format agreement;
  - no long builds.

**Status: statement drafted and type-checked; proof planned; no proofs written.** Nothing pushed.
- The draft (below, verbatim) elaborates as a scratch module against the built `HD11964` package:
  - `lake env lean`, one process, 4 GB cap, 5 s, 3.7 GB peak;
  - no `sorry`. The planned lemmas are stated as `Prop` definitions, so their statements are type-checked without
    proofs.
- The decidable plan check `CoverPlan.ok` was run with `decide +kernel` on the exact rational plans generated from
  both fitted covers. Both are accepted, in about 5 s each:
  - `κ = 0.2`: 50 cells, 52 wedges;
  - `κ = 0.2`, `nmult = 4`: 57 cells, 56 wedges.
- Sanity checks are rejected as they should be: an empty plan, and a fan whose tangential half-width is too small.
- No Lean file is committed. This is a draft for agreement, and no core or package file changed. The scratch files
  are in `~/kam-data/hd11964/coverlemma/`.

## Which fitted cover: a correction to the ruling's numbers

The ruling says "κ = 0.2 with sector counts a multiple of 4 (50 cells, margin ≈ 5.9, cost ≈ 0.46)". Those numbers
belong to the plain `κ = 0.2` cover. With sector counts rounded to multiples of 4 (`nmult = 4`), the cover has 57
cells, margin 6.03 and cost 0.52 (HD11964-CELLS).

**Multiples of 4 are no longer needed.**
- The refined step 3 below splits the plane at `(±1, 0)` into two chains of rays.
- A sector that straddles `(−1, 0)`, which happens for odd `n`, simply appears in both chains with the same cell.
- So both plans pass the same check, and the 50-cell plan, the one whose numbers the ruling quotes, is a valid kernel
  target.

Taken (conservative): the statement covers both; both rational plans are generated and checked. Owner question 1
asks which one to use.

## The statement (for the cell-format agreement)

**Cell coordinates and cells.**
- With `assemble I φ p q = (append φ q, append I p)`, `ξ_i = slow w.1 i` and `η_i = slow w.2 i`.
- `chartRot θ` rotates `(ξ_i, η_i)` by `θ` for every planet.
- A cell constrains `(Λ_c, Λ_b, ξ_c, η_c, ξ_b, η_b)` and contains every angle.

**The agreement, in one line.**
- A cell is `AffineCell` (rational `c, h : Fin 6 → ℚ` and `a, b : ℚ` with `a² + b² = 1`).
- Its set is `AffineCell.toSet`: `cellCoord w = c + M u` for some `‖u‖_∞ ≤ 1`, at every angle.
- The kernel's cell check proves its bounds for `w ∈ k.toSet ∩ region d`.
- The cover lemma proves `CoversReps cells d`.

The full draft:

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.NoCrossing

/-!
# DRAFT (HD11964-COVERLEMMA): the cover lemma for affine cells

Statement draft for the cell-format agreement with kamx-hd-layer; not part of the package, no
proofs. The planned lemmas are stated as `Prop`s so that their statements type-check.

* `AffineCell`: rational data of a cell `x = c + M u`, `‖u‖_∞ ≤ 1`, in the cell coordinates
  `x = (Λ_c, Λ_b, ξ_c, η_c, ξ_b, η_b)` (`cellCoord`); `M = diag (h₀, h₁, h₂, h₃) ⊕ Rot (a, b) ·
  diag (h₄, h₅)`, `Rot (a, b) = [[a, -b], [b, a]]` an exact rational rotation (`a² + b² = 1`).
* `CoversReps cells d`: every rotation representative (`η_c = 0`, `ξ_c ≥ 0`) of `R(d)` lies in a
  cell of the list. This is the cover statement of the agreement.
* `CoverPlan`, `CoverPlan.ok`: the plan of the fitted cover (slabs in `ξ_c`, chains of wedges in
  `(ξ_b, η_b)`) and its decidable check; the planned theorem `coversReps_of_ok` (`CoverTheorem`)
  turns `P.ok = true` (by `decide +kernel`) into `CoversReps P.cells P.d`.
-/

@[expose] public noncomputable section

open Set KAM KAM.Planetary KAM.Application.LambdaDrift

namespace HD11964.CoverDraft

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
      (s.lo : ℝ) ≤ y 2 → y 2 ≤ s.hi → y 3 = 0 → y 4 ^ 2 + y 5 ^ 2 ≤ (s.R : ℝ) ^ 2 →
      0 ≤ (x.v 0 : ℝ) * y 5 - x.v 1 * y 4 → 0 ≤ y 4 * (x.w 1 : ℝ) - y 5 * x.w 0 →
      x.cell.MemIneq y

end HD11964.CoverDraft

end
```

## The proof plan

**The main theorem** (`coversReps_of_ok`, the `CoverTheorem` above) is `P.ok = true → CoversReps P.cells P.d`. For
the fitted plan, `fitPlan.ok = true` is one `decide +kernel` (measured: about 5 s). The plan is generated by
`scripts/cover2_plan_lean.py`.

Fix `w ∈ region d` with `η_c = slow w.2 0 = 0` and `ξ_c = slow w.1 0 ≥ 0`, and write `p = (ξ_b, η_b)`.

0. **Representatives** (`ExistsRep`; the consumer `HRSOfCovers`).
   - The rotation `θ` with `(sin θ, cos θ) = (−η_c, ξ_c)/r`, where `r = |(ξ_c, η_c)|` (any `θ` if `r = 0`), gives
     `η_c' = 0` and `ξ_c' = r ≥ 0`.
   - `chartRot_mem_region` keeps the image in `R(d)`.
   - So `CoversReps cells d` gives the `hRS` of `bracket_bound_of_rotation` and `range_bound_of_rotation`, with
     `R = region d` and `S = repSet cells d`. The kernel's per-cell bounds on `k.toSet ∩ region d` give their `hS`.
1. **Slab** (`ExistsSlab`).
   - `ξ_c² ≤ 2 chartAMD w ≤ 2 Cmax ≤ hi_last²`, and `ξ_c ≥ 0`, so `0 ≤ ξ_c ≤ hi_last`.
   - The checked chain `slabsChainOk` (consecutive endpoints from 0) gives a slab with `lo ≤ ξ_c ≤ hi`.
   - Proof: induction on the slab list.
2. **Disc** (`DiscOfRegion`).
   - `chartAMD w = (ξ_c² + η_c² + ξ_b² + η_b²)/2 ≤ Cbar + 2d`, with `η_c = 0` and `lo ≤ ξ_c`, gives
     `|p|² ≤ 2 Cmax − lo² ≤ R²`.
   - Proof: `nlinarith`, after unfolding `chartAMD` over `Fin 2`.
3. **Wedge** (`ExistsWedge`; a discrete intermediate-value argument).
   - If `η_b ≥ 0`, then `(1, 0) × p = η_b ≥ 0` and `p × (−1, 0) = η_b ≥ 0`: use the upper chain.
   - If `η_b < 0`, the lower chain from `(−1, 0)` to `(1, 0)` works the same way.
   - On a chain `v_0 = start, …, v_m = stop` with `v_0 × p ≥ 0` and `p × v_m ≥ 0`, some consecutive wedge has
     `v_s × p ≥ 0` and `p × v_{s+1} ≥ 0`. Induction on the list:
     - if `p × v_1 ≥ 0`, take the first wedge;
     - otherwise `v_1 × p > 0`, and recurse.
   - No ordering or angle bookkeeping is needed: only the chain's endpoints and the equality of consecutive rays,
     which `chainOk` checks.
4. **Sector ⊆ box** (`MemOfWedge`, then `MemToSetIff`).
   - With `cross(v, w) > 0`, Cramer gives `p = α v + β w`, where `α = (p × w)/(v × w) ≥ 0` and
     `β = (v × p)/(v × w) ≥ 0`.
   - Linearity then gives:
     - `rad p ≥ 0`, from `rad v`, `rad w ≥ 0`;
     - `|tng p| ≤ τ rad p`, from the two ray conditions.
   - The exact rotation gives `rad² + tng² = |p|² ≤ R²`. Hence:
     - `rad p ≤ R ≤ rad c_b + h₄`;
     - `rad p ≥ 0 ≥ rad c_b − h₄`;
     - `tng p² (1 + τ²) ≤ τ² R² ≤ (1 + τ²)(h₅ − |tng c_b|)²`, so `|tng p − tng c_b| ≤ h₅`.
   - The axes come from the region (`Λ`), the slab (`ξ_c`) and `η_c = 0`.
   - `MemToSetIff` turns the inequalities into `u`: `u_j = (x_j − c_j)/h_j` for `j < 4`, and
     `u₄ = rad(x − c)/h₄`, `u₅ = tng(x − c)/h₅`. The map identity holds because `a² + b² = 1`.
   - A disc slab uses `rad p`, `|tng p| ≤ |p| ≤ R` directly (`discOk`).

**Estimated size.**
- Steps 1–4 are generic lemmas of about 150–250 lines in all: elementary real inequalities, two list inductions and
  the casts `ℚ → ℝ`. No analysis.
- The plan data are about 230–250 lines of rationals (generated). Generated data longer than 100 columns must be
  wrapped. The draft's own lines are ≤ 100.
- The main risk is `push_cast` and `Rat.cast` bookkeeping in step 4, not mathematics.

## What the kernel's cell check is asked to provide

For each cell `k` of the plan: the bracket bound `|dF_i(X_H)| ≤ η_i` and the range `lo_i ≤ F_i − Λ_i ≤ hi_i` at every
`w ∈ k.toSet ∩ region d`.
- In `u` coordinates, that is every `u ∈ [−1, 1]⁶` and every angle.
- The producer's polynomial data are given in `u` (`cover2_fit.rotate`). Equivalently, the kernel seeds its jets with
  `c + M u`.

The rational cell data (`c`, `h`, `a`, `b`) are those of `cover2-plan-*.json`:
- `Λ`: centre `(Λlo + Λhi)/2`, half-width `(Λhi − Λlo)/2 + d`;
- `ξ_c`: the slab's centre and half-width;
- `η_c`: centre 0, half-width `1/500`;
- `(ξ_b, η_b)`:
  - frame `(a, b) = (1 − t², 2t)/(1 + t²)`, with `t` a rational `tan(φ/2)` to `10⁻⁶`;
  - centre `(R/2)(a, b)`;
  - half-widths `R/2` (radial) and `h_t ≥ τR/√(1 + τ²)` (tangential, rounded up to `10⁻⁶`).
- Disc slab: frame `(1, 0)`, centre 0, half-widths `R`.

The rational cells differ from the float64 cells of HD11964-CELLS by at most `10⁻⁶` in the frames and half-widths.
Their largest `ρ_eff` is 0.200214 for `κ = 0.2` (float64: 0.200213), so the float64 margins stand.

## Checks

- **Draft.**
  - `CoverDraft.lean` elaborates: `lake env lean`, exit 0, no output, 5 s, 3.7 GB peak under the 4 GB cap.
  - Lines ≤ 100. Module header, docstrings on every definition and field.
- **Kernel evaluation of `CoverPlan.ok`** (`decide +kernel`):
  - the empty plan → `false`;
  - a one-slab disc plan → `true`;
  - a 4-wedge fan with Pythagorean frames `(3/5, 4/5)` → `true`;
  - the same fan with a too-small tangential half-width → `false`;
  - the generated 50-cell and 57-cell plans → `true`. About 5 s each, 4.04 GB peak: just under the cap, because
    the import of `HD11964.NoCrossing` dominates.
- **Exact check in Python** (`cover2_plan_lean.py`, fractions): the same conditions, OK for both plans.
- **A false alarm, recorded.** A first sanity plan failed under `decide +kernel` with a "reduction got stuck at
  `Rat` …" message. The test data were wrong (`Cmax = 7/500`, not 7/250, and a `Λ_c` half-width too small). The
  "stuck" text is the elaborator's diagnostic after the kernel evaluated the check to `false`; rational literals
  such as `1/500` reduce fine in the kernel, in module and non-module files (checked separately).

## Owner questions

1. **50 or 57 cells.** The ruling's numbers (50 cells, 5.9, 0.46) are those of the plain `κ = 0.2` plan, while its
   wording ("multiple of 4") names the 57-cell plan (6.03, 0.52).
   - The refined step 3 makes multiples of 4 unnecessary, and both plans pass `decide +kernel`.
   - Taken: both generated and checked. I recommend the 50-cell plan, which is cheaper and the one the ruling's
     numbers describe.
2. **Cell format** (for kamx-hd-layer): the rational `AffineCell` and `toSet` above (every angle), the per-cell
   statement on `k.toSet ∩ region d`, and the plan data as `CoverPlan`. Its confirmation fixes the Lean data format.
3. **Where the lemma lives.** It would be `applications/hd11964/HD11964/Cover.lean` (application side; it uses
   `HD11964.region`). The generic chain and wedge lemmas could go to the core (`KAM/Application/LambdaDrift/`) if
   other applications want affine covers.
   - Taken: application side.
4. **The bridge's `hη`, `hG` after the cover.** The rotation lemmas need `F` rotation-invariant on `O`
   (`hFrot`; AUDIT-HD11964-P2B-1's forward note). This is separate from the cover lemma, and still open.

## Resume after reboot

- **Committed** (this handoff's commit):
  - `scripts/cover2_plan_lean.py`;
  - `validation/cover2-plan-k0.2-d2e-3.json` (50 cells) and `cover2-plan-k0.2-n4-d2e-3.json` (57 cells), the exact
    rational plans;
  - this handoff, with the draft verbatim.
- **Scratch Lean** (not in git) is in `~/kam-data/hd11964/coverlemma/`:
  - `CoverDraft.lean`, the draft;
  - `CoverDraftTest.lean`, the sanity plans;
  - `CoverDraftFit1.lean` and `CoverDraftFit4.lean`, the draft plus the generated plans and
    `example : fitPlan.ok = true := by decide +kernel`;
  - `fitPlan-n*.lean`.
- **To re-check**, from `applications/hd11964` (one process, 4 GB cap, about 5 s):
  `lake env lean ~/kam-data/hd11964/coverlemma/CoverDraftFit1.lean`.
- **To regenerate a plan:**
  `python3 -I applications/hd11964/scripts/cover2_plan_lean.py OUT.lean OUT.json --d=2e-3 --kappa=0.2 [--nmult=4]`.
- **Next:**
  - the cell-format agreement (owner question 2);
  - then `HD11964/Cover.lean`: the definitions above, steps 0–4, `coversReps_of_ok`, and
    `fitPlan.ok = true := by decide +kernel`.
