# Track SO: freeze proposal (for owner review)

**Status: PROPOSAL ONLY. Nothing is frozen.** Overnight ruling D29 ("No new statement is frozen") holds. This
document creates no file under `KAM/Frozen/`, `manifest/` or `KAM/Provider/` and changes no landed Lean file. The
anchor texts below are shown here for review; they are not written under `KAM/Frozen/`.

Prepared 2026-10-30 (package SO-FREEZE-PREP) on branch `inp-sofreeze`, at `inp` commit `2267da3f`. Sources:
D30 and the plan [`SPIN-ORBIT-PLAN.md`](../../campaign/design/SPIN-ORBIT-PLAN.md) (rulings O1–O5); the proposal
[`lunar-spin-orbit-certificate-proposal.md`](../../explorations/lunar-spin-orbit-certificate-proposal.md) §2–§3;
the design [`SO-LEAN-DESIGN.md`](design/SO-LEAN-DESIGN.md) (§6, the O1 and O5 rows); the draft signatures
`.drafts/design/SOSignaturesLunar.lean` §I.6; the landed modules `KAM/SpinOrbit/{Model,Barrier,LunarAssembly}.lean`
and `KAM/Certificate/{Defs,Soundness}.lean`.

## 0. Summary of recommendations

1. Freeze **two theorems**: `KAM.SpinOrbit.lunar_spin_confinement` (the headline, Theorem B) and
   `KAM.SpinOrbit.lunar_barriers` (Theorem A, continuous form). Both texts are taken verbatim from the draft
   signatures §I.6 and are identical to the conclusions of the landed parametric assembly
   (`lunar_barriers_of`, `lunar_spin_confinement_of`).
2. Freeze **ten definitions** with them, each in its own file: `soEcc`, `soEps`, `soCoeffPoly`, `soA`, `soModes`,
   `soV`, `soField`, `SoBarrier`, `lunarPLo`, `lunarPHi`. Only `SoBarrier` changes shape: its `invariant` field
   is written out instead of citing the unfrozen `KAM.ODE.IsInvariantSet`, because frozen files import only
   Mathlib and `KAM.Frozen.*` (precedent: every existing frozen file). The probe shows the written-out form and
   the landed form convert both ways field by field.
3. **Do not freeze the checker's soundness theorem now** (`checkTorusCertificate_sound` with `TorusCertificate`,
   `checkTorusCertificate`, `CertifiedTorus`). Revisit after SO-DATA fixes the data format (question Q4).
4. `lunarPLo`, `lunarPHi` must be literal rationals set by SO-DATA from the certified graph bounds before the
   freeze; the draft value `982/1000`, `1018/1000` is a placeholder used only to elaborate.

## 1. Candidate anchors (exact Lean text)

Common header of every file below (as in `KAM/Frozen/Iso/Defs/IsHamiltonianSolutionOn.lean`):

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
```

Proposed directory: `KAM/Frozen/SpinOrbit/{Defs,Theorems}/` (namespace `KAM.SpinOrbit`, as landed). Below, each
file is shown without the copyright header and without its module docstring. The import lists are exact. One
complete definition file, in the shape of the precedent, looks like this:

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Basic.Real.Basic

/-!
# Frozen definition `KAM.SpinOrbit.soEcc`

Owner-approved on <date> (decision D<k>). This file is frozen: it is hashed in
`manifest/frozen-anchors.json`; any change needs an owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

/-- The eccentricity `e_* = 549/10000` of the lunar model. -/
def soEcc : ℝ := 549 / 10000

end KAM.SpinOrbit

end
```

Definition files carry no FROZEN_ANCHOR markers (precedent: `KAM/Frozen/Iso/Defs/*.lean`). Theorem files carry
the copyright header before `-- FROZEN_ANCHOR_PREFIX_BEGIN`, as in `AllTimeConfinement.lean`.

### 1.1 `KAM/Frozen/SpinOrbit/Defs/SoEcc.lean`

```lean
module

public import Mathlib.Basic.Real.Basic

@[expose] public noncomputable section

namespace KAM.SpinOrbit

/-- The eccentricity `e_* = 549/10000` of the lunar model. -/
def soEcc : ℝ := 549 / 10000

end KAM.SpinOrbit

end
```

### 1.2 `KAM/Frozen/SpinOrbit/Defs/SoEps.lean`

```lean
module

public import Mathlib.Basic.Real.Basic

@[expose] public noncomputable section

namespace KAM.SpinOrbit

/-- The asphericity parameter `ε_* = 69/200000` (`ε = (3/2)(B − A)/C`) of the lunar model. -/
def soEps : ℝ := 69 / 200000

end KAM.SpinOrbit

end
```

### 1.3 `KAM/Frozen/SpinOrbit/Defs/SoCoeffPoly.lean`

```lean
module

public import Mathlib.Algebra.Field.Basic

@[expose] public noncomputable section

namespace KAM.SpinOrbit

/-- The coefficient polynomials `A_m(e)` of the model (zero outside `1 ≤ m ≤ 7`); `A_m = W(m/2, e)/2`
in Celletti's notation (eq. (7.55)). -/
def soCoeffPoly {R : Type*} [Field R] (e : R) : ℕ → R
  | 1 => -e / 4 + e ^ 3 / 32
  | 2 => 1 / 2 - 5 * e ^ 2 / 4 + 13 * e ^ 4 / 32
  | 3 => 7 * e / 4 - 123 * e ^ 3 / 32
  | 4 => 17 * e ^ 2 / 4 - 115 * e ^ 4 / 12
  | 5 => 845 * e ^ 3 / 96 - 32525 * e ^ 5 / 1536
  | 6 => 533 * e ^ 4 / 32
  | 7 => 228347 * e ^ 5 / 7680
  | _ => 0

end KAM.SpinOrbit

end
```

### 1.4 `KAM/Frozen/SpinOrbit/Defs/SoA.lean`

```lean
module

public import KAM.Frozen.SpinOrbit.Defs.SoEcc
public import KAM.Frozen.SpinOrbit.Defs.SoCoeffPoly

@[expose] public noncomputable section

namespace KAM.SpinOrbit

/-- `A_m(e_*)` as a real number. -/
def soA (m : ℕ) : ℝ := soCoeffPoly soEcc m

end KAM.SpinOrbit

end
```

### 1.5 `KAM/Frozen/SpinOrbit/Defs/SoModes.lean`

```lean
module

public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace KAM.SpinOrbit

/-- The index set `{1, …, 7}` of the seven forcing modes. -/
def soModes : Finset ℕ := Finset.Icc 1 7

end KAM.SpinOrbit

end
```

### 1.6 `KAM/Frozen/SpinOrbit/Defs/SoV.lean`

```lean
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import KAM.Frozen.SpinOrbit.Defs.SoEps
public import KAM.Frozen.SpinOrbit.Defs.SoA
public import KAM.Frozen.SpinOrbit.Defs.SoModes

@[expose] public noncomputable section

open Real

namespace KAM.SpinOrbit

/-- The period-one potential `V(q, φ) = -ε_* Σ_{m=1}^7 A_m(e_*) cos (2π (2q - mφ))`
(`q` spin angle, `φ` orbital phase, both in turns). -/
def soV (q φ : ℝ) : ℝ :=
  -soEps * ∑ m ∈ soModes, soA m * Real.cos (2 * π * (2 * q - m * φ))

end KAM.SpinOrbit

end
```

### 1.7 `KAM/Frozen/SpinOrbit/Defs/SoField.lean`

```lean
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import KAM.Frozen.SpinOrbit.Defs.SoV

@[expose] public noncomputable section

namespace KAM.SpinOrbit

/-- The physical spin–orbit vector field on `(q, p, φ)`: `q̇ = p`, `ṗ = -∂_q V`, `φ̇ = 1`.
Time is measured in orbital periods and `p` is the spin rate divided by the orbital mean motion. -/
def soField (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (x.2.1, -deriv (fun s => soV s x.2.2) x.1, 1)

end KAM.SpinOrbit

end
```

### 1.8 `KAM/Frozen/SpinOrbit/Defs/SoBarrier.lean`

```lean
module

public import Mathlib.Order.Interval.Set.OrdConnected
public import KAM.Frozen.SpinOrbit.Defs.SoField

@[expose] public noncomputable section

namespace KAM.SpinOrbit

/-- An invariant barrier graph `p = P(q, φ)` of the physical flow with values in `[lo, hi]`:
continuous, 1-periodic in both angles, and invariant (a solution on an interval that meets the
graph once stays on it). -/
structure SoBarrier (lo hi : ℝ) where
  P : ℝ → ℝ → ℝ
  continuous : Continuous fun x : ℝ × ℝ => P x.1 x.2
  periodic_q : ∀ q φ, P (q + 1) φ = P q φ
  periodic_φ : ∀ q φ, P q (φ + 1) = P q φ
  invariant : ∀ (J : Set ℝ) (y : ℝ → ℝ × ℝ × ℝ), J.OrdConnected →
    (∀ t ∈ J, HasDerivAt y (soField (y t)) t) →
    ∀ t₁ ∈ J, (y t₁).2.1 = P (y t₁).1 (y t₁).2.2 → ∀ t ∈ J, (y t).2.1 = P (y t).1 (y t).2.2
  lower : ∀ q φ, lo ≤ P q φ
  upper : ∀ q φ, P q φ ≤ hi

end KAM.SpinOrbit

end
```

Deviation from the landed `KAM.SpinOrbit.SoBarrier` (D-SOF-1): the landed field is
`invariant : KAM.ODE.IsInvariantSet soField Set.univ {x | x.2.1 = P x.1 x.2.2}`. Unfolded, `IsInvariantSet` with
`W = univ` reads `IsSolutionIn soField univ J y = ∀ t ∈ J, y t ∈ univ ∧ HasDerivAt y (soField (y t)) t`; the
written-out field drops the trivial `y t ∈ univ`. The two structures convert both ways by one-line bridges
(probe 2, §3), so the landed proofs are reused unchanged.

### 1.9–1.10 `KAM/Frozen/SpinOrbit/Defs/LunarPLo.lean`, `LunarPHi.lean`

```lean
module

public import Mathlib.Data.Rat.Init

@[expose] public section

namespace KAM.SpinOrbit

/-- Lower end of the certified initial momentum window (ruling O1). -/
def lunarPLo : ℚ := <LITERAL set by SO-DATA>      -- probe placeholder: 982 / 1000

end KAM.SpinOrbit

end
```

and identically `def lunarPHi : ℚ := <LITERAL set by SO-DATA>` (probe placeholder `1018 / 1000`). The literals
must satisfy, with the certified graph bounds of the two certificates, the five band inequalities that are the
hypotheses of the landed `lunar_barriers_of`: `967/1000 ≤ gL.pLo − dispL`, `gL.pHi + dispL < lunarPLo`,
`lunarPLo < lunarPHi`, `lunarPHi < gU.pLo − dispU`, `gU.pHi + dispU ≤ 1033/1000`.

### 1.11 `KAM/Frozen/SpinOrbit/Theorems/LunarBarriers.lean` (Theorem A)

```lean
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import KAM.Frozen.SpinOrbit.Defs.SoBarrier
public import KAM.Frozen.SpinOrbit.Defs.LunarPLo
public import KAM.Frozen.SpinOrbit.Defs.LunarPHi
import KAM.Provider.SpinOrbit.LunarBarriers

/-! # Frozen theorem `KAM.SpinOrbit.lunar_barriers` (docstring as in the precedent) -/

@[expose] public section

namespace KAM.SpinOrbit

/-- **Theorem A (continuous form).** In the seven-mode lunar spin–orbit model there are two invariant
continuous barrier graphs with values in the band `[0.967, 1.033]`, the lower one strictly below the
window end `lunarPLo` and the upper one strictly above `lunarPHi`. -/
theorem lunar_barriers :
    ∃ (Bm : SoBarrier (967 / 1000) (1033 / 1000)) (Bp : SoBarrier (967 / 1000) (1033 / 1000)),
      (∀ q φ, Bm.P q φ < Bp.P q φ) ∧
      (∀ q φ, Bm.P q φ < lunarPLo) ∧ (∀ q φ, (lunarPHi : ℝ) < Bp.P q φ) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.SpinOrbit

end
-- FROZEN_ANCHOR_SUFFIX_END
```

### 1.12 `KAM/Frozen/SpinOrbit/Theorems/LunarSpinConfinement.lean` (Theorem B, the headline)

```lean
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import KAM.Frozen.SpinOrbit.Defs.SoField
public import KAM.Frozen.SpinOrbit.Defs.LunarPLo
public import KAM.Frozen.SpinOrbit.Defs.LunarPHi
import KAM.Provider.SpinOrbit.LunarSpinConfinement

/-! # Frozen theorem `KAM.SpinOrbit.lunar_spin_confinement` (docstring as in the precedent) -/

@[expose] public section

namespace KAM.SpinOrbit

/-- **Theorem B.** In the seven-mode lunar spin–orbit model, every initial state `(q₀, p₀, φ₀)` with
`lunarPLo < p₀ < lunarPHi` (any angles) has a global solution, unique among global solutions, and its
spin rate satisfies `|p(t) − 1| ≤ 33/1000` for all real `t`. -/
theorem lunar_spin_confinement (q₀ p₀ φ₀ : ℝ) (hp : (lunarPLo : ℝ) < p₀ ∧ p₀ < lunarPHi) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).2.1 - 1| ≤ 33 / 1000) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.SpinOrbit

end
-- FROZEN_ANCHOR_SUFFIX_END
```

Theorem B's definition closure is `soField` and below plus the two window literals; it does **not** contain
`SoBarrier`. The headline therefore does not depend on the barrier notion at all: a reader checks only the model
(1.1–1.7), the window and the conclusion.

### 1.13 Freezing the general checker? Recommendation: not now

Candidate: `KAM.Certificate.checkTorusCertificate_sound` (landed, axioms clean), with `TorusCertificate`,
`CertParams`, `checkTorusCertificate`, `FreqEncloses`, `CertifiedTorus`, the classes `CertArith`,
`LawfulCertArith`, and transitively `HamExpr`, `CertEmbedding`, `Witnesses`, `ModelConfig`, `PiEnclosure`, every
sub-check, and `Iso.Apost.isoC2`.

- **For freezing.** It is the reusable product of D30 ("the black box"); a frozen, sealed soundness theorem lets
  later clients cite it as a trusted interface; its conclusion `CertifiedTorus` is a clean restatement of the
  sealed `g1_explicit` body.
- **Trust.** Once A and B are sealed through the checker, the kernel already checks the whole chain. Freezing
  soundness would add a reusable interface, not more trust in the lunar results.
- **Against (decisive now).** (a) The *statement* of soundness includes `checkTorusCertificate` itself: a frozen
  statement freezes the entire checker code (several thousand lines and the data format), which SO-DATA may still
  have to change (packaging, O5 advice shards). (b) Soundness is a proof step of Theorems A/B, not a claim about the
  Moon; the lunar results are already self-contained and sound without it. (c) The trust content of soundness is
  `CertifiedTorus`, whose closure includes `TorusCertificate.H`/`.K` denotations (`HamExpr.eval`,
  `CertEmbedding.eval`): an audit of those is a separate, larger statement audit. (d) `LawfulCertArith` is a class
  premise of the theorem; freezing it freezes the arithmetic interface laws.
- **Recommended path.** After SO-DATA lands and the format is stable, freeze a *versioned* v1 of the black box
  as a separate decision, with its own statement audit of `HamExpr.eval` and `CertEmbedding.eval`.

## 2. Refute-first statement audit

Source claim (D30, plan, proposal §1–§3): in the explicit conservative seven-mode lunar spin–orbit model of
proposal §2 (Celletti (7.55)), the spin rate `p` (spin angular velocity / orbital mean motion) of every solution
starting in an explicit region stays within 3.3 % of 1 for all time, i.e. `|p(t) − 1| ≤ 33/1000` for every real
`t`; the region is the constant momentum window of O1; the proof goes through two invariant tori of frequencies
`ν± = 1 ± 1/(40 + g)`, used as barriers.

### 2.1 Definitions

| Item | Check | Verdict |
|---|---|---|
| `soEcc = 549/10000`, `soEps = 69/200000` | Proposal §2.3 verbatim. `ε = (3/2)(B−A)/C ≈ 3.45·10⁻⁴` matches the lunar `(B−A)/C ≈ 2.3·10⁻⁴`. Real literals: `549/10000 : ℝ` is the real quotient, exact. | PASS |
| `soCoeffPoly` | Table of proposal §2.3, term by term (seven rows compared). `A_m = W(m/2,e)/2` (e.g. `A_2 = 1/2 − 5e²/4 + 13e⁴/32`, `W(1,e) = 1 − 5e²/2 + 13e⁴/16`). Junk value `0` outside `1..7` is never used (`soModes`). Generic over a field so the rational twin `soAQ` (unfrozen) shares the text. | PASS |
| `soModes = Finset.Icc 1 7` | All seven terms, nothing more (proposal: "All seven terms are part of the definition"). | PASS |
| `soV` | `V(q,φ) = −ε Σ A_m cos(2π(2q − mφ))`, verbatim; `m` is cast `ℕ → ℝ`. | PASS |
| `soField` | `(q, p, φ) ↦ (p, −∂_q V, 1)`. **Misreading risk:** `deriv` returns 0 where not differentiable; `soV` is entire in `q`, so this is the true partial derivative (landed `soField_eq`: `= (p, −4πε Σ A_m sin(2π(2q − mφ)), 1)`). **Units:** angles in turns, time in orbital periods (`φ̇ = 1`); with `x = 2πq`, `s = 2πt`: `d²x/ds² = −2ε Σ A_m sin(2x − mM) = −ε Σ W(m/2,e) sin(2x − mM)`, Celletti's radian equation; `dx/ds = p`, so `p` is the spin/mean-motion ratio in both conventions and the 3.3 % band is unit-free. **Autonomy:** `φ` is a state variable with `φ̇ = 1`, so `φ(t) = φ₀ + t`; the non-autonomous system is recovered exactly. | PASS (note N1) |
| `SoBarrier lo hi` | Continuous, doubly 1-periodic, invariant graph `p = P(q,φ)` in `[lo, hi]`. Invariance is two-sided (any order-connected `J`, both time directions). It does not demand the graph be a KAM torus or analytic (O4). | PASS (A only) |
| `lunarPLo`, `lunarPHi` | Must be literals (O1). Placeholder status now. **Vacuity risk:** if `lunarPLo ≥ lunarPHi`, Theorem B is vacuous. Mitigation: the literals are visible in the frozen file, and Q2 recommends freezing `lunarPLo_lt_lunarPHi` as an extra anchor or asserting it in the anchor docstring. | PENDING (SO-DATA) |

### 2.2 Theorem B `lunar_spin_confinement` (binder by binder)

- `q₀ φ₀ : ℝ` — arbitrary real initial angles (no reduction mod 1 needed; `V` is 1-periodic). Source: "any (q, φ)"
  (O1). Not a restriction.
- `p₀ : ℝ`, `hp : lunarPLo < p₀ ∧ p₀ < lunarPHi` — **the only premise**. It is the initial region of ruling O1
  (a constant momentum window), so it is a source premise and not a proof step. It is a rectangle strictly
  *inside* the region between the two barriers, not that whole region (Theorem A gives
  `Bm < lunarPLo` and `lunarPHi < Bp` at every angle). **Deviation D-SOF-2 (O1):** source §3.2 uses the
  graph-defined region `{Q₋ + d₋ < p < Q₊ − d₊}`. The frozen window is a subset of it, so the statement is weaker
  and still sound. The inequalities are strict, so the window is open.
- Conclusion 1: `z 0 = (q₀,p₀,φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t` — a **global** classical solution on all
  of `ℝ` (both time directions), carrier `ℝ × ℝ × ℝ` with the product (sup) norm; `HasDerivAt` of a product-valued
  map is componentwise, so this is the ODE system exactly.
- Conclusion 2: `∀ t, |(z t).2.1 − 1| ≤ 33/1000` — `(z t).2.1` is `p(t)` (component order `(q, p, φ)`);
  `33/1000 : ℝ`. Non-strict `≤` while the proof gives strict; weaker, faithful to "within 3.3 %".
- Conclusion 3: uniqueness among **global** solutions with the same initial value. Weaker than uniqueness among
  local solutions; it is what the source states ("a global existence, uniqueness ... theorem"), and local
  uniqueness follows from `soField` being C¹ (landed `soField_contDiff`) anyway. Noted as N2.
- Nothing about the angles' behaviour (no libration claim): the source explicitly disclaims libration (§2.1).

### 2.3 Theorem A `lunar_barriers`

- No binders. Existence of two `SoBarrier`s in `[967/1000, 1033/1000]`, ordered (`Bm < Bp` pointwise), with
  `Bm < lunarPLo` and `lunarPHi < Bp` at every angle. This is the source Theorem A in **continuous form** (O4:
  analyticity, the conjugacy and the frequencies `ν±` are not part of the statement). **Misreading risk N3:** the
  statement does not say the barriers are KAM tori, carry quasi-periodic motion with frequency `(ν±, 1)`, or are
  analytic; it says only what confinement needs. The KAM content is in the proof (the certificates), not the
  statement. If the owner wants the frequency in the statement, see Q3.
- **Deviation D-SOF-3 (D30):** source Theorem A (proposal §3.1) has the band `97/100 ≤ P₋ < P₊ ≤ 103/100`.
  The anchor uses `[967/1000, 1033/1000]`, the 3.3 % band of D30, because the pilot showed the 3 % band fails.
- **Invariance scope (note N6).** `SoBarrier.invariant` covers every solution on an order-connected interval `J`
  that meets the graph at some time in `J`, in both time directions. It is not phrased through a global flow.
  Global existence is a separate conclusion of Theorem B.
- The band `[0.967, 1.033]` is closed (`lower`/`upper` are `≤`); the pilot extrema `0.968007`, `1.031992` leave
  about 0.001 of headroom each side.

### 2.4 Global reading notes (for the docstrings and the release text)

- **N0 (model, not the Moon).** Both theorems are about this exact truncated conservative model with exact rational
  parameters: no tides, no neglected Fourier modes beyond `m = 7`, no higher-order eccentricity terms, no
  orbital variations, spin axis perpendicular to the orbit, no observational uncertainty in `e`, `ε`. They do not
  assert anything about the real Moon. Proposal §2.1 says so; the docstrings must say "in the seven-mode lunar
  spin–orbit model".
- **N1 (time scale).** `t` counts orbital periods (one sidereal month in the model's Keplerian orbit); "for all
  `t ∈ ℝ`" is an all-time statement in the model.
- **N2 (uniqueness).** Uniqueness is stated among global solutions (see 2.2).
- **N4 (rotated frame O5).** The certificates live in the rotated frame `Q1 = q − φ`, `P1 = p`; the frozen
  statements never mention the frame (the transfer is a proof step, landed in `Rotated.lean`/`Graph/Cert`).
- **N5 (3 % vs 3.3 %).** The proposal's original target was 3 %; D30 fixed 3.3 % after the pilot showed 3 % fails
  numerically. The text uses `33/1000`.

### 2.5 Premises inventory

| Theorem | Premise | Kind | Why it is not a proof step |
|---|---|---|---|
| B | `hp : lunarPLo < p₀ < lunarPHi` | source region (O1) | defines the set of initial data the claim is about |
| A | none | — | — |
| all | `soEcc`, `soEps`, `soCoeffPoly`, `soModes` literals | source model (§2.3) | they *are* the model |

The landed parametric theorems have many more premises (`checkTorusCertificate … = true`, `FreqEncloses`, band
inequalities): these are discharged by SO-DATA's kernel-checked data theorems and never appear in the frozen text.
`IsDiophantine` is discharged by the landed `lunarRotFreq{Minus,Plus}_isDiophantine` (SO-DIO).

## 3. Elaboration evidence

Three untracked probes in `.lake/abi-scratch/` (deleted afterwards), run with `nice -n 5 lake env lean` against the
landed build of `inp@2267da3f`:

1. `SoFreezeProbe.lean` imports `KAM.SpinOrbit.LunarAssembly` and `KAM.Certificate.Soundness`, re-elaborates
   1.1–1.8 (with the landed `IsInvariantSet` field) and both theorems in a probe namespace, and checks
   `soEcc`, `soEps`, `soCoeffPoly`, `soA`, `soModes`, `soV`, `soField` against the landed names by `rfl`, `SoBarrier`
   by field-wise conversion both ways, and Theorem B's text by
   `KAM.SpinOrbit.lunar_spin_confinement_of pLo pHi hB q₀ p₀ φ₀ hp` (accepted: the frozen conclusion is exactly
   the landed conclusion, with the probe `soField` unifying definitionally with the landed one). Output:

   ```
   SoFreezeProbe.lean:69:8: warning: declaration uses `sorry`     -- lunar_barriers (expected placeholder)
   SoFreezeProbe.lean:74:8: warning: declaration uses `sorry`     -- lunar_spin_confinement (expected placeholder)
   'SoFreezeProbe.lunar_spin_confinement_landed' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.SpinOrbit.lunar_barriers_of' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.SpinOrbit.lunar_spin_confinement_of' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Certificate.checkTorusCertificate_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'SoFreezeProbe.lunar_barriers' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
   ```
2. `SoFreezeProbe2.lean`: the written-out `SoBarrier` (1.8) with bridges `ofLanded`/`toLanded` to the landed
   structure. Elaborates with no output (rc 0).
3. `SoFreezeProbe3.lean`: one `module` file with **only Mathlib imports** that contains the declarations of
   1.1–1.12 verbatim under `KAM.SpinOrbit` (placeholder literals `982/1000`, `1018/1000`). This shows the frozen
   closure is self-contained in Mathlib. Output: two expected `sorry` warnings (the theorem placeholders), rc 0.
4. Per-file import checks (after the review). `SoEcc` and `SoModes` each elaborate with only their own import, rc 0.
   The definition chain through `SoBarrier`, plus `lunarPLo`, elaborates with only the union of the listed Mathlib
   imports, together with `lunarPLo < 1018/1000` by `decide +kernel`, rc 0. The reviewer separately checked
   `LunarPLo` and `SoCoeffPoly` alone. The first run warned that `Mathlib.Data.Real.Basic` is deprecated in favour
   of `Mathlib.Basic.Real.Basic`; the import lists above now use the new name, which elaborates with no warning.
   Remaining step: at freeze time, build every frozen file through the gate with its real frozen imports.

Placeholder status: Theorems A and B have no proof yet; they are sealed by `lunar_barriers_of` /
`lunar_spin_confinement_of` applied to SO-DATA's data theorems (`lunar{Lower,Upper}Cert_{ham,params,passes,freq}`,
`lunar{Lower,Upper}Graph_passes`) and the band inequalities by `decide +kernel` or `norm_num`. Plain `decide` gets stuck on ℚ division literals. The parametric assembly's axioms are the
standard three.

Implementation consequence at freeze time (not done here): `KAM/SpinOrbit/Model.lean` imports the frozen
definitions instead of defining `soEcc`…`soField`, and `Barrier.lean` keeps its `IsInvariantSet` barrier as an
internal notion with the bridge of probe 2 (or switches to the frozen structure).

## 4. Proposed manifest entries (shape; hashes TBD)

One entry per file, `state: "AUTHOR_APPROVED"` at freeze, `"SEALED"` after the provider lands. Example for B:

```json
{
  "id": "spinorbit.d<k>.lunar_spin_confinement.v1",
  "kind": "theorem",
  "author_approval": {
    "approved_by": "Scott Armstrong",
    "approved_at": "TBD",
    "approval_ref": "owner reply to the SO freeze review page; docs/DECISIONS.md D<k>",
    "approval_version": "1"
  },
  "source": {
    "revision": "KAM@<inp sha> docs/tracks/SO/FREEZE-PROPOSAL.md; .drafts/design/SOSignaturesLunar.lean §I.6 (sha256 TBD)",
    "range": "proposal §3 Theorem B with D30 (33/1000) and O1 (constant window); Celletti (7.55)"
  },
  "contract": { "id": "spinorbit.lunar_spin_confinement", "version": "1" },
  "path": "KAM/Frozen/SpinOrbit/Theorems/LunarSpinConfinement.lean",
  "export": "KAM.SpinOrbit.lunar_spin_confinement",
  "split_policy": { "source_group": "spinorbit.lunar", "mode": "NOT_SPLIT", "ruling_ref": "docs/DECISIONS.md D<k>" },
  "abi_sha256": "TBD",
  "definition_closure": [
    { "path": "KAM/Frozen/SpinOrbit/Defs/SoEcc.lean", "sha256": "TBD" },
    { "path": "KAM/Frozen/SpinOrbit/Defs/SoEps.lean", "sha256": "TBD" },
    { "path": "KAM/Frozen/SpinOrbit/Defs/SoCoeffPoly.lean", "sha256": "TBD" },
    { "path": "KAM/Frozen/SpinOrbit/Defs/SoA.lean", "sha256": "TBD" },
    { "path": "KAM/Frozen/SpinOrbit/Defs/SoModes.lean", "sha256": "TBD" },
    { "path": "KAM/Frozen/SpinOrbit/Defs/SoV.lean", "sha256": "TBD" },
    { "path": "KAM/Frozen/SpinOrbit/Defs/SoField.lean", "sha256": "TBD" },
    { "path": "KAM/Frozen/SpinOrbit/Defs/LunarPLo.lean", "sha256": "TBD" },
    { "path": "KAM/Frozen/SpinOrbit/Defs/LunarPHi.lean", "sha256": "TBD" }
  ],
  "implementation": {
    "module": "KAM.Provider.SpinOrbit.LunarSpinConfinement",
    "export": "KAM.Provider.SpinOrbit.lunar_spin_confinement"
  },
  "state": "AUTHOR_APPROVED",
  "prefix_sha256": "TBD",
  "suffix_sha256": "TBD",
  "draft_allowlist": { "frozen_paths": [], "audit_paths": [] }
}
```

`lunar_barriers` is the same with closure `+ SoBarrier.lean`. Definition entries follow `kam.actionNbhd.v1`:
`kind: "definition"`, `definition_closure` = their frozen imports, `full_file_sha256: "TBD"`, no
`implementation`.

## 5. Open questions for the owner (with recommendations)

- **Q1. Which theorems to freeze?** Recommended: both A and B (B is the headline; A records the barrier content).
  Alternative: B only (smallest trusted surface: no `SoBarrier`).
- **Q2. Window literals and nonvacuity.** Recommended: SO-DATA picks literals with at least `10⁻⁴` margin inside the
  certified gap, rounded to short decimals (e.g. `9819/10000`, `10181/10000` if certified); also freeze
  `lunarPLo_lt_lunarPHi : lunarPLo < lunarPHi` (proved by `decide +kernel` or `norm_num`; plain `decide` gets
  stuck on ℚ division literals) as a third theorem anchor, so non-vacuity is
  part of the frozen surface rather than a reader's arithmetic.
- **Q3. Frequencies in Theorem A?** Recommended: no (O4 keeps analytic/quasi-periodic content out of v1); a later
  corollary can add "the barrier is the graph of an invariant torus with rotation vector `(ν±, 1)`".
- **Q4. Freeze the black box now?** Recommended: no; versioned freeze after SO-DATA (§1.13).
- **Q5. `SoBarrier` form.** Recommended: the written-out invariance (1.8) over freezing `KAM.ODE.IsSolutionIn` and
  `IsInvariantSet` as two more frozen definitions (the precedent forbids frozen files importing implementation).
- **Q6. Coefficient split.** Recommended: keep `soCoeffPoly` generic over a field and `soA` separate (matches the
  landed code, so the provider is `rfl`). Alternative: inline the seven numeric values into `soV`; shorter closure
  but loses the visible correspondence with the proposal's table.
- **Q7. Uniqueness among global solutions only.** Recommended: keep (source wording, landed proof).
  Alternative: strengthen to local uniqueness on any open interval containing 0, at small extra proof cost.

## 6. Independent refutation pass

A fresh Opus subagent was asked to refute §1–§2, read-only, with Lean probes in scratch. It reported **no HIGH
finding**: neither theorem is false, vacuous or trivially true. Its findings and the resolutions:

| # | Sev. | Finding | Resolution |
|---|---|---|---|
| 1 | MED | "proved by `decide`" is wrong: `decide` gets stuck on `(982/1000 : ℚ) < 1018/1000`; `decide +kernel` and `norm_num` work | Fixed in §3 and Q2; confirmed by probe 4 |
| 2 | LOW | Probe 3 combined all files, so it did not test each file's own import list | Probe 4 added (§3); deprecated import renamed; gate build of every file at freeze time |
| 3 | LOW | The band change `97/100…103/100` → `967/1000…1033/1000` was not recorded as a deviation from source Theorem A | Added as D-SOF-3 (§2.3) |
| 4 | LOW | §2.2 said the window is "exactly" the region between the barriers; it is a smaller rectangle (O1 deviation from source §3.2) | Reworded; recorded as D-SOF-2 |
| 5 | LOW | Definition files were shown without a module docstring | One complete definition file is now shown (§1) |
| 6 | NOTE | "Two-sided invariance" holds only for solutions on intervals, not for a global flow | Added as N6 (§2.3) |
| 7 | NOTE | Not freezing soundness is right; once A and B are sealed, freezing it adds a reusable interface, not more trust in the Moon results | Adopted in §1.13 |

Claims the reviewer tried and failed to refute:
- the 2π unit conversion, including Celletti's `A_m = W(m/2,e)/2`;
- the sign of the force;
- the `deriv` junk value;
- all seven coefficient rows and both parameters;
- the component order `(q, p, φ)`;
- equivalence of the written-out `SoBarrier.invariant` with the landed form;
- textual identity of A and B with the landed parametric conclusions;
- B's closure excluding `SoBarrier`;
- non-triviality of A (no constant graph is invariant, since `∂_q V ≢ 0`);
- strict vs non-strict inequalities, the scope of uniqueness, and the angle binders.

The one item it could not settle is B's non-vacuity, which waits on the SO-DATA literals (Q2).

### Deviations introduced by this proposal (for the errata/deviation ledger)

- **D-SOF-1:** `SoBarrier.invariant` is written out instead of citing `KAM.ODE.IsInvariantSet`. It is equivalent
  (probe 2).
- **D-SOF-2:** O1's constant window replaces the graph-defined region of source §3.2 (owner ruling O1).
- **D-SOF-3:** the 3.3 % band replaces the source's 3 % (owner ruling D30).

No suspected erratum in a pinned source was found.
