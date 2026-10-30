# Track SO: freeze proposal 2, the sharp route at N = 65 (for owner review)

**Status: PROPOSAL ONLY. Nothing is frozen.** This document creates no file under `KAM/Frozen/`, `manifest/` or
`KAM/Provider/` and changes no landed Lean file. The anchor texts below are shown for review only.

Prepared 2026-10-30 (package SO-FREEZE-PREP2) on branch `inp-sofreeze2`, at `inp` commit `f4953508`. It
**supersedes** [`FREEZE-PROPOSAL.md`](FREEZE-PROPOSAL.md) (SO-FREEZE-PREP, N = 40, 3.3 %) wherever the two differ;
whatever is not restated here (the manifest entry shape, the per-file header precedent, the analysis of the
black box in §1.13 there) carries over unchanged.

Sources: D36 (sharp certifier), D37 (band target 2.8–2.9 %), D38 (N = 65, band about 2.71 %; recorded on `main` at
`54d944cb`, not yet in this branch's `docs/DECISIONS.md`);
[`lunar-band-2p8-2p9.md`](../../explorations/lunar-band-2p8-2p9.md); SO-GEN3's interim study
(`inp-sogen3:docs/tracks/SO/studies/SO-GEN3.md`, commit `d89b02c7`); the landed modules
`KAM/SpinOrbit/{Model,Barrier,LunarAssemblySharp,RotFreqN}.lean` and `KAM/Certificate/QuadraticDiophantineN.lean`.

## 0. Summary of recommendations

1. Freeze **three theorems**: `lunar_spin_confinement` (Theorem B, the headline), `lunar_barriers` (Theorem A,
   continuous form) and `lunarPLo_lt_lunarPHi` (non-vacuity of the window; this was Q2 of the first proposal, now
   recommended outright). Their texts mention only the ODE and three groups of literals: the band, the window and
   the model parameters. Nothing about the certifier, the frequencies `ν±`, `N`, the parameter packages or the
   rotated frame appears in them.
2. Freeze the **same ten definitions** as the first proposal, with unchanged text: `soEcc`, `soEps`, `soCoeffPoly`,
   `soA`, `soModes`, `soV`, `soField`, `SoBarrier` (invariance written out, D-SOF-1), `lunarPLo`, `lunarPHi`.
   Only the values of the two window literals change.
3. **The band.** Theorem B concludes `|p(t) − 1| ≤ δ` with δ a literal in the statement; Theorem A has the band
   `[1 − δ, 1 + δ]` as two literals. The candidate shown is **δ = 2714/100000 (2.714 %)**, band
   `[97286/100000, 102714/100000]`: rule B of §1.4 applied to the worst case of the five-decimal interim figure
   (`M ≤ 0.027135`); on the interim figure itself (`M = 0.02713`) rule B would give `2713/100000`. The final value
   comes from the final data.
4. **The window.** Interim candidates `lunarPLo = 9933/10000`, `lunarPHi = 10067/10000`, i.e. the initial spin rate
   is within 0.67 % of synchronous. The rule that fixes them is in §1.4.
5. **Freeze only after** the final N = 65 data pass the kernel and the literals are fixed by the rules. The owner
   can approve the shape and the rules now (Q8, Q9).
6. Both frozen theorems are **instances** of the landed band-parametric theorems `lunar_barriers_of_sharp` and
   `lunar_spin_confinement_of_band`: one application each, plus small glue (three ℚ→ℝ literal-cast rewrites, the
   reshape `κ/67 = κ * (1/67)`, the positivity facts `0 < c`, `0 < κ`), and, at freeze time, the change of
   `SoBarrier` described in §4 (probe 1, §2).
7. Still do **not** freeze a certifier soundness theorem, either `checkTorusCertificate_sound` or the new
   `checkTorusCertificateSharp_sound` (Q4).
8. **Before the freeze, resolve the `SoBarrier` name clash** (refutation finding 1): the frozen
   `KAM.SpinOrbit.SoBarrier` and the landed one have the same full name, so a provider importing both cannot
   compile. Recommended: the landed `Barrier.lean` switches to the frozen structure (Q11).

### What changed from the first proposal

| Item | Proposal 1 (SO-FREEZE-PREP) | Proposal 2 (this document) | Ruling |
|---|---|---|---|
| Barrier frequencies (proof only) | `ν± = 1 ± 1/(40+g)` | `ν± = 1 ± 1/(65+g)`, `g = (√5−1)/2` | D38 |
| Certifier (proof only) | `checkTorusCertificate` (R1, about 88 digits) | `checkTorusCertificateSharp` (about 40 digits) | D36, D37 |
| Diophantine lemma (proof only) | `lunarRotFreq{Minus,Plus}_isDiophantine`, γ = κ/42 | `lunarRotFreq{Minus,Plus}N_isDiophantine_65`, γ = κ/67 | SO-DION |
| Landed assembly used by the provider | `lunar_barriers_of`, `lunar_spin_confinement_of` (literals fixed at 3.3 %) | `lunar_barriers_of_sharp`, `lunar_spin_confinement_of_band` (band, window, ν, packages all parameters) | SO-SHARPLINK |
| Theorem B bound | `≤ 33/1000` (3.3 %) | `≤ 2714/100000` (2.714 %; interim) | D38 |
| Theorem A band | `[967/1000, 1033/1000]` | `[97286/100000, 102714/100000]` (interim) | D38 |
| Window | placeholder `982/1000 … 1018/1000`; data: above 0.98212, below 1.01788 | `9933/10000 … 10067/10000` (interim); data: above 0.99322, below 1.00678 | D38 |
| Non-vacuity anchor | optional (Q2) | recommended third theorem `lunarPLo_lt_lunarPHi` | — |
| Definition texts 1.1–1.8 | — | unchanged | — |

The barriers moved toward the synchronous resonance, so **both** the band and the window shrank. The N = 65
Theorem B is therefore **not** a strengthening of the N = 40 one: its conclusion is sharper (2.714 % against 3.3 %),
but its premise covers fewer initial data (`|p₀ − 1| < 0.67 %` against `< 1.77 %`). Neither statement implies the
other. Q10 asks whether that matters.

## 1. Candidate anchors (exact Lean text)

The header precedent, the proposed directory `KAM/Frozen/SpinOrbit/{Defs,Theorems}/`, the namespace
`KAM.SpinOrbit` and the complete-file template are those of the first proposal (§1 there). As there, each file
below is shown without the copyright header and the module docstring; the import lists are exact.

### 1.1 Definitions (text unchanged from the first proposal, §1.1–§1.8)

`KAM/Frozen/SpinOrbit/Defs/SoEcc.lean`:

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

`SoEps.lean` (imports `Mathlib.Basic.Real.Basic`):

```lean
/-- The asphericity parameter `ε_* = 69/200000` (`ε = (3/2)(B − A)/C`) of the lunar model. -/
def soEps : ℝ := 69 / 200000
```

`SoCoeffPoly.lean` (imports `Mathlib.Algebra.Field.Basic`):

```lean
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
```

`SoA.lean` (imports `KAM.Frozen.SpinOrbit.Defs.SoEcc`, `KAM.Frozen.SpinOrbit.Defs.SoCoeffPoly`):

```lean
/-- `A_m(e_*)` as a real number. -/
def soA (m : ℕ) : ℝ := soCoeffPoly soEcc m
```

`SoModes.lean` (imports `Mathlib.Order.Interval.Finset.Nat`; `@[expose] public section`):

```lean
/-- The index set `{1, …, 7}` of the seven forcing modes. -/
def soModes : Finset ℕ := Finset.Icc 1 7
```

`SoV.lean` (imports `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` and the frozen `SoEps`, `SoA`,
`SoModes`; `open Real`):

```lean
/-- The period-one potential `V(q, φ) = -ε_* Σ_{m=1}^7 A_m(e_*) cos (2π (2q - mφ))`
(`q` spin angle, `φ` orbital phase, both in turns). -/
def soV (q φ : ℝ) : ℝ :=
  -soEps * ∑ m ∈ soModes, soA m * Real.cos (2 * π * (2 * q - m * φ))
```

`SoField.lean` (imports `Mathlib.Analysis.Calculus.Deriv.Basic` and the frozen `SoV`):

```lean
/-- The physical spin–orbit vector field on `(q, p, φ)`: `q̇ = p`, `ṗ = -∂_q V`, `φ̇ = 1`.
Time is measured in orbital periods and `p` is the spin rate divided by the orbital mean motion. -/
def soField (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (x.2.1, -deriv (fun s => soV s x.2.2) x.1, 1)
```

`SoBarrier.lean` (imports `Mathlib.Order.Interval.Set.OrdConnected` and the frozen `SoField`):

```lean
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
```

D-SOF-1 (unchanged): the landed field is `invariant : KAM.ODE.IsInvariantSet soField Set.univ {x | …}`; the
frozen text writes it out and drops the trivial `y t ∈ univ`. Probe 3 re-checks both bridges.

### 1.2 The window: `LunarPLo.lean`, `LunarPHi.lean` (imports `Mathlib.Data.Rat.Init`; `@[expose] public section`)

```lean
/-- Lower end of the certified initial momentum window (ruling O1). -/
def lunarPLo : ℚ := 9933 / 10000      -- interim candidate; fixed by rule W of §1.4
```

```lean
/-- Upper end of the certified initial momentum window (ruling O1). -/
def lunarPHi : ℚ := 10067 / 10000     -- interim candidate; fixed by rule W of §1.4
```

(The comments mark the proposal status; the frozen files carry no such comment.)

### 1.3 Theorems

`KAM/Frozen/SpinOrbit/Theorems/LunarBarriers.lean` (Theorem A). Imports: `public import` of the frozen
`SoBarrier`, `LunarPLo`, `LunarPHi`; `import KAM.Provider.SpinOrbit.LunarBarriers`.

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
continuous barrier graphs with values in the band `[0.97286, 1.02714]`, the lower one strictly below the
window end `lunarPLo` and the upper one strictly above `lunarPHi`. -/
theorem lunar_barriers :
    ∃ (Bm : SoBarrier (97286 / 100000) (102714 / 100000))
      (Bp : SoBarrier (97286 / 100000) (102714 / 100000)),
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

`KAM/Frozen/SpinOrbit/Theorems/LunarSpinConfinement.lean` (Theorem B, the headline). Imports: the frozen
`SoField`, `LunarPLo`, `LunarPHi`; `import KAM.Provider.SpinOrbit.LunarSpinConfinement`. Same wrapper as A.

```lean
/-- **Theorem B.** In the seven-mode lunar spin–orbit model, every initial state `(q₀, p₀, φ₀)` with
`lunarPLo < p₀ < lunarPHi` (any angles) has a global solution, unique among global solutions, and its
spin rate satisfies `|p(t) − 1| ≤ 2714/100000` (2.714 %) for all real `t`. -/
theorem lunar_spin_confinement (q₀ p₀ φ₀ : ℝ) (hp : (lunarPLo : ℝ) < p₀ ∧ p₀ < lunarPHi) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).2.1 - 1| ≤ 2714 / 100000) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  sorry
  -- FROZEN_ANCHOR_PROOF_END
```

`KAM/Frozen/SpinOrbit/Theorems/LunarWindow.lean` (non-vacuity). Imports: the frozen `LunarPLo`, `LunarPHi`;
`import KAM.Provider.SpinOrbit.LunarWindow`. Same wrapper.

```lean
/-- The initial momentum window of `lunar_spin_confinement` is nonempty. -/
theorem lunarPLo_lt_lunarPHi : lunarPLo < lunarPHi :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  sorry
  -- FROZEN_ANCHOR_PROOF_END
```

Its provider is `by decide +kernel` (plain `decide` gets stuck on ℚ division literals; `norm_num` also works).

Theorem B's definition closure is `SoEcc … SoField` plus the two window files; it does not contain `SoBarrier`.
Theorem A's closure adds `SoBarrier`. `lunarPLo_lt_lunarPHi`'s closure is the two window files.

### 1.4 How the literals are fixed from the final data

Notation: for the certified lower and upper graphs `gL`, `gU` with packages `PL`, `PU`, the certified ranges are
`[gL.pLo − PL.disp, gL.pHi + PL.disp]` and `[gU.pLo − PU.disp, gU.pHi + PU.disp]` (all rationals; the data
theorems of the final SO-DATA package). Let `M = max(1 − (gL.pLo − PL.disp), (gU.pHi + PU.disp) − 1)`, the
certified max `|p − 1|` over both barriers.

- **Rule B (band).** `δ = ⌈M · 10⁵⌉ / 10⁵`, the smallest five-decimal literal `≥ M`; Theorem A's band is
  `lo = 1 − δ`, `hi = 1 + δ`, written as the unreduced literals `(100000 − 100000δ)/100000` and `(100000 + 100000δ)/100000`.
  Interim: `M ≈ 0.02713` (lower torus bottom 0.97287, upper torus top 1.02713, disp ≈ 1e-14) gives
  `δ = 2714/100000`, `lo = 97286/100000`, `hi = 102714/100000`. The interim figures are rounded to five decimals,
  so the final δ may come out as `2713/100000` or `2714/100000` (or higher if the certified enclosure is looser than
  the grid maximum by more than 10⁻⁵). `gL.pLo`, `gU.pHi` are bounds chosen by the data emitter and only checked
  (`checkSoGraph` verifies `pLo ≤ Re K ≤ pHi`), so `M` is an upper bound for the true extremum: rule B also requires
  the emitter to set them within about 10⁻⁶ of the computed extrema, so that slack does not inflate δ. Q8 offers a
  rounder alternative.
- **Rule W (window).** `lunarPLo` is the smallest four-decimal literal strictly greater than `gL.pHi + PL.disp`;
  `lunarPHi` the largest four-decimal literal strictly less than `gU.pLo − PU.disp`. Interim: `0.99322` and
  `1.00678` give `9933/10000` and `10067/10000`. (The first proposal asked for a 10⁻⁴ margin; the margin buys nothing
  once the literal is computed from the certified, final numbers, so rule W drops it. Q2.)
- The five band inequalities of `lunar_barriers_of_sharp` (`lo ≤ gL.pLo − PL.disp`, `gL.pHi + PL.disp < lunarPLo`,
  `lunarPLo < lunarPHi`, `lunarPHi < gU.pLo − PU.disp`, `gU.pHi + PU.disp ≤ hi`) then hold by construction and are
  closed by `decide +kernel`. Probe 1 closes them for the interim numbers.

## 2. Relation to the landed band-parametric theorems

The frozen theorems are instances, with every hypothesis discharged by data, the N = 65 Diophantine lemma, or a
rational inequality:

- **Theorem A** = `lunar_barriers_of_sharp gL gU PL PU c κ (1/67) (1/67) lo hi lunarPLo lunarPHi
  (lunarNuMinusN 65) (lunarNuPlusN 65) …`, where:
  - `hhamL/U`, `hparL/U`, `hcL/U` (`checkTorusCertificateSharp … = true`), `hgL/U` (`checkSoGraph … = true`),
    `hωL/U` (`FreqEncloses`) are SO-DATA's kernel-checked data theorems;
  - `hc0 : 0 < c` and the `hκ : 0 < κ` needed by the `_65` lemmas are `decide +kernel` on the package constants;
  - `hτL/U : P.tau = 1` and `hγL/U : P.γ ≤ κ * (1/67)` are `rfl`/`decide +kernel` on the packages;
  - `hdL/U` come from the landed `lunarRotFreq{Minus,Plus}N_isDiophantine_65` (γ = κ/67), reshaped `κ/67 = κ * ((1/67 : ℚ) : ℝ)` (a `simpa [div_eq_mul_inv]` in probe 1);
  - the five band inequalities by `decide +kernel`;
  - followed by `rwa [cast_lo, cast_hi] at h` to turn `((lo : ℚ) : ℝ)` into the real literal (the `simp`/`simpa`
    family cannot rewrite inside the dependent `SoBarrier` type; `rw` can).
- **Theorem B** = `lunar_spin_confinement_of_band lo hi δ lunarPLo lunarPHi (by norm_num) (by norm_num)
  (by rw [cast_lo, cast_hi]; exact lunar_barriers) q₀ p₀ φ₀ hp`, under `simpa only [cast_δ]`. With `lo = 1 − δ`,
  `hi = 1 + δ` the two side conditions are equalities.
- **Window** = `decide +kernel`.
- **Data hygiene** (refutation note 11): state the data facts as `gL.pLo = <literal>` etc. (by `rfl` or
  `decide +kernel` on the data), then close the band inequalities on the literals, so the kernel does not unfold the
  whole certificate inside each inequality.
- With the frozen `SoBarrier` (§4, Q11), A is the above with the landed barrier being the frozen one; if instead
  the landed structure is kept under a new name, the provider applies the probe-3 bridge `ofLanded` to both
  barriers.

Probe 1 elaborates exactly these shapes, with the data premises as hypotheses (§4).

**Note for SO-DATA (not a freeze issue).** SO-GEN3's threshold study assumes `γ = c/((N+1)s)` (binding mode
`(1, 0)`, `γ((ν−1, 1)) = 1/(N+g) > 1/(N+1)`), whereas the landed lemma certifies `κ/(N+2) = κ/67` at N = 65. The
package must satisfy `γ ≤ κ/67`; the threshold cost of 66 → 67 is a factor `(66/67)⁴ ≈ 0.94`, negligible.

## 3. Refute-first statement audit

**Physical claim (D38 with D30, O1, O4).** In the explicit conservative seven-mode lunar spin–orbit model
(Celletti (7.55), `e = 0.0549`, `ε = 3.45·10⁻⁴`), every solution whose initial spin rate lies in the window
`(lunarPLo, lunarPHi)` ≈ `(0.9933, 1.0067)` (any initial angles) exists for all time, is unique, and its spin rate
stays within 2.714 % of synchronous for all time; two invariant barrier graphs in `[0.97286, 1.02714]` separate the
window from the outside.

### 3.1 Carried over unchanged

The definition rows (`soEcc`, `soEps`, `soCoeffPoly`, `soModes`, `soV`, `soField`, `SoBarrier`), the binder-by-binder
reading of Theorem B (angles arbitrary, the window the only premise, global classical solution, uniqueness among
global solutions, the `(q, p, φ)` component order), the reading notes N0 (model, not the Moon), N1 (time in orbital
periods), N2 (uniqueness), N4 (rotated frame never mentioned), N6 (invariance on order-connected intervals) and the
premises inventory are those of the first proposal §2, verbatim: the texts they audit did not change (probe 3 checks
every definition against the landed one by `rfl`). They are not repeated here.

### 3.2 New and changed items

| # | Item | Attempted refutation | Verdict |
|---|---|---|---|
| R1 | Band literal δ = 2714/100000 is **false** (too small)? | The literal must be `≥` the certified bound `M` (an upper bound for the max, as tight as the emitter makes `pLo`/`pHi`; see rule B) of `\|p − 1\|` on both barriers, and confinement then gives `≤ δ` for the solution (between the barriers). Rule B makes δ `≥ M` by construction; the interim `M ≈ 0.02713` with five-decimal rounding leaves `M ≤ 0.027135 < 0.02714`. The final literal is computed from certified data, so no risk survives into the frozen text. | PASS (rule B) |
| R2 | Band below the **separatrix floor**? | In the pendulum approximation of the dominant `m = 2` term (a heuristic, not a theorem for the seven-mode model), a rotational barrier enclosing the 1:1 resonance reaches `\|p − 1\| ≥ 2√(εA₂) ≈ 0.02617`. `0.02714 > 0.02617` (probe 1). A δ below the floor would signal an error in the data; none here. | PASS |
| R3 | Theorem B **trivially true** (no barriers needed)? | No exact integral: `H = p²/2 + V(q, φ)` is time-dependent, and in the rotated frame only the `m = 2` term is autonomous. The landed force bound gives `\|ṗ\| ≤ soForceBound ≈ 4πε Σ\|A_m\| ≈ 2.7·10⁻³` per period, so an a-priori argument confines `p` only for about 7.6 periods from the window edge (about 10 from `p₀ = 1`). All-time confinement needs the barriers. | PASS (not trivial) |
| R4 | Theorem B **vacuous** (empty window)? | `lunarPLo = 0.9933 < 1.0067 = lunarPHi`; frozen as the third theorem `lunarPLo_lt_lunarPHi`, so non-vacuity is part of the frozen surface. The window contains exact synchronous rotation `p₀ = 1` (probe 1). | PASS |
| R5 | Theorem A **vacuous/trivial**? | A constant graph is not invariant (`∂_q V ≢ 0`, first proposal). The band `[0.97286, 1.02714]` contains both barriers by rule B, and `Bm < lunarPLo < lunarPHi < Bp` forces two distinct graphs. | PASS |
| R6 | Frozen texts **mention the certifier** or proof data? | Closures: B = model + window; A = model + `SoBarrier` + window; window theorem = window. No `ν±`, `N`, `κ`, `CertParams`, `checkTorusCertificateSharp`, `IsDiophantine`, frame. Probe 2 elaborates each file with only its own Mathlib imports and inlined frozen dependencies. | PASS |
| R7 | **Stronger than the old statement?** | No: the window shrank from `(0.9823, 1.0177)` (N = 40 data) to `(0.9933, 1.0067)`. Sharper conclusion, smaller premise; neither implies the other. Recorded as D-SOF-4; Q10. | NOTE |
| R8 | **Literal reading.** `2714 / 100000 : ℝ` is the real quotient `0.02714`; `97286 / 100000 : ℝ` likewise. Is `\|(z t).2.1 − 1\|` the spin rate deviation? | `(z t).2.1` is `p(t)`; `p` is spin rate over mean motion (unit-free; first proposal §2.1 units row). | PASS |
| R9 | Band **asymmetry** lost? | The interim tori are symmetric about 1 to `10⁻⁵`, so one δ costs nothing. A's band is `[1 − δ, 1 + δ]`, which makes B's side conditions equalities. | PASS |
| R10 | Does the **N = 65 proof** fit the frozen text (premises all dischargeable)? | Probe 1: the frozen A text follows from `lunar_barriers_of_sharp` with the N = 65 Diophantine lemma and the data premises only, axioms `[propext, Classical.choice, Quot.sound]`; B follows from A's text. | PASS |
| R11 | **Data not yet final.** | The literals are interim (SO-GEN3 grid maxima, not certified enclosures). Freeze only after the final data (Q9). | PENDING (SO-DATA) |

### 3.3 Deviations (for the errata/deviation ledger)

- **D-SOF-1** (unchanged): `SoBarrier.invariant` written out instead of `KAM.ODE.IsInvariantSet`; equivalent (probe 3).
- **D-SOF-2** (unchanged): O1's constant window replaces the graph-defined region of source §3.2.
- **D-SOF-3** (revised): source Theorem A (proposal §3.1) has the band `[0.97, 1.03]` with `ν± = 1 ± 1/(40+g)`.
  The anchor has the band `[1 − δ, 1 + δ]` with δ ≈ 2.714 %, **inside** the source band, obtained from barriers at
  `ν± = 1 ± 1/(65+g)` (D38). The frequencies are not part of the statement (O4).
- **D-SOF-4** (new): the window `(0.9933, 1.0067)` is narrower than the N = 40 window `(0.9823, 1.0177)`, and
  narrower than source §3.2's region between the N = 40 tori, because the N = 65 tori lie closer to the resonance
  (D38). The headline trades initial-data coverage for a sharper band.

No suspected erratum in a pinned source was found. One record-keeping item: D38 is on `main` (`54d944cb`) but not
yet in `inp`'s `docs/DECISIONS.md` (SO-SHARPLINK's handoff noted the same).

### 3.4 Independent refutation pass

See §6.

## 4. Elaboration evidence

Untracked probes in `.lake/abi-scratch/` (deleted after the run), each `nice -n 5 lake env lean <file>` against the
landed build of `inp@f4953508`. No heartbeat override anywhere.

1. **`SoFreeze2Probe.lean`** (imports `KAM.SpinOrbit.LunarAssemblySharp`, `KAM.SpinOrbit.RotFreqN`). It states the
   frozen A text (placeholder `sorry`), proves the frozen B text from it via `lunar_spin_confinement_of_band`, proves
   the frozen A text from the N = 65 data premises via `lunar_barriers_of_sharp` and
   `lunarRotFreq{Minus,Plus}N_isDiophantine_65` (`lunar_barriers_of_data`), checks the interim band inequalities
   and `lunarPLo < lunarPHi` by `decide +kernel`, `lunarPLo < 1 < lunarPHi`, and δ above the separatrix floor.
   Output (rc 0):

   ```
   SoFreeze2Probe.lean:20:8: warning: declaration uses `sorry`        -- placeholder Theorem A only
   'SoFreeze2Probe.lunar_barriers_of_data' depends on axioms: [propext, Classical.choice, Quot.sound]
   'SoFreeze2Probe.lunar_spin_confinement' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
   'KAM.SpinOrbit.lunar_barriers_of_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.SpinOrbit.lunar_spin_confinement_of_band' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.SpinOrbit.lunarRotFreqMinusN_isDiophantine_65' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.SpinOrbit.lunarRotFreqPlusN_isDiophantine_65' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.CertificateSharp.checkTorusCertificateSharp_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   (`sorryAx` in B comes only from the placeholder A.) A first attempt with `simpa using` failed: `simp` does not
   rewrite the cast `((97286/100000 : ℚ) : ℝ)` inside the type of `SoBarrier`; `rw`/`rwa` does, as in the landed
   `lunar_barriers_of_viaBand`.
2. **`Probe2_<File>.lean`**, one per proposed frozen file (13 files): a `module` file with exactly that file's own
   Mathlib imports plus those of its frozen dependencies, the dependencies' texts inlined, `@[expose] public
   noncomputable section`. All 13 rc 0; the only output is the expected `sorry` warning in the three theorem files.
   The texts were generated from one set of source snippets, which are also the texts shown in §1.
3. **`SoFreeze2Probe3.lean`**: the §1 texts in a namespace `Fz` next to the landed modules. Checks by `rfl`:
   `soEcc`, `soEps`, `soCoeffPoly`, `soA`, `soModes`, `soV`, `soField` equal the landed ones, the window literals
   equal probe 1's; `SoBarrier.ofLanded`/`toLanded` convert both ways; the frozen A text follows from the landed-form
   A (`Fz.lunar_barriers_of_landed`); the frozen B text is accepted **definitionally** as probe 1's landed-form B
   (term `SoFreeze2Probe.lunar_spin_confinement q₀ p₀ φ₀ hp`). Output: three expected `sorry` warnings (placeholders),
   the bridges and `lunar_barriers_of_landed` depend on `[propext, Classical.choice, Quot.sound]`, rc 0.

Probe 3 places the frozen texts in a separate namespace `Fz`, so it does **not** test coexistence with the landed
names. Importing the landed modules next to the frozen texts under `KAM.SpinOrbit` fails with
`KAM.SpinOrbit.SoBarrier has already been declared` (refutation finding 1); the same holds for every frozen
definition that duplicates a landed one (`soEcc … soField`).

Implementation consequence at freeze time (not done here; it corrects the first proposal §3, which had the same gap):
- `Model.lean` imports the frozen `soEcc … soField` and deletes its own copies (the texts agree by `rfl`, probe 3);
- `Barrier.lean` either (recommended, Q11) uses the frozen `SoBarrier` directly, with a one-line lemma
  `SoBarrier.isInvariantSet : KAM.ODE.IsInvariantSet soField univ {x | x.2.1 = B.P x.1 x.2.2}` (the `toLanded`
  direction of probe 3) for its existing proofs, or renames its structure (for example `SoBarrierInv`, used in seven
  files) and keeps the probe-3 bridges;
- then build every frozen file through the gate with its real frozen imports, and the providers
  (`KAM/Provider/SpinOrbit/{LunarBarriers,LunarSpinConfinement,LunarWindow}.lean`).

The probe files were deleted after the run.

## 5. Manifest entries

Shape as in the first proposal §4. Changes: `source.range` cites D38 and this document; Theorem B's and A's
closures are unchanged; add `spinorbit.d<k>.lunarPLo_lt_lunarPHi.v1` (kind theorem, closure `LunarPLo.lean`,
`LunarPHi.lean`, provider `KAM.Provider.SpinOrbit.LunarWindow`).

## 6. Independent refutation pass

A fresh Opus subagent was asked to refute §1–§5 and §7, read-only, re-elaborating the texts itself in scratch
probes (deleted). It reported **no HIGH finding**: neither theorem is false, vacuous or trivially true, and nothing
about the certifier, the frequencies or the frame leaks into the frozen text.

| # | Sev. | Finding | Resolution |
|---|---|---|---|
| 1 | MED | The frozen `KAM.SpinOrbit.SoBarrier` clashes with the landed one (`Barrier.lean:36`); a provider importing both cannot compile (`… has already been declared`). Probe 3 hid this by using a namespace `Fz`. The first proposal had the same gap. | §0 item 8, §4 (implementation consequence), Q11 |
| 2 | LOW | "One-line instances" undercounted the glue (barrier bridge, `κ/67` reshape, `0 < c`, `0 < κ`) | §0 item 6 and §2 reworded |
| 3 | LOW | Rule B on the interim `M = 0.02713` gives `2713/100000`; 2714 is the five-decimal worst case | §0 item 3 states both |
| 4 | LOW | `pLo`/`pHi` are emitter-chosen bounds; slack inflates δ | Rule B requires them within about 10⁻⁶ of the extrema (§1.4) |
| 5 | LOW | R3's "about 7 periods" is the worst case (7.6 from the window edge, 10.1 from `p₀ = 1`) | R3 reworded |
| 6 | LOW | On a fallback the docstrings change too, not only the five literals | Q9 reworded |
| 7 | LOW | Q8(b): measured from the interim 2.713 % the tolerance is 0.007 points | Q8 reworded |
| 8 | LOW | Probes were still present when reviewed | Deleted after the review (§4) |
| 9 | NOTE | The separatrix floor is a pendulum heuristic, not a theorem for the full model | R2 reworded |
| 10 | NOTE | The `(66/67)⁴` cost assumes γ⁴ scaling for the sharp threshold | Kept as a note; negligible either way |
| 11 | NOTE | `decide +kernel` on band inequalities unfolds the data | Data-hygiene item added to §2 |

Claims it tried and failed to refute: each frozen file elaborates with only its own imports and the definition
texts match `Model.lean`; A and B follow from `lunar_barriers_of_sharp` (with the `_65` Diophantine lemmas) and
`lunar_spin_confinement_of_band` with the standard three axioms, and the argument order in §2 is right; `rwa`
rewrites casts inside `SoBarrier`; the window contains `p = 1` and is nonempty; the arithmetic (separatrix 0.026169,
`A₂ = 0.496236`, `Σ|A_m| = 0.61975`, force bound 2.69·10⁻³, `1/(65+g) = 0.015240`, N = 40 window 1.77 % against
0.67 %, fallback bands 2.755 % and 2.82 %, Q8(c) cost 0.036 points); B and A are not trivially true; neither the
N = 40 nor the N = 65 headline implies the other; the D37/D38 and SO-GEN3 citations; rules B and W are sound by
construction.

## 7. Open questions for the owner (with recommendations)

- **Q1. Which theorems to freeze?** Recommended: A, B and the window theorem (B is the headline; A records the
  barrier content; the window theorem makes non-vacuity part of the frozen surface). Alternative: B and the window
  theorem only (no `SoBarrier` in the trusted surface).
- **Q2. Window literals.** Recommended: rule W (four decimals, strictly inside the certified gap, no extra margin);
  interim `9933/10000`, `10067/10000`; freeze `lunarPLo_lt_lunarPHi` (now part of Q1). Alternative: keep the first
  proposal's 10⁻⁴ margin (`9934/10000`, `10066/10000`), which only matters if the freeze precedes the final data.
- **Q3. Frequencies in Theorem A?** Recommended: no, still (O4). With N = 65 the frequencies are a proof choice
  that may still fall back to N = 60 or 55; keeping them out of the statement keeps the frozen text independent of
  that choice except through the literals.
- **Q4. Freeze a certifier soundness theorem?** Recommended: no, for both `checkTorusCertificate_sound` and
  `checkTorusCertificateSharp_sound`. The arguments of the first proposal §1.13 apply with more force: there are now
  two certifiers and D36 announces further versions with the same format. Freeze a versioned black box later, as a
  separate decision with its own audit of `HamExpr.eval` and `CertEmbedding.eval`.
- **Q5. `SoBarrier` form.** Recommended: unchanged, the written-out invariance (D-SOF-1).
- **Q6. Coefficient split.** Recommended: unchanged, `soCoeffPoly` generic over a field plus `soA`.
- **Q7. Uniqueness among global solutions only.** Recommended: unchanged, keep.
- **Q8 (new). Which band literal?** Options: (a) **the rule-B literal, interim 2.714 %** — recommended: it is the
  sharpest honest number, it is fixed from certified data before the freeze, and "as good as we can get" is the D38
  instruction; (b) **2.72 %** (`272/10000`), a rounder headline that tolerates a final enclosure up to 0.006 points
  looser than 2.714 % (0.007 looser than the interim 2.713 %), at the cost of 0.006 points; (c) **2.75 %** — not recommended: it gives away 0.04 points
  and still does not cover the N = 60 fallback (2.755 %); a literal that survives fallback to N = 60 would be
  2.76 %, to N = 55 2.82 %. Robustness is only an issue if the freeze precedes the final data; Q9 avoids that.
  Notation sub-question: write `2714 / 100000` (precedent `33 / 1000`) rather than the scientific literal
  `0.02714`; recommended the fraction, for the same elaboration as the precedent.
- **Q9 (new). Freeze timing and fallback.** Recommended: approve the statement shapes and rules B and W now; freeze
  once the final N = 65 certificates pass the kernel, with the literals computed by the rules and recorded in the
  approval. If N = 65 fails and SO falls back to N = 60 or 55, the five literals change, and with them the numbers
  quoted in the docstrings of A and B (so those files' hashes change); the shapes and every definition stay, and the
  owner re-approves the literals.
- **Q10 (new). The narrower window.** Recommended: accept (D-SOF-4). The headline is the band; the window still
  contains synchronous rotation and is explicit. Alternative: additionally keep a 3.3 % statement with the wider
  N = 40 window as a second frozen headline. Not recommended: it needs the R1 data (superseded by D37) to be
  completed and doubles the frozen surface for a weaker band.
- **Q11 (new). The landed `SoBarrier` at freeze time.** The frozen and landed structures share the full name
  `KAM.SpinOrbit.SoBarrier` (§4). Recommended: switch the landed code to the frozen structure (one structure, no
  bridge in the providers; the landed proofs use `invariant` through one adapter lemma). Alternative: rename the
  landed structure and bridge in the providers.
