# Track LP specification (conventions and definitions)

Status: 2026-11-01, overnight mode. Nothing here is frozen or owner-approved. The Lean declarations of wave 1 are
ordinary (non-frozen) definitions and theorems, written in the exact form intended for the final statement surface,
so that the morning freeze proposal (`FREEZE-PROPOSAL.md`) can quote them. Open choices are logged in
`OWNER-DECISIONS.md`; the default taken overnight is stated there and below.

Source: [`source/MAIN.md`](source/MAIN.md) (pinned; audited PASS WITH NOTES, amended by
[`source/AMENDMENTS.md`](source/AMENDMENTS.md), which overrides the cited lines; cite `LP:MAIN L<k> (lines)`), planning:
[`source/LEAN-ROADMAP.md`](source/LEAN-ROADMAP.md) §1–§4. Background on `main`: `docs/explorations/amd-crossing/`
(README, A1–A9; A8 = MAIN, A9 = roadmap).

## 1. Physical conventions (MAIN §1, lines 9–93)

- Units G = 1, stellar mass 1; planet masses `μ * ν i`, `0 < ν i`, normalization `max ν = 1` (OD-3).
- Heliocentric positions `q i`, scaled canonical momenta `p i` (physical momentum `μ p i`), form `Σ dp ∧ dq`.
  Exact model: the repository's frozen `KAM.Planetary.movingHamiltonian 1 1 ν μ` and
  `KAM.Planetary.IsMovingSolutionOn ν μ J z` (MAIN (1)); solutions in physical time.
- Planar phases: `KAM.Planetary.Phase (n * 2)` with `bodyVector`; spatial (wave 4): `Phase (n * 3)`.
  Physical lengths are `planeLength` (Euclidean), never the ambient sup norm of a Pi type.
- Repository dictionary (planar, frozen definitions, mass argument `m := ν`):

  | MAIN | Lean |
  |---|---|
  | `ν_i E_i` (total Kepler energy of planet i) | `keplerEnergy ν z i` = `planeSq p / (2ν) − ν/|q|` |
  | `a_i` | `keplerAxis ν z i` = `−ν/(2·keplerEnergy)` |
  | `I_i = Λ_i = ν_i √a_i` | `keplerAction ν z i` |
  | `𝐞_i` | `keplerEccVector ν z i`; `e_i = planeLength (keplerEccVector ν z i)` |
  | `L_i = q_i × p_i` (planar scalar) | `planeCross (bodyVector z.1 i) (bodyVector z.2 i)` |
  | `L = Σ L_i` | `totalMomentum z` |
  | `C = Σ I_i − |L|` | NEW `strongAMD ν z` (OD-1); equals `physicalAMD ν z` when `0 ≤ totalMomentum z` |

- Max norm `‖·‖_∞` on action vectors = the Pi norm on `Fin n → ℝ`.
- Angles: period 2π in MAIN; the Track N interface (wave 2) is period one (`θ = λ/(2π)`, roadmap §1).

## 2. New definitions (roadmap §1; wave-1 subset in bold)

Namespace `KAM.Planetary.StrongAMD`; modules under `KAM/Planetary/StrongAMD/` (planar and dimension-free) and
`KAM/Planetary/Spatial/` (wave 4). Names below are the intended ones; a prover may refine a name only to avoid a
clash and must report it.

| Lean name (intended) | Meaning (MAIN reference) |
|---|---|
| **`chamber ν : Set (Fin n → ℝ)`** | `𝒬`: `∀ i, 0 < I i` and `i < j → (I i / ν i)^2 < (I j / ν j)^2` (MAIN §1, line 51) |
| **`actionAxis ν I i`** | `a_i(I) = (I i / ν i)^2` |
| **`eccDeficit u`** | `D(u) = 1 − √(1 − u²)` (used on `u ∈ [0,1]`) |
| **`pairFeasible ν I i j : Set (ℝ × ℝ)`** | `{(u,v) ∈ [0,1]² : a_i(I)(1+u) ≥ a_j(I)(1−v)}` |
| **`pairObjective I i j (u,v)`** | `I i * D u + I j * D v` |
| **`pairThreshold ν I i j`** | `B_ij(I)`: `sInf (pairObjective I i j '' pairFeasible ν I i j)` (OD-2), exported with the attained-minimum characterization on `chamber ν`, `i < j` |
| **`crossThreshold ν I`** | `B_cross(I) = min_{i+1<n} B_{i,i+1}(I)` (n ≥ 2) |
| **`starThreshold I`** | `B_⋆(I) = min_i I_i` |
| **`strongThreshold ν I`** | `B(I) = min(B_cross(I), B_⋆(I))` (MAIN (3)) |
| **`strongAMD ν z`** | planar `C = Σ_i I_i − |L|` (MAIN (2)) |
| **`strongThresholdModulus ν U r`** | `Ω_B(r) = sup{|B I − B J| : I,J ∈ U, ‖I−J‖_∞ ≤ r}` (MAIN L6) |
| `strongSlowBall`, `actualOsculatingElements`, `angularMomentum3`, `canonicalAMD3`, `spatialPoincare`, … | waves 2–4, per roadmap §1 |

Rules for every definition (roadmap §1): the minimum-value characterization accompanies `pairThreshold`; no
numerical optimizer, no arbitrary feasible choice, no `if … then … else 0` totalization. Finite minima over
`Fin`-indexed families must be literal (`Finset.inf'` / `⨅` over a nonempty finite index) and come with
"`≤` each member" and "equals some member" lemmas.

## 3. Packages and the DAG

Packages are the rows of roadmap §3; the DAG is roadmap §4 (until the owner freezes the anchors and the source
dependency graph is built). Wave 1 (no anchor; elementary): Threshold (L4), Geometry (L5),
ThresholdModulus+Continuation (L6), Momentum planar (L2–L3 planar), PlanarDictionary (L7). Waves 2–4 are open (audit PASS WITH
NOTES).

| Package | Module prefix | Source |
|---|---|---|
| LP-THR | `KAM/Planetary/StrongAMD/Threshold*` | MAIN L4 (lines 141–160) |
| LP-MOM | `KAM/Planetary/StrongAMD/Orbital*`, `…/Momentum*` | MAIN L2 (110–128), L3 (130–139), planar |
| LP-GEO | `KAM/Planetary/StrongAMD/Geometry*` | MAIN L5 (162–175) |
| LP-MOD | `KAM/Planetary/StrongAMD/Modulus*`, `…/Continuation*` | MAIN L6 (177–189) |
| LP-DICT | `KAM/Planetary/StrongAMD/PlanarDictionary*` | MAIN L7 (193–242) against `KAM/Planetary/Poincare/*` |

## 4. Docstring and naming conventions

- Module docstring: package id, MAIN lemma and line range, and the phrase "track LP, non-frozen; the statement
  surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md".
- Main declaration docstrings carry the tag `(LP:MAIN L4 (141–160))` etc.
- Distinct descriptive names; never reuse a frozen name or a short name that clashes with Mathlib or another
  package (the audit runs `main_shortname_check.py`).
