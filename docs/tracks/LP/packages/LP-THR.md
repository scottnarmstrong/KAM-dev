# Package LP-THR: attained, continuous, sharp thresholds (MAIN Lemma 4)

Wave 1. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (read it first; it carries the hard rules,
the capped build wrappers and the handoff format).

## Source

`docs/tracks/LP/source/MAIN.md`: definitions §1 lines 41–55 (chamber `𝒬`, `a_i(I)`, `D`, (3)), Lemma 4 lines
141–160. Conventions and intended names: `docs/tracks/LP/SPEC.md` §2. Roadmap §1 (definitions table and the
characterization rule) and §3 row 4.

## Owned files

`KAM/Planetary/StrongAMD/Threshold/*.lean` and the facade `KAM/Planetary/StrongAMD/Threshold.lean` (imports the
parts). Suggested split: `Defs.lean` (definitions, `@[expose]`), `Pair.lean` (attainment, contact reduction,
positivity, `< I j`), `Continuity.lean`, `Strong.lean` (cross/star/strong minima). Nothing else.

## Definitions (namespace `KAM.Planetary.StrongAMD`; `ν I : Fin n → ℝ`)

- `chamber ν : Set (Fin n → ℝ)`: `(∀ i, 0 < I i) ∧ ∀ i j, i < j → actionAxis ν I i < actionAxis ν I j`.
- `actionAxis ν I i := (I i / ν i) ^ 2`.
- `eccDeficit u := 1 - Real.sqrt (1 - u ^ 2)`.
- `pairFeasible ν I i j : Set (ℝ × ℝ) := {uv | uv.1 ∈ Icc 0 1 ∧ uv.2 ∈ Icc 0 1 ∧
   actionAxis ν I j * (1 - uv.2) ≤ actionAxis ν I i * (1 + uv.1)}`.
- `pairObjective I i j uv := I i * eccDeficit uv.1 + I j * eccDeficit uv.2`.
- `pairThreshold ν I i j := sInf (pairObjective I i j '' pairFeasible ν I i j)` (overnight default OD-2: a total
  literal formula; its meaning is fixed by the characterization theorem below).
- `starThreshold I` = `min_i I i`, `crossThreshold ν I` = `min` over adjacent pairs `(i, i+1)` with `i + 1 < n` of
  `pairThreshold`, `strongThreshold ν I := min (crossThreshold ν I) (starThreshold I)`. Use literal finite minima
  (`Finset.inf'` over a nonempty index finset, or `⨅` over a nonempty `Fintype` index) and state any `n` lower
  bound you need (`1 ≤ n` for the star, `2 ≤ n` for the cross minimum) as an explicit hypothesis of the theorems,
  never inside the definition by an `if`. If the literal form of the adjacent index needs a choice (e.g.
  `Fin (n - 1)` with casts vs a subtype of `Fin n`), take the one that states most cleanly and report it.

## Freeze-ready API (OD-2, binding)

The frozen definition will most likely live on the source carrier. So also define the subtype
`OrderedActions ν := {I // I ∈ chamber ν}` and carrier versions `orderedPairThreshold (I : OrderedActions ν)
(i j : Fin n) (hij : i < j)` and `orderedStrongThreshold` (for `2 ≤ n`), each proved equal to the total `sInf`
helper by a one-line lemma. Every downstream-facing theorem (items 2–8) must be stated so it transfers by that
equation: state the characterization with `IsLeast` / an attained minimum, and never rely on the off-carrier
value of the total formula.

## Theorems to prove (all with `hν : ∀ i, 0 < ν i` where needed)

1. `pairFeasible` is nonempty and compact for every `I` (`(1, 1)` is feasible; it is a closed subset of `[0,1]²`).
2. **Characterization** (roadmap §1, verbatim shape): for every `I` and `i j`,
   `∃ uv ∈ pairFeasible ν I i j, pairObjective I i j uv = pairThreshold ν I i j ∧
     ∀ vw ∈ pairFeasible ν I i j, pairThreshold ν I i j ≤ pairObjective I i j vw`.
3. **Contact reduction** (MAIN lines 147–150): on `chamber ν` with `i < j`, the minimum is attained at a point with
   `actionAxis ν I j * (1 - v) = actionAxis ν I i * (1 + u)`; and the parameterization (15) over `t ∈ [0,1]`
   with `α = a_i/a_j`, `m(α) = min 1 ((1-α)/α)`, `u = m t`, `v = 1 - α - α m t`, i.e.
   `pairThreshold ν I i j = sInf ((fun t => pairObjective I i j (m t, 1 - α - α m t)) '' Icc 0 1)`
   (or an equivalent attained-minimum statement over `Icc 0 1`).
4. **Positivity**: `I ∈ chamber ν → i < j → 0 < pairThreshold ν I i j`.
5. **Strict upper bound** (14): `I ∈ chamber ν → i < j → pairThreshold ν I i j < I j`
   (competitor `(0, 1 - α)`, and `eccDeficit (1 - α) < 1`).
6. **Continuity**: `ContinuousOn (fun I => pairThreshold ν I i j) (chamber ν)` for `i < j` (MAIN route: the
   fixed-interval parameterization, joint continuity in `(I, t)`, uniform continuity on compact neighborhoods and
   `|min F(I,·) − min F(J,·)| ≤ sup |F(I,·) − F(J,·)|`; any correct route is fine). Also `IsOpen (chamber ν)`.
7. **Strong threshold**: on `chamber ν` (with the needed `n` bounds): `crossThreshold` and `strongThreshold` are
   `ContinuousOn (chamber ν)` and positive; `strongThreshold ν I ≤ pairThreshold ν I i (i+1)` for each adjacent
   pair, `strongThreshold ν I ≤ I i` for each `i`, and it equals one of these values (characterization of the
   finite minimum); and (14): `strongThreshold ν I = min (crossThreshold ν I) (I ⟨0, _⟩)`.
8. **Feasibility consumer** (for Geometry, MAIN L5 line 166): if `0 ≤ u ≤ 1`, `0 ≤ v ≤ 1` and
   `actionAxis ν I j * (1 - v) ≤ actionAxis ν I i * (1 + u)` then
   `pairThreshold ν I i j ≤ I i * eccDeficit u + I j * eccDeficit v`.

Out of scope (a later package): the interior-optimizer claim and the geometric realization / sharpness paragraph
(MAIN lines 154–158), and the Laskar–Petit identification (line 158). Do not prove them here.

## Checks and stop condition

Build `KAM.Planetary.StrongAMD.Threshold` (and each part, in import order) with `lp_build.sh`; `lp_lint.sh` exits 0;
`#print axioms` of items 2–8. Stop when items 1–8 are proved, or when an item is blocked (report it; never weaken
a statement or add a hypothesis silently). Expected size 600–1,500 lines over 3–4 files.

## Handoff

`docs/tracks/LP/audits/LP-THR-handoff.md` (committed) and `.drafts/handoff-LP-THR.md`, per the prover brief, then
`touch .drafts/READY-LP-THR`.
