# Package LP-THR2: carrier repair of the ordered thresholds (statement review finding F3)

Wave 3 fix. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers,
handoff). Base: `inp-lp`. This package may edit the landed THR file `KAM/Planetary/StrongAMD/Threshold/Defs.lean`
and the THR parts that use the changed definitions. That is an explicit orchestrator decision: nothing is
frozen yet.

## Why

The independent statement review of the freeze proposal (`docs/tracks/LP/freeze/STATEMENT-REVIEW-1.md`, F3)
found that `orderedCrossThreshold` has no `2 ≤ n` argument. For `n = 1` the adjacent family is empty, and Lean's
real `⨅` returns 0, which is not the source minimum. The freeze will expose only the source-facing ordered
thresholds, so they must carry the guard. The ordered pair threshold also needs its own carrier-level
characterization.

## Changes (exact, from the review)

1. `orderedCrossThreshold {ν} (_hn : 2 ≤ n) (I : OrderedActions ν) : ℝ :=
   ⨅ a : AdjIdx n, orderedPairThreshold I a.1 a.upperIdx a.lt_upperIdx`.
2. `orderedStrongThreshold {ν} (hn : 2 ≤ n) (I : OrderedActions ν) : ℝ :=
   min (orderedCrossThreshold hn I) (⨅ i : Fin n, I.1 i)`.
3. Update every lemma that uses them: `orderedStrongThreshold_eq` must stay `rfl`, and
   `orderedStrongThreshold_pos`, `continuous_orderedStrongThreshold`, `orderedStrongThreshold_eq_min_first`
   follow. Add `orderedCrossThreshold_eq : orderedCrossThreshold hn I = crossThreshold ν I.1` (`rfl`).
4. New exports (exact text from the review):
   - `orderedPairThreshold_isLeast (I : OrderedActions ν) (i j) (hij : i < j) :
     IsLeast (pairObjective I.1 i j '' pairFeasible ν I.1 i j) (orderedPairThreshold I i j hij)`;
   - `orderedPairThreshold_existsUnique_value … : ∃! b, IsLeast (…) b`.
   Optional: the same characterization for `orderedCrossThreshold` and `orderedStrongThreshold` as finite
   minima (`∃ member = value ∧ ≤ every member`).
5. Grep all of `KAM/` for uses of the changed definitions and fix every call site. At `inp-lp` only the THR
   files use `orderedCrossThreshold`.

## Owned files

`KAM/Planetary/StrongAMD/Threshold/{Defs,Strong}.lean` (and `Pair.lean` for item 4). No other file.

## Checks and stop condition

- `lp_build.sh` on `KAM.Planetary.StrongAMD.Threshold` and every LP module importing it, in import order.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` on the THR modules exits 0.
- `#print axioms` of the new and changed theorems.

Expected size under 150 changed lines. Handoff `docs/tracks/LP/audits/LP-THR2-handoff.md` (committed) and
`.drafts/handoff-LP-THR2.md`, then `touch .drafts/READY-LP-THR2`.
