# LP-THR handoff (MAIN Lemma 4, lines 141–160; track LP, non-frozen)

## Files (666 lines total, all well under the cap)
`KAM/Planetary/StrongAMD/Threshold.lean` (facade), `Threshold/Defs.lean` (95), `Pair.lean` (200),
`Continuity.lean` (178), `Strong.lean` (173). Namespace `KAM.Planetary.StrongAMD`.

## Items (all 1–8 proved) and declarations
Definitions (Defs): `actionAxis`, `chamber`, `eccDeficit`, `pairFeasible`, `pairObjective`,
`pairThreshold` (literal `sInf`), `AdjIdx n := {i : Fin n // i.val+1<n}`, `AdjIdx.succ`,
`crossThreshold := ⨅ a : AdjIdx n, pairThreshold ν I a.1 a.succ`, `starThreshold := ⨅ i, I i`,
`strongThreshold := min cross star`. OD-2 carrier API: `OrderedActions ν := {I // I ∈ chamber ν}`,
`orderedPairThreshold I i j hij`, `orderedCrossThreshold`, `orderedStrongThreshold (hn : 2 ≤ n) I`, with
one-line `rfl` lemmas `orderedPairThreshold_eq`, `orderedStrongThreshold_eq`.
1. `isCompact_pairFeasible`, `pairFeasible_nonempty` (every I, ν).
2. `pairThreshold_isLeast` (IsLeast form) and `exists_pairThreshold_attained` (verbatim shape); every I, no hypotheses.
3. `exists_contact_minimizer` (hν, chamber, i<j); parameterization (15): `contactScale`, `contactPoint`,
   `contactObjective`, `pairThreshold_isLeast_contact`, `pairThreshold_eq_sInf_contact`.
4. `pairThreshold_pos`; 5. `pairThreshold_lt` (14).
6. `continuousOn_pairThreshold`, `isOpen_chamber` (route: jointly continuous contact objective on the
   subtype × [0,1], `IsCompact.continuous_sInf`).
7. `crossThreshold_le`, `starThreshold_le`, `strongThreshold_le_pair/_le_action`, `strongThreshold_eq_member`,
   `exists_crossThreshold_eq`, `exists_starThreshold_eq`, `crossThreshold_pos`, `strongThreshold_pos`,
   `continuousOn_crossThreshold`, `continuousOn_strongThreshold`, `strongThreshold_eq_min_first` (14). Carrier
   versions: `orderedPairThreshold_pos/_lt`, `continuous_orderedPairThreshold`, `orderedStrongThreshold_pos`,
   `continuous_orderedStrongThreshold`, `orderedStrongThreshold_eq_min_first`.
8. `pairThreshold_le_of_feasible` (all I, ν).
Hypotheses: `hν : ∀ i, 0 < ν i` on items 3–7 (needed so `actionAxis > 0`; with `ν i = 0` division by zero breaks
`a_i > 0`); `2 ≤ n` for cross/strong, `1 ≤ n` for star. Full signatures: see the files (all statements elaborated as written).

## Not done
Interior-optimizer / geometric realization / Laskar–Petit identification (explicitly out of scope).

## Checks
`lp_build.sh` of Defs, Pair, Continuity, Strong, Threshold: all "Build completed successfully", no warnings
in my files. `lp_lint.sh`: exit 0 (FROZEN-ANCHOR GUARD OK, ABI HASHES OK). `#print axioms` (via `lp_lean.sh`
on `.drafts/ax.lean`) of isCompact_pairFeasible, pairFeasible_nonempty, exists_pairThreshold_attained,
pairThreshold_isLeast, exists_contact_minimizer, pairThreshold_isLeast_contact, pairThreshold_eq_sInf_contact,
pairThreshold_pos, pairThreshold_lt, continuousOn_pairThreshold, isOpen_chamber, continuousOn_strongThreshold,
strongThreshold_pos, strongThreshold_eq_member, strongThreshold_eq_min_first, pairThreshold_le_of_feasible,
continuous_orderedStrongThreshold: all exactly `[propext, Classical.choice, Quot.sound]`.

## AUDIT FOCUS
- `pairFeasible` orientation: `a_j(1−v) ≤ a_i(1+u)` as in MAIN; `contactPoint` uses `α = a_i/a_j`, `v = 1−α−α m t`.
- `crossThreshold` index: `AdjIdx` subtype with `succ`; empty family would give `0` (⨅ over empty in ℝ), hence the explicit `2 ≤ n`.
- `strongThreshold_eq_min_first`: (14) needs `B_{i-1,i} < I_i` for i ≥ 2 (I_i need not be increasing); proved so.
- Total `pairThreshold` off the chamber is only the literal sInf (still an attained min, item 2).

## Source defects / deviations / design signals
No errata found in Lemma 4. Deviation: added `hν` (positivity of ν) which MAIN assumes ("positive masses"). No
heartbeat or size problems; every file builds in < 10 s.
