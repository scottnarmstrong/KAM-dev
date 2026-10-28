# E9 prover handoff (branch inp-p14-e9, c7f3c5ad; offloaded package run by the main orchestrator)


## Files
- NEW `KAM/Planetary/Exponential/Lift.lean` (326 lines, lines <= 100 cols). Nothing else touched.

## Declarations / nodes
- `KAM.Planetary.lift` (`bpP:p14:lift`) — statement copied VERBATIM from P14Signatures.lean (~l.343).
- Steps, all inside the proof of `lift` (labelled by comments, no separate exported lemmas in the signature file):
  `li-init` (w0 from `poincareProd_image_prograde`, collision-free from `hz.2`),
  `li-max` (`gen_maximal` for `hamiltonianVectorField (liftChartHam m mu)` on open `chartSafe`; C1 by
  `contDiffOn_liftField`, periodic by `liftField_periodic`),
  `li-proj` (`liftPhysicalDeriv` + `moving_ode` + `gen_uniqueness_inter`),
  `li-cont` (`uniform_data` (E8) on `liftQ B`, `gen_continuation`, `liftQ_of_orbit`, `liftQ_mem_chartSafe`
  using E3 `real_domain`/`original_cylinder_subset` and `enlarge`),
  `li-concl` (E1 `sec_domain_chart_facts`).
- Helpers (public, `li`/`lift`-prefixed; short names grep-checked unique in KAM): `liftChartHam`, `liftQ`,
  `liftPhysicalDeriv`, `isOpen_chartSafe`, `chartSafe_subset_dom`, `analyticOnNhd_liftChartHam`,
  `contDiffOn_liftField`, `liftFastShift_neg`, `chartSafe_shift_iff`, `liftField_periodic`,
  `liftQ_isClosed`, `liftQ_slow_bound`, `liftQ_fast_bound`, `liftQ_isCompact`, `chartAMD_zeroAngle`,
  `liftQ_of_orbit`, `liftQ_mem_chartSafe`.

## Approach
`poincareProd : Phase (n+n) → Phase (n*2)` is not an endomorphism, so `chart_orbit` (fixed `d`) is applied to
the equal-dimension chart `poincareProdCast` through `phaseCast (Nat.mul_two n)` (`liftPhysicalDeriv`).
The compact zero-angle set `liftQ B` is closed and bounded (closed ball in the sup norm); E8 `uniform_data`
needs `hQW`, obtained because `enlargedCylinder` membership does not see the fast angles.

## Checks
- `inp_lake_build.sh ... KAM.Planetary.Exponential.Lift`: "Build completed successfully (9137 jobs)",
  no warning in Lift.lean (warnings shown are pre-existing, in Chart.lean / RealDomain.lean).
- `#print axioms KAM.Planetary.lift`: [propext, Classical.choice, Quot.sound].
- `scripts/lint_sources.sh`: only complaint is pre-existing `KAM/Frozen/Planetary/Theorems/AmdConfinement.lean:77`
  (101 cols; frozen file, not mine; already fixed by a later commit on inp "amdConfinement seal: rewrap").
- No `set_option`, no sorry/axiom; no EuclideanSpace; no provider or DRAFT_SORRY import.

## Uncertainties / notes
- `KAM.Planetary.SecularSpectrum.lift` (SecularSpectrum/Lift.lean) shares the short name `lift` in a different
  namespace; the signature file mandates `KAM.Planetary.lift`. Callers that `open SecularSpectrum` get ambiguity.
- `lift` consumes `enlarge`/`EnlargedData` internally only to place `liftQ B` in `chartSafe`.
- No errata or deviations found; statement was provable as written.

AUDIT FOCUS: design docs/tracks/P/design/P14-LEAN-DESIGN.md row E9 (lift) and its node table; P14 design audits; signatures /root/code/KAM-inp/.drafts/design/P14Signatures.lean line ~343. Audit ONLY KAM/Planetary/Exponential/Lift.lean. Common to all: (a) every declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
