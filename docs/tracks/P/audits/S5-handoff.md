# S5 prover handoff (branch inp-p14-s5, 0dbb6ad4; offloaded package run by the main orchestrator)


**Files:** new `KAM/Planetary/SecularBox/Smooth.lean` (≈345 lines). No other file touched.

**Declarations (verbatim from P14Signatures.lean):** `explicitSecularIntegrand` (def),
`secular_integrand_identity` (sb-sm-1), `secular_integrand_smooth` (joint C^∞ on `S ×ˢ univ` +
2π-periodicity; sb-sm-2), `sb_smooth_prop` (C^∞ of `exactSecularHamiltonian` on `sb_sdef`,
literal `SecularRegular` on `sb_sdef`, global λ-independence; sb-sm-3/sb-sm-4 are internal steps,
sb-sm-3 uses S4 `secular_parametric_integral`). `secular_field_components` belongs to S7, not here.
Integrability is the third clause of `SecularRegular` (continuity of the explicit integrand on the
compact box).

**Approach:** identity by `simp only` unfolding plus `fast/slow` of `assemble`. Smoothness: pointwise
`ContDiffAt` chain (eccentricity scale `sqrt`, root, position, momentum, Jacobian, `ellipsePhase`,
`movingHamiltonian` at `NoCollision` points via `analyticAt_planeLength`), with side conditions from
`sb_s`; composition and product. C^∞ via `contDiffOn_infty` and `secular_parametric_integral` for
each finite order. All helpers are `private` (`sbSmooth_*`); no new public names besides the three
signature declarations + def (grepped: none existed in KAM).

**Checks:** gate build `KAM.Planetary.SecularBox.Smooth` succeeds, no warnings/sorry.
`scripts/lint_sources.sh`: PASS (`check_lean_modules`, frozen guard, ABI hashes); it reports an
existing 101-col line in Frozen/.../AmdConfinement.lean and `KAM.lean out of date` (not mine, not edited).
`#print axioms` for sb_smooth_prop, secular_integrand_identity, secular_integrand_smooth:
`[propext, Classical.choice, Quot.sound]`.

**Uncertainties / errata / deviations:** none. No heartbeat issues (default budget). No
signature changes; no frozen/quarantined imports.

**Addendum (orchestrator note):** Region does not yet export the sb-S-1 radicand margin; Smooth proves it locally as private `sbSmooth_radicand_margin` (both 99/100 < 1-γ/(2Λ) and 99/(100Λ) < (…)/Λ) and `sbSmooth_reg` consumes it. Rebuilt via gate: OK. When Region's fix lands, this local copy can be replaced by the export.

AUDIT FOCUS: design docs/tracks/P/design/P14-LEAN-DESIGN.md row S5 (sb_smooth_prop, explicitSecularIntegrand, secular_integrand_identity, secular_integrand_smooth, integrability) and its node table (sb-sm-*); P14 design audits; signatures /root/code/KAM-inp/.drafts/design/P14Signatures.lean lines ~441-465. The handoff says secular_field_components belongs to S7: check. Note S3 is being fixed (radicand margin of sb-S-1, consumed by sb-sm-2): check how S5 obtains that bound. Audit ONLY KAM/Planetary/SecularBox/Smooth.lean. Common to all: (a) every declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public helper short name, no root shadow, lines <= 100.
