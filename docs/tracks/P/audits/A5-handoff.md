# A5 prover handoff (branch inp-p14-a5, 8d0d536b; off inp; offloaded P14 package run by the main orchestrator)


**Files:** new `KAM/Planetary/AMD/AngularMomentum.lean` (branch inp-p14-a5). KAM.lean not touched (lint reports it out of date; the orchestrator regenerates).

**Declarations** (all in `KAM.Planetary`; signatures verbatim from P14Signatures.lean):
- `interval_constancy` (bpP:p14:x-calc wrapper): proof via `constant_of_has_deriv_right_zero` on `Icc a b ⊆ J` (OrdConnected), both orders. Deviation from the design's suggested route (`Convex.is_const_of_fderivWithin_eq_zero`): simpler, same statement, no extra premise.
- `sum_mass_mul_cross_fKernel` (ordered-pair cancellation; new helper, name grepped unused): `∑ i, m i * planeCross (q i) (fKernel m q i) = 0`, by antisymmetry of the double sum.
- `ang_mom` (bpP:p14:ang-mom; steps am-eq/am-der/am-const): per-body derivative from `hasDerivAt_bodyVector`, `hamiltonianVectorField_moving` (private `cross_rate_eq`), sum cancels via the cross-product identity `P×P=0` and the ordered-pair cancellation; conclusion by `interval_constancy`.
No other declaration in the signature file belongs to A5.

**Checks:** gate build `KAM.Planetary.AMD.AngularMomentum`: success, no warnings in my file (only pre-existing Kepler/Energy linter warnings). `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only message: "KAM.lean is out of date; run scripts/gen_root_imports.py" (generated file, not mine to edit).
`#print axioms` for ang_mom, interval_constancy, sum_mass_mul_cross_fKernel: [propext, Classical.choice, Quot.sound].

**Rules:** no maxHeartbeats, no sorry/axiom, no EuclideanSpace, no provider/DRAFT_SORRY imports (frozen Defs only). Imports `KAM.Kepler.Plane` for `planeLength_sub_comm`.

**Uncertainties / errata / design signals:** none. No heartbeat problems.

AUDIT FOCUS (design docs/tracks/P/design/P14-LEAN-DESIGN.md row A5 and its proof plan; P14 design audits; signatures /root/code/KAM-inp/.drafts/design/P14Signatures.lean): (1) interval_constancy and ang_mom = signature file EXACTLY, and the A5 slice COMPLETE (steps am-eq/am-der/am-const; read the design row and proof plan line by line; a sibling package failed for an omitted proof-plan obligation); (2) the route deviation for interval_constancy (constant_of_has_deriv_right_zero on Icc a b inside J, both orders instead of Convex.is_const_of_fderivWithin_eq_zero): sound and covers every order of the endpoints; (3) ang_mom: the per-body derivative, the ordered-pair cancellation helper sum_mass_mul_cross_fKernel, and the consumption of hamiltonianVectorField_moving; no added premises; (4) hygiene (no EuclideanSpace; no public short name already used elsewhere in KAM; no root shadow). Audit ONLY KAM/Planetary/AMD/AngularMomentum.lean.
