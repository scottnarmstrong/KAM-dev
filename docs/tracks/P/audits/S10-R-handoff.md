# S10-R prover handoff (branch inp-s10r, c1db3418; contains inp-s10f (in audit) and inp-s10h (audited); offloaded package run by the main orchestrator; prover on claude-12)


**File (new):** KAM/Planetary/Nondegeneracy/Frequency.lean (230 lines). KAM.lean NOT regenerated (lint says out of date; orchestrator to run scripts/gen_root_imports.py).

**Declarations (signatures verbatim):** action_diffeomorphism (bpP:p10:conv#data), frequency, frequencyAxes (bpP:p10:sec-rnd#data), rnd (bpP:p10:rnd), scaling (bpP:p10:scaling). `rnd_def` imported from S10-Z AnalyticZeros. Helpers (new public names, grepped unique): analyticAt_action, analyticAt_axis, axis_action, action_axis, actionDomain_eq, analyticAt_frequency, analyticAt_frequencyAxes, exists_relation_ne, sum_append, exists_freq_ne.

**Approach:** action/axis: explicit formulas; actionDomain = {I>0, axis I ∈ axes}, open as preimage; analyticity by sqrt/pow/div. rnd: analyticity of frequency at action a from sorted_analytic (S10-H) and the axis/action inverse; frequencyAxes by composition. rnd_def: f_nonzero + fc_analytic + analytic_zero_null on `axes n` give a point of any nonempty open B ⊆ axes with fc_def ≠ 0, hence the identity-permutation relation ≠ 0; the five rnd_def clauses follow by choosing c̃ = (c1, 2c2), (c,0), (0,c) etc. scaling: reindex by p.symm with coefficients c(p⁻¹ j)·s(p⁻¹ j).

**Checks:** gate build `inp_lake_build.sh ... KAM.Planetary.Nondegeneracy.Frequency`: success, no warnings in my file. `#print axioms` of action_diffeomorphism, rnd, scaling: [propext, Classical.choice, Quot.sound]. scripts/lint_sources.sh: check_lean_modules PASS, frozen guard OK, ABI hashes OK; only message "KAM.lean is out of date" (generated; not edited per rule).

**Imports:** AnalyticZeros, GoodAxes (convex_axes, isConnected_axes, sorted_analytic), SymmetricRelation. No provider / DRAFT_SORRY imports. No maxHeartbeats, no sorry/axiom.

**Uncertainties / errata / deviations:** none. Note rnd's simpleAxes hypothesis is only used for analyticity; the rnd_def clauses need only B ⊆ axes open nonempty. No heartbeat design signals.

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S10-R and its proof plan; audits DESIGN-P810-design-audit-{1,2}.md; signatures .drafts/design/P810Signatures.lean): (1) action_diffeomorphism, frequency, frequencyAxes, rnd, scaling = signature file exactly, and the S10-R slice COMPLETE;  matters doubly because P11A-W2 ports it exactly; (2) proofs sound (S10-F relation, S9-S local_analytic / sorted_analytic, S10-Z analytic zeros consumed as designed; actionDomain openness; analyticity); the note that rnd's simpleAxes hypothesis is only used for analyticity: confirm it is a SIGNATURE premise (not added) and not vacuous; no added premises; (3) hygiene (no EuclideanSpace; no public name already used elsewhere in KAM). Audit ONLY KAM/Planetary/Nondegeneracy/Frequency.lean.
