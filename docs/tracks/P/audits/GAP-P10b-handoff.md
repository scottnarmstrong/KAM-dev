# GAP-P10b prover handoff (branch inp-gp10b, 20bf611a; off inp with GAP-P10a (landed); graph-gap programme package run by the main orchestrator)


Files: new `KAM/Planetary/Nondegeneracy/RelationNodes.lean` (committed on inp-gp10b). `FiniteTypeNodes.lean`
not created: all its nodes were already closed. KAM.lean not edited (lint reports it out of date: regenerate).

## Node map
- `bpP:p10:scaling` (was NOT_STARTED): `Nondegeneracy.rnd_def_scale_iff` (R-nondegeneracy invariant, an iff,
  for any positive diagonal s) and `Nondegeneracy.scaling_index_amount` (rnd iff; finiteness of the index iff;
  index equal for any two existence proofs; lo^2*beta <= beta~ <= hi^2*beta at the index). Hypotheses are the
  source setting only: B open, K compact nonempty in B, 0<m, omega analytic on B, 0<lo<=s_i<=hi. Built from
  `scaling`, `scaling_amount`, `betaFamily_nonneg`, `Nat.find_congr'`.
- Already closed (LEAN_STATUS PROVED on this branch, named to parents): `stepP:p10:F-A`, `F-B`, `F-C`
  (f_nonzero), `ft-pt`, `ft-cover`, `ft-min` (finite_type), `st-prod` (stability). No new exports written.

## Checks
- Gate build `KAM.Planetary.Nondegeneracy.RelationNodes`: success, no warnings in my file.
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI OK; only message: KAM.lean out of date (generated, not mine).
- `#print axioms` of both theorems: propext, Classical.choice, Quot.sound.

## Uncertainties / errata / deviations
None. No heartbeat overrides; file ~85 lines. Diagonal rescaling only (no permutation), as in the source remark;
permutation form is already `scaling`.

ORCHESTRATOR RULING (OVERNIGHT 01:20, 01:35): graph-gap programme. This package appends UNSIGNED exports stating the LITERAL conclusion of each listed graph node; nodes already PROVED or BYPASSED in the graph are skipped. Package definition: section '**GAP-P10b:**' of /root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-P.md. KAM.lean regeneration is the sub-orchestrator's job at merge, not a finding.

AUDIT FOCUS: bpP:p10:scaling: read its NODE record in docs/graph/P/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and the blueprint lines it cites; does ONE named declaration (or the pair the handoff names, then say whether one of them states the whole node) state its literal conclusion under only the source's hypotheses, quantifiers in source order? An export taking a proved dependency's OUTPUT as a premise is a FAIL. Also verify that each node the handoff lists as 'already closed' is PROVED or BYPASSED in docs/graph/P/DEPGRAPH.md or AMENDMENTS.md. Audit ONLY KAM/Planetary/Nondegeneracy/RelationNodes.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
