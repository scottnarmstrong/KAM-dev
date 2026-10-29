# N10-4 prover handoff (branch inp-n104, df56ace5; offloaded package run by the main orchestrator)


**Files:** new `KAM/Nekhoroshev/Assembly/Existence.lean` (~85 lines). Nothing else touched.

**Declarations (signatures verbatim from N10Signatures.lean):** `ex_ball`, `existence`,
`head_solution_restrict`, `uniqueness`. Nodes: `bpN:p10:existence`, `stepN:p10:ex-rho/ex-ball/ex-apriori/ex-glue`,
`bpN:p10:uniqueness`, `stepN:p10:un-restrict/un-apply`.

**Approach:** `ex_ball` by triangle inequality with `cp_size` (rho ≤ R/4, ‖I0‖ < R/2). `existence`: `Data` built
as `⟨hp.hR, hp.hs, hh.1, hf⟩`; `ODE.confinement_glue` with U = actionBall n p.R (isOpen_ball, ball_subset_ball
for R ≤ R+s), hconf := `confinement` (valid for every OrdConnected J, in particular open ones); uniqueness part
of the glue output discarded. `head_solution_restrict`: pointwise restriction. `uniqueness`: exact
`ODE.uniqueness_closed` after restricting z; L = 0 handled inside it.

**Checks:** gate build `KAM.Nekhoroshev.Assembly.Existence`: "Build completed successfully (3338 jobs)".
Only warning in my file: unused variable `hL` in `uniqueness` (signature-mandated binder, kept verbatim).
`#print axioms` of all four: `[propext, Classical.choice, Quot.sound]`.
`scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK. It also reports
two pre-existing, non-mine items: line >100 cols at `KAM/Frozen/Planetary/Theorems/AmdConfinement.lean:77`
(frozen, untouched) and "KAM.lean is out of date" (generated; I do not edit it, orchestrator regenerates).

**Uncertainties / errata / deviations / design signals:** none. No heartbeat issues.

AUDIT FOCUS: design docs/tracks/N/design/N10-LEAN-DESIGN.md row N10-4 (ex_ball, existence, head_solution_restrict, uniqueness) and its audit; signatures /root/code/KAM-inp/.drafts/design/N10Signatures.lean. Contains N10-3 (in a re-scope audit; its signed cf_branch is deliberately narrowed to |t| <= 2T): check that N10-4's consumption is consistent with that. Audit ONLY KAM/Nekhoroshev/Assembly/Existence.lean. Common to all: (a) every declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name (signed names follow the signature file), no harmful root shadow, lines <= 100.
