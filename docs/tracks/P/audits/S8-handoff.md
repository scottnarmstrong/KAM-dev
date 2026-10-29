# S8 prover handoff (branch inp-p14-s8, 3f56dc48; offloaded package run by the main orchestrator)


**Files:** new `KAM/Planetary/SecularBox/SlowFlow.lean` (~210 lines, lines ≤ 100 cols). Nothing else touched.

**Declarations:** `KAM.Planetary.sb_slow` (signature verbatim; `bpP:p14:sb-slow`). Private helpers
`sbSlow*` (slice map `sbSlowG`, AMD `sbSlowA`, `sbSlow_conserved`, membership iff).

**Approach (steps):** sb-sl-1: `sb_smooth_prop` composed with the affine slice map, `ham_smooth_c1`;
sb-sl-2: `gen_maximal`; sb-sl-3: `sbSlow_conserved` via `secular_field_components` + `sb_field`
(derivative of AMD is 0, constant on the open interval); sb-sl-4: K = {AMD = A0} compact (closed, bounded by
1+2A0), K ⊆ slice using hI and 50·A0 < 87/100 (from hA < 16373/2500000, inline); sb-sl-5:
`gen_continuation_compact` both ends ⇒ Tp=⊤, Tm=⊥, `eIoo_bot_top`.

**Checks:** gate build `KAM.Planetary.SecularBox.SlowFlow` OK, no warnings; `scripts/lint_sources.sh`:
check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK (it only reports KAM.lean out of date,
which is generated and not edited by me). `#print axioms KAM.Planetary.sb_slow` = [propext, Classical.choice, Quot.sound].
No set_option, no sorry.

**Uncertainties / errata / deviations:** none. No heartbeat issues.

AUDIT FOCUS: design docs/tracks/P/design/P14-LEAN-DESIGN.md row S8 (sb_slow; S7, S0, ODE/Maximal, Continuation) and its node table; P14 design audits; signatures /root/code/KAM-inp/.drafts/design/P14Signatures.lean line ~495. S7 is in a fix round (sb-pr-1 regularity, omega continuity; append-only): note whether S8 needed those facts and how it obtained them. Audit ONLY KAM/Planetary/SecularBox/SlowFlow*.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
