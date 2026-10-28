# S3 prover handoff (branch inp-p14-s3, b1f2c0ae; offloaded package run by the main orchestrator)


**Files:** new `KAM/Planetary/SecularBox/Region.lean` (~175 lines). No other file touched.

**Declarations (verbatim from P14Signatures.lean):** `sb_sdef` (def), `sb_s` (theorem, proved).
Graph nodes: `bpP:p14:sb-smooth#data` / `sb-Sdef` -> `sb_sdef`; `sb-S` -> `sb_s`; steps `sb-S-1/2/3` are internal
(private `sbRegion_planet` for S-1, S-2; the radii step S-3 and the pairwise NoCollision are inline in `sb_s`).
No S3 node belongs to another package.

**Approach:** openness: S is a finite intersection of strict inequalities of continuous functions
(private `sbRegion_*` continuity lemmas, `isOpen_lt`). Geometry: `sb_chart` (S1) gives root, ecc, Jacobian and the
position-length identity; k>49/50 from 50Γ<Λ, e^2=1-k^2<99/2500<1/25, J≥1-e>4/5; radii |q0|<53/10·6/5,
|q1|>47/5·4/5, reverse triangle inequality gives |q1-q0|>0, positivity of |q_i| = a_i J_i.
`sb_numerics` (S0) is imported but the rational comparisons (N6c, N6d) are closed inline by norm_num/nlinarith.

**Checks:** gate build `inp_lake_build.sh ... KAM.Planetary.SecularBox.Region`: success, no warnings (after
replacing deprecated `mem_setOf_eq`/`push_neg`). `scripts/lint_sources.sh`: after wrapping two long lines, the only
remaining message is "KAM.lean is out of date" (generated, deliberately not edited); module check, frozen-anchor guard
and ABI hashes OK. (I did not re-run the full lint after wrapping the lines; the awk check shows 0 lines >100.)
`#print axioms KAM.Planetary.sb_s` and `sb_sdef`: [propext, Classical.choice, Quot.sound].

**Uncertainties / errata / deviations:** none. No heartbeat overrides; no set_option. Signatures unchanged.
Note: `lake env lean` on a scratch file failed with a missing `SecularBox/Covariance.olean` (stale environment
artifact, unrelated to this module); axioms were obtained via a temporary `#print axioms` in the gate build, then removed.

AUDIT FOCUS: design docs/tracks/P/design/P14-LEAN-DESIGN.md row S3 (sb_sdef, sb_s) and its node table/proof plan; P14 design audits; signatures /root/code/KAM-inp/.drafts/design/P14Signatures.lean lines ~371 (sb_sdef), ~435 (sb_s). sb_sdef is a definition: it must mean the source secular box region on its whole carrier. S3 contains S0 and S1 (both audited separately; S1 has a round-2 positivity addition on its own branch). Audit ONLY KAM/Planetary/SecularBox/Region.lean. Common to all: (a) every declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established; an exported lemma named after a graph node must state that node's literal conclusion; steps the design keeps internal may stay internal; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public short name, no root shadow, lines <= 100.
