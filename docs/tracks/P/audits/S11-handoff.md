# S11 prover handoff (branch inp-p14-s11, a137e910; offloaded package run by the main orchestrator)


**Files:** `KAM/Planetary/SecularBox/Safety.lean` (new, 279 lines, all lines <= 100 cols). Nothing else touched.

**Declaration:** `KAM.Planetary.sb_safety`, signature copied verbatim from `P14Signatures.lean`
(sorry replaced by a proof; no premise added, hmu is an unused signed binder).

**Approach (graph steps, all internal private helpers):**
- sb-th-1 `sbSafety_actions`: 87/100<L0<23/10, 87/100<L1<97/100 (squares, N2/N3).
- sb-th-2 `sbSafety_amd` (+ `sbSafety_gamma_lt`): sb_chart gives k, Gamma=L(1-k); AMD<16373/2500000.
- sb-th-3 `sbSafety_mem`: w0 in `sb_sdef`.
- sb-th-4 `sb_global`; sb-th-5 `sb_unique` (regularity hypothesis of (b) unused).
- sb-th-6 `sbSafety_ecc`: e<3/20 from conserved actions (N5a/b).
- sb-th-7: `sb_smooth_prop`.2.1 on w t in S.
- sb-th-8 `sbSafety_bridge`; sb-th-9/10 `sbSafety_rad` (+ sb_chart radial bounds, axis conserved);
  sb-th-11: `barycentricPositions_succ_sub_zero/succ` + planeLength triangle lemmas, case split on Fin 3.
Inputs used: sb_chart, sb_s (via sb_smooth_prop), sb_global, sb_unique, Newtonian/Barycentric.
Rational facts discharged inline by norm_num/linarith (sb_numerics not destructured).

**Checks:**
- Gate: `inp_lake_build.sh ... KAM.Planetary.SecularBox.Safety` -> "Build completed successfully", only
  warning: unused `hmu` (signed binder, kept verbatim). No sorry warning.
- `#print axioms KAM.Planetary.sb_safety` -> `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI hashes OK; only note
  "KAM.lean is out of date; run scripts/gen_root_imports.py" (new module; orchestrator regenerates, not edited).
- No set_option, no EuclideanSpace, no new public helpers (all helpers private, `sbSafety_*`).

**Uncertainties / errata / deviations:** none. No signature or source defects found.



AUDIT FOCUS: design docs/tracks/P/design/P14-LEAN-DESIGN.md row S11 (sb_safety; S0, S1, S3, S5, S9, S10, Barycentric) and its node table incl. stepP:p14:sb-sf-* steps; P14 design audits; signatures /root/code/KAM-inp/.drafts/design/P14Signatures.lean. On the critical path of the frozen anchors secularBoxSafety and secularBoxAtCitedMasses. Audit ONLY KAM/Planetary/SecularBox/Safety.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
