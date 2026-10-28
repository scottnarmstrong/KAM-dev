# P11A-P5W prover handoff (branch inp-p11ap5w, 6f5b7340; contains P11A-P2f (passed) and P11A-P5 round 2 (in audit); offloaded package run by the main orchestrator)


Branch `inp-p11ap5w`. Merged inp-p11ap5 twice (second after READY-P11A-P5c: amended `p11d1 = min (p11s1 C eps*C.sigma) (C.rz^2)`).

## Files
- NEW `KAM/Planetary/Preparation/FastSigned.lean` (~55 lines), imports `Fast` and `HoloAssembly` (no cycle; Fast.lean untouched).

## Declarations
- `p11SecularHReal_of_spec : P11SecularSpec D C -> P11SecularHReal C` (unsigned helper, distinct name): uses the amended
  h-realness clause (`hC.2.1 J _ |>.2`); ball form converted to norm form by `mem_ball_iff_norm, <- map_sub, norm_realInclusion`.
- `avg_fast` (verbatim signed statement): `avg_fast_of_spec (holo_chart D).choose_spec.1 (p11SecularHReal_of_spec ..)`.
- `p11FastData` (verbatim signed).
No new hypothesis on signed statements; no frozen/provider import.

## Checks
- Gate build `KAM.Planetary.Preparation.FastSigned` (after P5c merge): success. Only warnings are pre-existing unused-variable
  lints in HoloAssembly (not mine).
- `#print axioms` of `avg_fast`, `p11FastData`, `p11SecularHReal_of_spec`: `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only remark "KAM.lean out of date" (generated, not edited).

## Uncertainties / errata / deviations
None new. E1 (P5) is now closed: `P11SecularHReal` is derived from the spec. `P11SecularHReal` remains a premise of the core
`avg_fast_of_spec` (P5 owns it). P7 should use P5c's exported eta1 rate for `as-osc`.

ORCHESTRATOR RULINGS: 21:50 (P5 parametric core; signed avg_fast/p11FastData are wrappers once holo_chart exists), 22:46 (P11SecularSpec h-realness clause), 23:20 (p11d1 parenthesization).

AUDIT FOCUS: the signed avg_fast and p11FastData (P11ASignatures.lean ~lines 822-830) EXACTLY, proved without any added hypothesis from holo_chart's spec and P5's avg_fast_of_spec; p11SecularHReal_of_spec derives P5's realness hypothesis from the AMENDED P11SecularSpec only; graph node bpP:p11:avg-fast now complete (with P5's steps af-*). Audit ONLY KAM/Planetary/Preparation/FastSigned.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
