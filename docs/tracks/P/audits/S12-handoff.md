# S12 prover handoff (branch inp-p14-s12, 52942a18; contains S11 Safety (in audit) and S7-S10; offloaded package run by the main orchestrator)


**Files:** new `KAM/Planetary/SecularBox/CitedMasses.lean` (~60 lines, max width 100).
**Declarations:** `KAM.Planetary.sb_cited` (signature verbatim; node `bpP:p14:sb-cited`, step `sb-ci-1`),
`KAM.Planetary.sbCited_mass_identity : (4773/5000000:ℝ)*(476/1591) = 357/1250000` (`norm_num`;
same fact also in `sb_numerics`).
**Approach:** `sb_cited` = `sb_safety (476/1591) (4773/5000000) (by constructor <;> norm_num) (by norm_num) w0 hw0`;
the conclusion is defeq-literal, no unfolding needed.
**Checks:** gate build of `KAM.Planetary.SecularBox.CitedMasses` succeeded (only warning: pre-existing unused `hmu`
in S11 Safety.lean:157). `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI hashes OK; it
reports "KAM.lean is out of date" (expected, generated; not edited).
`#print axioms sb_cited` and `sbCited_mass_identity`: [propext, Classical.choice, Quot.sound].
**Provider terms (not edited):**
- secularBoxAtCitedMasses: `by exact KAM.Planetary.sb_cited w0 hw0` (imports `KAM.Planetary.SecularBox.CitedMasses`).
- secularBoxSafety: `by exact KAM.Planetary.sb_safety saturn mu hsaturn hmu w0 hw0` (imports `KAM.Planetary.SecularBox.Safety`; S11 sb_safety already has the exact frozen telescope).
**Uncertainties / errata / deviations:** none. No heartbeat overrides. The unsigned helper
`sbCited_mass_identity` is an extra export; short name unused elsewhere in KAM.

AUDIT FOCUS (SEAL-KEY AUDIT): design docs/tracks/P/design/P14-LEAN-DESIGN.md row S12 (sb_cited and the exact decimal mass identity; S11, S0) and its node table; P14 design audits; signatures /root/code/KAM-inp/.drafts/design/P14Signatures.lean. This package is the provider for TWO frozen anchors: KAM.Planetary.secularBoxSafety (KAM/Frozen/Planetary/Theorems/SecularBoxSafety.lean, manifest id planetary.d25.secularBoxSafety.v1) via S11's sb_safety, and KAM.Planetary.secularBoxAtCitedMasses (KAM/Frozen/Planetary/Theorems/SecularBoxAtCitedMasses.lean, manifest id planetary.d25.secularBoxAtCitedMasses.v1) via sb_cited. For EACH anchor: (1) compile an exact-type probe in a scratch file outside KAM/, of the form example : type_of% @KAM.Planetary.secularBoxSafety := @KAM.Planetary.sb_safety (and likewise sb_cited), or the exact term the handoff gives, and report the result; (2) a PROSPECTIVE seal: in a scratch copy only (never edit the frozen files or the manifest), replace the frozen body 'by sorry' with the handoff's 'by exact ...' term and confirm it elaborates and that #print axioms shows only propext, Classical.choice, Quot.sound; (3) confirm the provider chain consumes S0-S11 as designed with no added premise, and that the frozen statements' binders are matched exactly. Audit KAM/Planetary/SecularBox/CitedMasses.lean in full; S11 Safety.lean has its own audit, but check the sb_safety-to-anchor seal key here. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
