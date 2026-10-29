# T17 prover handoff (branch inp-p11c-t17, 959be8bf; contains T13 (in audit) and T6 round 1; offloaded package run by the main orchestrator)


Files: new `KAM/Planetary/PlanarTorsion/TorsionBound.lean` (~35 lines).
Node `bpP:p11b:remain`: `KAM.Planetary.remain`, signature verbatim from P11CSignatures.lean.
Approach: empty K gives B = 1; otherwise `IsCompact.exists_isMinOn` on `|det|` (`ContinuousOn.abs`),
B = |det at the minimiser| > 0 by hn.
Checks: gate build of KAM.Planetary.PlanarTorsion.TorsionBound succeeded (9250 jobs); no warnings in
my file. `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI hashes OK; it prints
"KAM.lean is out of date" (generated root; not edited per rules, new module needs gen_root_imports.py).
`#print axioms KAM.Planetary.remain`: [propext, Classical.choice, Quot.sound].
Uncertainties: none. Errata: none. Deviations: none. Design signals: none.

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row T17 (remain via compact positivity; T13, Mathlib compact minimum) and its node table incl. bpP:p11b:remain; P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean. Audit ONLY KAM/Planetary/PlanarTorsion/TorsionBound.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
