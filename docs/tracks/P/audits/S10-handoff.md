# S10 prover handoff (branch inp-p14-s10, cd7f46c1; offloaded package run by the main orchestrator)


**Files:** new `KAM/Planetary/SecularBox/Uniqueness.lean` (~100 lines). KAM.lean not touched (lint reports it
out of date: root imports need regeneration by the orchestrator).

**Declarations:** `KAM.Planetary.sb_unique` (signature verbatim, only line-wrapped for the 100-col limit);
private helper `sbUnique_local`. Nodes `sb-un-1`/`sb-un-2` = `sbUnique_local` (continuity keeps v in open S near
an agreement point; `sb_pred` converts to `IsSolutionIn`; `sb_regular.2` gives C^1 field; `KAM.ODE.gen_uniqueness`
on a ball). `sb-un-3` = in `sb_unique`: u = interior of agreement set is open, `closure u ∩ U ⊆ u` by continuity
of v,w, then `IsPreconnected.subset_of_closure_inter_subset` with `Convex.isPreconnected`.
Imports: KAM.ODE.Uniqueness, SecularBox.Field (S9 not needed; sb_global not used).

**Checks:** gate build `KAM.Planetary.SecularBox.Uniqueness`: success, no warnings. `scripts/lint_sources.sh`:
check_lean_modules PASS, frozen guard OK, ABI hashes OK; only message "KAM.lean is out of date" (not edited, per rules).
`#print axioms KAM.Planetary.sb_unique`: [propext, Classical.choice, Quot.sound].

**Uncertainties / errata / deviations:** none. No heartbeat issues. No sorry.



AUDIT FOCUS: design docs/tracks/P/design/P14-LEAN-DESIGN.md row S10 (sb_unique; S9, S7, gen_uniqueness, connectedness) and its node table incl. stepP:p14:sb-un-*; P14 design audits; signatures /root/code/KAM-inp/.drafts/design/P14Signatures.lean. S10 uses S7's fix-round export sb_regular (S7 round 2 in audit). Audit ONLY KAM/Planetary/SecularBox/Uniqueness.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
