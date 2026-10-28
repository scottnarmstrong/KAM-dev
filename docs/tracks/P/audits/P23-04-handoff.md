# P23-04 prover handoff (branch inp-p2304, 4f40f9c; off inp; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/TwoScale/Cover.lean` (~100 lines); this handoff. KAM.lean untouched (lint reports it out of date, as expected; orchestrator regenerates).

**Proved:** `bpP:p3:cover` -> `KAM.Planetary.cover`, signature verbatim from P23Signatures.lean (namespace `KAM.Planetary`).

**Approach:** cv-ext: `KAM.mcshane` extends `g|X` to a `lam`-Lipschitz `G` on the whole space. cv-bij: `x ↦ x+G x` has the two-sided bound, hence is injective; surjective by Banach fixed point of the contraction `x ↦ y - G x` (`ContractingWith.fixedPoint_isFixedPt`); `Equiv.ofBijective`. cv-loc: for `y∈X`, `x=F.symm y` gives `‖x-y‖=‖G x‖ ≤ lam‖x-y‖+‖g y‖`, so `(1-lam)‖x-y‖ ≤ η`. Cases `η=0` and `X=∅` need no special handling. No Measure.Lipschitz import was needed.

**Checks:** gate build `KAM.Planetary.TwoScale.Cover`: success; only warning: `hη` unused (kept: signature verbatim; the bound `‖g x‖≤η` on X for X nonempty already forces η≥0, and the empty case never needs it). `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only message "KAM.lean is out of date". `#print axioms KAM.Planetary.cover`: [propext, Classical.choice, Quot.sound].

**Uncertainties / errata / deviations / design signals:** none. No heartbeat issues.

AUDIT FOCUS (design docs/tracks/P/design/P23-LEAN-DESIGN.md revision 2, row P23-04 and its proof plan; audits DESIGN-P23-design-audit-{1,2}.md; signatures .drafts/design/P23Signatures.lean; blueprint-P p3a cover): (1) statement = design signature and blueprint (cover; fixed point for the inverse, including eta = 0 and the empty base); (2) proof sound; no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY the P23-04 module(s) (KAM/Planetary/TwoScale/Cover*).
