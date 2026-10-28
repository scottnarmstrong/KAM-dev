# N11-B prover handoff (branch inp-n11b, 0980c13b; offloaded package run by the main orchestrator)


**Files:** new `KAM/Nekhoroshev/Partial/Constants.lean` (~115 lines), committed on inp-n11b.

**Declarations (verbatim from N11Signatures.lean):** `exponents` (proved), `PartialConstants` and its
namespace defs (s, m1, M1, g1, r0, A, eps0, R0, kappaC, cK, eps, K, d, kappa, rTheta, blockTime),
`PartialData`, `constants`, `DefiniteSign`. Graph steps `stepN:p11:ex-den`/`ex-cmp` are internal to
`exponents`.

**Approach:** `exponents`: D = 6n²−3n+14 > 0 by nlinarith; positivity; `div_lt_div_of_pos_right`; the
last inequality reduces to 12n < D, i.e. 6n²−15n+14 > 0 (nlinarith).

**Checks:** gate build `KAM.Nekhoroshev.Partial.Constants`: success, no warnings. `#print axioms
KAM.Nekhoroshev.exponents`: propext, Classical.choice, Quot.sound. No lines > 100 columns. Lint
(`scripts/lint_sources.sh`): check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; the only
message is "KAM.lean is out of date" (new module; KAM.lean must not be edited by me, orchestrator regenerates).

**Name check:** the short name `constants` also exists as `KAM.Planetary.TwoScale.constants` (different
namespace, fully qualified names differ); kept verbatim per the signature. No other clashes found.

**Uncertainties / errata / deviations:** none. Not done here (other packages): block_setting, signedH,
signedF, slowScale, blockPert (need PartialBlock, N11-A) and `hessian` (N11-E3).

AUDIT FOCUS: design docs/tracks/N/design/N11-LEAN-DESIGN.md row N11-B (Constants: PartialData/PartialConstants, DefiniteSign, exponents, literal numerical formulas) and both design audits DESIGN-N11-design-audit-{1,2}.md; signatures /root/code/KAM-inp/.drafts/design/N11Signatures.lean. Check every literal numerical formula and exponent against the source and the frozen exponents; the handoff lists items left to other packages (block_setting, signedH, ...): confirm the design assigns them elsewhere. Audit ONLY KAM/Nekhoroshev/Partial/Constants.lean. Common to all: (a) every declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established; an exported lemma named after a graph node must state that node's literal conclusion; steps the design keeps internal may stay internal; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public short name, no root shadow, lines <= 100.
