# P11A-C0 prover handoff (branch inp-p11ac0, e3e3bb8; base inp; offloaded package run by the main orchestrator; prover on claude-12)


Files (new): KAM/Planetary/MaximalStep/Basic.lean (62 lines), KAM/Planetary/MaximalStep/Constants.lean (84 lines).
Branch also contains a merge of inp-p11aw0 (audited W0), see deviation 1.

Declarations (verbatim from P11ASignatures.lean): Basic: domain_def, p11Admissible, p11Bound, p11Real, p11Cut,
p11Taylor, p11Cutoff (nodes c2-conv#data/#bracket carried by existing Phase/actionNbhd/poissonBracket;
domain-def). Constants: p11C, p11Error, p11Loss, p11Lambda, theorem p11_lambda_spec (sec-hom#lambda).

Approach: p11_lambda_spec from KAM.Fourier.exp_sums (b),(c) at x = 2*pi*delta: HasSum over all k gives
coth(pi delta)^n; split off k=0 (modeSize 0 = 0, term 1) via tsum_eq_add_tsum_ite and tsum_subtype; the
bounds are exp_sums (b) bound raised to the n-th power and (c) with 8n/(2 pi delta) = 4n/(pi delta).
hn is unused (exp_sums holds for all n), kept to match the signature.

Checks: gate build `inp_lake_build.sh <wt> KAM.Planetary.MaximalStep.Constants`: "Build completed successfully".
`#print axioms KAM.Planetary.p11_lambda_spec`: [propext, Classical.choice, Quot.sound].
scripts/lint_sources.sh: check_lean_modules PASS (524 files), FROZEN-ANCHOR GUARD OK, ABI HASHES OK; it also
prints "KAM.lean is out of date" (expected; KAM.lean is generated, not edited by me). No long lines.

Deviations / uncertainties:
1. P11Vec/P11CVec/P11Family are defined in WeakMeasure/Basic (W0) in the signature file's namespace; to avoid
   duplicate declarations I merged inp-p11aw0 and Basic imports KAM.Planetary.WeakMeasure.Basic. This is an
   import edge beyond the design's C0 row ("existing Weighted/frozen objects"); the orchestrator may instead
   move the carrier abbrevs. Merge will be trivial if W0 lands first.
2. Basic additionally imports KAM.Strip.RealRestriction and Frozen.Planetary.Defs.Phase (Phase, realInclusion₂).
3. Constants p11C/p11Error/p11Loss/p11Lambda placed in Constants; p11Cutoff etc. in Basic.
No errata, no heartbeat issues.

AUDIT FOCUS (design docs/tracks/P/design/P11A-LEAN-DESIGN.md row P11A-C0 and proof plan; audits DESIGN-P11A-design-audit-{1,2,3}.md; signatures .drafts/design/P11ASignatures.lean): (1) statements/definitions = design signatures (MaximalStep/Basic, Constants; the lambda lattice identity), faithful on their whole carrier; (2) proofs sound; no added premises; (3) hygiene. Audit ONLY KAM/Planetary/MaximalStep/{Basic,Constants}*.lean.
