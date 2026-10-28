# P4-LI prover handoff (branch inp-p4li, 778a9bd; contains inp-p45s (P45-S, audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/PGMeasure/CompactLipschitz.lean` (170 lines). Nothing else touched.

**Declarations** (signatures as in P45Signatures.lean; `{a : ℕ}` made explicit in `lip_inverse` since the file has no `variable`):
- `ext_deriv` (bpP:p4:ext-deriv): `AnalyticOnNhd.fderiv` + `AnalyticOnNhd.contDiffOn_of_completeSpace`.
- `lip_compact` (bpP:p4:lip-compact), printed partial-C1 premises. Private helper `lip_local`: local uniform bound of the
  partial derivative near a point of O, mean value inequality on a ball (stepP:p4:lc-local). Main proof by contradiction
  (stepP:p4:lc-contra): sequence of violating triples (t,x,y) for L=n, compact subsequence on T×X×X, f bounded on T×X so
  |x_n−y_n|→0 hence limits x=y, then contradiction with local bound at the limit.
- `lip_compact_c1`: derived from `lip_compact` (partial derivative = fderiv f ∘ inr, continuity from `ContDiffOn.continuousOn_fderiv_of_isOpen`). Distinct conditional helper, not used in place of lip_compact.
- `lip_inverse` (bpP:p4:lip-inverse): g is the frozen inverse; continuity of fastFrequency from `hA.fderiv`; compactness of image of
  closure V; R from bounded image (max C 1); L = max L' 1 from `lip_compact_c1` with p=0, T={0}, O=univ ×ˢ (fastFrequency H0 '' W), f=g∘snd.

**Checks:** `inp_lake_build.sh … KAM.Planetary.PGMeasure.CompactLipschitz`: builds, no sorry. One linter warning: `hW` unused in
`lip_inverse` (kept: signature verbatim, hW is a frozen-signature binder). `scripts/lint_sources.sh`: check_lean_modules PASS,
FROZEN-ANCHOR GUARD OK, ABI HASHES OK; it also prints "KAM.lean is out of date; run scripts/gen_root_imports.py" (new module not in
the generated root; I did not edit KAM.lean per rules — orchestrator to regenerate).
`#print axioms` for all four: propext, Classical.choice, Quot.sound only.

**Uncertainties / errata / deviations:** none. No heartbeat problems; no heartbeat overrides. No frozen/provider imports.

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md row P4-LI and its proof plan; audits DESIGN-P45-design-audit-{1,2,3}.md; signatures .drafts/design/P45Signatures.lean): (1) statements = design signatures (ext_deriv, lip_compact, lip_compact_c1, lip_inverse), the frozen hfreq shape as designed; (2) proofs sound; no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Planetary/PGMeasure/CompactLipschitz*.lean (compare with branch inp-p45s).
