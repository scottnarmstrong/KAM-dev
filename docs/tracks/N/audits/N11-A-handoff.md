# N11-A prover handoff (branch inp-n11a, 9d16b312; offloaded package run by the main orchestrator)


## Files
- `KAM/Nekhoroshev/Partial/Setting.lean` (177 lines): Ext/EC/ER, fastAction, slowPair, extCx, extRe,
  extReal, wfield, realWfield, extBracket, extAd, PartialBlock (+lam, c, base, realDom, SL), ext_class,
  slowLoss, liftFast, realHamiltonianExt, ExtOrbit, ExtCanonical, ExtNFHyp, ExtConjHyp, reExtMap,
  RealFastConvex, FastConvex, NearResonance. All verbatim from N11Signatures.lean.
- `KAM/Nekhoroshev/Partial/Coordinates.lean` (298 lines): theta, thetaInv, converted, theorem `orbit`
  (verbatim statement, proved), plus helpers: theta_fst/fast/slowq/slowp, thetaInv_q_*/p_* eval lemmas,
  thetaInv_theta, theta_thetaInv, ext_cases, thetaCLM, thetaInvCLM (+_apply), thetaInv_single_*,
  fderiv_converted, realWfield_converted.

## Approach
`orbit`: theta is a linear equivalence (thetaCLM/thetaInvCLM). Chain rule gives
fderiv (converted H) (theta z) v = (2π)⁻¹ fderiv H z (thetaInv v); componentwise matching of
realWfield (2π) (converted H) (theta z) = theta (X_H z); then transport HasDerivAt both ways.

## Checks
- Gate builds `KAM.Nekhoroshev.Partial.Setting` and `...Coordinates`: success (only linter warnings in
  Coordinates: never-executed tactics / `<;>` style in the thetaInv_single_* proofs).
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK, but prints
  "KAM.lean is out of date; run scripts/gen_root_imports.py" (new modules; I did not edit KAM.lean — orchestrator
  regenerates).
- `#print axioms KAM.Nekhoroshev.orbit` (also thetaInv_theta, theta_thetaInv): [propext, Classical.choice, Quot.sound].
- No sorry, no heartbeat overrides, lines ≤ 100, no EuclideanSpace.

## Uncertainties / deviations
- NAME CLASH (needs owner ruling): the signature name `KAM.Nekhoroshev.orbit` has the same short name as
  `KAM.Planetary.orbit` (KAM/Planetary/PlanarTorsion/OrbitJet.lean). Fully qualified names differ; I kept the
  signature verbatim. Rename (e.g. `orbit_theta`) if the short-name rule is to be strict; consumers N11-N/provider affected.
- The design assigns no module to `liftFast`; I put it in Setting (leaf). `scaled` (assigned to N11-C by
  the design table, with `vf`) and `extFlow` (E1) are NOT in my files. `exponents`/`PartialConstants` are N11-B.
- The signature stub namespaces (zBall, freq, dotC, conjExp, IsNonresonant, FreqLipschitz, DivisorBound,
  RealOnParam, resSpan, IsActionNorm) are NOT copied: imported from existing owners
  (NormalForm/Setting, NormalForm/Homological, Stability/Gradient, Stability/Setting).
- Setting imports Stability.Gradient (for resSpan) and NormalForm.Homological (RealOnParam): heavy but acyclic.
- No source errata found.

AUDIT FOCUS: design docs/tracks/N/design/N11-LEAN-DESIGN.md row N11-A (Setting, Coordinates: Ext/projections/wfield/bracket, FastConvex/RealFastConvex bundles, block geometry, extReal/ext_class, ExtCanonical, ExtNFHyp, ExtConjHyp, reExtMap, NearResonance; orbit, theta/theta-inverse) and both design audits; signatures /root/code/KAM-inp/.drafts/design/N11Signatures.lean. The definitions and source bundles must mean the source objects on their whole carriers (no fallback branches; bundles contain only source premises, no conclusion-shaped hypotheses). Note: the signed KAM.Nekhoroshev.Ext shares its name with the root Mathlib constant Ext (homological algebra); no other KAM file uses that name, so it was accepted as a warning: confirm no N11 module needs Mathlib Ext. Audit ONLY KAM/Nekhoroshev/Partial/{Setting,Coordinates}.lean. Common to all: (a) every declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established; an exported lemma named after a graph node must state that node's literal conclusion; steps the design keeps internal may stay internal; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public helper short name, no root shadow, lines <= 100.
