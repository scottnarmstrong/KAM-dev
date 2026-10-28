# S9-2 prover handoff (branch inp-s92, 92d3a376; contains inp-s9g and inp-s9d (audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/SecularSpectrum/TwoPlanets.lean` (~425 lines). No other file touched; KAM.lean not edited.

**Declarations (signatures verbatim from P810Signatures.lean):** `SecularSpectrum.n2` (bpP:p9:n2), `SecularSpectrum.n2_global_frame`.

**Approach.**
- n2 (stepP:p9:n2-mat): explicit entries of the 2x2 `coeffs` (`coeffs_two_*`); det formula by field_simp; `pairB>0`, `pairA>pairB` give det>0; `tr^2-4det = (A/c0-A/c1)^2 + 4B^2/(c0c1) > 0`; `sigma0+sigma1=trace`, `sigma0*sigma1=det` from `charpoly_eq_prod_sorted` + `Matrix.charpoly_fin_two`, so sigma0<sigma1; sigma<0 from `definite`. nr4 <-> ratio ≠2,3 by bounded casework (interval_cases on k in [-4,4]^2); trace/det form via factorisation (σ0-2σ1)(2σ0-σ1)(σ0-3σ1)(3σ0-σ1).
- n2_global_frame (stepP:p9:n2-res): `local_analytic` gives a local analytic SO frame at each a; it is shown to diagonalise with sigma (trace/det argument, `frame_sigma`); the sign ambiguity (±R, from `frame_eq_signs`) is removed by normalising `R 1 1 > 0` (`R 1 1 ≠ 0` because the off-diagonal entry is positive); the normalised frame is unique (`normFrame_unique`), so the pointwise choice agrees locally with an analytic frame. `isOpen_axes` proved locally.

**Checks.** `inp_lake_build.sh ... KAM.Planetary.SecularSpectrum.TwoPlanets`: Build completed successfully (the only warning shown is an upstream unused-variable one). `scripts/lint_sources.sh`: ABI HASHES OK; remaining reports concern the generated KAM.lean root (DRAFT_SORRY imports), none mention TwoPlanets. No line >100 chars. No sorry/axiom/maxHeartbeats/EuclideanSpace.
`#print axioms n2` and `n2_global_frame`: [propext, Classical.choice, Quot.sound].

**Imports:** Definiteness, LocalAnalytic, GoodPolynomial (no frozen theorem, no provider).

**Uncertainties / errata / deviations:** none; statements needed no extra hypotheses. No design (heartbeat) signals. Note: `open Polynomial` omitted because `Polynomial.coeffs` clashes with `SecularForm.coeffs`.

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S9-2 and its proof plan; audits DESIGN-P810-design-audit-{1,2}.md; signatures .drafts/design/P810Signatures.lean): (1) n2 and n2_global_frame = signature file exactly; (2) proofs sound (two-planet entries of coeffs, determinant and discriminant positivity from pairB > 0 and pairA > pairB, ordered spectrum, global frame; S9-D, S9-S, S9-G consumed as designed); no added premises; (3) hygiene (no EuclideanSpace; no public name already used elsewhere in KAM, check the coeffs_two_* helpers). Audit ONLY KAM/Planetary/SecularSpectrum/TwoPlanets.lean.
