# S9-G prover handoff (branch inp-s9g, 8d5767d; contains inp-s9s (audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/SecularSpectrum/GoodPolynomial.lean` (about 285 lines). No other file touched
(`KAM.lean` not regenerated; `lint_sources.sh` reports "KAM.lean is out of date", which is the expected
new-module notice).

**Declarations (verbatim from P810Signatures.lean):** `k4`, `nr4`, `discriminant`, `k4_finite`, `good`,
`goodAxes`, `simpleAxes`, `good_characteristic`, `good_set` (a,b + permutation invariance),
`good_set_dichotomy`. All in `KAM.Planetary.SecularSpectrum`.

**Approach**
- `k4_finite`: `k4 n` lies in the finite box `Icc (-4) 4` of `Fin n → ℤ`.
- Symmetry: generic over a `CommRing`. `discrGen s = pairSign * pairProd s`, where `pairProd` is the product
  over ordered pairs of distinct indices. That product is permutation-invariant by `Equiv.prodCongr`. The
  permutation product is invariant via `Equiv.mulLeft`. This gives `good_comp` and, with `s = X`, that
  `goodPoly n` is symmetric.
- `good_ne_zero_iff`: `discriminant ≠ 0 ↔ Injective`, and reindexing `k ↦ k ∘ p.symm` for the factors. It holds
  for every `s`, not only on the axes.
- `good_characteristic`: `goodPoly n` is symmetric, so `esymmAlgEquiv` gives `P'` with
  `aeval (esymm (i+1)) P' = goodPoly`. Set `P = aeval (X_i ↦ (-1)^(i+1) X_{rev i}) P'`. Then
  `Multiset.prod_X_sub_C_coeff` (Vieta) applied to `charpoly_eq_prod_sorted` gives the result.
- `good_set` (a): `good ∘ sigma D` is `aeval` of charpoly coefficients. These are analytic by the universal
  charpoly (`Matrix.charpoly.univ`, `univ_map_eval₂Hom`) and `AnalyticAt.aeval_mvPolynomial`, with
  `coeffs_analytic`.
- `good_set_dichotomy`: `Nondegeneracy.generic` (r = 1) for openness and closure,
  `Nondegeneracy.analytic_zero_null` for the null set; otherwise the identically-zero branch.

**Checks**
- `inp_lake_build.sh /root/code/KAM-inp-s9g KAM.Planetary.SecularSpectrum.GoodPolynomial`: built successfully,
  no warnings in this file, no `sorry`.
- `scripts/lint_sources.sh`: no over-length lines, check_lean_modules PASS, frozen-anchor guard OK, ABI hashes
  OK; the only message is "KAM.lean is out of date" (not mine to edit).
- No `maxHeartbeats`, no `EuclideanSpace`, no `sorry` in the file (grep).
- `#print axioms` for `k4_finite`, `good_characteristic`, `good_set`, `good_set_dichotomy`: each
  `[propext, Classical.choice, Quot.sound]`.

**Imports:** `SecularForm.Coefficients`, `SecularSpectrum.LocalAnalytic`, `Nondegeneracy.AnalyticZeros` (no
provider or frozen theorem).

**Uncertainties / errata / deviations:** none. Statements needed no extra hypotheses. I added helper lemmas
(`good_comp`, `good_ne_zero_iff`, `goodPoly`, `analyticAt_charpoly_coeff`, and others), all unconditional.
Design signals: none (default heartbeats throughout).

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S9-G and its proof plan, incl. the gs-c analytic route note; audits DESIGN-P810-design-audit-{1,2}.md; signatures .drafts/design/P810Signatures.lean): (1) statements and definitions = signature file exactly (k4, nr4, discriminant, k4_finite, good, goodAxes, simpleAxes, good_characteristic, good_set, good_set_dichotomy); (2) proofs sound (S9-S local_analytic, S10-Z analytic zeros, esymmAlgEquiv; the analytic route, not root continuity); no added premises; (3) hygiene (no EuclideanSpace). Audit ONLY KAM/Planetary/SecularSpectrum/GoodPolynomial.lean.
