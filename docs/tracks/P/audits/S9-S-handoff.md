# S9-S prover handoff (branch inp-s9s, 1d3815c; contains inp-s8c (audited); offloaded package run by the main orchestrator; prover on claude-12)


## Files (all new)
KAM/Planetary/SecularSpectrum/LocalAnalytic.lean (facade, imports Unique) and under
KAM/Planetary/SecularSpectrum/LocalAnalytic/ (84-173 lines each, ~880 lines in total):
Projection, Frame, Analytic, Eigenvalues, Sorted, Existence (`local_analytic`), Unique
(`local_analytic_unique`). Signatures copied verbatim from P810Signatures.lean (only the long hDiag
binder line is wrapped); no signature changed, no hypothesis added.

## Declarations
- `bpP:p9:local-analytic` -> `KAM.Planetary.SecularSpectrum.local_analytic` (Existence),
  `KAM.Planetary.SecularSpectrum.local_analytic_unique` (Unique).
- `la-ev`: `exists_analytic_root` (scalar analytic IFT via `ContDiffAt.implicitFunction` at order ω),
  `exists_eigenvalue_branch` (Eigenvalues); `sorted_strictMono`, `charpoly_eq_prod_sorted`,
  `charpoly_eq_prod_of_roots` (Sorted).
- `la-adj`: `eigProj` + algebra (Projection), analyticity (Analytic).
- `la-vec`: `eigFrame`, orthonormality, diagonalisation (Frame), `analyticAt_eigFrame` (Analytic).
- `la-so`: sign normalisation by connectedness (`IsPreconnected.eq_one_or_eq_neg_one_of_sq_eq`) in Existence;
  uniqueness in Unique.

## Approach / deviation (reported)
The design's "adjugate projection" is realised by the Lagrange polynomial projection
`Π_j = ∏_{k≠j} (M-σ_k)/(σ_j-σ_k) = aeval M (Lagrange.basis univ σ j)` (equal to adj(σ_j-M)/p'(σ_j));
it is a polynomial in M, so analyticity is a finite product of analytic matrices, and symmetry,
idempotence, MΠ=σΠ, Π_jΠ_l=0 follow from Cayley-Hamilton + Lagrange. Existence of a positive diagonal
entry uses tr(Π)=ΣΠ_ik² and Π u = u for an eigenvector u. This is a proof-route deviation only;
the statements are unchanged. Uniqueness pointwise (s=t via charpoly and StrictMono.range; Rᵀ S diagonal by
commutation with diag s), constancy of signs by preconnectedness.

## Checks
- `scripts/lint_sources.sh`: PASS for all my files (only message: "KAM.lean is out of date", generated file, not edited by me).
- gate build `inp_lake_build.sh ... KAM.Planetary.SecularSpectrum.LocalAnalytic`: "Build completed successfully (9118 jobs)", no sorry warnings.
- `#print axioms` for `local_analytic` and `local_analytic_unique`: [propext, Classical.choice, Quot.sound].
- No maxHeartbeats, no file > 175 lines. Only warning in my files: unused binder `hW` in `local_analytic_unique` (signature-fixed).

## Uncertainties / errata / design signals
None. No suspected errata in the pinned source (note: the source says "n distinct eigenvalues,
equivalently discr ≠ 0"; the signature uses injectivity of `eigenvalues`, which is what is proved from).
No heartbeat problems. Quarantine respected: imports only Mathlib and `SecularSpectrum.Norms`.

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S9-S and its proof plan; audits DESIGN-P810-design-audit-{1,2}.md; signatures .drafts/design/P810Signatures.lean): (1) statements = design signatures exactly (local_analytic, local_analytic_unique; the wrapped hDiag binder must be token-identical); (2) proofs sound (adjugate projection and SO frame proof cuts; matrix spectral theorem; analytic IFT; S8-C and S9-N consumed as designed); no added premises; (3) hygiene (facade + 7 modules). Audit ONLY KAM/Planetary/SecularSpectrum/LocalAnalytic.lean and LocalAnalytic/*.lean.
