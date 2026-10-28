# Independent package audit S10-W, audit 1

Overall verdict: **PASS WITH NOTES** for S10-W's Weyl infrastructure. No mathematical or statement-fidelity failure found. This package proves no frozen anchor and supplies no provider export; “seal-ready” is therefore inapplicable. No physical headline, full Part 10, or root closure is certified.

Audited HEAD: `3aa0f5c3f8c4f2f1e26ce5115a29194701116116`. Scope is exactly `KAM/Planetary/Nondegeneracy/Weyl*.lean`, as narrowed by the handoff's AUDIT FOCUS; the sole matching file is the 168-line `Weyl.lean`. Read AGENTS.md, PLAN.md, DECISIONS.md, the assigned package brief and handoff, P810 design Revision 2 and design audits 1–2, the original shared signatures, p9 norm/spectral conventions, p10 Weyl statement/proof/consumers, track P statements, imported norm definitions and relevant frozen definitions. The user-specified report destination inside this worktree overrides the brief's generic main-worktree destination.

## Comparison scope and notes

**N1 — inherited comparison/root discrepancy (informational).** Ran both `git diff inp...HEAD` and `git diff inp-s9n...HEAD`. `inp` has multiple merge bases with HEAD; Git warned that it selected `50de825c3f654adc885132a6517d4ad6c090d131`. The other merge base is `5991245cabc06e69ec900cb6006b45f72cc85eb0`. At observation, `inp` was `05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2` and `inp-s9n` was `50de825c3f654adc885132a6517d4ad6c090d131`.

The broad three-dot comparisons contain inherited unrelated packages and four added generated-root imports (`CorrectorRegular`, `ComplexGlue`, `ResonanceSlow`, `SecularForm.Basic`). Consequently the brief's literal broad protected-path emptiness check is **not empty for KAM.lean**; it must not be reported as passing. `git diff inp...HEAD -- KAM/Frozen manifest README.md` is empty. Attribution is independently resolved by `git diff 87e590f..HEAD --stat`: after the S9-N merge, the only change is `Weyl.lean`, 168 insertions; `git diff 87e590f..HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. The scoped verdict does not approve the unrelated inherited changes. No generated file was edited during this audit.

**N2 — exact boundary of the min-max cut (informational).** The design at lines 338–340 explicitly permits “Courant–Fischer or an equivalent direct spectral subspace argument in explicit Euclidean norms.” The implementation follows the second route. It proves the comparison consequence needed by Weyl, rather than exporting the full min/max-over-subspaces identity printed at blueprint p10:44. This is an acceptable proof-route substitution for the parent theorem. A downstream consumer needing the literal Courant–Fischer formula would still need a separate theorem; this report does not certify that formula as a public export.

**N3 — signature provenance and harmless warnings.** `.drafts/design/P810Signatures.lean` is absent locally; the actual original at `/root/code/KAM-inp/.drafts/design/P810Signatures.lean` was read and compared, as was the checked Appendix A in the local design. `weyl`'s declaration header through its result is byte-identical to the original (lines 415–417) and design (lines 972–974). Neither supplies a literal signature for the internal subspace helper; its contract is assessed against the design proof plan and blueprint proof obligation. The unused `hE` binder is retained verbatim; symmetry of E also follows from the two other Hermitian hypotheses. The unused local facts `hU1` and `hy` do not conceal a premise or affect the proof. The handoff's “173 lines” is stale; the committed file has 168.

## Declaration and node inventory

Names are relative to `KAM.Planetary`. Every new public declaration appears below.

| Node / role | Lean declaration and source line | Verdict | Reason |
|---|---|---|---|
| `bpP:p9:e-spec`, spectral ingredient | `SecularSpectrum.exists_eigenframe`, 34 | PASS | Builds one frame, before all x, from the matrix-valued real spectral theorem. Reindexes Mathlib eigenvalues to the increasing sorted list; returns Parseval and the exact diagonal quadratic form. No spectral conclusion is assumed. |
| sorted-order ingredient | `SecularSpectrum.sorted_mono`, 74 | PASS | Reversal of Mathlib's antitone ordering gives increasing order, with repetitions retained. |
| `stepP:p10:weyl-pert`, scalar estimate | `SecularSpectrum.abs_dot_mulVec_le`, 79 | PASS | Cauchy–Schwarz and the proved induced Euclidean operator bound give the homogeneous estimate for every real matrix E. Omitting Hermitian symmetry here is a valid strengthening. |
| `stepP:p10:weyl-mm`, direct comparison substitute | `SecularSpectrum.sorted_le_of_quad_le`, 102 | PASS WITH NOTES | Proves ordered spectral comparison from a quadratic-form inequality for all x, for any real slack t. The hypothesis is the explicit input of a distinctly named conditional helper; the parent proves it twice. Full Courant–Fischer is not exported (N2). |
| `bpP:p10:weyl`; combines both proof cuts | `Nondegeneracy.weyl`, 154 | PASS | Exact signed type: same A,E,hA,hE,hAE order, all indices, constant 1 and explicit op2. Both signs are proved, with no additional premise or parameter dependence. |

No frozen-anchor row applies. No frozen theorem or provider is imported: recursive project-import inspection found only SEALED definition anchors (47 frozen files) and zero provider modules, among 65 project-closure module names. In particular no DRAFT_SORRY theorem is an input. Frozen/provider type equality and actual frozen seal-body probes are inapplicable; a fresh independently restated signed-type theorem and explicit application probe were used instead.

## Proof and definition audit

`exists_eigenframe` uses `hM.eigenvectorUnitary` and `hM.spectral_theorem`; `U Uᵀ = 1` proves preservation of squared length. Its permutation τ reverses Mathlib's ordering and transports the quadratic sum without losing multiplicities. The exported proposition gives exactly the frame identities consumed downstream, without separately exporting the eigenvector equations.

For `sorted_le_of_quad_le`, the map at lines 107–112 has n-dimensional domain `Fin n → ℝ` and an (n−1)-dimensional codomain indexed by `{j // j ≠ i}`. It imposes vanishing B-frame coordinates for j<i and C-frame coordinates for j>i. A nonzero kernel vector exists by finite rank. Its squared length is strictly positive, proved directly from its nonzero coordinates (lines 120–125), so no unit-vector existence or division-by-zero assumption is hidden. Parseval and monotonicity yield

```text
b_i (x·x) ≤ x·B x ≤ x·C x + t(x·x) ≤ (c_i+t)(x·x).
```

Cancellation is justified by `x·x>0`; the proof permits negative t. At n=0, any conclusion indexed by `Fin 0` is vacuous; the subspace argument starts from an existing i and derives n>0. At n=1 the codomain is zero-dimensional and the same argument works. Repeated eigenvalues require only monotonicity. The perturbation helper proves `|x·E x| ≤ op2 E (x·x)` on the exact Pi carrier with explicit Euclidean length; it never treats the ambient max norm as Euclidean. `weyl` instantiates the comparison for `(A+E,A)` and `(A,A+E)`, discharging both quadratic premises using matrix additivity and the two sides of the absolute-value estimate.

**New global definitions/abbreviations/structures: none.** Local U is the actual orthogonal spectral matrix; e and τ are finite reindexing equivalences; f is the stated linear constraint map. All are defined on their full carriers, with no fallback or junk branch. Inherited `Vec`/`Mat` are literal Pi/matrix aliases. Inherited `length2` is sqrt of the sum of squares, `op2` is the supremum of matrix images of Euclidean unit vectors, and `sorted` is Mathlib's eigenvalue enumeration reversed by i.rev. The inherited bounds ensure the op2 supremum is bounded, and its n=0 empty-sphere convention cannot influence a nonempty spectral conclusion. No new instance, bundled hard step, or conclusion-shaped premise was introduced.

## Independent checks

All completed Lean checks below are recorded with their actual outcomes. No production source was edited; probes live only in `.lake/abi-scratch/` and are removed at completion.

1. Targeted gate build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s10w KAM.Planetary.Nondegeneracy.Weyl
   [inp-gate] slot 1 acquired 10:08:43 for KAM.Planetary.Nondegeneracy.Weyl
   ⚠ [9111/9111] Replayed KAM.Planetary.Nondegeneracy.Weyl
   warning: KAM/Planetary/Nondegeneracy/Weyl.lean:154:49: Variable name `hE` is not explicitly referenced.
   Build completed successfully (9111 jobs).
   exit 0
   ```

   The gate invokes `nice -n 5 lake build`. Dependencies replayed unused-variable warnings in Kepler/Energy, Poincare/Chart and Kepler/Mass. This was an incremental targeted build using the existing overlay, not a clean rebuild.

2. Required source lint, completed rerun:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (525 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The sole lint failure is the explicitly permitted stale generated root. The root was not regenerated. A preliminary lint invocation was interrupted and discarded after discovering that lint itself starts a Lean ABI subprocess; its descendants were stopped before this completed rerun. The completed lint, subsequent probe and kernel replay were scheduled sequentially with `LEAN_NUM_THREADS=1` and nice priority 5. The initial lint had briefly overlapped the gate's Lake build/replay process; this was an audit scheduling deviation, not a source change or a claimed validation receipt.

3. Signed-type/application probe and every new public theorem's axioms:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S10WAudit1.lean
   'KAM.Planetary.SecularSpectrum.exists_eigenframe' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.sorted_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.abs_dot_mulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.sorted_le_of_quad_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Nondegeneracy.weyl' depends on axioms: [propext, Classical.choice, Quot.sound]
   exit 0
   ```

   The probe independently states the exact signed Weyl type under a fresh name, proves it with `by exact KAM.Planetary.Nondegeneracy.weyl A E hA hE hAE`, and checks `example : type_of% @signed_weyl := @KAM.Planetary.Nondegeneracy.weyl`. It also restates and applies the subspace-comparison helper, and specializes Weyl to the empty spectrum. No sorry or resource override is used. All five public declarations have exactly the permitted axiom set.

4. Independent kernel replay, one invocation for the only new module (the five declarations all reside in it):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Nondegeneracy.Weyl
   replaying KAM.Planetary.Nondegeneracy.Weyl
   exit 0
   ```

5. Static and final artifact checks:

   ```text
   git diff --check inp-s9n...HEAD -- 'KAM/Planetary/Nondegeneracy/Weyl*.lean'
   exit 0; no output
   git diff --check
   exit 0; no output
   git diff --no-index --check /dev/null /root/code/KAM-inp-s10w/docs/tracks/P/audits/S10-W-audit-1.md
   exit 0; no output
   ```

   Independent scans found five public declarations, no new global def/abbrev/structure, 168 lines, no forbidden proof escapes, no EuclideanSpace token and no set_option directive. Copyright, module declaration, public imports, module docstring and public noncomputable section are present. The original signature comparison returned `Weyl signature byte-identical: True`. Recursive import inspection confirmed 47 SEALED definition files and no frozen theorem/provider imports. The temporary probe and the scratch file left by the discarded lint run were deleted; the completed lint's own temporary file was automatically removed. Final status has only the new audit report and the pre-existing untracked S10-W handoff. No state-changing git operation was used.




## Suspected defects, deviations and limits

No suspected pinned-source mathematical erratum or blueprint contradiction was found in the audited obligation. No ledger edit is proposed. The direct spectral subspace route is explicitly permitted by the design; the literal min-max identity is not separately formalized. The blueprint p10:41 continuity consequence follows mathematically from the Lipschitz bound, but this package's signed export does not separately state a topological continuity theorem. The inherited Norms module's heading says “decreasingly sorted spectrum” although its actual definition and this module's `sorted_mono` are increasing; this is an upstream documentation typo at `KAM/Planetary/SecularSpectrum/Norms.lean:16`, not a definition change or new source erratum.

The scoped theorem statements and proof arguments pass. The overall notes preserve the inherited-root comparison discrepancy, expected stale generated-root lint result, permitted proof-route substitution and absence of any frozen seal. Only this report is an intended repository edit.
