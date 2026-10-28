# S8-Q independent package audit 2 — delta audit

2026-10-28. **Overall verdict: PASS WITH NOTES. F1 and F2 are resolved.** The signed infrastructure theorem `quadratic_form` retains PASS; the complete assigned S8-Q slice (`qf-pair`, `qf-assembly`, `qf-diag2`) is accepted, subject to the previously permitted generated-root lint exception. No frozen theorem anchor is implemented or sealed by this package; “seal-ready” is inapplicable.

## Scope and snapshot

Audited worktree: `/root/code/KAM-inp-s8q`. Report destination is this exact worktree, following the explicit user instruction over the brief's generic main-worktree destination. Read AGENTS.md, PLAN.md, DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the AUDIT FOCUS in `S8-Q-handoff.md`, Round 1, and `.drafts/handoff-S8-Q.md` including “Round 2 fix”. Compared the current source/packet, signed P810 signatures, design package rows and both design audits; inspected the frozen symplectic and oscillator definitions and Track P conventions. This is a delta audit: unchanged mathematical proofs and definitions retain Round 1's review, with fresh build, axiom and kernel checks of the entire scoped package. No delegation, proof edits, generated-file changes, or state-changing git commands.

HEAD: `af08fbac8f13effb1b7c13a0ecac1fdb81ebf0a2`; Round 1 baseline: `625009a7`; observed `inp`: `d9183adae208ecf2e726620694b69c8168e33006`. The requested `git diff inp...HEAD` warns about multiple merge bases and selects `2357d954eb506f13424878cde5561628ba303dfe`. It contains 29 files / 4465 additions, including inherited S8-D/S8-X and Round 1 reports. Those inherited proofs are outside this audit. The authoritative fix delta `git diff 625009a7 HEAD` has exactly three files, 96 insertions / 12 deletions:

| File | Delta and assessment |
|---|---|
| `KAM/Planetary/SecularForm/Quadratic.lean` | Public import of `Quadratic.Diag`, corrected diagonalisation documentation, one remainder-name replacement in an `rfl` proof step. |
| `KAM/Planetary/SecularForm/Quadratic/Diag.lean` | New 82-line module, three public theorems, no definitions or instances. SHA-256 `55c7655f0b5b376696de4f5bc8d662b66bec62b16351aa1dcd0b91803d238047`. |
| `KAM/Planetary/SecularForm/Quadratic/Uniform.lean` | Exactly the global textual substitution `quadRemainder` → `quadFormRemainder`; byte comparison after that substitution passed. |

## Findings and source fidelity

**F1 resolved.** `blueprint-P/parts/p8-secular-form.tex:170` says the map is “symplectic for $d\eta\wedge d\xi$” and gives the invariant sum of squares and half-square definition of the new actions. The containing theorem at line 157 explicitly gives `sum sigma_j*(xi_tilde_j^2+eta_tilde_j^2) = sum 2*sigma_j*Gamma_tilde_j`. Packet `docs/graph/P/packets/P-p8.nodes.md:1262–1283` records SO membership, `Q_h = varrho diag(sigma) varrho^T`, and the same three conclusions. `Diag.lean:32–64` now exports exactly these three mathematical claims as separate lemmas. No spectral simplicity, eigenvalue sign, axis condition, analytic frame, dimension lower bound, supplied remainder estimate or coefficient bundle is added.

The first two lemmas need only SO membership; omission of the diagonalisation hypothesis there is a valid strengthening. The identity uses a generic real matrix `Q`, specialized to `coeffs D (axis D I)` for the source application; this also strengthens applicability without changing the source object. Its only substantive premise is the prescribed matrix factorization. The SO premise is present as `_hϱ`, but is unused: substitution and matrix multiplication already give `x^T Q x = sum sigma_j*(varrho^T x)_j^2` for arbitrary real `varrho`. This is mathematically correct and does not assume the identity as a hypothesis. The determinant-one component is likewise unnecessary for the first two proofs, which use orthogonality only.

The RHS is literally

```lean
∑ j, 2 * σ j * (((ϱ.transpose.mulVec ξ) j ^ 2 +
  (ϱ.transpose.mulVec η) j ^ 2) / 2)
```

Thus the factor 2 multiplies the frozen half-square action; it is neither an extra factor in the quadratic polynomial nor the uncorrected printed-source matrix. `quad` is the actual full double sum from `SecularForm/Coefficients.lean:44`. The form is the frozen `KAM.symplecticForm`, whose value is `sum (v.2*w.1-v.1*w.2)`, with the required sign. Preservation is quantified over every pair of tangent vectors, which is the symplectic claim for this fixed linear rotation. The separate identity map on Lambda leaves Lambda unchanged. These lemmas do not assert symplecticity of an action-dependent rotation on full phase space: S9-L owns its angle correction and derivative terms.

**S9-Q consumption passed.** The signed `diagonalize` in `/root/code/KAM-inp/.drafts/design/P810Signatures.lean:364–386` supplies precisely `isSO (R I)` and the factorization required here. A fresh Lean example specializes `qfDiagIdentity` to an arbitrary `R, Q, sigma` and proves the exact consumer-shaped RHS

```lean
∑ j, (2 * σ j) *
  oscillatorAction (R.transpose.mulVec η) (R.transpose.mulVec ξ) j
```

by `simpa only [oscillatorAction, add_comm]`. The swapped argument order is correct: the frozen oscillator action is `(p_j^2+q_j^2)/2`, and addition commutes. Only the proved facade is imported. This verifies public reachability and the normalization without importing any signed `sorry` declarations. It does not claim to prove the remaining average, negativity, uniform rotated remainder or full S9-Q theorem.

**F2 resolved.** The definition and all its scoped uses are now `KAM.Planetary.SecularForm.quadFormRemainder`. A declaration scan of every scoped theorem/lemma/def/abbrev/structure against every other KAM source found no outside-scope short-name matches, including the three new theorem names. The pre-existing `KAM.Apost.quadRemainder` is unaffected. There is no alias retaining the old SecularForm short name, root-level redeclaration, local shadow definition of `quad`, `isSO`, `symplecticForm` or `oscillatorAction`, or root-file change. The facade's `public import` exposes the new exports.

**Signed theorem unchanged.** Python compared the exact substring from `theorem quadratic_form` up to (excluding) `:=` against both `git show 625009a7:KAM/Planetary/SecularForm/Quadratic.lean` and the current signed signature file: all three byte-identical. SHA-256 of that substring, including its trailing whitespace before `:=`, is `3cb5efe1b7b20f8730c5f984a6b80378c6e3a677d46b70c3a3f602ea6544d578`. The earlier report's header hash used a different substring boundary; the actual equality is checked directly. A fresh copy named `auditS8Q2Signed`, with body `exact quadratic_form D ha`, and `example : type_of% @auditS8Q2Signed := @quadratic_form` both elaborate.

## Per-node and changed-declaration verdicts

All declarations below are in `KAM.Planetary.SecularForm`.

| Node / declaration | Verdict | Reason |
|---|---|---|
| Signed `quadratic_form` | PASS | Byte-identical signed type; exact application probe; only proof-name substitution. |
| `stepP:p8:qf-pair` / `secular_eq_sum_pair` and pair helpers | PASS retained | No delta to the literal-average assembly; Round 1 mathematical review retained. |
| `stepP:p8:qf-assembly` / `quad_pair_sum`, jet, Schwarz and constants helpers | PASS retained | No mathematical delta; actual remainder definition retained under rename. |
| `stepP:p8:qf-diag2` / `qfDiagSymplectic` (`Diag:32`) | PASS | Frozen bilinear form preserved on all vector pairs from SO orthogonality. |
| `stepP:p8:qf-diag2` / `qfDiagSumSq` (`Diag:47`) | PASS | Exact sum of squares, no norm replacement or factor change. |
| `stepP:p8:qf-diag2` / `qfDiagIdentity` (`Diag:61`) | PASS | Exact matrix factorization and `2*sigma*Gamma` identity, generic Q; redundant SO premise harmless. |
| `quadFormRemainder` (`Uniform:31`) | PASS | Exact original remainder body; F2 short-name collision removed. |
| `analyticAt_remainder` (`Uniform:58`) | PASS | Statement/body change only refers to the renamed definition. |
| `remainder_pointwise` (`Uniform:122`) | PASS | Statement/body change only refers to the renamed definition. |

The remaining public declaration rows and fifteen whole-carrier definition classifications in `S8-Q-audit-1.md` remain applicable, with the single remainder-name substitution. No other new public declaration is introduced by the fix.

## Definition and import classification

`Diag` introduces no `def`, `abbrev`, `structure`, instance or bundled premise. `quadFormRemainder` is exposed and is the actual pointwise difference between the literal secular function, constant term and two quadratic forms on the entire `Slow n` carrier. It has no fallback or junk branch. All fourteen other scoped definitions are byte-unchanged; their Round 1 classifications are retained.

Fresh recursive import inspection from the facade reaches 124 local KAM modules, no provider, and no frozen theorem. All 55 frozen imports match manifest entries of `kind=definition`, `state=SEALED`. The additional dependency is `SecularSpectrum.Norms` for its existing `isSO`, not a provider, unproved spectral theorem or conclusion-shaped instance. No provider/frozen type equality or frozen seal-body probe is applicable.

## Verification receipts

Every Lean/Lake operation below ran serially with `LEAN_NUM_THREADS=1`; direct invocations use `nice -n 5`, and the build wrapper supplies it. No clean build, cache download, package change or resource override.

1. Targeted gated build:

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s8q KAM.Planetary.SecularForm.Quadratic
[inp-gate] slot 1 acquired 17:20:17 for KAM.Planetary.SecularForm.Quadratic
Build completed successfully (9170 jobs).
exit 0
```

Only inherited warnings were replayed (unused variables in input modules and deprecated `ite_cond_eq_false` in `Coefficients`); no warning in the scoped files.

2. Fresh exact-type, consumer-shape and all-public-theorem axiom probe:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S8Q2Probe.lean
exit 0; 90 axiom outputs; no errors
```

All 90 public theorem/lemma outputs give exactly `[propext, Classical.choice, Quot.sound]`. Representative exact output:

```text
'KAM.Planetary.SecularForm.quadratic_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qfDiagSymplectic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qfDiagSumSq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qfDiagIdentity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The initial inventory also requested the qualified source spelling of private `continuous_planeLength_q`, yielding `Unknown constant`; removed that private-only request and reran successfully. This was a probe inventory correction, not a package failure or source edit. Round 1 had 87 public results; three are added here.

3. One kernel replay invocation, all fifteen scoped modules:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.Quadratic \
  KAM.Planetary.SecularForm.Quadratic.Algebra \
  KAM.Planetary.SecularForm.Quadratic.Calculus \
  KAM.Planetary.SecularForm.Quadratic.Coeff \
  KAM.Planetary.SecularForm.Quadratic.Constants \
  KAM.Planetary.SecularForm.Quadratic.Diag \
  KAM.Planetary.SecularForm.Quadratic.Jet \
  KAM.Planetary.SecularForm.Quadratic.Marginal \
  KAM.Planetary.SecularForm.Quadratic.PairDiag \
  KAM.Planetary.SecularForm.Quadratic.PairHessian \
  KAM.Planetary.SecularForm.Quadratic.PairIdentify \
  KAM.Planetary.SecularForm.Quadratic.PairLocal \
  KAM.Planetary.SecularForm.Quadratic.PairSplit \
  KAM.Planetary.SecularForm.Quadratic.Schwarz \
  KAM.Planetary.SecularForm.Quadratic.Uniform
replaying KAM.Planetary.SecularForm.Quadratic
replaying KAM.Planetary.SecularForm.Quadratic.Calculus
replaying KAM.Planetary.SecularForm.Quadratic.Uniform
replaying KAM.Planetary.SecularForm.Quadratic.PairSplit
replaying KAM.Planetary.SecularForm.Quadratic.Diag
replaying KAM.Planetary.SecularForm.Quadratic.Marginal
replaying KAM.Planetary.SecularForm.Quadratic.PairHessian
replaying KAM.Planetary.SecularForm.Quadratic.PairLocal
replaying KAM.Planetary.SecularForm.Quadratic.Constants
replaying KAM.Planetary.SecularForm.Quadratic.Jet
replaying KAM.Planetary.SecularForm.Quadratic.PairIdentify
replaying KAM.Planetary.SecularForm.Quadratic.Algebra
replaying KAM.Planetary.SecularForm.Quadratic.PairDiag
replaying KAM.Planetary.SecularForm.Quadratic.Coeff
replaying KAM.Planetary.SecularForm.Quadratic.Schwarz
exit 0
```

4. Required source lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (744 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole failure is the brief's explicitly permitted generated-root staleness. Module-system, frozen-anchor and all 144 frozen ABI checks pass. The Round 2 handoff's “743 modules” is an older count; the fresh check reports 744.

5. Static and repository checks:

- Code-mask scan of all fifteen scoped sources: no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace` or `set_option`. No heartbeat, recursion or synthesis override. All module headers and exposure conventions pass lint; maximum file length 257, new `Diag` 82, below 1500.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty stdout, exit 0; only the documented multiple-merge-base warning on stderr.
- `git diff --check 625009a7 HEAD`: exit 0. `git diff --check inp...HEAD -- KAM/Planetary/SecularForm/Quadratic.lean KAM/Planetary/SecularForm/Quadratic`: exit 0.
- Full `git diff --check inp...HEAD`: exit 2 solely for inherited S8-X `CrossJet/Selection.lean:198`, trailing whitespace after `simp_rw [mul_comm (Real.cos _)]`. This is unchanged from Round 1 and outside the audit scope; no repair performed.
- Complete `quadratic_form` proof and trailing module text also match the baseline after the single name substitution. All other scoped source bytes are unchanged except the enumerated import/documentation and new module.
- Only this report is newly present in `git status --short`. All audit-created scratch probes and logs were removed after recording receipts; no pre-existing scratch file was removed. Final HEAD remains `af08fbac8f13effb1b7c13a0ecac1fdb81ebf0a2`.

## Errata, deviations and limits

No new suspected pinned-source or blueprint defect, and no auditor-introduced deviation. The existing p8 line 157 provenance gap (“Le calcul complet est un peu long”, [LR95] not pinned), source factor-half discussion, and valid S8-W bypass retain their Round 1 status. The fix adds the missing elementary rotation proof; it does not rely on a numerical ratio or change any coefficient normalization. The source/graph node metadata still says `LEAN_STATUS: NOT_STARTED`; this report certifies the corresponding Lean exports, without editing the graph packet or claiming campaign-level bookkeeping closure.

The accepted scope is S8-Q's signed quadratic expansion and assigned three cuts. S8-D/S8-X remain separately audited inputs; no full S9-Q theorem, action-dependent lift, planetary headline, frozen theorem seal or resolution of external source provenance is certified here. F1 is discharged by the three publicly reachable `qfDiag*` theorems and F2 by the exact remainder rename. **PASS WITH NOTES** reflects only the permitted generated-root exception and inherited out-of-scope whitespace.
