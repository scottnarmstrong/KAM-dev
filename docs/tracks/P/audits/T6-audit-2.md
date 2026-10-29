# T6 independent package audit 2 — delta audit

**Overall verdict: PASS WITH NOTES. Round 1 F1 is discharged.** The signed `quartic_explicit` and `p11c_coeffs` still pass; `quartic_diagonal` establishes the literal Part-8 diagonal formula for both coefficients. The note is the brief-permitted stale generated root. T6 delivers infrastructure, no provider or frozen theorem anchor; no frozen seal or planetary headline is certified here.

## Scope and comparison

Audited 2026-10-28 in `/root/code/KAM-inp-p11c-t6`, HEAD `c981f7096d05082e57fd148f252990c9ff5b890f`. Delta baseline: `676cd5a3`; current `inp`: `f7029b2a0fc1463f67864cc513161ca93fc67f56`. Read the user rules/AGENTS.md, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, T6 handoff/AUDIT FOCUS, both draft handoffs including the Round 2 fix, Round 1 report, P11C design/design audit, track-P statement, relevant Part-8/11b blueprint statements, current signatures and the reused physical/frozen interfaces. The explicit user destination overrides the generic brief's main-worktree destination.

`git diff inp...HEAD` was inspected for inventory and the scoped T6 slice. Git warns `multiple merge bases, using b5e58ec5e766134ead4e306f3ed3c4dc0da81acd`. The comparison contains 27 added files / 7298 insertions: 17 inherited T5 files, eight T6 Lean files, and the two Round 1 documents. Inherited T5 internals remain outside the audit-only scope. This delta audit retains the Round 1 substantive findings for unchanged code, verifies exact preservation, and independently reruns the build, signature/body, all-public-theorem axiom, kernel and hygiene gates for the current T6 package.

`git diff --numstat 676cd5a3..HEAD` yields exactly:

```text
23      0       KAM/Planetary/PlanarTorsion/Quartic.lean
276     0       KAM/Planetary/PlanarTorsion/Quartic/Diagonal.lean
```

There are no deletions or edits of prior declarations. The facade adds one public import and the documented theorem immediately after `quartic_explicit`, before namespace closure. Removing precisely those additions recovers the entire baseline facade byte-for-byte. Each of the other six original T6 source files is byte-identical to baseline. Thus “only appends” holds as additive source changes, with the necessary import inserted in the import block; it is not literally an end-of-file-only append.

Live signature SHA-256: `6a9b154b4d1d18dc40d41e41a914452c3efe6f8ebe8a9701f3d23b1c2c07c5b7`, `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean`. Design SHA-256: `51533142c3d8aa6611dd280f64f7ee06b54513cf2578684547fd393b53abfd36`. Both signed types and the coefficient body match the current authoritative signature modulo whitespace; all existing proof text is unchanged.

## F1 resolution and graph verdicts

Design `docs/tracks/P/design/P11C-LEAN-DESIGN.md:104–107` assigns all four rows below to T6. Blueprint `blueprint-P/parts/p11b-planar-torsion.tex:108,115` requires the comparison missing in Round 1; `blueprint-P/parts/p8-secular-form.tex:222–224` states the exact diagonal expression and the reversed radial arguments for the second planet.

| Node | Lean declaration / fragment | Verdict | Reason |
|---|---|---|---|
| `bpP:p11b:quartic-explicit` | `quartic_explicit`, `p11c_coeffs`, `quartic_diagonal`; reused `p11c_homogeneousPart` | PASS | Signed analytic/physical-jet result preserved; separate literal diagonal comparison now proved. |
| `stepP:p11b:qe-conv` | `qeScale`, `qeV`, `qe_alg`, `qe_pairJet_qeV`, `qe_quartic_coeffs` | PASS, retained | Exact conversion and all six coefficient formulas unchanged. |
| `stepP:p11b:qe-an` | `qe_remainder_bound`, `qe_fix_jet`, `qe_mov_jet`, `qe_coeffs_analyticAt` | PASS, retained | Analyticity, order-six remainder and actual moving/fixed same-jets proof unchanged. |
| `stepP:p11b:qe-c12` | `quartic_diagonal`, `Quartic.lean:222` | PASS | Both `p11c_coeffs p a 0/1` equal the required radial-derivative expression with denominator `(p.actions a i)^2`. |

The new export assumes only `p : PlanarData`, validity `hp`, axes `a : Fin 2 → ℝ`, and `ha : a ∈ p11c_axes`. Its conjunction states

```text
c₁ = -G m₁ m₂ (h₁⁽⁴⁾(0)/64 - h₁''(0)/16)/Λ₁², h₁ = radialH a₁ a₂;
c₂ = -G m₁ m₂ (h₂⁽⁴⁾(0)/64 - h₂''(0)/16)/Λ₂², h₂ = radialH a₂ a₁.
```

No analyticity, assumed expansion, coefficient identity, or assumed physical representation escapes into this export. `hP` in the distinctly named conditional helpers is discharged using `qeS_analyticAt` and the proved eventual physical equality. Evaluating `qe_fix_jet` on the two unit coordinate directions gives `24*c₁` and `24*c₂`; the diagonal helpers identify the same derivatives, and `linarith` cancels 24. No extra factor of 2, factorial, action, axis, or gravitational mass is dropped.

Every new public declaration has a separate row (all names are in `KAM.Planetary`; helper locations are in `Quartic/Diagonal.lean`):

| Node / purpose | Declaration and line | Verdict | Reason |
|---|---|---|---|
| qe-c12 / calculus | `qeDiag_iteratedDeriv_four:59` | PASS | Analytic order-six remainder implies fourth derivative `24*A4`; explicit helper premises discharged by the actual Part-8 bound. |
| qe-c12 / calculus | `qeDiag_iteratedFDeriv_line:80` | PASS | Arbitrary-order diagonal derivative equals derivative of the actual line restriction; uses an open analytic neighborhood and continuous linear map. |
| qe-c12 / pair jet | `qeDiag_pair_ray:102` | PASS | Applies `SecularForm.pairSlowSecular_diag_jet` directly, with positive actions and distinct physical axes; shrinks the ray radius and retains the plane-length factor in the order-six bound. |
| qe-c12 / physical attachment | `qeDiag_secular_ray:144` | PASS | Actual fixed secular average equals the actual pair average near zero via `exists_pair_nbhd`, `secular_embedSlow_eq`, and `pairData_self`; chart membership and separation are proved locally. |
| qe-c12 / inner eccentric | `qeDiag_fix_first:176` | PASS | First unit ray, physical action/axis identities and positive actions give Part-8 formula with `radialH (a 0) (a 1)`. |
| qe-c12 / outer eccentric | `qeDiag_fix_second:217` | PASS | `pair_swap_nbhd` proves local equality to reversed pair; transfers analyticity and applies diagonal jet at indices `1,0` with actions exchanged. Correct reversed radial function and denominator; commutation restores `m₁*m₂`. |
| qe-c12 / literal export | `quartic_diagonal`, `Quartic.lean:222` | PASS | Conjunction of the two requested coefficient identities, source hypotheses only. |

The two new private polynomial lemmas (`qeDiag_deriv_poly:33`, `qeDiag_poly4:47`) differentiate explicit degree-four polynomials. The local equality in `qeDiag_secular_ray` preserves frozen phase assembly and the literal angular normalization; it is used only inside the proved separated neighborhood. The swapped proof does not assume symmetry of `radialH` and does not incorrectly apply an inner-only formula to outer axes.

## Definitions, imports and hygiene

No new `def`, `abbrev`, `structure`, instance, or root namespace declaration is added by the delta. The ten existing T6 definitions retain Round 1's classification as concrete physical adapters or finite polynomials with standard total real division/sqrt/rpow; physical uses prove the necessary positive-action/local-chart conditions. `p11c_coeffs` is unchanged and is checked by definitional equality against a fresh copy of the authoritative body.

Repository-wide source-masked declaration inventory: 61 public declarations (51 theorems and ten definitions); no reused public short names. All new helpers are in `KAM.Planetary`; no harmful root shadow or global instance is introduced. Source-masked scan of all eight files finds no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, or resource-budget override. Every file has copyright, `module`, public imports, module docstring, and public section; definitions needing unfolding remain exposed.

Transitive KAM import closure: 180 modules; no providers and no frozen theorem imports. All 56 imported frozen files have manifest entries in state `SEALED`. Frozen-provider signature/seal-body probes are inapplicable because T6 supplies neither a provider nor an anchor. Read frozen Phase/Assemble/SecularAverage and the physical adapters at their current definitions; no carrier or angular-normalization substitution was found.

| File under `KAM/Planetary/PlanarTorsion/` | Lines | Maximum Unicode columns |
|---|---:|---:|
| `Quartic.lean` | 243 | 100 |
| `Quartic/Algebra.lean` | 154 | 98 |
| `Quartic/Bounds.lean` | 299 | 98 |
| `Quartic/Compose.lean` | 125 | 98 |
| `Quartic/Defs.lean` | 36 | 95 |
| `Quartic/Diagonal.lean` | 276 | 100 |
| `Quartic/Jet.lean` | 124 | 100 |
| `Quartic/Reduce.lean` | 152 | 100 |

## Independent validation

All Lean-facing commands below were serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`; each process was observed to exit before the next started. Only the named report is a lasting edit; probes/logs are confined to `.lake/abi-scratch/` and removed after recording receipts. No generated root, frozen file, manifest, source, dependency package, or git state was modified.

Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-t6 KAM.Planetary.PlanarTorsion.Quartic
```

Exit 0. Gate output: `[inp-gate] slot 2 acquired 23:03:46 for KAM.Planetary.PlanarTorsion.Quartic`; final output: `Build completed successfully (9226 jobs).` Replayed warnings are upstream unused-variable/deprecation/style warnings; no warning or error is attributed to a T6 file.

Signature/body/literal-conclusion and all-public-theorem axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T6audit2-probe.lean
```

Exit 0 on the final probe. The authoritative coefficient body is copied under a fresh name in a noncomputable section and equated by `rfl`; the authoritative `quartic_explicit` statement is copied under a fresh name and proved with `by exact quartic_explicit p hp`, followed by full polymorphic `type_of%` equality. A separately written literal two-coefficient diagonal statement elaborates with `by exact quartic_diagonal p hp ha`, followed by full polymorphic `type_of%` equality. Initial scratch-only run exited 1 because the copied definition lacked its surrounding noncomputable section; correcting the probe context produced the clean rerun without any production-source edit.

Exact `#print axioms` output for every public T6 theorem (51/51):

```text
'KAM.Planetary.qe_iteratedFDeriv_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_quartic_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qePoly_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qePoly_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_eventually_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_fix_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_mov_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_coeffs_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.quartic_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.quartic_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_alg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeScale_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeV_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeV_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeA_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeA_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeV_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_pairJet_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_quartic_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_pairJet_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_gap_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_alpha_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeS_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qePoly_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_sig_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_remainder_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeScale_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeScale_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeV_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeV_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeV_slowLength_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_pairJet_qeV' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_quartic_coeffs' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeDiag_iteratedDeriv_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeDiag_iteratedFDeriv_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeDiag_pair_ray' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeDiag_secular_ray' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeDiag_fix_first' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeDiag_fix_second' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeJet_diag_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeJet_iteratedFDeriv_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeJet_isBigO_of_jet_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_pairPotential_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_position' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_poincareV' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_axis_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_actions_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_integrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_secular_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay, one invocation:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.Quartic KAM.Planetary.PlanarTorsion.Quartic.Defs KAM.Planetary.PlanarTorsion.Quartic.Jet KAM.Planetary.PlanarTorsion.Quartic.Reduce KAM.Planetary.PlanarTorsion.Quartic.Algebra KAM.Planetary.PlanarTorsion.Quartic.Compose KAM.Planetary.PlanarTorsion.Quartic.Bounds KAM.Planetary.PlanarTorsion.Quartic.Diagonal
```

Exit 0. Exact output:

```text
replaying KAM.Planetary.PlanarTorsion.Quartic.Defs
replaying KAM.Planetary.PlanarTorsion.Quartic.Reduce
replaying KAM.Planetary.PlanarTorsion.Quartic.Jet
replaying KAM.Planetary.PlanarTorsion.Quartic.Algebra
replaying KAM.Planetary.PlanarTorsion.Quartic.Diagonal
replaying KAM.Planetary.PlanarTorsion.Quartic.Compose
replaying KAM.Planetary.PlanarTorsion.Quartic.Bounds
replaying KAM.Planetary.PlanarTorsion.Quartic
```

Final repository lint, after kernel replay exited:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the explicitly allowed generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (977 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Module hygiene, frozen-anchor integrity and all 144 ABI hashes pass. The generated root was left untouched as required.

```sh
git diff --check inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

Both exit 0. No whitespace finding or protected-path diff; both emit only the multiple-merge-base warning recorded above.

## Errata, deviations, uncertainties and disposition

No new suspected defect in a pinned source, frozen declaration or blueprint was found. The existing Part-8 CP11 erratum is not re-adjudicated; the fix compares with the actual radial formula, not CP11's printed quartic coefficients. The already recorded generic-helper placement and SpectralAdapter dependency remain unchanged; the import closure is acyclic. The historical T6 handoff's statement that no separate diagonal export was needed is superseded by its Round 2 fix and `handoff-T6b.md`.

F1 is closed for both eccentric-planet cases. All graph rows assigned to T6 now have their required proof/export. No new hypothesis, weakened conclusion, source restriction, or fallback object was introduced. Remaining scope limits: this is a delta package audit, carrying forward the unchanged Round 1 analytic review; it does not audit inherited T5 internals anew, certify downstream consumers' proofs, or seal a frozen theorem. Final validation and scratch cleanup are recorded below.

Final cleanup: all files created by this audit under `.lake/abi-scratch/T6audit2-*` were removed after recording the receipts. `git diff --exit-code` passes (tracked files unchanged); report-only trailing-whitespace validation passes; final `git status --short` contains only `?? docs/tracks/P/audits/T6-audit-2.md`.
