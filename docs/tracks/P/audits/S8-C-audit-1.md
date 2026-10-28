# Independent S8-C package audit 1

Overall verdict: **PASS WITH NOTES** for the assigned S8-C implementation. No frozen anchor is proved or sealed by this package; provider/frozen-type and frozen-seal probes are therefore not applicable. The package exports the exact design contracts, not the full downstream secular expansion, spectral regularity or planetary headline.

Audited HEAD: `fcf99720d2823512b072b865e8b3c87121b593fb`. Compared with `inp` at `f4d1a3178d2fd696e15dc0e0c9dd383f03b5e80c` using `git diff inp...HEAD`. Git warns of multiple merge bases and chooses `63d355613cb892d2ad76be5f33af4184982f39af`. The resulting comparison includes 70 files and inherited work. In accordance with the explicit AUDIT FOCUS, the implementation audit is restricted to `KAM/Planetary/SecularForm/Coefficients.lean`. The package-specific delta `git diff 80b6ec7..HEAD` contains only this 125-line file (commits `2c1d8ba`, `fcf9972`).

The report is written in `/root/code/KAM-inp-s8c`, as explicitly requested by the user, overriding the generic brief's main-worktree destination. No production source was edited. Temporary probes are confined to `.lake/abi-scratch/` and removed after checking.

## Contracts and declaration inventory

Read AGENTS.md, PLAN.md, DECISIONS.md, the package brief and handoff, design revision 2 and both design audits, relevant Part 8/9 blueprint passages, track-P statement conventions, the Basic/Laplace/Norms interfaces, and the frozen secular-average and oscillator-action definitions. The worktree has no `.drafts/design/P810Signatures.lean`; the canonical file at `/root/code/KAM-inp/.drafts/design/P810Signatures.lean` is available and was used directly. Its nine assigned declaration signatures/bodies match the design appendix and implementation after whitespace normalization. No changed premises, constants, carriers, quantifier order or conclusions were found.

Names below are relative to `KAM.Planetary`. Locations refer to `KAM/Planetary/SecularForm/Coefficients.lean`.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| `bpP:p8:coeffs`, L31 | `SecularForm.pairA` | PASS | Exact symmetric min/max pair formula, coefficient 1/4, Laplace index 1 and exponent 3/2. |
| `bpP:p8:coeffs`, L34 | `SecularForm.pairB` | PASS | Same exact formula with Laplace index 2. |
| `bpP:p8:coeffs`, L37 | `SecularForm.constantTerm` | PASS | Negative sum over each ordered inner/outer pair exactly once; index 0, exponent 1/2. |
| `bpP:p8:coeffs`, L40 | `SecularForm.qhat` | PASS | Negative erased diagonal sum and literal positive off-diagonal coefficient. |
| `bpP:p8:coeffs`, L42 | `SecularForm.coeffs` | PASS | Literal diagonal congruence by inverse square roots of actions; no factor 2 inserted. |
| Quadratic evaluation, L44 | `SecularForm.quad` | PASS | Literal double sum, no hidden half or ambient-norm substitution. |
| Additional symmetry helper, L46 | `SecularForm.pairB_comm` | PASS | Unconditional symmetry follows from min/max commutativity; no assumed hard step. |
| `bpP:p8:coeffs`, L49 | `SecularForm.coeffs_hermitian` | PASS | Exact design type, valid for all real vectors a, even outside the physical domain. |
| `bpP:p8:coeffs`, L87 | `SecularForm.coeffs_analytic` | PASS | Exact design type: real analyticity in axes a on positive strictly increasing axes. |
| `bpP:p9:conv#data`, L121 | `SecularSpectrum.sigma` | PASS | Exact imported sorted spectrum of coeffs with the proved Hermitian witness; defined after that witness, as required by design audit F4. |
| Private evaluation helper, L57 | `analyticAt_eval` | PASS | Coordinate projection analyticity. |
| Private ratio helper, L60 | `analyticAt_ratio` | PASS | Positive denominator from axes. |
| Private composition helper, L65 | `analyticAt_laplace_ratio` | PASS | Strict monotonicity and positivity establish ratio in (0,1), then S8-L composition. |
| Private pair helper, L74 | `analyticAt_pair` | PASS | Distinct indices imply min < max; literal rational prefactor is analytic with nonzero denominator. |

The seven new definitions are ordinary total formulas: pairA, pairB, constantTerm, qhat, coeffs, quad and sigma. There are no new structures, abbreviations, instances, choice-based substitutes or hypothesis bundles. Diagonal auxiliary pair values are unused: qhat erases its diagonal sums and uses pairB only off diagonal. Off physical axes, Lean's total division, square root and integral conventions remain literal formula values; no analytic/physical theorem depends on a fallback at singular data. Hermitian symmetry is algebraic there and remains valid even for zero denominators. On axes, physical masses and G are positive, so each action and each square-root denominator is strictly positive. For n=1, erased sums vanish, consistently with the design; no definiteness claim is made.

The analyticity proof has no added source premise: each entry uses S8-L `analyticOnNhd_laplace_def` at s=3/2, positivity of the physical data, coordinate evaluations, products, sums and division. Its two square-root analyticity conversions use Mathlib's analytic ContDiff level, with strict positivity at the point; finite smoothness is not substituted for analyticity. The diagonal is a finite sum over distinct indices. The unconditional Hermitian proof uses the extra public pair symmetry lemma and commutes the denominator factors.

The imported S9-N `sorted` reverses Mathlib's antitone eigenvalue list, matching increasing eigenvalue order. The S9-N docstring says “decreasingly sorted”; this is an inherited documentation discrepancy, not the body used here. Its body and design agree. No new spectral theorem or claim of global analytic eigenvalues is asserted by sigma.

## Scope notes and defects

1. The exact brief check `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **not empty**: it contains inherited changes to `KAM.lean` (32 insertions). Frozen files, manifest and README have empty diffs. The package-specific `git diff 80b6ec7..HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. Thus the broad protected-path check does not literally pass, but no protected-path edit belongs to S8-C. This is retained as a note, not silently waived.
2. Blueprint Part 8 L150 says “All are real analytic functions of Λ”. The exact S8-C design contract proves only coeffs analyticity in axes a. Analyticity after action-coordinate conversion, and separate analytic exports for constantTerm/pair auxiliaries, are not exported here; they remain cooperating/downstream work. This package passes its explicitly assigned design contract and does not certify the whole prose clause independently.
3. `KAM/Planetary/SecularSpectrum/Norms.lean:16` describes the spectrum as “decreasingly sorted”; its L34–35 definition reverses `eigenvalues₀`, yielding increasing order as required by design L20 and blueprint Part 9 L158. Documentation-only inherited discrepancy; no edit made under this audit scope.

No new suspected pinned-source erratum or mathematical blueprint contradiction was found. Existing half-normalization deviations are preserved exactly; this audit does not independently re-audit their pinned PDFs. No hypothesis or source convention was repaired. No heartbeat issue arose.

## Independent checks

The final build, probe, replay and lint commands explicitly use `LEAN_NUM_THREADS=1` and `nice -n 5`; build uses the prescribed compile gate. Resource-protocol deviation: an initial plain `sh scripts/lint_sources.sh` was interrupted to correct its environment and serialization. Its ABI subprocess had already spawned an orphan `lake env lean` process, discovered during final process inspection and terminated (PIDs 99622/100150). Consequently the requested one-process constraint was not maintained throughout this audit; no claim of full resource-protocol compliance is made. The final commands completed with the receipts below, and no source or proof-budget setting was changed. There is no provider export in scope. A transitive KAM-import scan visits 69 modules and finds no provider and no frozen theorem module, so no DRAFT_SORRY dependency or SEALED-theorem applicability issue arises.

### Targeted build: PASS, exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s8c KAM.Planetary.SecularForm.Coefficients
```

Terminal output:

```text
[inp-gate] slot 1 acquired 11:58:18 for KAM.Planetary.SecularForm.Coefficients
⚠ [9115/9115] Built KAM.Planetary.SecularForm.Coefficients (19s)
Build completed successfully (9115 jobs).
```

Three package deprecation warnings for `ite_cond_eq_false` occur at 54:8, 54:44 and 112:21. They recommend `ite_eq_right_of_eq_false`. Replayed upstream Energy/Chart/Mass modules also report unused-variable warnings. No error or heartbeat override occurred.

### Exact signature/body and axiom probe: PASS, exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S8CAudit.lean
```

The probe imports the audited module, copies all seven literal definition bodies under fresh names and proves their equality to the implementation by `rfl`. It copies the two canonical theorem types under fresh names with bodies `by exact coeffs_hermitian D a` and `by exact coeffs_analytic D`, respectively. All nine declarations additionally pass `example : type_of% @original := @audit_copy`. This tests design equality in place of an inapplicable frozen seal test.

The initial scratch attempt omitted a surrounding noncomputable section for function-valued examples, producing `lean.dependsOnNoncomputable` errors. Adding that section corrected the probe infrastructure; no implementation or copied contract changed. The corrected invocation exits 0.

Exact axiom output:

```text
'KAM.Planetary.SecularForm.pairA' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairB' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.constantTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qhat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.coeffs' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.quad' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairB_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.coeffs_hermitian' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.coeffs_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.sigma' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay: PASS, exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.Coefficients
```

Exact output:

```text
replaying KAM.Planetary.SecularForm.Coefficients
```

There is one audited implementation module and no provider module, so this is the single required replay invocation.

### Source lint: PASS with the expressly permitted generated-root exception

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit code **1**, with exact complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (556 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The only failing lint item is the expected generated-root freshness check, explicitly allowed by the brief. The module check, frozen-anchor guard and all 144 ABI hashes pass. KAM.lean was not regenerated or edited. The earlier interrupted lint attempt is not counted as a completed receipt; its orphan process is disclosed above.


### Static hygiene and protected paths

- `rg -n 'sorry|admit|axiom|unsafe|opaque|set_option|EuclideanSpace' KAM/Planetary/SecularForm/Coefficients.lean`: no matches (exit 1).
- 125 physical lines, below the 1500-line cap; copyright, `module`, public imports, module documentation and exposed public noncomputable section are present. No global norm instance is installed.
- `git diff --check inp...HEAD`: exit 0, only the multiple-merge-base warning. `git diff 80b6ec7..HEAD --check`: exit 0, no output.
- `git diff inp...HEAD --name-only -- KAM/Frozen manifest README.md`: no paths, only the multiple-merge-base warning. The broader protected-path diff includes only the inherited KAM.lean change discussed above.
- `git diff 80b6ec7..HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, empty output.

The report itself is the only auditor-created repository file. The pre-existing untracked handoff is preserved. All probes and auditor-created scratch logs are deleted after transcribing the receipts. No git state-changing command, root generation, cache update, full-library build, frozen edit or source repair was performed.



