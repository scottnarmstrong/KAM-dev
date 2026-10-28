# N12-04 independent package audit 1

Overall verdict: **PASS WITH NOTES** for the N12-04 infrastructure package. No mathematical or signature-fidelity defect found. The expected stale generated `KAM.lean` is the only source-lint exception. Targeted build, exact-signature probes, allowed-axiom checks, and kernel replay all pass.

This audits only `KAM/Nekhoroshev/Averaging/Coefficients.lean`, as required by the handoff's AUDIT FOCUS. No frozen anchor is being sealed. `averaging_mean` and `averaging_most` remain `DRAFT_SORRY` / **FROZEN_UNPROVED**; this package does not close either theorem. Provider-to-frozen type and seal-body probes are consequently N/A.

## Scope and evidence

Date: 2026-10-28. Worktree: `/root/code/KAM-inp-n1204`.

| Input | Pinned revision / SHA-256 |
|---|---|
| HEAD | `66d3e865eb8f634320898037ae21a3c79220eeaf` |
| `inp` at audit | `f390de8f741ebb8dab2d17ff12ec7f7e5b6d4f46` |
| `inp-n1201` at audit | `ff9fb32a2ef3af73a293dd5b77f59b6e6fc4c3c5` |
| Coefficients module | `4b20717b9d8d2b8a2cc780bf9ba728bec46e0db5062894516125e7e2abd78ac0` |
| Local `N12-LEAN-DESIGN.md` | `d66059fe35c7b3f76307ae60df90aa3da66ea089cd3ec073b39cbe2ffd1b6370` |
| `/root/code/KAM-inp/.drafts/design/N12Signatures.lean` | `0ad9cf0f84ffc435f1d85360516ad94f5ec100ff4a53c76d410f9e7d3b028369` |
| Local Part 12 blueprint | `dd549dc5c3069e1a185767b5fa580d979963fa920a4b9e7939529047d13ebbfc` |

Read AGENTS, PLAN, DECISIONS, the supplied package-audit brief, the local N12-04 handoff, track-N statement conventions, relevant frozen definitions and averaging theorem anchors, Part 12's standing data and coefficient statement/proof, design row N12-04 and signatures, and the two design audits. The signatures file is absent locally; the exact named copy was read from the main inp worktree. The design audits are at `docs/tracks/N/design/DESIGN-N12-design-audit-{1,2}.md` in that main worktree, rather than the handoff's `audits/` directory. No authority was silently reconstructed from an implementation.

`git diff inp...HEAD` reports three added files: Coefficients (336 lines), Field (219), Setting (112). Git warns:

```text
warning: inp...HEAD: multiple merge bases, using ef8fc426c638557035e6101216aad4ef8b8a570e
```

Accordingly, the requested broad comparison was supplemented with `git diff inp-n1201 HEAD -- KAM/Nekhoroshev/Averaging`: exactly the 336-line Coefficients addition. Setting and Field are byte-unchanged against `inp-n1201`. The moving `inp-n1201` ref also contains unrelated later work; a three-dot comparison with that ref includes unrelated modules, so its full diff is not described as the package delta. Existing N12-01 infrastructure was inspected where consumed, without claiming a fresh package audit of it.

Method: independent source/signature reconstruction, complete reading of the coefficient proof, definition-body checks, expanded-premise review, fresh targeted build, exact-type/equation/consequence probes, axiom inspection, kernel replay, source lint, and protected-path checks. Applied the `lean-statement-audit` skill's relevant checks. No delegation or state-changing git operations.

## Public declaration and node ledger

All names below are in `KAM.Nekhoroshev`. Line numbers refer to the audited Coefficients module.

| Node / contract | Declaration / clause | Verdict | Evidence |
|---|---|---|---|
| `bpN:p12:s-data#data`, p12:87 | `avgCoeff`, L31 | PASS | Exact existing `KAM.Weighted.coeff`; unit-cube Bochner coefficient, negative period-one character. |
| Same | `avgBeta`, L33 | PASS | Exact `exp (-π*s*modeSize k)`; `modeSize` is the sum of absolute integer coordinates. |
| Same | `avgQ`, L35 | PASS | Exact real scalar `∑ j, k_j * frequencyMap h I j`; frequency is the frozen real gradient. |
| `bpN:p12:coef`, p12:90 | `coef`, L276–290 | PASS | Entire type equals both source-facing design signatures, including binder order, domains, constants, all six conjuncts. |
| `co-a`, p12:93 | `coef` conjuncts 1–2 | PASS | Holomorphy on the full action tube and decay there; no `R ≤ s` premise or domain enlargement. |
| `co-b`, p12:94 | `coef` conjunct 3 | PASS | Complex action partial at real actions, exact coefficient bound `(2/s)*β_k`. |
| `co-c`, p12:95 | `coef` conjuncts 4–5 | PASS | Genuine `HasSum` of f and the complex inclusion of the real slow field, with sign `-2πi k_j`; absolute convergence checked separately. |
| `co-d`, p12:96 | `coef` conjunct 6 | PASS, stronger | Summability over all modes, including zero, implies the source's zero-excluded weighted sum is finite. |

The zero slow-field term is identically zero because of `k j`; all-mode summation therefore agrees with the blueprint's exclusion of zero. Absolute convergence is not merely inferred from informal Fourier notation: the probe compiles `.summable.norm` for both `HasSum` clauses, using finite-dimensional real targets. No new standalone public polynomial-summability theorem was promised by the signatures; that result is the final conjunct of `coef`.

## Definition classification

These are all new definitions/abbreviations. No new structure or instance.

| Definition | Classification and full-carrier assessment |
|---|---|
| `avgCoeff` | Literal alias of an existing total Bochner-integral coefficient. No conditional, selected witness, or extra fallback introduced. On the analytic tube, the proof supplies regularity and the integral's intended Fourier meaning; global function arguments follow the track's stated extension convention. |
| `avgBeta` | Literal exponential formula for every real s and integer mode. Positivity of s is needed for summability, not for definition fidelity. |
| `avgQ` | Literal finite dot product for every h, k, I, using the unchanged frozen total frequency map. Analytic hypotheses guard derivative interpretation at source points; no division by a frequency component. |
| private `baseD`, L39 | Literal abbreviation `realInclusion n '' actionBall n R`; no enlargement, auxiliary law, or valid-locus branch. |

For each of these four definitions:

```text
BODY_MATCH: OK
PUBLIC_CARRIER: OK (baseD is private; its declared carrier is also correct)
WELL_DEFINEDNESS: N/A_LITERAL
CHARACTERIZATION: N/A_LITERAL
CHOICE_INDEPENDENCE: N/A
DEFINITION_VERDICT: PASS
```

The public bodies and types match the signatures verbatim. Three `rfl` equation probes independently confirm the public defining equations on their entire declared carriers.

## Expanded binder and hypothesis audit

`coef` has inferred implicit parameters `{n R s h f}` in the order fixed by its type and one explicit binder `(d : AveragingData n R s h f)`. There are no new instance binders. Expanding d gives precisely the following standing premises. The bundle itself adds no additional premise beyond its fields.

| Binder / expanded logical input | Bin | Source / reason |
|---|---|---|
| `n : ℕ` | TYPING | Dimension, p12:17. |
| `R : ℝ` | TYPING | Action radius, p12:17. |
| `s : ℝ` | TYPING | Geometric strip/tube width, p12:17. |
| `h : (Fin n → ℂ) → ℂ` | TYPING | Fixed integrable Hamiltonian, p12:17. |
| `f : AvgComplexPhase n → ℂ` | TYPING | Fixed perturbation, p12:17. |
| `d.hn : 1 ≤ n` | STANDING | Explicit Part 12 dimension convention, p12:17. |
| `d.hR : 0 < R` | STANDING | p12:17. |
| `d.hs : 0 < s` | STANDING | p12:17. |
| `d.hh`: holomorphy of h on action tube | STANDING | p12:17; frozen `IsAnalyticIntegrable`:35. |
| `d.hh`: continuity on closure | STANDING | Same definition:36. |
| `d.hh`: existential nonnegative value bound for h | STANDING | Same definition:37; bound chosen after h, not a new uniform parameter. |
| `d.hh`: reality on real action domain | STANDING | Same definition:38. |
| `d.hh`: real C³ regularity | STANDING | Same definition:39; existing redundant derivative guard. |
| `d.hf`: `0 ≤ 1` | STANDING | Frozen `IsAnalyticPerturbation`:35 at size one; tautological. |
| `d.hf`: holomorphy on `complexDomain n R s` | STANDING | Same definition:35. |
| `d.hf`: continuity on closure | STANDING | Same definition:36. |
| `d.hf`: invariance under every integer angle shift | STANDING | Same definition:37–38; periodicity, not a Fourier-series premise. |
| `d.hf`: reality at real angles/actions in real action domain | STANDING | Same definition:39–40. |
| `d.hf`: pointwise norm bound by one on complex domain | STANDING | Same definition:41. |
| `d.hrank`: frozen rank alternative | STANDING | p12:17; `HasAveragingFrequencyRank`:39–42: either Dω is onto everywhere on the ball, or ω is nonzero and `(v,u) ↦ Dω v + u•ω` is onto everywhere. No slab-volume conclusion is assumed. |

Counts, treating each displayed conjunction field and the one rank disjunction as a logical input: TYPING=5, STANDING=15, SOURCE=0 separately from those standing fields, RULED=0, EXCESS=0. The rank alternatives are not simultaneous hypotheses. No compact K, flow, coefficient-decay witness, summability witness, or derivative estimate is hidden in d. Several standing premises are unnecessary for this coefficient lemma, but the unchanged source-facing package signature uses the common data bundle.

## Proof review, including private helpers

| Declaration (line) | Verdict | Checked role |
|---|---|---|
| `cast_single` (41) | PASS | Integer-coordinate cast agrees with complex unit coordinate. |
| `dom_eq` (46) | PASS | Weighted domain equals the frozen strip times action tube, via `actionNbhd_eq_polyNbhd`. |
| `inClass` (51) | PASS | Derives holomorphy and unit periodicity from hf on exactly that domain. |
| `slice_diff` (58) | PASS | Holomorphic slice restriction for width at most s. |
| `slice_per` (64) | PASS | Slice periodicity derived from full integer periodicity. |
| `coeff_decay` (72) | PASS | Boundary-radius decay at width s gives `exp(-2πs|k|₁)`, then weakens to the required β. |
| `norm_fderiv_le` (86) | PASS | Closed max-norm ball of radius s/2 around a slice point in strip s/2 lies strictly in the full domain; Cauchy yields 2/s. |
| `realI_mem` (110) | PASS | Real source action lies in its positive-width complex tube. |
| `norm_dir_le` (117) | PASS | Operator-norm bound supplies directional bound. |
| `norm_single_prod_fst` (124) | PASS | Angle unit direction has norm at most one. |
| `norm_single_prod_snd` (128) | PASS | Action unit direction has norm at most one. |
| `coeff_dir_decay` (133) | PASS | Cauchy bound on strip s/2, then Fourier decay at that width, yields exactly `(2/s)*β`. Its private class premise is produced by `coefficients_deriv`, not exposed as a public assumption. |
| `hasSum_slice` (161) | PASS | Existing Fourier reconstruction plus actual summability gives a `HasSum` at every real angle. |
| `summable_poly` (183) | PASS | With c=πs/2>0, exponential domination bounds the cubic weight by `(6/c³)*exp(c)*exp(-c|k|₁)`; existing lattice exponential sum pays convergence. |
| `single_eq` (212) | PASS | Real inclusion sends a real basis vector to the complex one. |
| `iota_mem` (217) | PASS | Source real phase point maps into analytic domain. |
| `real_partial` (224) | PASS | Restricts complex derivative to real directions; imaginary part vanishes on an open neighborhood, so the real-part derivative is the actual complex partial. |
| `polyNbhd_real` (253) | PASS | Same real-action membership in weighted-domain notation. |
| `hasSum_class_slice` (258) | PASS | Supplies `hasSum_slice` hypotheses by actual class/domain restriction. |
| `coef` (276) | PASS | Produces every private premise from d or the existing coefficient-derivative theorem and assembles all six conclusions. |

The action-partial argument is a valid proof-route variation: bound derivatives of f on the half-width angle strip, identify their Fourier coefficients with action derivatives of coefficients, and decay those coefficients. It achieves the blueprint's exact result without assuming it. The real slow-field reconstruction uses the correct Hamiltonian minus sign and period-one factor 2π.

## Mechanical verification

All Lean/Lake/checker invocations initiated by this audit were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5` (the build gate itself applies nice). Lint's ABI subprocess inherited both settings. No clean, update, cache download, or package mutation was requested.

1. Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1204 KAM.Nekhoroshev.Averaging.Coefficients
```

Output, exit 0:

```text
[inp-gate] slot 2 acquired 08:15:39 for KAM.Nekhoroshev.Averaging.Coefficients
Build completed successfully (3179 jobs).
```

2. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Output, exit 1 solely for the brief-permitted generated-root exception:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (469 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

3. Probe, generated from the external signature rather than the implementation type:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N1204Audit.lean
```

Exit 0. It copies the entire `coef` declaration under fresh name `n1204AuditSignature` with body `by exact coef d`, checks all three public definition equations with `rfl`, and derives norm-summability of both Fourier series from the exported conjuncts. Exact printed axiom output:

```text
'KAM.Nekhoroshev.coef' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgCoeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgBeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgQ' depends on axioms: [propext, Classical.choice, Quot.sound]
```

4. Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Averaging.Coefficients > .lake/abi-scratch/N1204-leanchecker.log 2>&1
```

Exit 0. Complete output:

```text
replaying KAM.Nekhoroshev.Averaging.Coefficients
```

Only one new module is in this focused package, so this single invocation covers its complete lemma module; there is no provider module to add.

5. Static checks:

- Python comparison: `avgCoeff`, `avgBeta`, `avgQ` literal type/body matches = `True` against both signatures sources; `coef` exact signature matches = `True` against both.
- Full file: 336 lines, zero lines longer than 100 Unicode characters; no forbidden proof escapes, ambient `EuclideanSpace`, or resource overrides. Module header, copyright, public imports, module docstring, exposed public section all present.
- Recursively traversed 49 project modules: 18 imported frozen modules, all under `Defs/`, all manifest state `SEALED`; no provider and no frozen theorem imports. Thus no `DRAFT_SORRY` theorem enters the production import closure.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: no diff, only the multiple-merge-base warning quoted above.
- `git diff --check`: exit 0, no output, including the final closeout rerun. The new report was also checked separately for trailing whitespace and unresolved draft markers.

## Findings, errata, limitations and handoff

No suspected defect in the coefficient blueprint/source contract; no new source erratum or mathematical deviation introduced. The known Part 12 source repairs and the design-audit-1 `wreg` finding concern other obligations; audit 2 resolves that signature finding, and this package makes no corrector/flow/averaging-root closure claim.

Notes: the stale generated root is explicitly allowed by the audit brief and left untouched; the broad `inp` comparison has multiple merge bases; the handoff's supporting-file locations needed the read-only resolutions listed above. These are recorded without repairing protected files or changing scope.

Owned output: this report only. The pre-existing untracked `N12-04-handoff.md` is preserved. Temporary audit probes/logs were removed at closeout. No production file, frozen file, manifest, generated file, git index, or git history was changed by the auditor.
