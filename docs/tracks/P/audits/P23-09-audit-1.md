# P23-09 independent package audit 1

Overall verdict: **PASS WITH NOTES** for `KAM.Planetary.fourier_compact` and its
`bpP:p3:fourier-compact` contract. The proof supplies all iterated Fréchet derivative
orders on every inner closed strip, with a common limit holomorphic on the whole open
strip. No material mathematical or interface defect found. Note N1 concerns only the
wording of an auxiliary definition's docstring; N2 records the permitted generated-root
lint exception. This infrastructure package introduces no provider or frozen theorem;
no frozen anchor is being certified seal-ready by this report.

## Scope and authority

Audited HEAD `f1827573f7b98da656dbccd9c2eb74504b835a64`, compared using
`git diff inp...HEAD` with `inp` at `33c688a1d1c9d25d7099f328479f4f53b0301bb4`.
The entire branch diff is two added Lean files, 334 lines:

- `KAM/Planetary/TwoScale/FourierCompact.lean` (256 lines).
- `KAM/Planetary/TwoScale/FourierCompactCauchy.lean` (78 lines).

Read AGENTS.md, PLAN, DECISIONS, the shared `inp-audit-package.md` brief, the local
P23-09 handoff/AUDIT FOCUS, revision 2 of `docs/tracks/P/design/P23-LEAN-DESIGN.md`
(row P23-09, node table, proof/signature and consumer context), its two design audits,
`/root/code/KAM-inp/.drafts/design/P23Signatures.lean` lines 763–778,
`blueprint-P/parts/p3b-two-scale-limit.tex` lines 64–75 and consumers at 94 and 123,
and the Track P statement. The signature scratch file is absent from this package
checkout; the shared original was read without modification. The design audits live
under `docs/tracks/P/design/`, rather than the handoff's abbreviated audits location.
The prompt's explicit report destination in this package checkout overrides the
shared brief's generic main-worktree destination.

The transitive local import closure has 19 modules and contains no provider or frozen
theorem module. Its only frozen modules are the definitions `ComplexStrip`,
`IsPrimaryOnStrip`, and `IsRealOnReals`; these were read. Thus provider/frozen-type
and frozen seal-body probes are inapplicable. An independent exact design-signature
application probe was run instead. No I/N/P frozen headline is proved by this package.

## Node and declaration review

Names in the first file are in `KAM.Planetary`; Cauchy helpers are in `KAM`.
Private declarations are identified as such and included for completeness.

| Node / obligation | Lean declaration (file line) | Verdict | Reason |
|---|---|---|---|
| `bpP:p3:fourier-compact` | `fourier_compact` (Compact:174) | PASS | Exact design type: same source premises, full-strip bounded periodic holomorphic extension, every `0 < v < w`, then every derivative order `m`. No changed norm, carrier, constant dependence or quantifier. |
| `stepP:p3:fc-decay` | private `coeff_decay` (Compact:49) | PASS | Uses upstream full-width coefficient decay, obtained by a limit from smaller contour shifts; includes zero mode. Stronger bound at `w` implies blueprint bounds at `w′ < w`. |
| `stepP:p3:fc-coef` | private `tendsto_coeff` (Compact:60) | PASS | Uniform real convergence gives continuity of `f` and coefficient convergence via the torus-average norm bound. No assumed continuity premise added. |
| `stepP:p3:fc-tail` | private `eventually_norm_sub_lt` (Compact:95) | PASS | Summable majorant `2 B exp(-2π(w-ρ)|k|₁)` controls coefficient differences uniformly on each inner strip. Dominated convergence of the sum implements the finite-part/tail argument. |
| Inner-strip decay predicate | `StripDecay` (Cauchy:32) | PASS WITH NOTES | Exposed, one-sided uniform smallness predicate, used only on nonnegative norms; see N1. |
| Cauchy derivative step for `fc-tail` | `stripDecay_fderiv` (Cauchy:36) | PASS | Arbitrary complex normed codomain; only holomorphy and convergence of input norms assumed. Closed ball radius `(w-ρ)/2` lies in the midpoint strip; bound `(εδ/2)/δ < ε`. |
| All derivative orders for `fc-tail` | `stripDecay_iteratedFDeriv` (Cauchy:64) | PASS | Induction using analytic iterated derivatives and the norm identity for their Fréchet derivatives. No higher-derivative hypothesis assumed. |
| Integer-lattice adapter | private `intCast_single` (Compact:38) | PASS | Coordinatewise cast of a single integer mode is the corresponding complex vector. |
| Real inclusion continuity | private `continuous_ofReal_pi` (Compact:45) | PASS | Product continuity of the coordinatewise real embedding. |
| Periodicity adapter | private `periodic_single` (Compact:81) | PASS | Restricts the given full lattice law to each unit coordinate translation. |
| Exponential majorant identity | private `exp_mul_exp_aux` (Compact:87) | PASS | Exact exponential multiplication/algebra identity for arbitrary real inputs. |

## Proof, definitions and consumer applicability

`StripDecay` is the only new named `def`/`abbrev`/`structure`. Its body has no
fallback, junk output or hidden source assumption. For norm inputs it is exactly the
required uniform convergence to zero on all smaller open strips, for all real widths
below `w`. There are no new structures or instances. The local choices `a`, `c`,
`bd`, and `H` are respectively the real limit's Fourier coefficients, the sequence's
coefficients, the explicit summable exponential bound, and `F j - G`.

`G = fourierSum (torusCoeff f)` is a total ambient function. Although a general
`tsum` may default outside its summability domain, the proof establishes weighted
summability and absolute convergence at every point of the original open strip before
using the series there. No conclusion constrains or relies on its values outside that
strip. The original `F j` are also total ambient functions; all derivative conclusions
are at points interior to their holomorphy domain. Ambient Pi max norms, integer Fourier
indices, and the period-one `2π` convention agree with the design.

The full-width coefficient estimate is inherited from `norm_torusCoeff_le`, whose
upstream proof takes the limit of estimates at widths strictly below `w`; it does not
shift a contour onto an unprovided boundary. The coefficient limit inherits this bound.
The weighted summability proof pays the positive gap `w-ρ`. The Tannery theorem is the
standard summable-majorant version of finite-mode convergence plus a uniformly small
tail, so there is no missing infinite-mode argument.

Holomorphy of the common Fourier sum is proved locally at every point of the whole
strip. Its bound, extension identity and lattice periodicity follow from pointwise
limits. For derivatives, the difference `H j = F j - G` is holomorphic; Cauchy induction
propagates inner-strip convergence to every order. The final midpoint width strictly
contains the closed strip of width `v`; subtraction of iterated derivatives is justified
by analyticity at those points. This valid alternative to termwise polynomial-weighted
Fourier tails preserves the blueprint conclusion and is explicitly authorized in the
handoff focus. No conclusion-shaped input or hard proof step is assumed.

The public theorem retains the design's redundant `hB : 0 ≤ B`; its use is immaterial
since the uniform bound at any real point already forces nonnegativity. It does not
introduce an extra hypothesis. The theorem also handles `n = 0`, which is harmless and
stronger than positive-dimensional standing conventions. The scalar theorem can be
applied componentwise in `lp-an`; its all-order convergence includes the same first
derivatives required for the `lg-lim` passage. This checks the supplied interface, not
completion of those later packages or their common-witness release gate.

## Independent validation

Every Lean/Lake invocation below was sequential with `LEAN_NUM_THREADS=1` and
`nice -n 5`. No heartbeat, recursion-depth or synthesis overrides were used.

1. Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2309 KAM.Planetary.TwoScale.FourierCompact KAM.Planetary.TwoScale.FourierCompactCauchy
```

Exit 0, output:

```text
[inp-gate] slot 1 acquired 07:08:38 for KAM.Planetary.TwoScale.FourierCompact KAM.Planetary.TwoScale.FourierCompactCauchy
Build completed successfully (3134 jobs).
```

2. Kernel replay, one invocation covering both new modules:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.TwoScale.FourierCompact KAM.Planetary.TwoScale.FourierCompactCauchy
```

Exit 0, output:

```text
replaying KAM.Planetary.TwoScale.FourierCompactCauchy
replaying KAM.Planetary.TwoScale.FourierCompact
```

3. Exact-signature probe and all public theorem axioms:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2309Audit.lean
```

The probe imported only the implementation module, copied the full shared design
signature under `example`, and supplied body
`by exact KAM.Planetary.fourier_compact hw hB hhol hper hb hconv`.
This elaborated without a draft import or `sorry`, exit 0, with output:

```text
'KAM.Planetary.fourier_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.stripDecay_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.stripDecay_iteratedFDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1; complete output (collected across the running command):

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (441 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The sole failure is the generated-root exception expressly permitted by the audit
brief. In particular, no 100-character-line violation was emitted. No generated root
was regenerated.

5. Static hygiene and protected paths:

```sh
git diff --check inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

Both exit 0 with empty output. An independent Python scan of both new files found:

```text
KAM/Planetary/TwoScale/FourierCompact.lean: 256 lines; max 100 chars; over 100: []
forbidden: []
KAM/Planetary/TwoScale/FourierCompactCauchy.lean: 78 lines; max 100 chars; over 100: []
forbidden: []
Local transitive import closure: 19
Provider imports: []
Frozen theorem imports: []
Frozen imports: ['KAM.Frozen.Defs.ComplexStrip', 'KAM.Frozen.Defs.IsPrimaryOnStrip', 'KAM.Frozen.Defs.IsRealOnReals']
```

The forbidden-token scan included `sorry`, `admit`, `axiom`, `unsafe`, `opaque`,
`EuclideanSpace`, and any `set_option`. Both files have copyright/authors, `module`,
public imports, module docstrings, and `@[expose] public section`; the only new
named definition is exposed. No provider quarantine violation or `DRAFT_SORRY`
dependency was found. Axioms and kernel replay additionally check actual dependencies.

## Notes, errata, deviations and limits

**N1 — minor documentation imprecision, no proof repair required.**
`FourierCompactCauchy.lean:31` says: “A real function sequence tends to `0` uniformly
on every strip of width `ρ < w`.” The actual predicate at lines 32–33 is one-sided:
`∀ ε > 0, eventually φ j z < ε`, uniformly on each inner strip. For arbitrary signed
inputs, the constant sequence `φ = -1` satisfies it but does not converge to zero.
Every theorem and application here passes a norm, so nonnegativity makes the predicate
exactly correct for all current consumers. Suggested wording: “Uniform eventual upper
smallness on every inner strip; equivalent to convergence to zero for nonnegative
inputs.” No source or frozen defect follows from this docstring issue.

**N2 — permitted integration note.** Source lint exits 1 solely because `KAM.lean`
is stale after the two module additions. The brief explicitly permits this exception;
root regeneration belongs to integration and was not performed during this audit.

**Source/blueprint defects:** none newly suspected in the audited mathematical
contract. The blueprint's polynomial-weighted derivative-tail argument is replaced
by Cauchy induction after the scalar exponential-tail argument; this is a valid proof
route variation with the same conclusions. No frozen definition, normalizer, source
premise, or consumer type was changed. No primary-source PDF claim beyond the supplied
blueprint/design was independently reverified in this package audit.

**Audit edits and cleanup:** only this report was written in the repository. The
pre-existing untracked `P23-09-handoff.md` was left untouched. The temporary probe was
removed from `.lake/abi-scratch/`. No state-changing git command was used; no production,
frozen, manifest, generated-root, README, or shared signature file was edited.

All required targeted checks completed. This is a package-level PASS WITH NOTES;
it does not close P-G, P-PLANAR, P-FIXED or later limit/measure proof obligations.
