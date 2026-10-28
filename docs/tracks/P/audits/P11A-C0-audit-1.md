# P11A-C0 independent package audit 1

Overall verdict: **PASS WITH NOTES** for the scoped C0 infrastructure and `KAM.Planetary.p11_lambda_spec`. No mathematical or statement-fidelity defect was found. The notes are the declared additional dependency on W0 and the brief-permitted stale generated root. This is not a seal of P-FIXED.

## Scope, authority and snapshot

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-p11ac0`.
Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and `docs/tracks/P/audits/P11A-C0-handoff.md`. The user's exact report destination overrides the generic brief's main-worktree destination. Applied the `lean-statement-audit` method to the scoped declarations.

Compared `git diff inp...HEAD` at:

```text
HEAD       e3e3bb86c222d0ed7230726a18bc1e128821e25a
inp        5991245cabc06e69ec900cb6006b45f72cc85eb0
merge-base 5991245cabc06e69ec900cb6006b45f72cc85eb0
```

The six changed tracked files comprise the two C0 modules, merged `WeakMeasure/Basic.lean`, and three W0 audit/handoff documents. The C0 handoff was already untracked at entry. Per its AUDIT FOCUS, this audit covers only `KAM/Planetary/MaximalStep/Basic.lean` and `Constants.lean`; it does not repeat the W0 theorem audit. W0's carrier abbreviations and the transitive import boundary were inspected because C0 uses them.

Authority: `docs/tracks/P/design/P11A-LEAN-DESIGN.md`, especially sections 1–3, the node registry, row P11A-C0 at L711, import-DAG rule at L738–743, and Appendix A; the three `DESIGN-P11A-design-audit-{1,2,3}.md` reports, with their final accepted R3 scope; delivered `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`; `blueprint-P/parts/p11a2-cutoff-step.tex` L22–28, L42–46, L70–73, L97–99, L113–115, and L170. Read the track-P statement's P-FIXED section and the downstream frozen theorem for scope control.

| Input | SHA-256 |
|---|---|
| C0 `Basic.lean` | `097e7cc1149b63134fe66d3542f4659a365ce48b51af5888980c0def400666ed` |
| C0 `Constants.lean` | `d2aba1deca236bd9298c6621bcf845b778ef88a29d54d895b91e41f491c71d8f` |
| Design | `8619ea896c856347a9a5c5efac5080f0c830ea19245320b5f03a2b4267a300b9` |
| Delivered signatures | `c31fda0b479f2dd0488b12e7f2daeda18f965eb316610df1c65f14012dfcb092` |
| p11a2 blueprint | `990694a832aa02dca0138c5cbb3bab842984583f4ca92576479eff04786ed3ec` |

The signature file is byte-identical to the design's Lean Appendix A and matches the accepted R3 pin. No proof-bearing signature file was imported.

## Declaration and node ledger

All names below are in `KAM.Planetary`, unless qualified otherwise.

| Node / responsibility | Declaration and implementation locator | Verdict | Reason |
|---|---|---|---|
| `c2-conv#data` | Existing `Phase`, `P11Vec`, `P11CVec`, `P11Phase`, `P11Family`, `actionNbhd` | PASS WITH NOTES | Pi/product carriers preserve the ambient max norms; no new norm instance. Carrier aliases come from W0, an extra import edge. |
| `c2-conv#bracket` | Existing `KAM.Canonical.poissonBracket`, `KAM.hamiltonianVectorFieldℂ` | PASS | No replacement definition. Existing bracket is the stated angle-first sum with positive angle/action term and negative action/angle term. C0 proves no new flow theorem. |
| `domain-def` | `domain_def`, Basic L32–33 | PASS | Exactly `Weighted.Dom n {0} s r ×ˢ B`; width/radius argument order is correct. |
| `domain-def` | `p11Admissible`, Basic L36–39 | PASS | Joint complex differentiability and domain-local period-one angle shifts; exact design predicate. |
| `domain-def` / bound representation | `p11Bound`, Basic L42–43 | PASS | Pointwise upper bound on the intended set, as explicitly selected in design section 1.4. |
| real-slice guard | `p11Real`, Basic L46–49 | PASS | Tests all real angle/action/parameter points whose complex inclusions belong to the domain. |
| `domain-def` / Fourier truncation | `p11Cut`, Basic L52–54 | PASS | Existing truncation applied in angles with action and parameter held fixed; correct factor `2π` through existing characters. |
| `taylor-cutoff` construction | `p11Taylor`, Basic L57–58 | PASS | Value plus complex Fréchet derivative in action at zero, applied to the actual action vector. No coordinate-sum norm substitution. |
| `cutoff` construction | `p11Cutoff`, Basic L61 | PASS | Fourier cutoff of the Taylor polynomial, in the prescribed order. Estimate theorems belong to later packages. |
| `fourier-cutoff` constant | `p11C`, Constants L26–27 | PASS | Literal `2(1+1/π)(3n/(eπ))^(n−1)`, natural exponent. |
| `fourier-cutoff` error | `p11Error`, Constants L29 | PASS | Literal `c_n(1+d^(−n))exp(−πTd)`, implemented as inverse of the natural power. |
| `loss-choice` construction | `p11Loss`, Constants L31–32 | PASS | Correct numerator, natural factor n, and denominator `πT`; no altered dependence. |
| `sec-hom#lambda` definition | `p11Lambda`, Constants L34 | PASS | Existing `Weighted.coth(πδ)^n−1`, with `coth=cosh/sinh`. |
| `sec-hom#lambda` identity and bounds | `p11_lambda_spec`, Constants L38–85 | PASS | Exact design type, explicit summability, correct nonzero lattice and both stated upper bounds. Independently elaborated and kernel-replayed. |

Only the final row is a new public theorem. No C0 provider or frozen theorem is claimed by the handoff. Consequently the brief's provider/frozen type comparison and frozen seal-copy checks are **not applicable** to this package. An analogous exact-type and explicit-binder application probe was run for its actual theorem, described below.

Downstream anchor `planetary.fixedSunPlanetaryKAM.v1`, export `KAM.Planetary.fixedSunPlanetaryKAM`, remains manifest state `DRAFT_SORRY` at `KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM.lean`. Its proof is still `by sorry`. **PROOF_STATUS: FROZEN_UNPROVED; no seal-ready verdict.** C0 is only the declared infrastructure/lattice portion of that route; the P-FIXED source/statement audit is not repeated here.

## Expanded binder audit of `p11_lambda_spec`

Source: p11a2 L22 gives `N ≥ 1`; L170 gives `δ > 0`, the identity and both bounds. There are no instance binders or bundled hypotheses in the theorem.

| Binder, in order | Type / information | Bin | Source |
|---|---|---|---|
| `{n}` | implicit `ℕ` | TYPING | L22 dimension of angles/actions |
| `hn` | explicit `1 ≤ n` | SOURCE | L22 `N ≥ 1` |
| `{delta}` | implicit `ℝ` | TYPING | L170 real strip loss |
| `hd` | explicit `0 < delta` | SOURCE | L170 `δ > 0` |

Counts: SOURCE 2; STANDING 0; TYPING 2; RULED 0; EXCESS 0. No assumed identity, summability, estimate, or conclusion-shaped premise is hidden in an alias or typeclass. `hn` is unused by the proof because the reused exponential-sum result holds for all n; retaining the source restriction is faithful. No constant witness has been moved across a quantifier.

Independent proof reconstruction: set `x=2πδ>0` in `KAM.Fourier.exp_sums n` (`KAM/Fourier/ExpSums.lean` L256–271). Its `HasSum` supplies summability on all integer modes, hence on the nonzero subtype. The zero mode has `modeSize 0=0` and contributes exactly one. `tsum_eq_add_tsum_ite` and `tsum_subtype` remove precisely that mode, yielding `coth(πδ)^n−1`. The nonnegative coth bound can be raised to the natural power and then reduced by one. The nonzero-mode bound uses `8n/(2πδ)=4n/(πδ)`. The exponent is the lattice l1 norm throughout. There is no nonsummable real-tsum shortcut.

## Definition classification and whole-carrier checks

All eleven definitions are **literal constructions/predicates**; none is characterization-defined, selected by choice, or an output/assumption structure. For each of the eleven rows below:

```text
BODY_MATCH: OK
PUBLIC_CARRIER: OK
WELL_DEFINEDNESS: N/A_LITERAL
CHARACTERIZATION: N/A_LITERAL
CHOICE_INDEPENDENCE: N/A
DEFINITION_VERDICT: PASS
```

| Definition | Classification and carrier check |
|---|---|
| `domain_def` | Literal subset of the complex family product. `Weighted.Dom` unfolds to strip × `polyNbhd {0} s`; the latter is exactly `‖eta‖<s`. The frozen strip is the coordinatewise strict imaginary-part bound. |
| `p11Admissible` | Literal analytic/periodic predicate. It factors openness of B into callers' separate `hB : IsOpen B`, as the accepted signatures do; it does not assert B is open. Periodicity does not constrain off-domain values. |
| `p11Bound` | Literal universal pointwise bound, including empty U and arbitrary M. It does not claim an unguarded real supremum exists or equals a junk value. |
| `p11Real` | Literal real-slice predicate using the actual frozen real phase and existing inclusions. |
| `p11Cut` | Literal existing Fourier operator. On every finite real threshold T the l1 lattice ball is finite (empty for T<0); its indicator tsum therefore represents a finite sum. The Bochner coefficient is the existing integral of the real angle slice. Analytic reconstruction estimates require later admissibility hypotheses. |
| `p11Taylor` | Literal total value/Fréchet-derivative expression. On the source open admissible domain with positive s, the action-zero derivative is a genuine complex derivative. For arbitrary total functions Lean retains its standard total `fderiv` semantics, exactly as in the design; C0 proves no analytic assertion from an off-domain/default derivative. |
| `p11Cutoff` | Literal composition of the preceding two operators. |
| `p11C` | Literal real formula on `ℕ`; the source theorems restrict n≥1, with no theorem exploiting n=0. |
| `p11Error` | Literal real arithmetic/exponential formula for every real T,d. Analytic uses restrict d>0 and T≥0 separately. |
| `p11Loss` | Literal real arithmetic/logarithm formula. Source estimates require T≥1 and 0<alpha≤1; C0 makes no estimate at zero/negative parameters. |
| `p11Lambda` | Literal hyperbolic formula on all real delta. The proved lattice specification requires delta>0, excluding the singular source parameter. |

There is no newly introduced `if`/`dite`, fallback, arbitrary witness, global instance, alternative Hamiltonian, or replacement norm. The standard total integral/derivative/division/logarithm operations are the exact accepted formulas, not a new substitute object. Their off-source values are not used in the sole C0 theorem.

## Independent mechanical checks

Checks were serialized: no audit build, probe, replay or lint ABI elaboration overlapped another. Every Lean/Lake invocation inherited `LEAN_NUM_THREADS=1` and niceness 5. No clean, update, cache operation, package modification, budget override or generated-root regeneration was performed.

### Targeted gate build

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ac0 KAM.Planetary.MaximalStep.Constants
```

Exit 0; output:

```text
[inp-gate] slot 1 acquired 09:52:31 for KAM.Planetary.MaximalStep.Constants
Build completed successfully (9085 jobs).
```

This is the targeted gate's own summary, including its dependency jobs, not a claimed clean rebuild.

### Exact type, definition equations and axioms

Created only `.lake/abi-scratch/P11AC0Audit1.lean`. It imported the completed Constants module, copied the eleven definitions from the pinned design into a fresh namespace, and checked for each:

```lean
example : @KAM.Planetary.<name> = @<copied name> := rfl
```

It also copied the entire exact `p11_lambda_spec` statement under a fresh namespace, replacing only `:= sorry` by:

```lean
by exact KAM.Planetary.p11_lambda_spec hn hd
```

Then checked:

```lean
example : type_of% @KAM.Planetary.p11_lambda_spec := @p11_lambda_spec
```

Command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AC0Audit1.lean
```

Exit 0, no warnings/errors. Complete axiom output:

```text
'KAM.Planetary.domain_def' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Cut' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Taylor' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Cutoff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11C' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Error' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Loss' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Lambda' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_lambda_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.MaximalStep.Constants KAM.Planetary.MaximalStep.Basic
```

Exit 0. Complete output:

```text
replaying KAM.Planetary.MaximalStep.Basic
replaying KAM.Planetary.MaximalStep.Constants
```

### Lint, imports and protected paths

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the explicitly permitted stale-root exception. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (526 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The live module count is 526; the handoff's 524 is an older receipt, not this independent run. No other lint failure was printed.

Static inspection and an import-closure traversal found 39 project modules, no provider imports, and no frozen theorem imports, including transitively. Frozen definition imports do not invoke any DRAFT_SORRY anchor. Thus there is no imported frozen theorem whose manifest state needs a SEALED exemption.

Both files have copyright/license/author headers, `module`, public imports, module docstrings, and `@[expose] public noncomputable section`. They have 63 and 85 total lines, respectively; maximum line length is 99 characters in each. No scoped file contains `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, or `set_option`. No recursive or instance-search budget override is present.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit 0, with empty output. No production or protected path was edited by this audit.

## Notes, suspected defects and limits

1. **Declared architectural deviation, nonblocking for mathematical correctness:** Basic L12 imports `KAM.Planetary.WeakMeasure.Basic` for the four carrier abbreviations (W0 L26–29). Design row C0 lists existing Weighted/frozen inputs, and L738–743 says the import DAG consists exactly of listed edges. The implementation therefore adds C0→W0. The edge is acyclic, shares the intended Pi carriers, and introduces no mathematical premise or global norm instance, but the implementation does not literally retain the planned package independence. Reconcile the schedule/DAG or extract shared carriers when integrating. This audit does not silently amend the design.
2. The additional real-restriction and frozen Phase imports implement the accepted real-slice definition. Splitting constants between Basic and Constants preserves the declarations. Broad Mathlib imports are a possible later performance concern, not a correctness finding here.
3. The generated-root lint exception is expressly permitted by this audit brief. The root remains untouched.
4. **No new suspected pinned-source or blueprint defect was found in C0.** The inherited design reports' reality/totality and upstream-port notes remain outside this package's delivered theorem claims. The formulas audited here do not depend on those unpaid analytic/physical steps.
5. No claim is made for Fourier/Taylor estimates, loss estimates, the homological solution, canonical step, W0 proof closure, or any Part 13/frozen-root assembly. In particular a successful C0 package audit cannot promote P-FIXED from FROZEN_UNPROVED.

Only this Markdown report is retained as an audit edit. The exact-type/definition probe was deleted after successful elaboration. Final `git diff --check` and `git diff --check inp...HEAD` exited 0; a trailing-whitespace scan of the new report passed. Final status contains only the pre-existing untracked C0 handoff and this new untracked audit report. HEAD and the two scoped module hashes remained unchanged.
