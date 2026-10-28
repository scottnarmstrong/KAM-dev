# P23-13c independent package audit 1

Overall verdict: **PASS WITH NOTES**. No mathematical or signature failure found. This package proves infrastructure only; no frozen anchor is offered for sealing, and this audit does not close `osc_iter` or release P23-15.

## Scope and authority

Audited HEAD `5dd9c207fbe6122c54dd3f39b07efc00a4335f1a` in `/root/code/KAM-inp-p2313c`. Read AGENTS.md, PLAN, DECISIONS, the shared package audit brief, local P23-13c handoff and its AUDIT FOCUS, Revision 3 and Appendix A.3 of `docs/tracks/P/design/P23-LEAN-DESIGN.md`, the design audit, shared `/root/code/KAM-inp/.drafts/design/P23Signatures.lean`, track-P statement, and `blueprint-P/parts/p2-averaging.tex:167–196`.

The user's exact report destination overrides the generic brief's main-worktree destination. Audit scope is ONLY `KAM/Planetary/Averaging/OscillatorAdjoint*.lean`. `git diff inp...HEAD` contains the new 312-line OscillatorAdjoint and inherited 335-line OscillatorSeriesAlgebra. The focused `git diff inp-p2313b...HEAD -- 'KAM/Planetary/Averaging/OscillatorAdjoint*.lean'` contains only the former. The broader comparison with inp-p2313b has unrelated integration differences, which are outside this explicitly narrowed audit. Recorded refs: inp `05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2`, inp-p2313b `2990ba1bbe1fef94c42f1b224e06c873939a211e`.

No provider or frozen theorem is implemented here, so provider/frozen ABI equivalence and a frozen seal-copy probe are inapplicable. Instead, exact signed declarations were copied under fresh names into `.lake/abi-scratch/P2313cAudit.lean`, with these proof bodies:

```lean
by exact osc_adjoint_bound hn hm hφ hu hbφ hbu hΦ hA hwidths houter j
by exact osc_ratio_range m hd hΦ hs
```

The two signature headers are text-identical to the shared signed headers and Appendix A.3. Numerical definitions also match textually, and separately copied noncomputable definitions satisfy function-level `rfl` equality with the production definitions. No fixture or signed `sorry` body was imported by the probe.

## Declaration-by-declaration findings

All declarations below have prefix `KAM.Planetary`; line numbers refer to OscillatorAdjoint.lean.

| Node / role | Declaration / line | Verdict | Reason |
|---|---|---|---|
| oi-ratio, numerical definition | `oscLieRatio`, 37 | PASS | Exact `exp 1 * (1 + exp 1 * m) * Φ / (2*d)`. |
| oi-range, numerical definition | `oscTheta`, 38 | PASS | Exact `2 * exp 1 * (1+m) * Φ / d`. |
| `stepP:p2:oi-range` | `osc_ratio_range`, 40 | PASS | Signed binders and all five conclusions preserved; valid for every natural m, including zero. |
| restriction helper | `oscBound.mono_gen`, 76 | PASS | Smaller parameter carrier/angle width and larger majorant; termwise nonnegative comparison proves summability and bound. No class or nonemptiness premise added. |
| class helper | `oscClass.const_mul`, 90 | PASS | Scalar multiplication preserves holomorphy and fast-angle periodicity. |
| oi-ratio product | `osc_prod_step`, 95 | PASS | Exact product `C^h*h!/(2h)!`, including h=0 and arbitrary real C. Denominators are positive natural shifts. |
| oi-ratio scalar step | `osc_ratio_step`, 114 | PASS | Outer margin and positive loss give ratio at most `1/(h+1+i)`. Holds for every natural i, stronger than the induction's i<h use. |
| oi-ratio constant | `osc_step_const_le`, 124 | PASS | All four ratios bounded separately; minimum product equals d/h²; coefficient is exactly `2*(1/e+m)`. Explicit nonnegative Φ and B support multiplication. |
| oi-ratio induction | `osc_adjoint_induction`, 169 | PASS | For i≤h proves actual adPow class and bound on all four shrinking widths; no bracket/induction conclusion is assumed. |
| oi-ratio factorial | `osc_final_estimate`, 237 | PASS | Uses proved `Canonical.factorial_ge (2*h)` and exact numerical identity for q; no asymptotic premise. |
| `stepP:p2:oi-ratio` | `osc_adjoint_bound`, 266 | PASS | Exact Appendix A.3 type, quantifier order, norms, carrier, majorant and factorial normalization. General four-loss result, with j=0 proved separately. |

The seven auxiliary theorems are proof-local refinements of the two blueprint steps, not substitutes for the signed interface. Their premises are typing, domain, class/bound or numerical data. No conclusion-shaped hypothesis, bundled unpaid step, wider constant dependence or weakened signed conclusion was found.

## Proof and applicability review

Write d=min(ρσ,ρpρq) and c_m=2(1/e+m). For h≥1, the proof keeps the generator on its original outer domain and applies `osc_bracket` to the current iterate, losing `(ρ,ρp,ρq,σ)/h` at each step. The source margins imply the four ratios are ≤1/(h+1+i), and the minimum loss product is d/h². Thus each step costs at most c_m*h²*Φ/(d*(h+1+i)). Positivity of the current majorant is proved from hA and hΦ. The successor sign from `adPow_succ_eq_neg` is handled by scalar multiplication by -1, whose norm is one.

At i=h the domains are exactly the claimed four-loss domains. The product is `(c_m*h²*Φ/d)^h*h!/(2h)!`. Scaling by inverse h! and applying `(2h)!≥(2h/e)^(2h)` yields q^h*A, using the exact identity `q=(c_m*h²*Φ/d)*(e/(2h))²`. The j=0 case restricts class and bound directly, avoiding division by zero. The adjoint theorem requires no smallness assumption: convergence smallness is correctly confined to the separately signed ratio theorem.

For oi-range, x=Φ/d≥0 and `16*(1+m)*x≤1`. The proof uses e<4 to derive q≤η, then η≤e/8, `(16/9)*η<1`, and x≤1/4. No positivity of D or its nonemptiness is inferred: nonnegative Φ and A are explicit signed premises and remain valid when the parameter domain is empty. The sharper q is stronger than the blueprint's coarser η bound. Generator margin hypotheses are exactly the generic signed helper's margins; they are not silently appended to `osc_iter`. Future series/flow identification must still supply the intended 3/4-loss instance and its own proof.

## Definition classification and imports

Only two new definitions occur: `oscLieRatio` and `oscTheta`. Both are exposed numerical expressions with intended bodies on their whole Lean carrier. Real division is total at d=0, but every theorem using division/comparison supplies positive d directly or from positive losses; no proof exploits a zero-denominator fallback. No new abbrev, structure, instance, alternative norm, Fourier index type or phase carrier occurs.

The existing `oscClass`, `oscBound`, `oscFunction`, `oscParams`, `oscDom`, packing, canonical adPow and bracket were read for applicability. The bound is the existing weighted coefficient sum at every flat parameter (I,p,q), with only θ Fourier-expanded, on the existing max-norm domain. No equal-dimension weighted theorem is substituted for the unequal parameter space.

A recursive source-import scan found 74 project modules, no provider import, and no frozen theorem import. The twelve imported frozen modules are definitions, all manifest state SEALED: ActionNbhd, ComplexStrip, HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, SymplecticForm, and Planetary Fast/Phase/Slow. Hence no DRAFT_SORRY anchor enters this import closure.

## Independent checks

All Lean/Lake commands are serialized with LEAN_NUM_THREADS=1 and nice -n 5; the build uses the required compile gate. No production code, frozen file, manifest, generated root or README was changed.

1. Targeted build:

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2313c KAM.Planetary.Averaging.OscillatorAdjoint
[inp-gate] slot 1 acquired 10:57:57 for KAM.Planetary.Averaging.OscillatorAdjoint
Build completed successfully (9120 jobs).
exit 0
```

2. Signed signature copies, definition equality and all public theorem axioms:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2313cAudit.lean
exit 0
```

Each of the nine public theorems printed exactly `[propext, Classical.choice, Quot.sound]`: osc_ratio_range, oscBound.mono_gen, oscClass.const_mul, osc_prod_step, osc_ratio_step, osc_step_const_le, osc_adjoint_induction, osc_final_estimate, osc_adjoint_bound. The first probe run exited 1 only because its two copied numeric definitions lacked `noncomputable`; this scratch harness issue was corrected to match the production noncomputable section before the successful rerun. No production change was needed.

```text
'KAM.Planetary.osc_ratio_range' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscBound.mono_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscClass.const_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_prod_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_ratio_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_step_const_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_adjoint_induction' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_final_estimate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_adjoint_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay (one invocation, only the scoped lemma module; no provider exists):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Averaging.OscillatorAdjoint
replaying KAM.Planetary.Averaging.OscillatorAdjoint
exit 0
```

4. Source lint:

```text
LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (553 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

This is precisely the expected generated-root exception allowed by the audit brief. No root regeneration was performed; no other lint diagnostic occurred. This is the reason for the overall WITH NOTES qualifier.

5. `git diff --check inp...HEAD`: no output, exit 0. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0. Scoped forbidden-token/resource-override search: no matches (rg exit 1). File length: 312 lines; module header, copyright, public imports, module docstring and exposed public noncomputable section present.

## Uncertainties, errata and deviations

No suspected defect in the scoped signed statements or blueprint proof steps was found. No new pinned-source erratum or mathematical deviation is alleged. This audit checks the pinned in-repository design/blueprint implementation contract; it does not claim a new independent PDF transcription audit. The existing broader oscillator-transfer source-gap note at `blueprint-P/parts/p2-averaging.tex:196` remains a campaign-level limitation, and the later Lie-series/flow/remainder/reality packages remain outside this report.

Only this report is a repository edit by the auditor; the pre-existing untracked P23-13c handoff is retained. The auditor-created `.lake/abi-scratch/P2313cAudit.lean` was deleted after the successful probe; no auditor probe remains. All required checks completed; the only accepted nonzero check is the documented stale-root lint exception.
