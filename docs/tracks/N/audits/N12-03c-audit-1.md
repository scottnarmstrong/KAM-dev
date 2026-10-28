# N12-03c independent package audit 1

Overall verdict: **PASS WITH NOTES** for the scoped infrastructure package and `KAM.Nekhoroshev.ext_dep`. The derivative-convergence and derivative-identification obligations are proved, with no additional regularity premise. No mathematical blocking finding was identified.

Frozen anchors: **not submitted for sealing by this package**. Neither `averaging_mean` nor `averaging_most` is proved here; no seal-ready verdict for either follows from this audit. Provider/frozen ABI and frozen seal-body probes are inapplicable to this infrastructure-only submission. Instead the exact design signature and its application body were checked independently.

## Scope and comparison evidence

Audited on 2026-10-28 in `/root/code/KAM-inp-n1203c`:

- HEAD `c0fdfc5c856d6831e629fa999f7b398b8ce477a6`.
- `inp` at comparison: `6e36995edb8c5fb4ee4ec0ed914f4a0c55a9b7f1`.
- `inp-n1203b`: `0db283262a5e45063c3382003143df4855214a5b`.
- Scoped file: `KAM/Nekhoroshev/Averaging/LocalDependence.lean`, 464 lines, SHA-256 `131c39d65425a84c0638b15febbd6cf4cb40444d2bd9d6a46af19602560852b1`.

Read AGENTS.md, PLAN.md, DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the local N12-03c handoff, N12-LEAN-DESIGN.md (especially row N12-03c and the local-dependence proof obligation), both DESIGN-N12 design audits, the exact `N12Signatures.lean`, blueprint Part 12, the track-N statement, and the downstream frozen averaging theorem statements. The two design audits are under `docs/tracks/N/design/`, not the handoff's abbreviated `audits/` location; the signatures are in the main inp worktree. The generic ODE predicate and the imported Picard derivative API were inspected directly. No external source theorem is used as a black box by this module.

Executed the requested `git diff inp...HEAD` and the focus comparison `git diff inp-n1203b...HEAD`. Both warn:

```text
multiple merge bases, using 6b0a10fa72ac1200e8c692d55ceaa3fdd0cf1849
```

Both broad three-dot diffs include inherited normal-form, resonance, planetary, PicardFamilies, documentation, and generated-root changes. In particular, the literal protected-path check against `inp` is **not empty**: `KAM.lean` has 12 added imports. `KAM/Frozen`, `manifest`, and `README.md` have no diff. This is a recorded comparison/hygiene note, not silently treated as an empty diff.

To determine attribution, additionally checked `git diff d4fd146..HEAD`: precisely one new file, LocalDependence.lean (464 lines). `d4fd146` is the merge of N12-03b immediately before the two N12-03c commits. Its protected-path diff is empty. The generated-root imports come from inherited commit `4dad814`, preceding N12-03c. The current branch tip named inp-n1203b is not a clean package-only comparison either. Per the explicit AUDIT FOCUS, no correctness verdict is issued on inherited out-of-scope modules.

## Declaration ledger

All names below have prefix `KAM.Nekhoroshev`. Line numbers refer to LocalDependence.lean. The only new objects are one definition and one proposition-valued structure; all nine public theorems are covered.

| Node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| Parameter-integral continuity helper | `continuousOn_intervalIntegral_param` (45) | PASS | Joint continuity on the closed time/initial-data box implies joint continuity of the variable-endpoint integral. Time clamping agrees on the entire integration interval, including negative time. More general codomain than the application is harmless. |
| Derivative iteration | `voltIter` (71) | PASS | Literal recursion Y₀=id, Yₘ₊₁=id+∫F′(uₘ)∘Yₘ; no fallback or substituted derivative. |
| Picard input data | `IterData` (77) | PASS | Numerical bounds, genuine field derivative, continuity, trapping, initial value, and Picard recurrence. Does not contain derivative-iterate convergence or differentiability of uₘ or of the limit as a field. |
| Composite-integrand continuity | `continuousOn_comp_integrand` (92) | PASS | Composition on the trap and continuous-linear-map composition give exactly the required joint continuity. |
| `ext-dep#derivative-limit`, iterate stage | `voltIter_spec` (101) | PASS | Induction proves continuity, uniform bound 1/(1−aΛ), and the actual Fréchet derivative of every uₘ on the open initial ball. No derivative-iterate conclusion is assumed. |
| Interval containment helper | `uIcc_zero_subset_Icc` (182) | PASS | Unordered interval from 0 to t lies in [−a,a] under a≥0 and t-membership. Covers both signs of t. |
| Time-slice continuity helper | `continuousOn_uIcc_of_joint` (186) | PASS | Restricts joint continuity to the integration interval and a fixed valid initial point. |
| `ext-dep#derivative-limit`, recurrence | `voltIter_step` (195) | PASS | Proves next error ≤aΛ ε+a dd/(1−aΛ) by splitting the operator-product difference. ε and dd are intermediate error bounds, not final theorem premises. |
| `ext-dep#derivative-limit`, convergence | `voltIter_uniform` (251) | PASS | Proves a single N uniform in t and x for every positive tolerance, using compact uniform continuity of F′ and q<1. Does not assume uniform convergence of derivative iterates. |
| `ext-dep#identify` | `hasFDerivAt_limit` (323) | PASS | Instantiates Mathlib's uniform derivative-limit theorem on an open ball with established derivatives, uniform derivative convergence, and pointwise map convergence. |
| `bpN:p12:ext-dep` | `ext_dep` (364) | PASS | Exact design telescope/conclusion, C¹ on open W only; constructs positive a,r, genuine local solutions in W, joint continuity, genuine initial derivatives, joint derivative continuity, and the Volterra identity. |

The separate conditional helpers take the already-constructed Picard/linear families and their estimates as arguments. Those are staged dependencies explicitly allowed by the design, not added premises of `ext_dep`. At lines 421–438 `picard_family` constructs u,y and all Picard estimates; `linear_family` constructs Y and its continuity/bound/equation; `hasFDerivAt_limit` then proves the missing derivative identification. All `IterData` fields are discharged there.

## Definition and hypothesis audit

`voltIter` is a total, exposed, noncomputable recursive definition with exactly the intended formula on its entire carrier. Bochner integrals are total in Lean, but every theorem that uses integral identities supplies the required continuity/integrability on the actual interval. The application uses complete E and hence a complete continuous-linear-map space. There is no use of junk integral values.

`IterData : Prop` has ten fields: nonnegative time, nonnegative derivative bound, contraction smallness, `HasFDerivAt F F′`, continuity of F′, its norm bound, u₀=id, joint continuity of uₘ, trap membership, and the Picard step equation. Its generated projections merely expose these assumptions. In particular neither differentiability of uₘ nor convergence of Yₘ nor differentiability of y is bundled. The structure is a conditional helper interface, fully constructed in the final proof, rather than a source assumption added to the final theorem.

The generic real normed-space carrier strengthens the finite-dimensional coordinate instance needed downstream; no ambient `EuclideanSpace`, alternate Hamiltonian, or altered norm is introduced. `FiniteDimensional`, `CompleteSpace`, and `ProperSpace` in `ext_dep` are exactly in the approved design signature. The helpers work under the appropriate more general completeness/properness assumptions. Constants a,r are existential after F,W,x₀; no uniformity or dependence was weakened.

## Critical proof checks

1. **Actual differentiation of iterates, lines 101–180.** The induction starts at u₀=id. For the successor, the open ball is a neighborhood of x. The integrand derivative is the operator composition F′(uₘ)∘Yₘ, with uniform bounds Λ and 1/(1−q); time continuity supplies interval integrability. `hasFDerivAt_intervalIntegral_comp` applies on this neighborhood. The equality with uₘ₊₁ is used as an eventual equality on the open ball, giving the genuine `HasFDerivAt` of the total map, rather than a derivative only within a closed ball.
2. **Derivative convergence, lines 267–319.** Set B=2/(1−q) and dstar=(η/2)(1−q)²/(a+1)>0. Uniform continuity of F′ on the compact trap and the geometric Picard error give a common tail where the derivative coefficient difference is ≤dstar. The recurrence yields `‖Y_(N+k)−Y‖ ≤ q^k B+η/2`. The choice of dstar makes the accumulated forcing ≤η/2, and geometric decay pays the other half. No Lipschitz-DF or C² input, and no contraction claim for the pair (y,Y), occurs.
3. **Limit theorem hypotheses, lines 337–354.** Checked Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean:420–425. `isOpen_ball` supplies the domain; `voltIter_uniform` at η/2 gives the strict-distance uniform convergence requested by the API, including the reversed subtraction norm; `voltIter_spec` supplies every derivative; squeezing the Picard bound gives map convergence at every point of that ball. No unproved side condition is passed to the limit theorem.
4. **Local construction and genuine derivative, lines 381–460.** A closed trap of radius δ inside W supplies bounds on F and fderiv F. Using L0=max L 0 and Λn=toNNReal Λ only enlarges these upper bounds; neither coerced bound changes F. The chosen a gives aL0≤δ/2 and aΛn≤1/2. PicardFamilies supplies trapping and time derivatives, and PicardDerivatives supplies the independent linear family. After identification, derivative uniqueness replaces Y with actual `fderiv` on the open initial ball, both in joint continuity and throughout the Volterra integral. Thus the conclusion cannot be satisfied merely by the junk value of fderiv on nondifferentiable maps.

The blueprint uses a larger auxiliary ball of radius 2δ; the implementation works directly on a radius-δ trap and takes initial radius δ/2. This is a valid internal radius choice with the same required margins, not a change in theorem hypotheses or conclusion. Avoiding the explicit real supremum dₘ and using tolerance bounds from uniform continuity also retains the entire derivative-convergence claim.

## Independent checks and exact results

All commands ran in the package worktree. Audit-owned Lean/Lake/checker invocations were serialized. No build from scratch, cache mutation, resource override, or generated-root regeneration was performed.

Targeted build, through the prescribed gate:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1203c KAM.Nekhoroshev.Averaging.LocalDependence
```

The gate executes `nice -n 5 lake build`. Exit **0**:

```text
[inp-gate] slot 2 acquired 08:40:06 for KAM.Nekhoroshev.Averaging.LocalDependence
Build completed successfully (2776 jobs).
```

Cached dependency warnings: PicardFamilies unused section variables (lines 60,82,203,208) and a style suggestion at 268. LocalDependence warnings: unused section variable at 45 and 186, and implicitly used binder p at 99. No errors, proof escapes, or heartbeat design signals. The build replayed cached diagnostics; fresh kernel replay below independently checks the module.

Exact signature/probe check:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N1203cAudit1.lean
```

Exit **0**. A Python comparison of the text from `theorem ext_dep` to `:=` returned `ext_dep signature byte equality: True` against `/root/code/KAM-inp/.drafts/design/N12Signatures.lean` (SHA-256 `0ad9cf0f84ffc435f1d85360516ad94f5ec100ff4a53c76d410f9e7d3b028369`). The fresh theorem copied that exact telescope and conclusion and used:

```lean
by
  exact KAM.Nekhoroshev.ext_dep hW hF hx
```

The same probe printed axioms for **every new public theorem**, with the complete output:

```text
'KAM.Nekhoroshev.continuousOn_intervalIntegral_param' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.continuousOn_comp_integrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.voltIter_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.uIcc_zero_subset_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.continuousOn_uIcc_of_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.voltIter_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.voltIter_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.hasFDerivAt_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.ext_dep' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay (one invocation; there is only one submitted module and no provider):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Averaging.LocalDependence
```

Exit **0**, output:

```text
replaying KAM.Nekhoroshev.Averaging.LocalDependence
```

Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the explicitly permitted stale generated root:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (480 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

This is PASS under the audit brief's stated exception; it is not a literal zero exit. The handoff's claim of lint rc 0 is not reproduced by either independent invocation.

An earlier invocation, `sh scripts/lint_sources.sh`, produced the same lint findings. Audit process deviation: that first lint invocation did not explicitly set LEAN_NUM_THREADS=1 or nice for its internally launched ABI Lean process. No other audit-owned Lean operation overlapped it. The final invocation above repeats lint under the requested environment and priority. All other audit-owned Lean operations explicitly used LEAN_NUM_THREADS=1 and nice -n 5.

Additional checks:

- `git diff d4fd146..HEAD --check`: exit 0, no output.
- Forbidden-token/resource-override search of LocalDependence: no matches. No `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, heartbeat/recursion overrides, or EuclideanSpace.
- File length 464; module header, copyright, public imports, module docstring, public noncomputable section, and exposed definitions present.
- Recursive KAM import closure is exactly LocalDependence, PicardDerivatives, PicardFamilies, and ODE.Basic. No provider and no frozen theorem module (DRAFT_SORRY or otherwise) is imported, directly or transitively.
- Probe files and the temporary kernel log were removed after the checks. No production file or git state was changed by this audit. The handoff was already untracked at entry; the only added repository artifact is this report.

## Notes, uncertainties, errata, and deviations

No suspected pinned-source erratum, false blueprint claim, frozen-statement defect, conclusion-shaped final hypothesis, or unproved derivative-convergence obligation was found. The inherited broader averaging source issues are outside this local ODE module; no fresh pinned-PDF audit of those issues is claimed.

The nonempty inherited generated-root diff, expected stale-root lint result, harmless compiler warnings, and audit-process lint invocation deviation are explicitly recorded above. No source or Lean correction was introduced. Package PASS does not certify the broad inherited diff, prove the downstream global-flow concatenation, establish averaging, or close either frozen root.
