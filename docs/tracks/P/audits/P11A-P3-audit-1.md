# Independent package audit: P11A-P3

Date: 2026-10-28. Overall verdict: **PASS WITH NOTES**. Both public theorem statements and proofs pass the mathematical review. No frozen theorem is claimed sealed by this infrastructure package.

## Scope and authority

Audited only `KAM/Planetary/Preparation/RectangularBracket.lean` at HEAD `6fd4eed1bcb9ab44179e133260b7cffdc2f93cc4`, against `inp` at `31f0bfbf70c07b1eefd006237f331c00e003a0e5`, using `git diff inp...HEAD`. The diff contains precisely this new 252-line module. Read AGENTS.md, PLAN.md, DECISIONS.md, the common package brief, the handoff and AUDIT FOCUS, the P statement conventions, P11A design P3 row and proof obligations, and blueprint-P/parts/p11-cp09-preparation.tex:120–128.

The user explicitly overrides the common brief's report destination: this report is inside `/root/code/KAM-inp-p11ap3`, not `/root/code/KAM-inp`. The handoff locates prior design audits under `audits/`; they actually reside under `/root/code/KAM-inp/docs/tracks/P/design/`. The signature draft is absent locally and was read from `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`. All three prior design audits were consulted for this package: audit 1's local-premise/field omissions were resolved in audit 2 and retained as PASS in audit 3. Their historical FAIL verdicts are not current P3 findings.

Input hashes:

- Module: `6f0c84135b8c086a9a768d5da0a3b2e5e5d37f644bbdf3d6cc8ba92a89d5fbf9`.
- Design: `8619ea896c856347a9a5c5efac5080f0c830ea19245320b5f03a2b4267a300b9`.
- Signature draft: `c31fda0b479f2dd0488b12e7f2daeda18f965eb316610df1c65f14012dfcb092`.
- Blueprint Part 11: `4c0e2dfefb50b1e06581e069a55846d25e0e4697a8826514ac699bbb83efb41f`.

## Declaration and node ledger

All names below are in `KAM.Planetary`; locators refer to the audited module.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| Rectangular domain | `p11Box` (L36) | PASS | Exact design signature and body; complex center, disjoint exhaustive Fin blocks, strict componentwise radii. |
| Weighted norm bound | `p11WBound` (L40) | PASS | Exact design signature and body; quantifies over the actual set, with summability and a uniform bound. |
| `bpP:p11:aniso-bracket`, field clause | `aniso_field` (L139) | PASS | Exact complete signature, local holomorphy/periodicity, frozen complex Hamiltonian field, max norm and separate action weights, stated constant. |
| `bpP:p11:aniso-bracket`, bracket clause | `aniso_bracket` (L188) | PASS | Exact signature, same domain and losses, summability as well as the bound; no dimension factor or extra premise. |
| `stepP:p11:ab-der` | `polyNbhd_box_subset` (private, L59), `field_bounds` (private, L88), weighted Cauchy inputs in `aniso_bracket` (L207–215) | PASS | Geometric inclusions and Cauchy bounds are proved/reused, not assumed. The summed angular derivative estimate comes from existing Weighted machinery. |
| `stepP:p11:ab-prod` | `aniso_bracket` L216–248 and `aniso_field` L162–183 | PASS | Existing `wbound_bracket` supplies the coefficient algebra/product estimate; slack is removed continuously and the exact coefficient is recovered algebraically. |
| Limit helper | `le_of_small` (private, L49) | PASS | Right-neighborhood limit of scalar inequalities; no analyticity or convergence premise smuggled in. |
| Nonnegativity helper | `wsum_nonneg'` (private, L54) | PASS | Nonnegative summands; used with actual summability/bounds where required. |
| Neighborhood membership | `mem_polyNbhd_self` (private, L71) | PASS | Self witness at every strictly positive slack radius. |
| Analytic restriction | `inClass_of_box` (private, L77) | PASS | Restricts the actual holomorphic periodic function using proved domain inclusion. |

There is no provider export or frozen theorem anchor in P3. Provider=frozen-type and literal frozen sealing probes are therefore **not applicable**. Instead, the scratch probe copies each of the four exact design signatures under a fresh name, elaborates an explicit application of the production declaration to all explicit binders in order, and checks `example : type_of% @audit_name := @KAM.Planetary.name`. No draft sorry declaration is imported. The complete signatures and both complete definition bodies also match after whitespace normalization.

## Definitions, hypotheses and proof review

The only new definitions are `p11Box` and `p11WBound`; there is no new abbrev or structure. `p11Box` is the intended product of open complex discs on its whole carrier, including empty blocks and arbitrary real radii. Empty-block quantification is the intended empty-product convention. `p11WBound` is meaningful over arbitrary action sets; openness is needed by analytic theorems, not by this predicate. It couples `WSummable` to `wsum`, so the underlying tsum's nonsummable fallback cannot discharge the results. No replacement Hamiltonian, derivative, field, norm, instance or torus is introduced.

All theorem premises are the prescribed local differentiability/periodicity, input weighted bounds, radii and strip comparisons. `hr1` and `hr2` are retained from the design despite being unused by these proofs. No conclusion-shaped hypothesis, bundled output premise or hard step assumed as an instance was found.

For the proof, put V = the target inner box, m = min(rho1,rho2), and d = min(r01-r1+rho1,r02-r2+rho2). Triangle inequalities in the existing Pi max norm prove `polyNbhd V m` and `polyNbhd V d` lie in the respective input boxes. The proofs explicitly establish m>0, d>0, sigma>0 and s0-s+sigma>0.

For each 0<delta<min(m,d), `wbound_bracket` is applied on base V with outer radii d and m and action loss m-delta. Its target is `polyNbhd V delta`, containing each target point. This proves summability and the bound

`exp(1)^(-1) * (1/((d-delta)*sigma) + 1/((s0-s+sigma)*(m-delta))) * U * W`.

Summability is taken from a fixed positive delta; only the scalar inequality is passed to delta=0. Thus no unjustified interchange of limits and infinite sums occurs. Positive denominators justify continuity and the final field_simp/ring identity with the blueprint's `(nu_theta+nu_I)/(e*m*sigma)` coefficient. The smaller strip and action set are exactly the advertised ones.

For the field, coefficient Cauchy and `sup_le_wbound` give `norm(dtheta phi) <= M/(e*sigma)` and `norm(dI phi) <= M/m`, the latter via the same slack argument. M>=0 follows at an actual target action from the input bound. The first field component is dI, the second is -dtheta, literally as in the frozen definition. Pi norm estimates and e>1 prove the maximum of the angle-scaled norm and the two separately scaled action-block norms is at most M/(m*sigma). No period conversion or ambient norm change occurs. Weighted.modeWeight uses `exp(2*pi*s*|k|_1)`, consistent with geometric strip widths and period-one angles.

The design's local obligation names `ab_der`/`ab_prod` are implemented through the private geometric helper and existing Weighted estimates rather than separate public lemmas. This is permitted by the design's proof-local obligation convention; it is not an unproved exported claim.

## Independent verification

All audit-launched Lean/Lake checks were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`. No resource override was used.

1. Targeted compile gate:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap3 KAM.Planetary.Preparation.RectangularBracket
[inp-gate] slot 1 acquired 12:42:10 for KAM.Planetary.Preparation.RectangularBracket
Build completed successfully (9086 jobs).
exit 0
```

This was the prescribed targeted build against the existing worktree build overlay; no clean/cache/update or from-scratch library build was requested.

2. Exact signature/application/type and axiom probe:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AP3Audit.lean
'KAM.Planetary.p11Box' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11WBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.aniso_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.aniso_bracket' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

The first generated probe had a parsing error because its extractor stopped at the field conclusion's `let X :=`. That audit-tool error was corrected to retain the complete signature. The corrected probe above elaborated without warnings; the initial recovery warning did not describe production code.

3. Kernel replay:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.RectangularBracket
replaying KAM.Planetary.Preparation.RectangularBracket
exit 0
```

One invocation replays the single new module, including its private helpers. There are no separate new lemma modules.

4. Source lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (650 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The only failing condition is the explicitly permitted stale generated root. Module, frozen-anchor and all 144 ABI checks pass; this is an accepted audit-gate result, not a claim that raw lint exited 0.

5. Import and source integrity:

The recursive KAM import closure has 40 modules, no provider, and no frozen theorem module. Its seven frozen modules are definitions, each manifest state SEALED: ActionNbhd, ComplexStrip, HamiltonianVectorField, HamiltonianVectorFieldC, IsPrimaryOnStrip, IsRealOnReals and OmegaZero. The actual frozen strip/field definitions and the relevant Weighted carriers, coefficient norm, Cauchy, bracket and sup-bound interfaces were inspected.

The new file has copyright, module, public imports, module docstring and an exposed public noncomputable section. It is 252 lines, below the 1500-line cap. Its only options are theorem-local `linter.unusedVariables false`; these do not alter elaboration budgets. No forbidden proof escape or resource override is present.

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(no output; exit 0)
git diff --check
(no output; exit 0)
```

Final HEAD and inp hashes remain the snapshot hashes above. The report is the only audit-created repository file; the untracked handoff pre-existed. The three audit-owned scratch files (signature probe and kernel/lint logs) were deleted after recording receipts. No tracked file was edited, no frozen/generated file changed, and no state-changing git command was run. The untracked report was separately checked for trailing whitespace, balanced code fences and unresolved placeholders; all checks passed.

## Notes, uncertainties, errata and deviations

No suspected mathematical source/blueprint defect or introduced statement deviation was found within P3. This review checks the designated blueprint and existing Lean estimates, not a fresh audit of the underlying pinned literature. The earlier design findings about global periodicity and the missing field clause are resolved here by local hypotheses and the actual field companion.

The generated root is intentionally untouched; an isolated stale-root lint result is the explicit exception allowed by the common audit brief. P3's package PASS does not close P11A-P4 averaging, later flow/normal-form consumers, any physical headline or a frozen anchor. No downstream consumer implementation was included in the requested single-module audit.
