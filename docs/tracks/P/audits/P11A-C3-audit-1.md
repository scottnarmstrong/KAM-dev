# P11A-C3 independent package audit 1

Overall verdict: **PASS WITH NOTES** for the two design-signature exports. Independent type probes, axiom checks, kernel replay and both targeted builds passed; lint has only the explicitly permitted stale-root exception. This package contains infrastructure lemmas, not a provider or a frozen theorem seal. No anchor is certified seal-ready by this report. The general external node `bpP:p11a:x-cauchy` is not fully exported; its required consequences for these two exports are proved.

## Scope and authority

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the package handoff, `docs/tracks/P/design/P11A-LEAN-DESIGN.md` (C3 row, registry, proof plan and signatures), design audits 1–3, the current `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`, `blueprint-P/parts/p11a2-cutoff-step.tex`, the relevant downstream parameter/Taylor calls, `docs/tracks/P/statement.md`, frozen neighbourhood/strip/phase definitions and the imported Cauchy/regularity infrastructure. Earlier design-audit FAILs concern other signatures; audit 3 is PASS and all three retain PASS for the two signatures here.

The user's exact worktree-local output path overrides the generic brief's main-worktree destination. Only this report is a persistent audit edit. Scratch probes are confined to this worktree's `.lake/abi-scratch/` and removed after checking. No git mutation, frozen edit, source repair or root regeneration.

Snapshot:

- HEAD: `027479ca6f9fa91f59328422f2f0b6061cfb5d8b`.
- `inp`: `872a014af58890f96058190624e431a0ed0228a5`.
- `inp-p11ac0`: `75c5ae1e02ad39f69589ff5acbaebb6c2c9cf4d8`.
- `git diff inp...HEAD`: exactly the two added source files below (360 lines).
- `git diff inp-p11ac0...HEAD`: includes unrelated intervening upstream changes; only `MaximalStep/Parameter*.lean` and `MaximalStep/Taylor*.lean` were audited. Both files are absent from both bases, so their scoped additions are identical in both comparisons.

| File | Lines | SHA-256 |
|---|---:|---|
| `KAM/Planetary/MaximalStep/Parameter.lean` | 100 | `9928f138f9d4959a1192246f17ef5064e8580d0636c506a9b48bc6dfcdc34a8b` |
| `KAM/Planetary/MaximalStep/Taylor.lean` | 260 | `0a327c6cee2b840a9942b37ea430d70363221f208de31288ccdfb84314e1f35d` |
| `docs/tracks/P/design/P11A-LEAN-DESIGN.md` | 2264 | `8619ea896c856347a9a5c5efac5080f0c830ea19245320b5f03a2b4267a300b9` |
| `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean` | 1320 | `c31fda0b479f2dd0488b12e7f2daeda18f965eb316610df1c65f14012dfcb092` |

## Declaration and node ledger

All declaration names below are in `KAM.Planetary`. Every new public declaration is a theorem; there are 12, with no new definitions, abbreviations or structures.

| Node / obligation | Declaration (file:line) | Verdict | Reason / scope |
|---|---|---|---|
| `pc-poly`: collar openness | `p11_isOpen_actionNbhd` (Parameter:30) | PASS | Exact union of open max-norm balls about real points; valid for all E and t, including empty collars. |
| `pc-iter`: all-order ball estimate | `p11_norm_iteratedFDeriv_le_of_closedBall` (Parameter:41) | PASS | Genuine bound `A / δ^k` on nested balls, including order zero. Finite-dimensional domain and complete second-countable codomain are typing/regularity data, not assumed estimates. |
| `bpP:p11a:param-cauchy` | `param_cauchy` (Parameter:75) | PASS | Exact design signature; all j≥1, vector max norm, same `j^j M/(t-tp)^j`, no altered constant dependence. |
| `tc-line`: scalar series tail | `p11_series_remainder` (Taylor:33) | PASS | Distinct specialized helper: closed-disc holomorphy/bound, q∈(0,1), tail at 1. Closed-disc inputs are proved from strict interior slack by its caller. |
| `tc-a`: full first derivative | `p11_norm_fderiv_le_of_ball` (Taylor:93) | PASS | Full operator norm ≤M/s for scalar-valued maps on an arbitrary complex normed space; stronger than a coordinate-column bound. No unjustified boundary evaluation. |
| `tc-b`: scalar Taylor tail | `p11_taylor_remainder` (Taylor:124) | PASS | Exact q²/(1−q), genuine Fréchet derivative, arbitrary complex normed domain. Positive s follows from the point hypothesis. |
| `domain-def` membership adapter | `p11_mem_domain_def` (Taylor:157) | PASS | Unfolds actual product domain to strip membership, max-norm action ball and b∈B. |
| `domain-def` openness adapter | `p11_isOpen_domain_def` (Taylor:161) | PASS | Open product, no hidden positivity/regularity premise. |
| `tc-line` slice adapter | `p11_slice_differentiableOn` (Taylor:166) | PASS | Restriction along the actual affine η slice; all membership conditions supplied explicitly. |
| `tc-a` derivative adapter | `p11_fderiv_slice` (Taylor:175) | PASS | Literal chain rule with derivative η↦((0,η),0); no substituted derivative object. |
| Taylor admissibility | `p11_taylor_admissible` (Taylor:187) | PASS | Joint holomorphy and local angle-periodicity from hF; equality of derivatives follows from equality on a neighbourhood of η=0. |
| `bpP:p11a:taylor-cutoff` | `taylor_cutoff` (Taylor:226) | PASS | Exact scalar design signature, all four conjuncts: admissible, 2M bound, q²-tail, full η-derivative bound M/s. |
| `bpP:p11a:x-cauchy` | Local `hp`, `hcoeff`, `hsum` in Taylor; nested-ball induction in Parameter | PASS WITH NOTES | Required applications are supplied. No general open-disc vector coefficient theorem or arbitrary unequal-radius mixed-polydisc theorem is exported; do not mark that full external statement proved from these exports alone. |

## Statement fidelity and proof review

A text comparison of each theorem header through the final conclusion (before `:=`) against the current signature file returns `True` for both `param_cauchy` and `taylor_cutoff`. They also match the design Appendix A. Fresh-name probes use exactly those design binders and `by exact param_cauchy htp ht hM hu hb hj` / `by exact taylor_cutoff hr hs hM hq hq1 hB hF hb`; no new hypotheses are inserted. The same probe also assigns each export to `type_of% @audit_<name>`. Provider/frozen-type and seal-body checks are inapplicable: neither file declares a provider and no frozen anchor is assigned to C3.

Parameter proof: for δ=(t−tp)/j, the closed ball of radius jδ about b lies strictly in E+t because the chosen real witness is at distance <tp. Each first-derivative estimate loses δ of radius. Induction applies to the actual fderiv map, whose holomorphy is derived, and `norm_iteratedFDeriv_fderiv` preserves the full multilinear operator norm. The resulting `M/δ^j` is exactly the specified j^j bound. This nested-ball proof replaces the blueprint's explicit auxiliary polydisc, without a polarization factor or changed premises. It handles full multilinear derivatives, not only diagonal directional derivatives.

Taylor proof: the complex line ζ↦φη(ζ)=φ(ζ•η) maps the entire closed disc of radius 1/q strictly into the open ball of radius s when ‖η‖<qs. Thus the helper's closed-disc hypothesis is genuinely supplied. `hasFPowerSeriesOnBall` gives the series of that function; `norm_cauchyPowerSeries_le` and the circle integral give Mq^k coefficient bounds. The first two coefficients are the actual value and derivative. The geometric tail from k=2 gives precisely Mq²/(1−q). The first-order bound on an open ball is obtained from every smaller closed-ball radius and a real inequality argument, not by assuming holomorphy at the boundary. The holomorphy and periodicity of the Taylor part are separately proved. The 2M estimate uses the full operator norm and ‖η‖<s, with no dimension factor.

No conclusion-shaped premise, assumed Cauchy estimate, supplied Taylor remainder, constant depending on extra data, or norm substitution was found. Unused hypotheses in the main signatures preserve the approved interface and do not conceal a missing premise.

The blueprint at p11a2:98 is vector-valued and also describes entire dependence on η and the refined pointwise `M(1+‖η‖/s)` bound; the accepted design at design:1198–1207 deliberately exports the scalar application and the four stated conclusions. This report certifies that exact interface, not every clause of the more general prose lemma. The operator bound implies the coordinate bound; the refined pointwise estimate follows from the same value/derivative estimates; entire η dependence follows from the affine formula on fixed strip/parameter slices. These are not separately exported here. Similarly the family version of parameter Cauchy is obtained by taking the b slice with fixed (θ,η), not by a separate family export.

## Definition classification and imports

There are **no new `def` / `abbrev` / `structure` declarations** in scope. Local `set` bindings denote the actual positive radius R=(1/q).toNNReal, the actual domain, and the actual derivative estimates. Positivity proves R=1/q in ℝ; no fallback is used.

Relevant inherited objects were inspected: `P11Vec n = Fin n → ℝ`, `P11CVec n = Fin n → ℂ`, the product `P11Family`, the true `domain_def`, pointwise `p11Bound`, local-periodic holomorphic `p11Admissible`, and the affine formula defining `p11Taylor`. `p11Taylor` uses totalized fderiv for arbitrary total F, but every theorem application here proves differentiability at the evaluated slice centre. Hence no derivative fallback supplies the result. No Euclidean-space carrier or norm instance is introduced.

The 40-module KAM import closure contains no `KAM.Provider.*` and no frozen theorem modules. Frozen imports are definitions only (including SEALED `KAM.actionNbhd`, `KAM.complexStrip`, `KAM.Planetary.Phase`), so there is no imported `DRAFT_SORRY` theorem. Main-export axiom checks independently test the actual dependency closure.

## Independent validation receipts

All Lean/Lake commands below run serially with `LEAN_NUM_THREADS=1` and `nice -n 5`; no resource-budget overrides. The first Parameter gate request waited without acquiring a slot and was explicitly terminated (exit 143) solely to run the remaining checks first; it is not counted as a successful build.

### Exact-type probes and all public theorem axioms

Command (exit **0**):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AC3Audit.lean
```

The probe imports the two modules, re-declares both current design signatures under fresh names with the direct application bodies described above, checks `type_of%` assignments, and issues `#print axioms` for all 12 theorem names in the ledger. Exact output:

```text
'KAM.Planetary.p11_isOpen_actionNbhd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_norm_iteratedFDeriv_le_of_closedBall' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.param_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_series_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_norm_fderiv_le_of_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_taylor_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_mem_domain_def' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_isOpen_domain_def' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slice_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_fderiv_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_taylor_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.taylor_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

Command (exit **0**):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.MaximalStep.Parameter KAM.Planetary.MaximalStep.Taylor
```

Complete output:

```text
replaying KAM.Planetary.MaximalStep.Taylor
replaying KAM.Planetary.MaximalStep.Parameter
```

### Source lint and protected paths

Command (exit **1**, exclusively the brief-permitted generated-root exception):

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (553 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No additional forbidden-token, resource override, source-length, line-length, errata-rendering, module-system, provider-quarantine, frozen-file or ABI failure was reported. Both scoped files carry the required copyright, `module`, public imports, module docstring and public section. Direct scoped search for `sorry|admit|axiom|unsafe|opaque|EuclideanSpace|set_option` found no matches (rg exit 1).

Commands (both exit **0**, empty output):

```sh
git diff --check inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

### Targeted compile-gate builds

Parameter command (exit **0**; completed successfully, replayed current cached target):

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ac3 KAM.Planetary.MaximalStep.Parameter
```

Complete output (the linter's suggested option is tool output, not an option used by this audit):

```text
[inp-gate] slot 1 acquired 12:02:13 for KAM.Planetary.MaximalStep.Parameter
⚠ [9085/9085] Replayed KAM.Planetary.MaximalStep.Parameter
warning: KAM/Planetary/MaximalStep/Parameter.lean:76:5: Variable name `htp` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _htp

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: KAM/Planetary/MaximalStep/Parameter.lean:76:34: Variable name `hM` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hM

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (9085 jobs).
```

Taylor command (exit **0**):

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ac3 KAM.Planetary.MaximalStep.Taylor
```

Complete output:

```text
[inp-gate] slot 2 acquired 12:03:09 for KAM.Planetary.MaximalStep.Taylor
⚠ [9085/9085] Built KAM.Planetary.MaximalStep.Taylor (20s)
warning: KAM/Planetary/MaximalStep/Taylor.lean:226:45: Variable name `hr` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hr

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (9085 jobs).
```

Post-build repetition: the exact-design/axiom probe and the single-invocation two-module kernel replay each exited **0** again; their output is byte-identical to the complete receipts above.

Both targeted invocations used the mandated gate, which internally calls `nice -n 5 lake build`. They were run separately and never overlapped another audit Lean/Lake invocation. Parameter was a cached-target replay; Taylor was rebuilt successfully in 20 seconds. Independent exact-design elaboration, all axiom queries and kernel replay were repeated after that rebuild against the final artifacts. No library-wide build, clean, update, cache fetch or root regeneration was performed.

The custom scratch probe `.lake/abi-scratch/P11AC3Audit.lean` was deleted after validation. Final source hashes and protected-path diff were rechecked; the report and the pre-existing untracked handoff are the only paths in `git status --short`.

## Findings, deviations and limits

1. **Coverage note (not a false theorem):** handoff line 10 says “`bpP:p11a:x-cauchy`: covered by the iterated-ball lemma / Cauchy power series coefficient bound”. Blueprint `p11a2-cutoff-step.tex:32` states the general vector open-disc coefficient expansion and arbitrary mixed-polydisc estimate, and design:246 maps that external node to a Cauchy helper. The present code proves the needed special case locally and bypasses the multivariable route for parameter derivatives. Record this as application coverage / route substitution; a full external-node PROVED label would require an actual general export or an explicit permitted bypass. This does not weaken either accepted design signature.
2. **Declared proof-route deviation:** Parameter:16–20 explicitly replaces polydisc parametrisation (`pc-poly`, `pc-iter`; blueprint:143–145 and D-13 at :308) with nested closed-ball iteration. The same exact bound and full norm are obtained. The handoff's blanket “deviations: None” should distinguish this benign implementation change from a source-statement deviation.
3. **No suspected pinned-paper erratum or false frozen/blueprint statement found in this scope.** The source mathematics used here is the blueprint's “Ours” Cauchy/Taylor infrastructure; no new claim about Rus01's pinned printed theorem was needed. No frozen declaration required repair. The previously recorded Taylor algebraic-cutoff deviation D-5 is inherited, not introduced by this package or this audit.
4. This is a scoped proof-package audit. It does not close P11A, P-FIXED, the graph, or the complete vector/entire/mixed-polydisc interfaces. No changes were made to source, design, graph, provider, manifest or frozen files.
