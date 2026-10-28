# N89-P5 independent audit 1

Overall verdict: **PASS WITH NOTES**. Target: `KAM.Nekhoroshev.thm1`, an internal Part-9 theorem for Part 10. Frozen-anchor verdict: **not applicable**; this package does not seal N-HEAD-C or any other anchor.

## Scope and authority

Audited HEAD `bd8304e28369b0b274afd4d361a6313ec5c5ef87` in `/root/code/KAM-inp-n89p5`. Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, the untracked N89-P5 handoff including AUDIT FOCUS, track-N statements, N89 design and both design audits, blueprint Part 9, and the consumed production interfaces. Only this report is a repository edit; audit probes use `.lake/abi-scratch/` and are removed after use.

The requested `git diff inp...HEAD` reports multiple merge bases, choosing `1b99fed967f7fa5a58d12207eb13d2a077f31e5e` (the other is `20c6eb074acfab86dc6f5b775479030b75c2a625`). Its broad delta contains 166 files, including 98 additions to generated KAM.lean. The protected-path command is therefore **not empty**: `git diff inp...HEAD --numstat -- KAM/Frozen manifest KAM.lean README.md` prints `98 0 KAM.lean`; frozen files, manifest and README have no delta. This is inherited integration history, not a P5 edit. Even `inp-n89p4...HEAD` has inherited integration differences. The handoff's explicit scope governs: `git diff HEAD^ HEAD --stat` adds only the 207-line Theorem1.lean, and `git diff HEAD^ HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. No generated file was repaired.

The local `.drafts/design/N89Signatures.lean` is absent. Read the supplied original at `/root/code/KAM-inp/.drafts/design/N89Signatures.lean` (read only), SHA-256 `01270a67c964001a1f6f86a2416ce572fee94f326c34cec43fcef7de0fea4b88`, agreeing with design audit 2 and design Appendix A. The text between `theorem thm1` and `:=` matches production **byte for byte**. The original's `sorry` body was never imported.

## Declaration and node review

Line numbers below refer to Theorem1.lean; blueprint authority is `blueprint-N/parts/p9-poschel-theorem1.tex:111–136` and design inventory rows for P5.

| Node / declaration | Lean implementation | Verdict | Reason |
|---|---|---|---|
| `bpN:p9:thm1` | `KAM.Nekhoroshev.thm1`, L74–201 | PASS | Exact joint signature; shared constants, arbitrary field extension, interval, genuine derivative, both norm-specific conclusions and strip membership retained. |
| `stepN:p9:t1-par` | `thm1`, L93–102 | PASS | Consumes elementary validity, K≥1, epsilon identity, reciprocal exponent; covering and full_rank_zone are applied with the intended parameters. |
| `stepN:p9:t1-b` | `thm1`, L196–201 | PASS | Strict low-frequency threshold gives membership of top block; admissibility is `Or.inl rfl`, valid for every time. Top≠bottom follows from n≥2; Euclidean block bound and top radius give r0/2. |
| `stepN:p9:t1-a-choice` | `thm1`, L104–127 | PASS | Covering gives a maximal block; full-rank iff contradicts ≥ threshold, excluding top, including equality at the boundary. Covering yields rΛ≤r0/(AK). |
| `stepN:p9:t1-a-theta` | private `time_bot`, L32–47; application L164–173 | PASS | From epsilon=m rb²/1024, A²rb≤r0 and mr0≤8Ω0, proves the exact multiplied admissibility inequality with coefficient 5. A²≤(AK)^n uses n≥2 and AK≥1. |
| `stepN:p9:t1-a-res` | private `time_mid`, L50–66; application L174–190 | PASS | volume≤K^d, d≥1 and A≥1 give rΛ≥A rb. The arithmetic proves the coefficient-288 admissibility inequality using the actual ΩΛ≤Ω0. No time lower bound is assumed. |
| `stepN:p9:t1-a-concl` | `thm1`, L128–163, L191–195 | PASS | Attained maximum comparison, exponent identity, both block-time cases, block_stab and reciprocal K identity produce the stated radius and time. |

There is exactly one new public theorem, `thm1`, and two private arithmetic theorems. Their premises are explicitly discharged at their callers; neither is a conclusion-shaped premise of thm1. The blueprint's separate P-nonempty hypothesis is redundant because hI exhibits an element of P. There is no changed constant dependence: A, epsilon0 and K use only their prescribed arguments; Ω0 is the frequency maximum on the prescribed ball, not an arbitrary upper bound.

The key maximum step is L132–139: `frequency_maximum (blockBall ...)` supplies an attained point Ib and `B.maximum = euclid (frequencyMap h Ib)`. Its ball membership gives distance≤rΛ/2; L124–127 proves rΛ/2≤r0/A. Applying omega0's all-point maximum inequality proves `B.maximum≤Om0`. No independent Omega is substituted. L129–131 derives Om0>0 from the branch hypothesis and positive m,r0 before denominator cancellation. The intermediate comparison uses multiplication-form blockAdm and never divides by ΩΛ, so it also avoids any fallback at zero.

The exponent identity L143–146 is literally πs K/(3√n) = 2π(K/√n)s/6. The final radius uses `(eps/epsilon0)^a=1/K`. Strip membership is a conclusion of block_stab, never an orbit-containment premise. The exceptional branch has no finite-time restriction.

## Definitions and imports

No new def, abbrev, structure, instance or function body occurs in the audited file. Definition classification: **none introduced**. Local lets I0, Om0 and B denote the initial action, actual omega0Ball maximum and actual blockBall respectively. The consumed FrequencyBall.maximum is a supremum on a guarded compact nonempty ball, with attainment proved by frequency_maximum; omega0Ball and blockBall have exactly the specified radii. Theorem1Setting contains the S1–S4 source assumptions and standing parameters, without orbit confinement or the theorem conclusion. Global derivatives are used on the analytically guarded domains.

The single direct public import is `KAM.Nekhoroshev.Poschel.BlockStability`, as designed. Recursively inspecting KAM imports gives 144 KAM modules, **no provider imports**, and 27 frozen definition modules; exact manifest-path matches are all **SEALED**. There are no imported frozen theorem modules, including no DRAFT_SORRY theorem. The ambient coordinate types are Fin-function types, with max norm for (a) and explicit euclid for (b).

## Verification receipts

1. Targeted build (exit **0**):

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n89p5 KAM.Nekhoroshev.Poschel.Theorem1
```

The gate invokes `nice -n 5 lake build`. Output includes:

```text
[inp-gate] slot 2 acquired 12:34:32 for KAM.Nekhoroshev.Poschel.Theorem1
Build completed successfully (3325 jobs).
```

Only inherited replay warnings occurred (unused variables/section variables in Gradient, Maximal, Blocks, BlockHypotheses, ODE.Exit, Transfer, Nonresonant, Resonant and ResonantStabilityCore). No warning or heartbeat failure in Theorem1.lean. No overrides were added.

2. Source lint: `LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh`, exit **1**, solely the explicitly allowed generated-root exception. Full diagnostic output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (651 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The final lint run's shell and guard were set to nice priority 5 before the ABI subprocess. An earlier lint attempt was terminated during the Python frozen guard and restarted with LEAN_NUM_THREADS=1; its partial output is not the receipt. Build completed before the ABI Lean invocation. Lean/Lake verification invocations were serialized.

3. Static checks: Theorem1.lean has 207 lines, the required copyright, module declaration, public import, module docstring and public section. Search for `sorry|admit|axiom|unsafe|opaque|EuclideanSpace|set_option` produces no matches. `git diff --check` exits **0**. All new definitions: none.

4. Exact-type and application probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N89P5Audit.lean
```

Exit **0**. The probe copied the complete original signature (including both let-expressions and conclusions) under `audit_thm1`, proved it by `exact thm1 S heps heps0 hfb hF hJ h0 hz hI`, and elaborated both `example : type_of% @thm1 := @audit_thm1` and its converse. Output:

```text
'KAM.Nekhoroshev.thm1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

An initial auditor probe incorrectly split the declaration at the first `:=` inside `let I0 :=`; it failed to parse. Correcting the extraction to the theorem-body delimiter yielded the successful probe above and a fresh complete-signature textual equality check (`True`). This was a scratch-generation error, not a package defect. Frozen-provider and frozen-seal probes are inapplicable because no frozen anchor or provider is implemented here; this probe exercises the analogous full internal contract.

5. Kernel replay (one invocation, exit **0**):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Poschel.Theorem1
```

Full output:

```text
replaying KAM.Nekhoroshev.Poschel.Theorem1
```

This is the only new module and contains all three new declarations, including the private arithmetic helpers. No additional lemma module belongs to P5. The temporary audit probe was deleted afterwards. Final `git diff --check` exits **0**; status contains only the pre-existing untracked handoff and the new audit report.

## Source/blueprint issues, limitations and disposition

No new suspected source or blueprint defect was found in this assembly. The declared adaptations already appear at `blueprint-N/parts/p9-poschel-theorem1.tex:146–150`: the source's quoted `r0≤4l/m` is strengthened to `r0≤ell/(2M)` for the full-rank stability route; the exponent loses sqrt(n) under the max/l1 norm adaptation; the exceptional branch uses strict `<` and radius r0/2. These are inherited documented changes, retained literally by S and thm1, not new deviations introduced by P5. This audit checks the package against the audited blueprint/design; it does not independently reopen the pinned PDF audit. No external web sources were used.

Nonblocking notes are the inherited generated-root divergence and stale root lint exception, the original scratch signature residing in the main inp worktree, and inherited replay warnings. The handoff's claimed clean lint result is not reproducible in the current checkout: the precise permitted exception is recorded above. The theorem is package-complete as an internal estimate; Part-10 application/existence assembly and frozen-root closure remain outside this audit. No premise, norm, maximum, branch, boundary threshold or consumer contract was silently repaired. No repository source, frozen object, manifest, generated root, README or git state was modified.
