# P11A-W4 independent package audit 1

Verdict: **PASS WITH NOTES** for `bpP:p11a:scalar-sublevel` / `KAM.Planetary.scalar_sublevel`. No blocking proof, statement, premise or carrier defect found. This is an infrastructure-package verdict; W4 contains no provider or frozen anchor to seal and does not close P-FIXED.

## Scope and authority

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the supplied handoff, track P statement (especially P-FIXED), the W4 design row and proof registry, the scalar signature in Appendix A and `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`, and design audits 1–3 (in the main inp worktree's `docs/tracks/P/design/`). The latest design audit accepts the scalar signature; that acceptance was independently checked here against the actual proof.

Snapshot HEAD: `980e204384bfbfebdc210d7ccbb40cc5f56f25ad`; `inp`: `5991245cabc06e69ec900cb6006b45f72cc85eb0`; `inp-p11aw3`: `29ee305d65ecee1725af0c55fc65569f6b9ced34`.

`git diff inp...HEAD --stat` contains `DividedDifference.lean` (125 added lines, inherited W3) and `ScalarSublevel.lean` (360 added lines). `git diff inp-p11aw3...HEAD --stat` contains only `KAM/Planetary/WeakMeasure/ScalarSublevel.lean` (360 added lines). Per AUDIT FOCUS, the independent declaration audit covers only the latter; W3 is a dependency, included in kernel replay. The existing untracked handoff was preserved. Only this report is a persistent audit edit, at the user's explicit worktree path, overriding the generic brief's main-worktree destination.

ScalarSublevel SHA-256: `4282207f3e89ab400247d982e2dcf3126a0de879d076eb46d9eff16c28dbbe88`.
Delivered signatures SHA-256: `c31fda0b479f2dd0488b12e7f2daeda18f965eb316610df1c65f14012dfcb092`.

## Declaration and node ledger

All names below are in `KAM.Planetary`; line references are to `KAM/Planetary/WeakMeasure/ScalarSublevel.lean`.

| Node / responsibility | Declaration / locator | Verdict | Reason |
|---|---|---|---|
| ss-phi / distribution | `p11Phi`, L32 | PASS | Actual real-valued distribution, with finite-measure guards where required; see definition classification. |
| ss-phi / interval split | `p11Phi_add`, L34 | PASS | Exact disjoint split at s; compact E supplies measurability and finite mass. |
| ss-phi / interval measure | `p11_measure_Ioc_le`, L59 | PASS | Subset bound by t−s, for arbitrary E; no measurability assumption needed for this upper bound. |
| ss-phi / monotonicity | `p11Phi_mono`, L67 | PASS | Compact E, s≤t; derived from nonnegative increment. |
| ss-phi / increment bound | `p11Phi_sub_le`, L71 | PASS | Distribution increment ≤ t−s; the needed Lipschitz estimate. |
| ss-phi / continuity | `p11Phi_continuous`, L76 | PASS | Constructs `LipschitzWith 1` internally and deduces continuity on ℝ. |
| ss-phi / plateau | `p11Phi_of_lt_inf`, L88 | PASS | An empty E∩(s,t] forces equal levels; stronger general compact-set helper. |
| ss-phi / total mass | `p11Phi_top`, L93 | PASS | E⊆[a,b] gives exact mass at b, without extra premises. |
| ss-phi / zero mass | `p11Phi_bot`, L99 | PASS | E⊆[a,∞) implies E∩(−∞,a]⊆{a}, a null set. |
| ss-gaps / factorial core | `p11_prod_range_dist`, L106 | PASS | Exact natural product; includes q=0. Condition i≤q is indexing data. |
| ss-gaps / factorial identity | `p11_prod_erase_nat`, L128 | PASS | Exact real absolute-gap product i!(q−i)! on Fin(q+1), including endpoints. |
| ss-nodes / positive levels | `p11_exists_node`, L156 | PASS WITH NOTES | Every c∈(0,vol E] attained at a point of E. IVT followed by maximum of E∩(−∞,s]; valid alternative construction, not a minimum-quantile identity. |
| ss-nodes / zero level | `p11_exists_node_zero`, L189 | PASS | Compactness and nonemptiness supply min E; singleton-null calculation gives level zero. |
| ss-gaps / lower product | `p11_gap_prod`, L198 | PASS | Exact i!(q−i)!(L/q)^q bound from explicit pairwise gaps. Gap premise belongs to this distinct helper and is proved before use in the main result. |
| ss-dd / combinatorics | `p11_sum_inv_factorial`, L229 | PASS | Exact sum 2^q/q!, proved via binomial coefficients; valid for q=0 too. |
| scalar-sublevel | `scalar_sublevel`, L249 | PASS | Type byte-for-byte identical to delivered signature; constant, measure, carrier, quantifiers and open-interior derivative premise preserved. |
| ss-nodes / assembled nodes | main proof L275–309 (`hnode`, `hlt`, `hgap`) | PASS WITH NOTES | Supplies tᵢ∈E, levels iL/q, strict ordering and all pairwise gaps; no minimality claim. |
| ss-dd / divided difference and root | main proof L312–358 | PASS | W3 witness lies in (a,b); β≤q!|S|, exact sum bound, factorial cancellation and positive q-th-root argument give the advertised 2q constant. |

The main theorem assumes only q≥1, a<b, positive β and ε, C^q regularity on [a,b], and the derivative lower bound on (a,b). No conclusion-shaped premise, typeclass assumption or bundled field supplies the sublevel estimate. `p11_gap_prod` is a genuine conditional helper, never substituted for the main theorem. Compactness of E, finite mass, nodes and all gaps are proved in the main body. Zero mass is treated before any division by L. Positive L gives nonempty E, positive L/q and strictly positive denominator products. The final root uses q≥1 and nonnegative RHS.

Blueprint p11a1 L94 states the derivative bound on [a,b]; the accepted design and implementation use only (a,b), a strictly stronger theorem because the divided-difference witness is interior. The original closed-interval premise restricts immediately to this premise. No endpoint derivative value is used.

## Definition classification

The only new definition is exposed `p11Phi E t := (volume (E ∩ Iic t)).toReal`. On arbitrary E this is literally ENNReal.toReal of the measure; infinite mass is totalized to zero by the library definition. It therefore must not be interpreted as an ordinary real distribution for infinite-measure E. Every monotonicity, additivity, continuity and node theorem here assumes compact E, so mass is finite. The endpoint lemmas either identify the same expression or prove a singleton-null bound. The arbitrary-E interval increment bound is bounded by a finite interval. No theorem relies on the infinite-mass fallback. For E⊆[a,b], this distribution agrees with the blueprint's `vol(E∩[a,t])`. No new structure, abbrev, default choice object or hidden analytic input exists.

## Notes, deviations and suspected defects

1. **Minor documentation defect:** ScalarSublevel L18 says “`p11Phi_dist_le`”, but no such declaration exists in the module. The actual increment bound is `p11Phi_sub_le` (L71), and the full Lipschitz proof is local to `p11Phi_continuous` (L76–86). Correct the prose locator when convenient; the proof does not depend on the missing name.
2. **Construction deviation:** blueprint `p11a1-weak-measure.tex` L101 and design registry L474 specify “t_i = min{t: phi(t) >= iL/q}”. W4 instead proves existence of a level point in E by IVT and compact maximum. It does not export or prove that the chosen positive-level node is that minimum. All properties used in ss-gaps, ss-dd and scalar-sublevel are derived, so this is an acceptable proof-route variation, not a weakened scalar statement. The handoff's “Deviations: none” should be read with this qualification.
3. **Stronger premise range:** the interior-only lower bound is the accepted design strengthening of the blueprint's closed-interval bound, as explained above.

No suspected mathematical blueprint/source defect was found in the audited scalar argument. The blueprint already declares its elementary proof and 2q constant as deviation D1 from Rus01's Bakhtin-based estimate; W4 follows that declared route. No independent re-audit of the external Rus01 PDF or W3's package verdict is claimed. No frozen declaration is changed or shown defective.

## Independent validation

All audit-owned Lean/Lake commands ran serially, with `LEAN_NUM_THREADS=1`, `nice -n 5`, and default proof resource limits. No clean, update, cache fetch, root regeneration, provider sealing or source repair was run.

Build command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11aw4 KAM.Planetary.WeakMeasure.ScalarSublevel
```

Exit 0. Output:

```text
[inp-gate] slot 1 acquired 09:22:28 for KAM.Planetary.WeakMeasure.ScalarSublevel
⚠ [9047/9048] Replayed KAM.Planetary.WeakMeasure.DividedDifference
warning: KAM/Planetary/WeakMeasure/DividedDifference.lean:96:59: Variable name `hab` is not explicitly referenced.
Build completed successfully (9048 jobs).
```

The remaining warning text is Lean's standard unused-variable hint. No W4 warning or default-heartbeat failure occurred; job count includes cached/replayed dependencies, not a clean rebuild.

Signature and axiom probe command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AW4Audit.lean
```

Exit 0. Probe imported only the built scalar module, copied the delivered scalar signature into an `example` with body `KAM.Planetary.scalar_sublevel hq hab hbeta heps hf hlow`, and printed axioms for all 15 new public theorems. A separate literal signature-text comparison returned `True`. Provider/frozen-type and seal-body probes are inapplicable: W4 introduces no provider or anchor. This signature probe checks the applicable package interface directly.

Axiom output:

```text
'KAM.Planetary.p11Phi_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_measure_Ioc_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Phi_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Phi_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Phi_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Phi_of_lt_inf' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Phi_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Phi_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prod_range_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prod_erase_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_exists_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_exists_node_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_gap_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_sum_inv_factorial' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.scalar_sublevel' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakMeasure.ScalarSublevel KAM.Planetary.WeakMeasure.DividedDifference
```

Exit 0. Exact output:

```text
replaying KAM.Planetary.WeakMeasure.DividedDifference
replaying KAM.Planetary.WeakMeasure.ScalarSublevel
```

Static checks: the W4 file has 360 lines (maximum line length 100 Unicode characters), module header, copyright, public imports, module docstring and exposed public noncomputable section. No forbidden proof escape, resource override or EuclideanSpace occurrence was found in W4 or its W3 import. W4 imports only Mathlib and DividedDifference; W3 imports only Mathlib modules. Thus no provider, DRAFT_SORRY or other frozen theorem is in this package's project import closure, and no imported frozen-module manifest-state check is needed. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. `git diff --check inp...HEAD` and `git diff --check` both exited 0 without output.

Final lint command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the explicitly permitted stale generated root. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (509 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No line-length, forbidden-token, oversized-file or errata-rendering error was emitted. The generated root was not edited. The lint exception is allowed by the current audit brief, rather than inferred from past audits.

Closeout: all 15 theorem axiom checks, delivered-signature elaboration, targeted gated build, kernel replay, protected-path comparison and whitespace checks passed; lint has only its authorized generated-root exception. The temporary `.lake/abi-scratch/P11AW4Audit.lean` was deleted. Final working-tree additions are this report and the pre-existing handoff only. No production source was changed. Remaining uncertainty is limited to downstream packages and external-source obligations outside W4; no unpaid inequality remains in this scalar proof. Overall **PASS WITH NOTES**, with the two minor documentation/construction qualifications above.
