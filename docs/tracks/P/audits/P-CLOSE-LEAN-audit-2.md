# P-CLOSE-LEAN independent audit 2

Overall: **PASS WITH NOTES; all five requested nodes PROVED.** The round-2 additions discharge both literal statement gaps identified in audit 1. The remaining note is an incorrect rho identification in the unchanged round-1 documentation, not a missing Lean conclusion in the new slow-data export.

Audited HEAD `ab97aa89aae983a1d3301c65f37de44d6ea1d508`, against `inp` `be4b40d5c5dd5b0ab472f8cc508e2600eee53ce4`. Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the local handoff including ROUND 2 FOCUS, audit 1, the five local DEPGRAPH records, blueprint P parts 14a/14b and relevant frozen definitions, and docs/tracks/P/statement.md. The latter is historical draft material; the graph and approved frozen definitions control this comparison. The report destination follows the user's exact absolute path, overriding the generic brief's main-worktree instruction.

Production audit scope is the diffs of `KAM/Planetary/AMD/Geometry.lean` and `KAM/Planetary/SecularBox/Covariance.lean`. The full `git diff inp...HEAD` was inspected: it adds four theorems in those files, two handoff documents, and audit 1. No provider or frozen anchor changes, so provider/frozen type equality and seal-body probes are inapplicable. No new per-anchor sealing claim is made.

## Node verdicts

All declaration names below have prefix `KAM.Planetary`. Comparison preserves quantifier dependencies and literal mathematical clauses, allowing independent conjunctions to be regrouped. No existential constant gains a wider dependence.

| Node | Declaration and locator | Verdict | Comparison with SOURCE_HYPOTHESES / SOURCE_CONCLUSION |
|---|---|---|---|
| `bpP:p14:geometry` | `geometry_complete`, `KAM/Planetary/AMD/Geometry.lean:260–289` | **PROVED** | From admissible B and z in `amdOuter B`, one declaration states the axis/eccentricity bounds, exact a(1±e) radial inequalities and d/R bounds, ordered-radius separation, `NoCollision`, momentum bound, membership in K1, compactness of K1, K1 contained in W, and all three inequalities of the pair-distance chain. These cover DEPGRAPH:33822–33825 and blueprint p14a:75–83. The additional barycentric `PairBounds` for every mu strengthens the conclusion without a mu premise. |
| `stepP:p14:geo-b` | `geometry_radial`, Geometry:176–199; also first conjunct of `geometry_complete`, :262–267 | **PROVED** | Both radial inequalities and d/R bounds are explicit for each i. The content is now a literal conjunct of the complete proved parent, so ruling (b) applies. Item (a) is derived from the enclosing source data, not added as a conclusion-shaped hypothesis. Round-1 PROVED stands. |
| `bpP:p14:sb-cov` | `sb_cov_full`, `KAM/Planetary/SecularBox/Covariance.lean:125–144` | **PROVED** | One declaration explicitly states Gamma, k and a invariance, v covariance, x and J shifts, and q/p covariance for every i,F. Binders are m,w,theta followed by i,F, with no changed dependence. The absence of ellipticity and mass-positivity premises is a valid strengthening: the identities preserve scalar inputs and hold on the whole carrier. The extra Gamma/Lambda equality is true and harmless for this parent, whose SOURCE_CONCLUSION does not mention rho. Unchanged since audit 1. |
| `stepP:p14:sb-cv-1` | `sb_cov_slow_data`, Covariance:148–159 | **PROVED** | The complete Gamma,k,rho,a,v conjunction is explicit for every i, using exactly `Real.sqrt ((1 - secularGamma w i / (2 * fast w.2 i)) / fast w.2 i)` for rho. This matches blueprint p14b:27,170 and the frozen eccentricity-vector factor. No extra premise is introduced. This is a direct public proof of the step; it is still not a literal conjunct of `sb_cov_full`, so this row does not invoke ruling (b) for that parent. The round-2 focus expressly permits checking the separate slow-data export. |
| `stepP:p14:sb-cv-2` | `sb_cov_full` second conjunct, Covariance:132–134 | **PROVED** | x and J shifts remain literal conjuncts of the proved parent for every i,F; only projections are needed, as confirmed by a fresh probe. Ruling (b) applies. Round-1 PROVED stands. |

For geometry, `amdOuter B` is the literal `LowAMDRegion` wrapper and `amdCompact B` is exactly the source's K1, with non-strict radial, momentum and pair-distance inequalities (`AMD/Setting.lean:31–41`). `collisionFreeDomain n` is `{z | NoCollision z.1}` (`Newtonian/Models.lean:39`). Universal pointwise membership is the source inclusion `R_out ⊆ K1`; a fresh Lean probe established that inclusion by introducing z,hz and projecting from `geometry_complete`, without calling another geometry result. Compactness and K1 containment are explicit conjuncts of the same declaration. The implicit n,z binders retain the source dependency, and the theorem is stronger by allowing all n rather than requiring n≥2. The original axis notation `(l/m)^2` is the same as l²/m².

## Definition and proof classification

There are **no new definitions, abbreviations, structures, instances or bundled hypotheses** in either diff. The existing `secularRotation` uses `assemble` to preserve both fast blocks and rotate each slow pair, with no selected solution or fallback. Physical lengths are `planeLength`, the Euclidean length of a physical two-vector, not the ambient Pi norm. The frozen `secularRoot`, `secularAxis`, `secularEccVector`, `longitudeJacobian`, `ellipsePosition`, and `ellipseMomentum` agree with the blueprint formulas. The covariance extensions to totalized division/sqrt are algebraic identities, not claims of elliptic geometry outside the elliptic domain; no junk branch supplies a hard result.

`geometry_radial` projects radial estimates from `elements` and bounds from `geometry`. `geometry_complete` combines this genuine result with `amd_compact`, projects the existing lower pair-distance bound, applies the plane triangle inequality for the middle bound, and adds the two radius bounds for the last inequality. `sb_cov_full` uses `sb_cov` and private invariance identities. `sb_cov_slow_data` rewrites Gamma and fast-action invariance inside the actual square-root expression; its other conjuncts are the established root, axis and vector identities. No hard step is assumed in a premise.

A fresh source-import traversal found 65 KAM modules in the combined closure, zero provider modules and zero frozen theorem modules. Thus no DRAFT_SORRY theorem or quarantined provider is imported. Frozen definition integrity was independently checked by repository lint.

## Independent checks

All commands ran in `/root/code/KAM-inp-pcloselean`. Lean/Lake checks were serialized, each with `LEAN_NUM_THREADS=1` and `nice -n 5`; lint started after kernel replay exited because its ABI stage invokes Lean. No generated-root regeneration, clean, update, cache operation, state-changing git command, or source edit was performed.

1. Targeted compile gate:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-pcloselean KAM.Planetary.AMD.Geometry KAM.Planetary.SecularBox.Covariance
   ```

   Exit **0**. Relevant output:

   ```text
   [inp-gate] slot 2 acquired 16:28:48 for KAM.Planetary.AMD.Geometry KAM.Planetary.SecularBox.Covariance
   ⚠ [9098/9111] Replayed KAM.Kepler.Energy
   Build completed successfully (9111 jobs).
   ```

   The two inherited warnings are `KAM/Kepler/Energy.lean:106:35` and `:106:48`, for implicitly used bindings `hm` and `hκ`. Neither audited module emitted a warning. No heartbeat/resource override was introduced.

2. Fresh scratch probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/PcloseAudit2.lean
   ```

   Exit **0**. Independently elaborated explicit copies of all four complete exported types applied to their source binders, the global `amdOuter B ⊆ amdCompact B` projection, the compactness/containment/pair-chain conjunction, and the x/J projection. Exact axiom output for every new public theorem:

   ```text
   'KAM.Planetary.geometry_radial' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.geometry_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.sb_cov_full' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.sb_cov_slow_data' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay, one invocation:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.AMD.Geometry KAM.Planetary.SecularBox.Covariance
   ```

   Exit **0**, complete output:

   ```text
   replaying KAM.Planetary.SecularBox.Covariance
   replaying KAM.Planetary.AMD.Geometry
   ```

4. Repository lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **0**, complete output:

   ```text
   check_lean_modules: PASS (1339 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No stale-root exception or other lint exception was needed.

5. Source and diff checks:

   ```sh
   git diff inp...HEAD
   git diff inp -- KAM/Planetary/AMD/Geometry.lean KAM/Planetary/SecularBox/Covariance.lean
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   git diff --check inp...HEAD
   ```

   Protected-path diff is empty, exit **0**; whitespace check exits **0**. A Python check removed precisely the four added documentation/theorem blocks and reconstructed each `git show inp:<file>` **byte for byte**. Thus all previous declarations, types and proof bodies are unchanged. A separate check against the round-1 code confirms the two round-1 exports are unchanged. Geometry is 295 lines, maximum width 100 Unicode characters; Covariance is 163 lines, maximum width 99. Both retain copyright, `module`, public imports, module docstring and public section. Neither contains a forbidden sorry/admit/axiom/unsafe/opaque/native_decide/EuclideanSpace token or any `set_option`. A declaration-name scan across KAM and Mathlib found exactly one occurrence of each new short name: `geometry_radial`, `geometry_complete`, `sb_cov_full`, `sb_cov_slow_data`, at the locations above. No reused public short name was found.

## Notes, suspected errata and limitations

- **Stale incorrect rho documentation remains.** `KAM/Planetary/SecularBox/Covariance.lean:123` says “ρ = Γ/Λ”; the handoff at lines 12 and 19 repeats “rho = Gamma/Lambda”. Blueprint `p14b-secular-box.tex:27` and frozen `SecularEccVector.lean:42–44` instead define rho as the square root of `(1 - Gamma/(2 Lambda))/Lambda`. The quotient equality in `sb_cov_full` is true but names another scalar. Its comment still overstates its coverage of `sb-cv-1`. The new theorem at :148 explicitly proves the correct source rho equality, so this documentation defect no longer blocks the five node contracts. The round-2 handoff's “Uncertainties/errata/deviations: none” at :51 overlooks this retained defect. Reported, not silently repaired.
- **The slow-data proof is a separate export.** The correct rho clause has not been added to `sb_cov_full`; claim `sb-cv-1` via `sb_cov_slow_data`, not by projecting the old parent's type. The complete direct step export satisfies the round-2 delta focus without changing an existing statement.
- No suspected defect in a pinned external publication, blueprint formula, or frozen statement was found within the two-file scope. The geometry gap and slow-data statement gap from audit 1 are repaired; none remains unpaid for these five nodes. This audit does not certify other graph nodes, consumers, or a new campaign-level theorem.
- No deviation or production edit was introduced by the auditor. Only this report is retained; the audit-created scratch probe was deleted after verification.
