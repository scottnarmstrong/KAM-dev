# N12-18 independent package audit 1

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-n1218`.
HEAD: `0e80171b03a52873bb4fe1eb6d86a0b127e1ceaa`.
Comparison ref `inp` at inspection: `31f0bfbf70c07b1eefd006237f331c00e003a0e5`.

## Verdict

| Frozen anchor | Verdict | Seal readiness |
|---|---|---|
| `KAM.Nekhoroshev.averaging_mean` | **PASS WITH NOTES** | Provider is seal-ready; exact-type and prospective-seal probes, build, allowed axioms and kernel replay passed. |
| `KAM.Nekhoroshev.averaging_most` | **PASS WITH NOTES** | Provider is seal-ready on the same evidence. |

No blocking mathematical, statement, import or kernel defect was found. Notes concern inherited documentation/scope and the explicitly permitted stale generated root. Both existing frozen anchors remain unsealed.

The destination explicitly required by the user overrides the common brief's main-worktree destination. No production source, frozen file, manifest, generated root or README was edited. This report is the only repository artifact added by the auditor; transient probes and verification logs are confined to `.lake/abi-scratch/` and removed at closeout. No delegation or state-changing git commands.

## Scope and authority

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the N12-18 handoff and AUDIT FOCUS, design row N12-18, section 7 and Appendix A of `docs/tracks/N/design/N12-LEAN-DESIGN.md`, the track-N statement, blueprint Part 0 lines 370–406 and Part 12's final assemblies, both frozen anchors and their frozen definitions, and the concrete core/flow/good-set interfaces.

`git diff inp...HEAD` contains three Lean files: `Mean.lean` (169 added lines), provider `AveragingMean.lean` (39 added lines; 54 total), provider `AveragingMost.lean` (37 added lines; 52 total). The handoff's “Nothing else” at line 4 describes `git diff HEAD^ HEAD` correctly, but not the requested full comparison: N12-16's `Mean.lean` also enters through the merged history. Accordingly, both of its new public helpers and its private helper were independently reviewed here. `Most.lean` is a dependency already present in the comparison baseline; its core signature and use were checked as well.

Both manifest entries (`nekhoroshev.d28.averaging_mean.v1`, `nekhoroshev.d28.averaging_most.v1`) remain `DRAFT_SORRY`, with D28 owner approval and the expected provider module/export. This audit tests the provider proofs and proposed seals; the existing frozen exports themselves are not claimed sorry-free or sealed.

## Declaration and node ledger

| Node / obligation | Lean declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| `bpN:p0:avg-mean`, N12-18 | `KAM.Provider.Nekhoroshev.averaging_mean` (`AveragingMean.lean:28`) | PASS | Frozen telescope and conclusion are byte-identical. Exact-type and explicit-binder seal probes elaborate. Picks core A and ε₀=1 after all fixed inputs. |
| `bpN:p0:avg-most`, N12-18 | `KAM.Provider.Nekhoroshev.averaging_most` (`AveragingMost.lean:28`) | PASS | Same literal signature and probe checks. Picks core A, ε₀=1, η₀=R/8; hR proves positivity and η₀≤R/4. Actual full-window solution remains a conclusion. |
| `stepN:p12:me-flow`, `me-cont` | `KAM.Nekhoroshev.mean_family` (`Mean.lean:44`) | PASS | Exactly the design Appendix A signature. Genuine supplied solutions agree with the maximal flow by maximality/uniqueness; K lies in its existence set. Continuity on K and compact integrability are derived, with no measurability or continuity premise on Φ. Works already for n≥1 and every ε>0, as designed. |
| `stepN:p12:me-good`, `me-bad`, `me-mean`, `me-markov`; `bpN:p12:s-mean#data` | `KAM.Nekhoroshev.averaging_mean_core` (`Mean.lean:88`) | PASS | Exactly the design Appendix A signature. Chooses A=13 A₁ before ε, Φ, κ. Bounds the maximum pointwise by 13 Ψ, then integrates; Markov set is measurable, contained in K, and has absolute volume ≤κ. |
| Internal identification | private `averagingError_eq_flow` (`Mean.lean:33`) | PASS | Equality of images under pointwise equality on the same time interval. No additional substantive assumption; not a public blueprint export. |
| N12-17 dependency / `stepN:p12:mo-E`, `mo-z` | `KAM.Nekhoroshev.averaging_most_core` (`Most.lean:31`) | PASS (consumer check) | Core accepts precisely AveragingData, compactness and inner action membership. E is K minus the actual-flow good set; existence and the pointwise drift conclusion are retained. Included in axiom and kernel checks. |

All listed provider/implementation declarations preserve the max-norm carriers `(Fin n → ℝ) × (Fin n → ℝ)`, complex counterparts, absolute product Lebesgue volume, the frozen Hamiltonian, time interval `[0,1/ε]`, and the source rank disjunction. No conclusion-shaped premise, enlarged constant dependence or weakened frozen conclusion was found.

## Provider premises and proposed seals

For each provider, `AveragingData n R s h f` has exactly six fields: `1≤n`, `0<R`, `0<s`, `IsAnalyticIntegrable R s h`, `IsAnalyticPerturbation R s 1 f`, and the frozen rank condition. The first is derived by `omega` from frozen `hn : 2≤n`; the other five are supplied unchanged. `K`, `hK`, and `hKI` pass directly. No core estimate, flow, future confinement or exceptional set is assumed.

`AvgPhase` and `AvgComplexPhase` are literal carrier abbreviations. `avgH h f ε` unfolds to `KAM.realHamiltonian h (fun w => (ε : ℂ) * f w)`. The mean core is used at ε≤1 with the supplied family premise unchanged; the most core at η≤R/8. Constants are selected before ε, Φ, κ or η, in the frozen order.

An exact source-text comparison of each provider telescope/conclusion (from `theorem ...` through the text before `:=`) with its frozen anchor returned:

```text
mean: binder/conclusion source text is byte-identical
most: binder/conclusion source text is byte-identical
```

The transient probe imported both frozen theorem modules and both providers, then elaborated:

```lean
example : type_of% @KAM.Nekhoroshev.averaging_mean :=
  @KAM.Provider.Nekhoroshev.averaging_mean
example : type_of% @KAM.Nekhoroshev.averaging_most :=
  @KAM.Provider.Nekhoroshev.averaging_most
```

It also copied each complete frozen telescope and conclusion under fresh names `audit_seal_mean` / `audit_seal_most`, replacing only the proof with:

```lean
by exact KAM.Provider.Nekhoroshev.averaging_mean hn R s hR hs h f hh hf hrank K hK hKI
by exact KAM.Provider.Nekhoroshev.averaging_most hn R s hR hs h f hh hf hrank K hK hKI
```

These supply exactly all thirteen explicit binders, in order; n remains implicit. The source text and successful probes jointly check binder order, implicitness and constant scope, without casts or added hypotheses. The probe's imports of draft anchors are confined to audit scratch; neither provider imports an anchor.

## Definition classification and totality

No new `def`, `abbrev` or `structure` occurs in the three-file comparison. The local `d` values are transparent proof bundles of source premises, not new mathematical objects or assumed proof steps.

Reviewed consumed definitions:

- `AveragingData`: source-only proposition bundle, with all fields discharged as above. `AvgPhase`, `AvgComplexPhase`, `avgDomain`, `avgH`: intended literal carriers, product domain and Hamiltonian.
- Frozen `averagingError`: real supremum, deliberately total outside its guarded locus. Here ε>0 makes the time interval nonempty (contains zero); actual actions in B(R) and initial actions in B(R/2) give an upper bound 3R/2. `mean_family` explicitly proves boundedness, nonnegativity and every pointwise displacement≤supremum. There is no reliance on an empty/unbounded supremum fallback.
- `avgMaximal` / `avgFlow`: inherited chosen maximal solution with a default branch outside the existence locus. `avgMaximal_spec` proves existence from the analytic data for x in the domain. Mean's inner action membership and Most's good-set membership discharge that guard. Every used time lies in the actual solution interval; arbitrary extensions/defaults are not used to prove dynamics or drift.
- `avgGood`: K membership, genuine existence through the terminal time, and strict supremum threshold. Most uses its measurability and actual maximal solution, not a surrogate family. The closed time interval lies in the maximal open interval, retaining two-sided endpoint derivatives in frozen `IsSolutionOn`.
- `avgStopped` / `avgStoppedExt`: inherited ENNReal stopped majorant and measurable extension, not definitions of the desired answer. `bad` supplies the integral, threshold and good-data pointwise bounds from the analytic/rank data. Core uses are on the guarded inner-action set.
- Mean's local E is `{x ∈ K | A*sqrt ε/κ < averagingError ε Φ x}`. Continuity on K yields its measurable subtype image. Positivity of A, ε and κ guards cancellation; ENNReal.ofReal of the threshold is nonzero and finite. The bound is on unnormalized volume. Values of Φ away from K are immaterial.

Mean's integral proof differs harmlessly from the blueprint's split-integral presentation: it proves `ofReal(m(x)) ≤ 13*Ψ(x)` pointwise. On good data m≤Ψ, and on bad data m≤3R/2=12(R/8)≤12Ψ. Integrating yields exactly the prescribed 13 A₁ constant. It never interchanges a time supremum and an integral.

## Independent check receipts

All Lean-related commands were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`; the build used the prescribed gate. No clean, cache, update, generated-root regeneration or heartbeat override was used.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1218 KAM.Provider.Nekhoroshev.AveragingMean KAM.Provider.Nekhoroshev.AveragingMost
   [inp-gate] slot 2 acquired 12:54:00 for KAM.Provider.Nekhoroshev.AveragingMean KAM.Provider.Nekhoroshev.AveragingMost
   Build completed successfully (3251 jobs).
   ```

   Exit 0. The gate executes `nice -n 5 lake build` on those targets. Replayed dependency warnings concern unused variables and deprecated names; no sorry warning or scoped-file elaboration failure. No default-heartbeat design signal.

2. Exact-type, prospective-seal and axiom probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N1218Audit.lean
   'KAM.Provider.Nekhoroshev.averaging_mean' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Provider.Nekhoroshev.averaging_most' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.mean_family' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.averaging_mean_core' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.averaging_most_core' depends on axioms: [propext, Classical.choice, Quot.sound]
   'audit_seal_mean' depends on axioms: [propext, Classical.choice, Quot.sound]
   'audit_seal_most' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   Exit 0. Every new public theorem is covered. No `sorryAx` or additional axiom in these proofs or their used proof dependencies.

3. Kernel replay (one invocation):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Provider.Nekhoroshev.AveragingMean KAM.Provider.Nekhoroshev.AveragingMost KAM.Nekhoroshev.Averaging.Mean KAM.Nekhoroshev.Averaging.Most
   replaying KAM.Nekhoroshev.Averaging.Most
   replaying KAM.Nekhoroshev.Averaging.Mean
   replaying KAM.Provider.Nekhoroshev.AveragingMost
   replaying KAM.Provider.Nekhoroshev.AveragingMean
   ```

   Exit 0.

4. Frozen-anchor guard:

   ```text
   python3 -I scripts/check_frozen_anchors.py --root /root/code/KAM-inp-n1218 --manifest /root/code/KAM-inp-n1218/manifest/frozen-anchors.json
   FROZEN-ANCHOR GUARD OK
   ```

   Exit 0.

5. Source lint and ABI:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (655 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   Exit 1 solely for the expected stale `KAM.lean` warning, expressly permitted by the audit brief. Module checks, frozen guard and all frozen ABI hashes pass. No root regeneration performed.

6. Static and integrity checks:

   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no output, exit 0. `git diff --check inp...HEAD` produced no output, exit 0. The two provider modules are imported only by their respective frozen anchors (verified by repository search and the guard). A recursive import scan found 93 local modules in the combined provider closure, with **zero frozen theorem modules and zero other providers**. Source-token review found no proof escape or resource-budget override in that closure; the only encountered `set_option`s are inherited unused-section-variable linter settings. The three changed files satisfy the module header, copyright, public imports, module docstring and public-section requirements; line counts are 169, 54 and 52. No new definitions require exposure.

   Reviewed source SHA-256:

   ```text
   5feb7c2cfbeef99dbc9842d9ceb0c6162aa16593595bcc9891f450007a4c066a  KAM/Nekhoroshev/Averaging/Mean.lean
   123f7b18e41c45d98c0d7742dfc8be4cac1bf983174f183ce66465bf0f912bc1  KAM/Provider/Nekhoroshev/AveragingMean.lean
   086064c46b3b79f5d3f1d06ac9f67422cf9d156588cc599dab6dce811740a082  KAM/Provider/Nekhoroshev/AveragingMost.lean
   ```

## Notes, suspected defects and deviations

- **Handoff scope note:** `docs/tracks/N/audits/N12-18-handoff.md:4`, “Nothing else”: true for the provider commit, not for the full requested branch comparison. The additional Mean module was audited above; no proof defect found.
- **Stale status:** `docs/tracks/N/statement.md:341`, “unapproved v0.5 candidates for a new independent audit”, predates D28 and the approved frozen/manifest entries. This is documentation drift, not a changed mathematical hypothesis or an approval gap.
- **Collar-route note:** `docs/tracks/N/statement.md:403–406` gives the example “η₀≤R/32” for a literal application of the printed Neishtadt collar restriction. The actual blueprint (`p0-conventions.tex:405`, `p12-averaging.tex:250`) explicitly uses its direct stopped proof with η₀=R/8; this is permitted by the frozen η₀≤R/4 and the core proves this endpoint. No silent strengthening or source-theorem application at an invalid collar occurs in the providers.
- **Inherited source defect, not newly discovered:** `blueprint-N/parts/p12-averaging.tex:298` records Nei76 p.1298 (17), quoted there as `sup_t z(t)=∫_{U'} h`, with h the time maximum. Generally only `sup_t ∫ ≤ ∫ sup_t` holds: on two unit atoms, errors t and 1−t on [0,1] give 1 versus 2. This is already ledger issue E-NAVG-NEI-17. The present proof bounds the maximum first and then integrates. The pinned PDF was not re-audited in this provider audit; this note reports the existing documented defect and checks that the Lean assembly does not use the invalid exchange.

No new suspected pinned-source or frozen-statement defect, no extra premise, and no production deviation introduced by this auditor. The integration step of actually sealing the two anchors remains with the orchestrator.

Closeout: all checks completed. The transient probe and its verification logs were deleted. Source hashes were rechecked unchanged; `git diff --check inp...HEAD` and the new report whitespace check pass. Git status contains only this new report and the pre-existing untracked N12-18 handoff. No unresolved check or blocking uncertainty remains for the two scoped provider seals.
