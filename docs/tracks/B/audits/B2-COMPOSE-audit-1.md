# B2-COMPOSE independent package audit 1

Verdict: **PASS WITH NOTES** for B2-COMPOSE. No blocking mathematical or implementation defect found. There are **no frozen anchors or provider exports in this package**, so “seal-ready” is inapplicable; this verdict accepts ordinary composition infrastructure only. B1-E and B1-T remain unchanged ordinary theorems. Notes concern the precise scope of finite matching data and the distinction between canonical composition and quantitative remainder/displacement estimates.

## Revision and authority

Audited worktree: `/root/code/KAM-inp-b2comp`.
HEAD: `975b456399b3b4e418bafd1a258e293144f11ad3`.
Comparison ref `inp`: `cf4f25b6024d29837da39af09d1c0dfe5dcd8b0c`.
`git diff inp...HEAD` contains exactly `KAM/EffectiveStability/ChartChain.lean` (189 lines) and `docs/tracks/B/audits/B2-COMPOSE-handoff.md` (51 lines). Initial working tree was clean.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the prescribed `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the handoff/AUDIT FOCUS, `/root/code/KAM-inp-b1/.drafts/B/brief-B2-COMPOSE.md` and `brief-B1-common.md`, Track B SPEC and FREEZE-PROPOSAL, the unchanged B1 consumers, and program-b-plan §3.2, lines 341–420, at `/root/code/KAM/docs/explorations/program-b-plan.md`. Track B's explicit focus supersedes the generic I/N/P blueprint/anchor checklist: its requested statements are the seven items in the B2 brief; nothing B2-specific is frozen. The user's exact report destination overrides the generic brief's main-worktree destination.

## Declaration review

Names below are in `KAM.EffectiveStability`.

| Brief item / source | Declaration (ChartChain.lean line) | Verdict | Reason |
|---|---|---|---|
| 1: B1 chart premises | `IsCanonicalChart` (30) | PASS | Exactly openness, C² smoothness, MapsTo, derivative symplecticity, and left inverse. No trajectory, drift, or confinement premise. |
| 1: projections | `IsCanonicalChart.chart_open`, `.chart_smooth`, `.chart_maps`, `.chart_symp`, `.chart_leftInv` (34–39) | PASS | Ordinary structure projections of precisely those source premises. |
| 2: pair composition | `IsCanonicalChart.chart_comp` (43) | PASS | Inner chart first; `V₂ ⊆ D₁` gives the outer evaluation domain. Forward order Ψ₁∘Ψ₂, inverse order Ψ₂inv∘Ψ₁inv. |
| 3: identity | `IsCanonicalChart.id_chart` (67) | PASS | Identity on arbitrary open D, including empty D and dimension zero. |
| 3: monotonicity | `IsCanonicalChart.mono_chart` (72) | PASS | Restricts to open D′⊆D and enlarges V⊆V′. Explicit openness is necessary for this bundle. |
| 4: step data | `ChartStep` and `stepMap`, `stepInv`, `stepDom`, `stepTgt` (80–84) | PASS | Unconstrained map/inverse/domain/target data; canonical validity is supplied separately. |
| 4: forward fold | `chartChainMap` (87) | PASS | Empty identity; head map acts after inner tail. |
| 4: inverse fold | `chartChainInv` (92) | PASS | Empty identity; reverses forward order. |
| 4: output domain | `chartChainTarget` (97) | PASS | Empty chain targets D; nonempty chain targets the outermost step's target. |
| 4: matching data | `ChartChainOK` (104) | PASS WITH NOTES | Finite recursive conjunction of source premises and inclusions, ending in IsOpen D. These analytic predicates are not an executable decision procedure. |
| 4: finite composition | `chartChain_isCanonical` (111) | PASS | Induction applies pair composition with the correct inner-tail target inclusion. D may be any open subset of the innermost step domain. |
| 5: pullback transfer | `hamiltonian_comp_transfer` (118) | PASS | Uses two source identities at valid domain points, with MapsTo Ψ₂ D₂ D₁. No assumed composite identity. |
| 6: B1-E convenience | `oscillator_confinement_of_chart` (127) | PASS | Same non-chart binders and full B1-E conclusion; invokes the unchanged headline directly. |
| 6: B1-T convenience | `torus_confinement_of_chart` (158) | PASS | Same non-chart binders, including remainder periodicity, and full B1-T conclusion; invokes the unchanged headline directly. |
| 7: smoke test | `chart_id_comp_id` (185) | PASS | Applies pair composition to two identity charts with reflexive inclusion. |

### Mathematical checks and applicability

At lines 49–64 the proof first obtains MapsTo Ψ₂ D₂ D₁. C² regularity on the two open domains gives DifferentiableAt at w and Ψ₂ w, so `fderiv_comp` is used with valid hypotheses. The outer symplectic identity applies to DΨ₂u,DΨ₂v at Ψ₂w; the inner identity then gives the original form. The left-inverse calculation uses Ψ₁inv(Ψ₁(Ψ₂w))=Ψ₂w in D₁ before Ψ₂inv(Ψ₂w)=w in D₂. No inverse regularity or unproved right-inverse fact is smuggled in.

For `[a,b,c]`, definitional probes establish `chartChainMap = a.stepMap ∘ b.stepMap ∘ c.stepMap` and `chartChainInv = c.stepInv ∘ b.stepInv ∘ a.stepInv`. A two-step canonical-chart probe elaborates with exactly ha, hb, `b.stepTgt ⊆ a.stepDom`, `D ⊆ b.stepDom`, and IsOpen D. `ChartChainOK` contains no canonicality assumption about the composite itself. “Decidable-in-spirit finite data” is satisfied as finitely supplied matching certificates, not computational decidability of arbitrary C² maps or set inclusions.

The five-field bundle includes source-domain openness. B1 has four explicit chart hypotheses because `osc (b+ε)` / `cyl (b+ε)` openness is already proved by `isOpen_osc` / `isOpen_cyl`. Thus adding that derived field does not restrict either wrapper. Independent scratch declarations copied the complete original B1 signatures and proved them by constructing this bundle and applying the wrappers. This checks the converse use as well as the wrappers' direct applications of B1. Existence past ±T, uniqueness on order-connected intervals in V, chart-image identity, endpoint drift bounds, all quantifiers, and the oscillator zero-action convention are preserved.

The result proves canonicality of already certified charts; it neither constructs actual flows nor propagates derivative, remainder, or displacement bounds. In particular program-b-plan §3.2 says “Propagate each through later charts before adding it” and “compose displacement bounds with the needed derivative factors”. Those quantitative obligations remain with their respective consumers and are not claimed paid by B2-COMPOSE.

## Definition classification

All six new explicit structures/definitions have their intended bodies over their entire carriers: `IsCanonicalChart` is the exact source-premise Prop bundle; `ChartStep` is four pieces of chart data; `chartChainMap` and `chartChainInv` are total finite compositions with identity neutral element; `chartChainTarget` selects the actual outermost target with the correct empty case; `ChartChainOK` recursively expresses matching source data. No junk values, zero fallbacks, special-case proof shortcuts, carrier substitutions, or conclusion-shaped fields are present. The `@[expose] public noncomputable section` exposes the definition bodies.

## Reproducible checks

Every Lean/Lake invocation below was serial and ran under this prefix (also inherited by the lint script's ABI subprocess):

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1
```

1. Targeted build, prefix followed by:

```sh
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b2comp KAM.EffectiveStability.ChartChain
```

Exit 0; exact output:

```text
[inp-gate] slot 1 acquired 01:12:21 for KAM.EffectiveStability.ChartChain
Build completed successfully (2877 jobs).
```

The driver itself runs `nice -n 5 lake build`; no uncapped parallel build or clean was run. The job count includes already available dependencies; no warning was emitted.

2. Prefix followed by `lake env lean .lake/abi-scratch/B2ComposeAudit.lean`: exit 0. The scratch file imported ChartChain, recovered both B1 signatures as described above, and checked the three-step definitional equalities and two-step matching example. No errors or warnings. `#print axioms` returned exactly `[propext, Classical.choice, Quot.sound]` for each of:

```text
KAM.EffectiveStability.IsCanonicalChart.chart_comp
KAM.EffectiveStability.IsCanonicalChart.id_chart
KAM.EffectiveStability.IsCanonicalChart.mono_chart
KAM.EffectiveStability.chartChain_isCanonical
KAM.EffectiveStability.hamiltonian_comp_transfer
KAM.EffectiveStability.oscillator_confinement_of_chart
KAM.EffectiveStability.torus_confinement_of_chart
KAM.EffectiveStability.chart_id_comp_id
B2ComposeAudit.recovered_oscillator_confinement
B2ComposeAudit.recovered_torus_confinement
```

These are all eight explicitly declared new public theorems, plus both independent wrapper-recovery probes. Frozen/provider type equality and seal-body probes are inapplicable: this package adds neither an anchor nor a provider.

3. Prefix followed by `lake env leanchecker --verbose KAM.EffectiveStability.ChartChain`: exit 0; exact output:

```text
replaying KAM.EffectiveStability.ChartChain
```

There is exactly one new lemma module and no provider module to add to that invocation.

4. Prefix followed by `sh scripts/lint_sources.sh`:

LINT_RESULT_PENDING

5. `python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-b2comp KAM.EffectiveStability.ChartChain`: exit 0, exact output `short-name check OK (no reused public short name)`.

6. Python character-width/line-count scan of ChartChain: `lines: 189 overlong: []`. Manual module check: copyright, `module`, public imports, module docstring, public section and expose attribute present. Forbidden-token/resource-override scan returned no matches. `git diff --check inp...HEAD` exited 0 with no output.

7. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md KAM/Root lakefile.lean`: exit 0, empty output. No generated root, frozen file, manifest, consumer, or application file changed. Recursive source import traversal reaches 20 frozen definition modules, zero frozen theorem anchors, and zero providers; no DRAFT_SORRY theorem enters this package.

## Notes, errata, and deviations

No suspected pinned-source or blueprint defect was found in this scope. No source-paper theorem is newly implemented here: the reviewed source claim is the elementary canonical-composition claim in program-b-plan §3.2 and the seven explicit B2 brief items. No broader I/N/P theorem or earlier B1 proof audit is certified by this report.

The documented signature/name deviations are acceptable: `chart_comp`, `id_chart`, and `mono_chart` avoid generic short names; domain shrinking explicitly requests IsOpen D′ because the bundle includes openness. The allowed list version is supplied; no Fin-indexed version was required. No constants, source carriers, normalizers, or conclusions changed. The raw handoff's “No other file touched” is read as a Lean implementation claim: the actual diff also adds the handoff itself, as recorded above.

Only this report was added to the repository; the audit probe was removed from `.lake/abi-scratch/`. No state-changing git command was used.
