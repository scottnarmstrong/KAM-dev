# GAP-WR independent package audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-gwr`.
Audited HEAD: `b09722a1f43b87e93e4327ee9d0f6d3cfbe9286c`.
Comparison `inp`: `52f2f69af6d0ba23dc715ed8b8b9d3f6285195ee`.

**Overall: PASS WITH NOTES.** The two scoped repairs pass: `stepP:p11:wr-chain` on the literal real carrier and `stepP:p11:wr-tube` with constants `4 n ε` and `2 n ε`. All 13 new theorems have only standard axioms; all four modules build and pass independent kernel replay. Notes concern the permitted generated-root lint exception, append-only integration, and the handoff's incorrect seal-status parenthesis. No blocking mathematical or hygiene defect was found in the audited files.

**Per-anchor status:** no provider or frozen anchor is implemented or changed by GAP-WR. Provider/frozen-type and seal-body probes are therefore not applicable to this slice. The inherited `KAM.Planetary.fixedSunPlanetaryKAM` anchor is still `DRAFT_SORRY` in this checkout, with a literal `by sorry` body; the handoff's “fixedSunPlanetaryKAM sealed” parenthesis is inaccurate here. This report certifies the new infrastructure, not that anchor's seal-readiness, any other track, or completion of the full wrapper slice.

## Authority, scope and signature coverage

Read AGENTS.md, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the local GAP-WR handoff and its AUDIT FOCUS, Track P statement, the relevant frozen physical definitions and FixedSunPlanetaryKAM anchor, P11A design/node table and exact signature artifact `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`, the prior P11A-P10 audit's F2/F3, and the live blueprint/graph contracts. The user's exact report destination overrides the generic brief's main-worktree destination.

Inspected the complete `git diff inp...HEAD`: precisely four added Lean modules, 744 lines. No inherited extra implementation diff needs attribution. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. The pre-existing untracked GAP-WR handoff was left untouched.

The four scoped modules are `Preparation/WrapperNodeCore`, `WrapperNodeChain`, `WrapperNodeTube` and `WrapperNodes`. The P11A design table at lines 189–195 maps the original wrapper and its six steps to `Preparation/Wrapper`; the handoff's explicit overnight ruling assigns only the two F2/F3 repairs to these new append-only modules. No signed declaration occurs among their 14 declarations (exact-name intersection with the delivered P11A signatures is empty). Existing signed exports are unchanged. No narrowed signed declaration is being used to substitute for a literal node export.

## Findings and proof review

1. **Chain carrier and hypotheses: PASS.** `WrapperNodeChain.lean:33–35` defines exactly the real action restrictions `|r_i| < 2`, `|rho'_i| < π/2`; all angles are unrestricted. The chart, full `Fin (n+n) → ℤ` lattice invariance and modulo-lattice injectivity are exported at lines 129–225 and in Part-1 `IsChart` form at lines 269–294. The Hamiltonian equality at lines 230–267 uses the actual fixed Hamiltonian, the same composition, and coefficient `ε`, preserving physical time. The formula on its RHS is the explicit extension of the prepared `N+P` formula to this carrier; it does not assert that arbitrary selected prepared-data values outside their specified complex domain already equal that extension.

   `4ε ≤ s₂` is stronger than `πε ≤ s₂` at a fixed ε, but is a legitimate source “for ε small” condition, not a conclusion-shaped premise. Indeed `|εr_i| < 2ε ≤ s₂/2` is exactly the new half-box requirement. `p11_pe_of_four` recovers the old premise, while `p11_four_eps_le_s2_ev` proves the stronger one eventually for each fixed `nu ≥ 1`, using the existing positive logarithmic lower bound on `s₂`. Constant dependence and quantifier order remain fixed data, fixed nu, then small ε. A scratch proof simultaneously combined this eventual condition with the two new tube conditions. A separate carrier probe accepted arbitrary real angles with `r=7/4`, `rho'=0`, beyond the old 3/2 action window.

2. **Core copies: PASS.** Compared the proof bodies directly with `PreparedBasic.lean:326–414` and `:429–490`. In each copy the sole proof-body change is deletion of `have hydom := p11Rescale_mem_dom ... hz`; `hydom` is now the explicit half-box premise. The Hamiltonian copy also exposes the same formula instead of the prepared-core projections. Reality is proved before taking real parts, the positive polar domain and fast/physical domains are proved, and division by ε is guarded by `0 < ε`. These are distinctly named conditional helpers: their map/identity premises are the prior chart and averaging results, supplied from `hC`, `hF`, `hS` at the node applications, not new unproved source assumptions.

3. **Tube constants and domains: PASS.** `WrapperNodeTube.lean:45–141` quantifies over every real point with `∀ j, |z.2 j| ≤ 1`, a stronger carrier than membership in the retained tori. It derives membership in the old prepared real domain rather than assuming it. The exported conjunction is literally the sum of the fast-output oscillator squares bounded by `4*n*eps`, each chart-input physical `poincareGamma` bounded by `2*n*eps`, and membership of the actual chain output in the frozen `circularTube` at `p11Zeta D`.

   The source's sum in rotated `(xi,eta)` coordinates is the same sum by real orthogonality: inherited `WrapperTube.lean:42–64` (`p11_orth_sq`) proves equality, and `p11_chartInput_gamma` at lines 67ff uses it on this exact chart input. Thus the fast-output sum in the export is the source's equivalent oscillator-coordinate expression; Gamma is already stated after the physical chart-input rotation. The proof establishes the slow-action displacement bounds, the pre-fast square bound, the sharpened fast-output bound, and the physical action margin before invoking `forward_tube`. The new scalar lemma uses `(u+e)^2 ≤ (7/6)u^2 + 7e^2`, twice, so the two-square bound is `(7/2)ε + 14d^2 ≤ 4ε` under `28d^2 ≤ ε`. There is no loss of an n factor.

   `hd` and `hΓε` are numeric smallness conditions on fixed data, not assumed tube/Gamma conclusions. `p11_ev_tube_node` proves them eventually: `d ≤ sqrt(ε)/6`, hence `28d^2 ≤ (28/36)ε ≤ ε`, and `2nε ≤ δ`. Existing `p11_ev_slowDisp`, `p11_ev_tube`'s first margin and `p11_wr_small` supply the other hypotheses. They are compatible with the new chain condition after a common threshold reduction.

4. **Integration note.** The existing signed wrapper is not rewired, and there is no new aggregate ε₀ lemma in production. This is permitted by the explicit append-only repair scope: the components needed for that threshold are proved, and no old signature or consumer is altered. A future consumer of the enlarged chain carrier must include `p11_four_eps_le_s2_ev` in its smallness selection. The two repaired graph nodes can pass without claiming that this worktree already integrated these new exports into the signed wrapper.

## Every new public declaration

Names are in `KAM.Planetary`. File abbreviations below refer to the four audited modules only.

| Node / role | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| wr-chain, carrier | `p11WrR`, Chain:33 | PASS | Exact real source rectangle; no angle bound. |
| wr-chain, lattice domain | `p11WrR_shift`, Chain:37 | PASS | All integer angle shifts preserve actions. |
| wr-chain, numeric helper | `p11_pe_of_four`, Chain:41 | PASS | π < 4 and ε > 0 recover prior bound. |
| wr-chain, half-box | `p11WrR_rescale`, Chain:45 | PASS | Each rescaled block lies in the specified slow half-box. |
| wr-chain, real domain chain | `p11_wrR_dom`, Chain:68 | PASS | Reality, positive polar actions, fast and physical domain membership. |
| wr-chain | `p11_wr_chain_node`, Chain:129 | PASS | Analyticity, ε-symplecticity, full lattice and quotient injectivity on R. |
| wr-chain, physical time | `p11_wr_ham_node`, Chain:230 | PASS | Fixed Hamiltonian equals ε times the explicit prepared formula on R. |
| wr-chain, Part-1 carrier | `p11_wr_xi_node`, Chain:269 | PASS | Exact phase reindexing; same chart and lattice conclusions. |
| wr-chain, eventual smallness | `p11_four_eps_le_s2_ev`, Chain:297 | PASS | Stronger numeric premise eventually follows from fixed-data estimates. |
| wr-chain, conditional core | `p11_wr_ham_core`, Core:29 | PASS | Prior Hamiltonian proof under explicit half-box membership. |
| wr-chain, conditional core | `p11_wr_chain_dom`, Core:129 | PASS | Prior complex domain-chain proof under explicit half-box membership. |
| wr-tube, scalar helper | `p11_tube_sq4`, Tube:31 | PASS | Sharpened two-coordinate perturbation bound. |
| wr-tube | `p11_wr_tube_node`, Tube:45 | PASS | Literal 4nε sum, 2nε Gamma and circular-tube inclusion. |
| wr-tube, eventual smallness | `p11_ev_tube_node`, Tube:145 | PASS | Both new numeric hypotheses hold eventually. |
| facade | `WrapperNodes`, lines 8–20 | PASS | Public imports of both node modules; no declarations. |

## Definition classification and import hygiene

Exactly one new definition, `p11WrR`: a transparent set predicate on all `Phase (n+n)`, with the intended coordinatewise inequalities and no fallback. No new abbrev, structure, instance, notation, selected data or choice function occurs. Existing total real-part maps are used only after proving reality/domain membership. No proof depends on junk values of an off-domain extension.

Recursive import inspection found 528 project modules, no providers, no frozen theorem modules, and 72 imported frozen definition files, each matched by its exact manifest `path` and marked `SEALED`. In particular no DRAFT_SORRY anchor is imported by these modules. All 14 new declaration short names have exactly one definition in KAM; they are within `KAM.Planetary`, with no root shadowing.

## Independent checks

Every Lean/Lake invocation below was sequential within this audit, with `LEAN_NUM_THREADS=1` and nice level 5 (the build gate itself applies `nice -n 5`). Lint's ABI subprocess ran after all direct Lean checks. No clean, update, cache retrieval, root regeneration, protected-file edit or git mutation was performed.

**Target build**, exit 0:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gwr KAM.Planetary.Preparation.WrapperNodeCore KAM.Planetary.Preparation.WrapperNodeChain KAM.Planetary.Preparation.WrapperNodeTube KAM.Planetary.Preparation.WrapperNodes
```

Output begins `[inp-gate] slot 1 acquired 04:46:20` and ends `Build completed successfully (9574 jobs).` Replayed dependency warnings include unused bindings and deprecated Mathlib names; none is from the four audited modules. This used the existing build overlay, not a library rebuild from scratch.

**Axioms**, exit 0:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPWRAudit.lean
```

The scratch file imported `KAM.Planetary.Preparation.WrapperNodes` and issued `#print axioms KAM.Planetary.<name>` for every new declaration. Exact output:

```text
'KAM.Planetary.p11WrR' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11WrR_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pe_of_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11WrR_rescale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_wrR_dom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_wr_chain_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_wr_ham_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_wr_xi_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_four_eps_le_s2_ev' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_wr_ham_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_wr_chain_dom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_tube_sq4' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_wr_tube_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_ev_tube_node' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The expanded final scratch probe (same command) also passed, exit 0, including the simultaneous eventual-condition conjunction and the `r=7/4` carrier witness. An initial expanded-probe run exited 1 solely because the auditor omitted `Fin.append_right` in simplifying that witness; the explicit simplification fixed the scratch proof. No production code changed, and the initial all-declaration axiom probe had already passed.

**Kernel replay**, one invocation, exit 0:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.WrapperNodeCore KAM.Planetary.Preparation.WrapperNodeChain KAM.Planetary.Preparation.WrapperNodeTube KAM.Planetary.Preparation.WrapperNodes
```

Exact output:

```text
replaying KAM.Planetary.Preparation.WrapperNodes
replaying KAM.Planetary.Preparation.WrapperNodeTube
replaying KAM.Planetary.Preparation.WrapperNodeChain
replaying KAM.Planetary.Preparation.WrapperNodeCore
```

**Source lint**, exit 1 solely for the permitted generated-root exception:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1266 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The brief explicitly allows the stale `KAM.lean` message. The module check, frozen-anchor guard and elaborated ABI check all pass. The generated root was not edited.

Static checks: Core 192 lines / maximum 97 characters; Chain 328 / 100; Tube 204 / 100; facade 20 / 97. All modules have copyright, `module`, public imports, module docstring and public section; the set definition is exposed by its section. No forbidden proof escape, resource override, EuclideanSpace, reused new short name or harmful root shadow was found. `git diff --check inp...HEAD` exits 0. Protected-path comparison is empty. Probe sources and audit-created scratch files were deleted after recording results.

## Suspected defects, deviations and limits

No new suspected pinned-source or blueprint defect. The controlling local contracts are `blueprint-P/parts/p11-cp09-preparation.tex:250` (“real analytic on ... |r| < 2 ... |rho'| < π/2”) and `:253` (“sum ... ≤ 4nε ... Gamma_i ... ≤ 2nε”), also recorded at `docs/graph/P/DEPGRAPH.md:21036–21037` and `:21137`. The new proofs support them; no source repair was made. This audit used the pinned local blueprint and did not re-audit external PDFs or their inherited errata.

Declared implementation deviation: replace `πε ≤ s₂` by eventual `4ε ≤ s₂` for the enlarged chain domain; mathematically justified above. Documentation discrepancy: the handoff title says “fixedSunPlanetaryKAM sealed”, while the audited manifest and frozen body still show DRAFT_SORRY. Neither GAP-WR's infrastructure nor this report seals it. Other track I/N/P results, older signed declarations and the remaining wrapper nodes are outside the explicitly restricted audit scope.
