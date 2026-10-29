# NSEAL-PARTIAL independent audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-nseal`.
Audited HEAD: `1a49c67839834f8f059f1169481a4f2cd6566ef9`;
comparison branch `inp`: `b09cc13973973e2b5848066267c34d14e744eaba`.

## Verdict

**FAIL under the literal requested quarantine condition.** The frozen theorem
`KAM.Nekhoroshev.partialConvex_nekhoroshev` passes the exact-type, seal-body,
axiom and kernel checks. Its assembly has no detected mathematical or statement-fidelity defect.
However, `KAM.lean:1278` directly imports the provider, contrary to AGENTS.md rule 9
and NSEAL-PARTIAL-handoff.md item 4. This report does not silently exempt the generated root.
There is also a missing N11-F2 audit receipt in the requested directory.
The proof checks passing does not establish that every predecessor has an independent package audit.

Scope: the handoff requests a seal-key audit and a spot-check of the N11 assembly, not a new
line-by-line audit of the entire N11 analytic chain. `git diff inp...HEAD` contains only the
23-line audit handoff; the sealed code is inherited from `inp`. Thus the historical seal was
also inspected explicitly using `git show a88de4b6` and its parent. No Lean declarations or
definitions are new in the three-dot diff. The user's exact report location overrides the
generic brief's main-worktree destination.

## Findings

1. **Q1 — quarantine FAIL, inherited policy discrepancy.**
   `rg -n 'import KAM.Provider.Nekhoroshev.PartialConvexNekhoroshev' --glob '*.lean'`
   finds exactly:

   ```text
   KAM.lean:1278:public import KAM.Provider.Nekhoroshev.PartialConvexNekhoroshev
   KAM/Frozen/Nekhoroshev/Theorems/PartialConvexNekhoroshev.lean:22:import KAM.Provider.Nekhoroshev.PartialConvexNekhoroshev
   ```

   AGENTS.md:24–25 says “no module except the frozen anchor may import a provider”.
   Handoff item 4 repeats that requirement for this provider. In contrast,
   `scripts/gen_root_imports.py:42–51` excludes only DRAFT_SORRY anchors and their providers;
   SEALED providers are root-imported. The earlier `N11-P-seal-audit-1.md` checklist 4c explicitly
   counts the anchor **and KAM.lean** yet calls quarantine PASS. That is not the literal current
   requirement. Resolve the generator/rule discrepancy or supply an explicit ruling before
   claiming this checklist passes. Do not hand-edit the generated root. No other production
   importer was found. This is an import-policy failure, not evidence of an invalid proof.

2. **A1 — missing predecessor audit record.** No `N11-F2` audit report exists under
   `docs/tracks/N/audits/`. Mentions of F2 and `canonical_map` inside F1/H and the lane handoff
   are consumer checks and historical references, not an F2 package audit report. Recover or
   supply that report before claiming complete independent package-audit coverage.
   Grouped reports do cover K1/K2 (`N11-K-audit-1.md`), M1/M2 (`N11-M-audit-1.md`),
   N/P (`N11-NP-audit-1.md`), and the seal (`N11-P-seal-audit-1.md`). Reports also exist for
   A, B (plus ruling), C, D, E1, E2 (round 2), E3 (round 2), F1, F3, G, H, J1, J2,
   L1 (plus ruling), L2 and O. F2 is the only missing package receipt in the design's A–P
   package inventory (the design has no package I). These receipts were inventoried; their
   historical results are not represented here as fresh independent reruns.

## Frozen identity and manifest

Across `a88de4b6^..a88de4b6`, the anchor changes only:

```diff
-  by sorry
+  by exact KAM.Provider.Nekhoroshev.partialConvex_nekhoroshev hn hk G G' D hG hGc hG' hGc' hD ρ g m
+      Mcomplex hρ hMc hcollar h hhol hC2 hreal hHess hdef
```

A Python comparison removing only the registered proof region returned
`Seal bytes outside proof identical: True`; the current anchor equals the seal-commit file.
For `nekhoroshev.d25.partialConvex_nekhoroshev.v1`, the sole manifest-entry change is
`state: DRAFT_SORRY -> SEALED`. Current state is SEALED. Unchanged hashes:

```text
ABI     821dd585d6c345a79062e33a20882725afb5182a058117723eb6a3655feec090
prefix  40b1b8eb885fc0f1eefec48483400f801d970ff00f80a0863876940da7dee5d4
suffix  1efcbce496c3a865046e94018aa1cc8bdafb0b9454c6939e2353d83cc98b6da8
```

`docs/MANIFEST-CHANGES.md` has the 2026-10-29 D26/D29 seal row, listing the exact
23 explicit binders. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`
is empty. No protected files were edited by this audit.

## Declaration and assembly checks

Names below are in `KAM.Nekhoroshev`, except provider exports in
`KAM.Provider.Nekhoroshev`. Provider locators refer to
`KAM/Provider/Nekhoroshev/PartialConvexNekhoroshev.lean`.

| Node / declaration | Lean location | Verdict | Check |
|---|---|---|---|
| Frozen partial theorem | frozen anchor:48 | PASS proof/type; FAIL package policy | Exact frozen statement, binder-applied seal, standard axioms; Q1 remains. |
| `bpN:p0:partial`, provider `partialConvex_nekhoroshev` | provider:53 | PASS proof/type | Exact-type probe and fresh declaration copying the frozen statement/body both elaborate. |
| `final-orbit`, provider `slowPair_theta` | provider:35 | PASS | Exact frozen slow positions/momenta, component identities; no premise. |
| `final-orbit`, provider `fastAction_theta` | provider:43 | PASS | Exact frozen fast momentum, component identity; no premise. |
| `final-orbit`, provider `innerCore_mono` | provider:49 | PASS | Smaller closed-ball radius preserves the actual frozen core; arbitrary normed additive carrier. |
| `final-empty` | provider:84–89 | PASS | G empty contradicts initial core membership; threshold 1; no nonemptiness added to frozen type. |
| `final-data` | provider:90–97 | PASS | PartialData contains exactly frozen source premises; sign extracted once from hdef. |
| `final-mu`, `threshold` | Threshold.lean:185; provider:98–105 | PASS | μ₀ chosen before μ,P,C,z,t; six numerical comparisons are conclusions, not assumed estimates. |
| `final-given` / time | provider:106–109 | PASS | Queried t is nonnegative, at most C, and at most blockTime via threshold. |
| `bpN:p11:orbit`, `orbit` | Coordinates.lean:281; provider:110–116 | PASS | Frozen differentiability and Hamilton equation supplied from IsSolutionOn; physical angle divided by 2π, Hamiltonian by 2π. |
| `dm-field`, `domain_field` | Domain.lean:118; provider:117 | PASS | Actual P and frozen perturbation predicate; EqOn is proved from coordinate/scalar identities. |
| `bpN:p11:block`, `block` | Block.lean:240; provider:126–152 | PASS spot-check | Numerical premises from threshold, field identity from domain_field, supplied orbit and stopped slow condition. No requested fast drift is a premise. |
| `final-drift` | provider:118–124 | PASS | Frozen slow margin used only on [0,t]; core monotonicity gives 3d/4 initial margin; R0/(2K) ≤ d/2 is threshold output. |
| `final-sign` | provider:125–156 | PASS | σ=1 on [0,C]; σ=−1 uses θ(z(−u)) on [−C,0], derivative −F, query −t and exact prefix conversion. |

This matches the binder plan at `docs/tracks/N/design/N11-LEAN-DESIGN.md:393–420`
and the final/block proofs in `blueprint-N/parts/p11c-partial-stability.tex`.
The original n≥2, k≥1, open/convex domain premises, actual h, collar, complex Hessian bound,
and fixed-h quantifier order are preserved. No frequency upper bound, future slow-domain
condition, global flow existence or extra inner-core confinement is introduced.

`block`'s `hF` is a field identification on a domain, supplied by `domain_field`, not a
fast-drift premise. Its `hstop` is exactly the source's stopped slow predicate.
The conditional helper `transfer_conditional` has T3 by design; the stability consumers
prove it: Nonresonant.lean:447–467 constructs hT3 by integration, and
Resonant.lean:327,417–427 obtains hT3 from energy_free before transfer. Neither block
nor the provider assumes T3. This was a spot-check of that discharge, not a fresh proof
review of every energy/continuation constant.

## Definition classification

There are **no new def/abbrev/structure declarations in inp...HEAD**, and none in the
provider. The inherited objects directly relevant to the assembly were checked as follows:

| Object | Classification / whole-carrier behavior |
|---|---|
| `PartialData` | Source-premise bundle only; no stability estimate or existence conclusion hidden in fields. |
| `PartialConstants`, `constants`, numerical projections | Literal numerical record/formulas; total real division/rpow outside positive inputs is Lean's standard operation. All inversion/positivity needed here is proved from source data and μ>0; no fallback used to obtain confinement. |
| `DefiniteSign` | Selected ±1 witness and the frequency/Hessian source clauses from HasDefiniteFastPart; extracted, not added. |
| `theta`, `thetaInv`, `converted` | Explicit linear regrouping/scaling and H∘thetaInv/(2π) on the whole carrier; no junk branch. |
| `fastAction`, `slowPair`, `extCx`, `extRe` | Coordinate projections/inclusions on the stated product types; match frozen fast/slow maps in the provider. |
| `block_setting`, `signedH`, `signedF`, `slowScale`, `blockPert`, `physicalDomain` | Explicit cores/radii, signed/scaled source functions and physical tube; no conclusion-dependent selection or surrogate dynamics. |
| Frozen `innerCore` | Membership plus closed max-norm ball inclusion, including on empty domains; correct monotonicity direction. |
| Frozen `HasDefiniteFastPart`, `IsPartialPerturbation`, `IsSolutionOn` | Source Hessian/frequency, analytic normalized perturbation, and guarded two-sided Hamiltonian ODE predicates, respectively. |
| Frozen exponents | Exactly 2/(6n²−3n+14) and 3/(6n²−3n+14); positive-gap usage justified for n≥2. |

No inherited definition was modified or substituted. Classification here covers the assembly
objects, rather than claiming a new exhaustive audit of every internal normal-form definition.

## Fresh validation

All Lean/Lake invocations were serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
Build used the required compile gate; no clean/update/cache commands or overrides were used.

1. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-nseal KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev
   ```

   Exit 0. Output includes `[inp-gate] slot 1 acquired 15:26:58` and
   `Build completed successfully (3369 jobs).` Replayed inherited tactic/unused-variable
   warnings occur (including Coordinates, Lie, Transfer and Threshold); no errors.

2. Scratch probe `.lake/abi-scratch/NsealAudit.lean`:

   ```lean
   import KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev
   import KAM.Provider.Nekhoroshev.PartialConvexNekhoroshev
   example : type_of% @KAM.Nekhoroshev.partialConvex_nekhoroshev :=
     @KAM.Provider.Nekhoroshev.partialConvex_nekhoroshev
   ```

   The same file copies the complete frozen declaration as `KAM.Nekhoroshev.auditSeal`
   with the actual binder-applied seal body, and prints axioms of all four provider public
   theorems, the anchor, auditSeal, threshold, block, domain_field, orbit, nonresonant,
   resonant and nf. Command:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/NsealAudit.lean
   ```

   Exit 0, no warnings/errors. For **each of those 13 declarations**, output is
   `'<name>' depends on axioms: [propext, Classical.choice, Quot.sound]`.
   In particular:

   ```text
   'KAM.Nekhoroshev.partialConvex_nekhoroshev' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Provider.Nekhoroshev.partialConvex_nekhoroshev' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay, one invocation:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev KAM.Provider.Nekhoroshev.PartialConvexNekhoroshev KAM.Nekhoroshev.Partial.Block KAM.Nekhoroshev.Partial.Threshold
   ```

   Exit 0. Exact output:

   ```text
   replaying KAM.Nekhoroshev.Partial.Threshold
   replaying KAM.Nekhoroshev.Partial.Block
   replaying KAM.Provider.Nekhoroshev.PartialConvexNekhoroshev
   replaying KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev
   ```

4. Source lint / guard / ABI:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 0. Exact output:

   ```text
   check_lean_modules: PASS (1336 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No generated-root exception was needed; root, errata, forbidden-token, line/file-size,
   module and frozen checks passed. Lint's acceptance of SEALED-provider root imports does
   not discharge the stricter prose condition in Q1.

5. Import/size/token scan: recursively reading project import lines gives 180 project
   modules in the provider closure, **no frozen theorem module** and **no other provider**.
   Thus no DRAFT_SORRY anchor is imported, directly or transitively. A code-mask scan of
   `KAM/Nekhoroshev/Partial/*.lean` and the provider finds no forbidden proof escapes,
   resource overrides or EuclideanSpace. Maximum file size is Domain.lean, 862 lines.
   The global module-system check is recorded with lint below.

## Source defects, deviations and limits

No new suspected defect in a pinned mathematical source was identified. The pinned PDFs
were not re-audited in this seal-key task. Q1 is a repository-policy/generator contradiction,
not an erratum in Nek77/Pos93. The historical blueprint status paragraph
(`p11c-partial-stability.tex:199–200`) still calls energy/transfer “Unaudited new mathematics”;
later L2/J2 receipts exist, so this is an older status note, not a freshly demonstrated source gap.
The frozen docstring's bare-provider sealing sentence omits the explicit binders; the actual
seal follows D26's binder-applied correction and elaborates correctly. It was left untouched.

Files written by this audit: this report only, plus temporary probes/logs under the permitted
`.lake/abi-scratch/`, removed after recording receipts. No git state-changing command, protected
source edit, new hypothesis, generated-root repair or claim of full downstream P14 closure.
