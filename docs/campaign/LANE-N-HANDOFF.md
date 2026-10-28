# Lane N (Nekhoroshev) handoff memo

Handoff memo, 2026-10-28, written at about 21:55 UTC by the main orchestrator (reviewed 22:00). Snapshot: `inp` at `8f19267d` (21:54); GitHub `main` at
`593af46b` (21:40). Anything this memo could not check is marked **UNVERIFIED**.

## 1. Purpose and what changed

- **Lane N is paused** as of 2026-10-28 at about 21:45 UTC. The owner (Scott Armstrong) is handing it to his
  co-author Zohar Komargodski's agents, who will continue it.
- **Lane P** (tracks P and I, including the shared `inp` integration branch) continues under the main
  orchestrator.
- **Lane N's single remaining goal** is to seal the frozen anchor `KAM.Nekhoroshev.partialConvex_nekhoroshev`
  (N-PARTIAL-CONVEX, decision D25). It is proved through the N11 package chain (blueprint-N Part 11). Every other
  frozen N theorem is already SEALED (§3).
- **Lane P depends on this seal.** Lane P's `planetaryExponentialSafety` (packages E11 and E12) cannot close
  until lane N delivers the provider for `partialConvex_nekhoroshev`. See OVERNIGHT 19:27 and design P14, gate N2
  (`docs/tracks/P/design/P14-LEAN-DESIGN.md:39`).

## 2. Where things are

**Repositories and branches**

- **GitHub** `scottnarmstrong/KAM-dev` has **only `main`**. `git ls-remote` lists `refs/heads/main` alone.
  - `origin/main` = `593af46b`. It contains N11-A, B, C, D, F3, L1, L2 and O, which arrived with the landing
    `c03d02b1` of `inp` at `d69dedec`.
  - A further landing, `d4d95536` "Land inp into main" (21:53), is committed in `/root/code/KAM`. It brings
    N11-E1 to main. At 22:00 it was being built by `scripts/land-branch.sh inp`, which pushes main to GitHub when the build
    succeeds; local main was then 30 commits ahead of origin.
- **`inp`** (integration branch; checkout `/root/code/KAM-inp`) **exists only on this machine.** It is 119
  commits ahead of `origin/main`.
  - At 21:53 it merged N11-E3, N11-G, N11-J1, N11-J2 and GAP-A (commits `5b2126a8`, `4425c1cf`, `4d744a2d`,
    `31377c9b`, `c80c6cb2`). None of these is on GitHub yet.
- **Every `inp-*` branch is local only.** The three branches below hold lane-N work that is not on `inp`:

| Branch | Tip | Worktree | Content |
|---|---|---|---|
| `inp-n11e2` | `b4ca71f4` (audit-2 commit; code tip `af8d6eb0`) | `/root/code/KAM-inp-n11e2` | Lie.lean, Adjoint.lean (+ inherited C files); being merged into `inp` now (orchestrator) |
| `inp-n11f2` | `56668d70` (audit-1 commit; code tip `1d5683c5`) | `/root/code/KAM-inp-n11f2` | ExtFlow.lean, CanonicalMap.lean (+ E1 files) |
| `inp-n11f1` | `adc0f148` | `/root/code/KAM-inp-n11f1` | Composition*, Transform* (+ merges of E1, E2 tip, F2 tip) |

- **Untracked files** in those worktrees, needed by the new team:
  - (`N11-E2-audit-2.md` is now committed on `inp-n11e2` as `b4ca71f4`.)
  - `/root/code/KAM-inp-n11f2/docs/tracks/N/audits/N11-F2-handoff.md` and `N11-F2-audit-1.md`
  - `/root/code/KAM-inp-n11f1/.drafts/handoff-N11-F1.md`
- **Handoff prerequisite (orchestrator action; status UNVERIFIED).**
  1. Commit those reports on their branches.
  2. Push `inp`, `inp-n11e2`, `inp-n11f2` and `inp-n11f1` (or a bundle) to GitHub.
  3. Publish the untracked signatures and briefs listed below.
- The tmux session `inp-mprov-n11f1` (the paused F1 prover) still exists on this machine.

**Documents** (paths relative to the repo root)

- **Blueprint:** `blueprint-N/parts/p11a-partial-route.tex`, `p11b-partial-nf.tex` and
  `p11c-partial-stability.tex`. The frozen-anchor proof is at p11c L170–180.
- **Track N:** `docs/tracks/N/statement.md` and `docs/tracks/N/notes.md`. The anchor docstring points to
  `notes.md`.
- **Designs** (`docs/tracks/N/design/`): `N2-`, `PART3-`, `PART145-`, `PART67-`, `N89-`, `N10-`, `N11-` and
  `N12-LEAN-DESIGN.md`, plus their `*-design-audit-*.md`.
- **The live design is `N11-LEAN-DESIGN.md`** (1305 lines; last change `eedc66fe`, the ext_flow rename). Its
  N11 design audits are 1 FAIL and 2 PASS. Key sections:

| Lines | Section |
|---|---|
| 65–88 | Hard rules for briefs |
| 159–297 | Node table (graph node → declaration) |
| 344–391 | Package plan (rows `N11-A / 1` … `N11-P / 10`, L353–375) |
| 393–420 | Binder-by-binder provider assembly |
| 422–452 | Risks |
| 454 onward | Appendix A (exact signatures) |

- **Package audits:** `docs/tracks/N/audits/<PKG>-handoff.md` and `<PKG>-audit-<round>.md`.
- **Graph:** `docs/graph/N/DEPGRAPH.md` (records start `NODE:`; fields `LEAN_STATUS`, `LEAN_REF`, `LEAN_NOTE`).
  Status updates must also be mirrored into `docs/graph/N/packets/N-p11ab.nodes.md` and `N-p11c.nodes.md`; see
  commit `9a0c51fe` for the pattern.
- **Manifest:** `manifest/frozen-anchors.json`. Changes are logged in `docs/MANIFEST-CHANGES.md`.
- **Decisions and rulings:**
  - `docs/DECISIONS.md`: D23 sub-orchestrator; D25 approval; D26 sealing guard; D27 BYPASSED; D29 overnight
    mode, no new freezes.
  - `docs/campaign/OVERNIGHT.md`: the authoritative copy is on `main`.

**Signatures**

- **The live N11 signature file is not in git:** `/root/code/KAM-inp/.drafts/design/N11Signatures.lean`
  (846 lines, SHA-256 `fe33b7d1689f…a8aeb`). The orchestrator will publish a tracked copy as
  `docs/tracks/N/design/N11-SIGNATURES.md`; this memo refers to that path. Two amendments since the design:
  - **L213:** `theorem ext_flow`, renamed from `flow` (ruling 20:50).
  - **L301–302:** `canonical_map` gained `(hc : 0 < b.c)` after `φ` (ruling 21:15).
- **The design's Appendix A is behind.** It is the 845-line Revision-2 text (SHA `23bd2cc2…`). It carries the
  rename but **not** the `hc` premise.
- Backups of the amended file live outside the repo: `N11Signatures.lean.bak-2050` and `.bak-2115` under
  `/mnt/HC_Volume_106379410/orchestrator-tools/handoffs/`.

**Other untracked or machine-local material**

- **Briefs:** `/root/code/KAM-inp/.drafts/briefs/`.
  - `inp-prover-common.md`, the common prover brief.
  - `inp-audit-package.md`, the common audit brief.
  - `offload-main/N11-*.md` and `GAP-A.md`, the per-package briefs.
- **Tooling:** `/mnt/HC_Volume_106379410/orchestrator-tools/`.
  - `inp_lake_build.sh`: the 3-slot compile gate.
  - `inp_new_worktree.sh`.
  - `main_inp_prover.sh` and `main_inp_audit.sh`: the launchers.
  - The pre-audit checks: `main_shortname_check.py`, `main_shadow_check.sh` and `main_name_clash_check.sh`.
- **In-repo scripts:** `scripts/lint_sources.sh`, `scripts/check_frozen_anchors.py`,
  `scripts/gen_root_imports.py` and `scripts/land-branch.sh`.
- **Toolchain:** Lean `v4.35.0`, Mathlib `v4.35.0`.

### GitHub branches pushed for this handoff (22:15 UTC, at the owner's request)

Every compiling lane-N branch is now on GitHub (`scottnarmstrong/KAM-dev`) so nothing has to be redone:

| GitHub branch | Tip | Content | Audit |
|---|---|---|---|
| `inp-n11e2` | `b4ca71f4` | N11-E2 Lie, Adjoint (round 2) | PASS WITH NOTES (round 2) |
| `inp-n11e3` | `318bc7c7` | N11-E3 Domain, Hessian (round 2) | PASS WITH NOTES (round 2) |
| `inp-n11g` | `7747325a` | N11-G BlockData | PASS WITH NOTES |
| `inp-n11j1` | `f618d28a` | N11-J1 Preimage | PASS WITH NOTES |
| `inp-n11j2` | `f0119ced` | N11-J2 Transfer | PASS WITH NOTES |
| `inp-gapa` | `bba61e86` | GAP-A ThresholdExplicit (+ lane-P Homological/Reality) | PASS WITH NOTES |
| `inp-n11f2` | `56668d70` | N11-F2 ExtFlow, CanonicalMap | FAIL (F2-C1, §10 Q1); code compiles |
| `inp-n11f1` | `7df1da94` | N11-F1 Composition, CompositionCoeff, Transform, TransformIntegral; contains E2 and F2 | not audited; compiles (gate build of all eight modules, 22:13) |
| `lane-n-handoff` | `5952d776` | `inp` (with E3, G, J1, J2, GAP-A) + `inp-n11f1`: every N11 module in one tree | all 28 `KAM/Nekhoroshev/Partial` modules compile together (gate build, 3351 jobs, 22:20); START HERE |

## 3. Frozen N anchors

The manifest holds 144 anchors: 137 SEALED and 7 DRAFT_SORRY. Six of the drafts are Planetary; the seventh is
the one below. The 26 N entries (paths under `KAM/Frozen/Nekhoroshev/`) are 25 SEALED and 1 DRAFT_SORRY.

| id | export (`KAM.Nekhoroshev.*`) | file | state |
|---|---|---|---|
| nekhoroshev.actionBall.v1 | actionBall | Defs/ActionBall.lean | SEALED |
| nekhoroshev.realActionDomain.v1 | realActionDomain | Defs/RealActionDomain.lean | SEALED |
| nekhoroshev.complexDomain.v1 | complexDomain | Defs/ComplexDomain.lean | SEALED |
| nekhoroshev.realPart.v1 | realPart | Defs/RealPart.lean | SEALED |
| nekhoroshev.IsAnalyticIntegrable.v1 | IsAnalyticIntegrable | Defs/IsAnalyticIntegrable.lean | SEALED |
| nekhoroshev.IsStrictlyQuasiConvex.v1 | IsStrictlyQuasiConvex | Defs/IsStrictlyQuasiConvex.lean | SEALED |
| nekhoroshev.HasDerivativeBounds.v1 | HasDerivativeBounds | Defs/HasDerivativeBounds.lean | SEALED |
| nekhoroshev.IsAnalyticPerturbation.v1 | IsAnalyticPerturbation | Defs/IsAnalyticPerturbation.lean | SEALED |
| nekhoroshev.IsSolutionOn.v1 | IsSolutionOn | Defs/IsSolutionOn.lean | SEALED |
| nekhoroshev.integrableOrbit.v1 | integrableOrbit | Defs/IntegrableOrbit.lean | SEALED |
| nekhoroshev.HasComplexHessianBound.v1 | HasComplexHessianBound | Defs/HasComplexHessianBound.lean | SEALED |
| nekhoroshev.quasiConvex_isoenergetic_derivative.v1 | quasiConvex_isoenergetic_derivative | Theorems/QuasiConvexIsoenergeticDerivative.lean | SEALED |
| nekhoroshev.zero_perturbation.v1 | zero_perturbation | Theorems/ZeroPerturbation.lean | SEALED |
| nekhoroshev.quasiConvex_nekhoroshev_complexBound.v1 | quasiConvex_nekhoroshev_complexBound | Theorems/QuasiConvexNekhoroshevComplexBound.lean | SEALED |
| nekhoroshev.d25.complexifyPhase.v1 | complexifyPhase | Defs/ComplexifyPhase.lean | SEALED |
| nekhoroshev.d25.innerCore.v1 | innerCore | Defs/InnerCore.lean | SEALED |
| nekhoroshev.d25.partialComplexDomain.v1 | partialComplexDomain | Defs/PartialComplexDomain.lean | SEALED |
| nekhoroshev.d25.HasDefiniteFastPart.v1 | HasDefiniteFastPart | Defs/HasDefiniteFastPart.lean | SEALED |
| nekhoroshev.d25.IsPartialPerturbation.v1 | IsPartialPerturbation | Defs/IsPartialPerturbation.lean | SEALED |
| nekhoroshev.d25.partialTimeExponent.v1 | partialTimeExponent | Defs/PartialTimeExponent.lean | SEALED |
| nekhoroshev.d25.partialDriftExponent.v1 | partialDriftExponent | Defs/PartialDriftExponent.lean | SEALED |
| **nekhoroshev.d25.partialConvex_nekhoroshev.v1** | **partialConvex_nekhoroshev** | **Theorems/PartialConvexNekhoroshev.lean** | **DRAFT_SORRY** |
| nekhoroshev.d28.HasAveragingFrequencyRank.v1 | HasAveragingFrequencyRank | Defs/HasAveragingFrequencyRank.lean | SEALED |
| nekhoroshev.d28.averagingError.v1 | averagingError | Defs/AveragingError.lean | SEALED |
| nekhoroshev.d28.averaging_mean.v1 | averaging_mean | Theorems/AveragingMean.lean | SEALED |
| nekhoroshev.d28.averaging_most.v1 | averaging_most | Theorems/AveragingMost.lean | SEALED |

**What seals the remaining draft**

- **The draft.** The anchor body is `by sorry` (`PartialConvexNekhoroshev.lean:79`). The manifest entry names
  module `KAM.Provider.Nekhoroshev.PartialConvexNekhoroshev` and export
  `KAM.Provider.Nekhoroshev.partialConvex_nekhoroshev`.
- **The provider module.** `KAM/Provider/Nekhoroshev/PartialConvexNekhoroshev.lean` is currently a 15-line stub:
  header and docstring only, no declaration. It is quarantined: nothing but the anchor may import it.
- **Sealing**, following the N-HEAD-C precedent (commits `7c254d1a` and `00afab9d`):
  1. Write the provider (package N11-P) with exactly the frozen type.
  2. Run an independent seal-key audit (`inp-audit-package.md`, item 1): a type-equality probe, a probe of the
     seal body, `#print axioms` (only propext, Classical.choice, Quot.sound) and a `leanchecker` replay.
  3. The integrating orchestrator, never a prover, changes the body and flips the manifest state from
     DRAFT_SORRY to SEALED, adds a `MANIFEST-CHANGES` row and marks `bpN:p0:partial` PROVED.
- **The seal body must name all 23 explicit binders.** The guard (D26 correction 2) requires the export applied
  to every explicit binder, in order, so the bare `by exact …` in the anchor docstring will not pass. The
  binders, extracted with the guard's own rule, are
  `hn hk G G' D hG hGc hG' hGc' hD ρ g m Mcomplex hρ hMc hcollar h hhol hC2 hreal hHess hdef`. Wrapped at 100
  columns, the body is 2 lines and about 159 bytes, inside the manifest limits of 3 lines and 240 bytes.
  **UNVERIFIED**: this was computed, not elaborated.

## 4. Graph status (`docs/graph/N/DEPGRAPH.md` on `inp` at `8f19267d`, 728 nodes)

**Overall: PROVED 332, NOT_STARTED 348, EXTERNAL 48.**

| Part | Nodes | PROVED | NOT_STARTED | EXTERNAL | bpN nodes (PROVED) | Design |
|---|---|---|---|---|---|---|
| p0 | 39 | 36 | 3 | 0 | 39 (36) | frozen roots |
| p1 | 56 | 17 | 35 | 4 | 19 (12) | PART145 |
| p2 | 26 | 26 | 0 | 0 | 6 (6) | N2 |
| p3 | 79 | 31 | 43 | 5 | 32 (26) | PART3 |
| p4 | 34 | 21 | 11 | 2 | 15 (11) | PART145 |
| p5 | 46 | 19 | 27 | 0 | 12 (12) | PART145 |
| p6 | 40 | 12 | 26 | 2 | 14 (12) | PART67 |
| p7 | 63 | 18 | 41 | 4 | 22 (18) | PART67 |
| p8 | 49 | 16 | 27 | 6 | 20 (14) | N89 |
| p9 | 34 | 16 | 16 | 2 | 12 (8) | N89 |
| p10 | 36 | 28 | 7 | 1 | 8 (6) | N10 |
| **p11** | **122** | **29** | **89** | **4** | 41 (16) | **N11 (live)** |
| p12 | 89 | 63 | 23 | 3 | 35 (30) | N12 |
| K:/I: externals | 15 | 0 | 0 | 15 | — | — |

Grouping is by the `pNN` part of the node id; `bpN:p6#data` and `bpN:p9#data` are counted with p6 and p9.

**Earlier parts are complete for sealing purposes**

- **Every frozen theorem those parts serve is SEALED.**
  - `zero_perturbation` and `quasiConvex_isoenergetic_derivative`: Part 2.
  - `quasiConvex_nekhoroshev_complexBound` (N-HEAD-C): Parts 1 and 3–10, sealed 19:55.
  - `averaging_mean` and `averaging_most`: Part 12.
- **There is no `sorry`** under `KAM/Nekhoroshev/`, `KAM/Provider/Nekhoroshev/` or `KAM/Frozen/Nekhoroshev/`,
  except the draft anchor itself.
- **Their NOT_STARTED residue is bookkeeping, not missing proofs.**
  - 239 step nodes have no note at all: internal proof steps that were never recorded one by one.
  - Several are route, data or claim nodes, for example the p1 `norm-convert` routes, `bpN:p3:s-N#data`,
    `bpN:p4:n-zero`, `bpN:p9:s-blocks#data`, and `bpN:p0:avg-sec#data` / `avg-totality`.
  - A few are signed exports that the design deliberately narrowed: `stepN:p10:cf-orbit` and `cf-branch`
    (ruling 18:47), `bpN:p10:hypotheses-check`, `stepN:p1:co-pert/co-exc/co-time` and `stepN:p5:fl-symmetry`.
- **No N11 package has reported a missing Part 1–10 declaration.** They consume Part 4–8 owners directly; see the
  reuse map, design L127–157.

**p11 sync backlog** (to do at the next graph sync)

1. **Merged packages not yet reflected.** The packages merged at 21:53 (E3, G, J1, J2, GAP-A) are still
   NOT_STARTED in the graph, including `final-mu` and `final-time`.
2. **Audit-passed steps never recorded.** These steps passed audit but were never marked PROVED:
   - `stepN:p11:ef-tube`, `ef-adm`, `ef-en`, `ef-en-energy`, `ef-en-taylor` and `ef-en-split`: rows PASS in
     `N11-L2-audit-1.md` L64–69.
   - `ex-den` and `ex-cmp`: "PASS, internal" in `N11-B-audit-1.md` L89–90.
   - `or-chain`: the N11-A audit maps its helpers. **UNVERIFIED** that it covers the full node.
3. **Partial literal-node gaps from A and B**, still with notes and not assigned to any package:
   - `bpN:p11:wfield`: Ω_c matrix and X = Ω_c ∇u not defined.
   - `bpN:p11:constants`: w = d/4, K_a = K/√n, μ₀, p, q, b_c not defined.
   - `bpN:p11:ext-class`: the claim (SL) ⇒ (SL)_{ρ,σ} has no Lean statement.
   - `bpN:p11:s-nf#data`: the dictionary constants ā, κ, q.

## 5. N11 package table

The modules live in `KAM/Nekhoroshev/Partial/`. Audit reports are at `docs/tracks/N/audits/` on the branch, or
in the worktree where marked. "Est." is the design estimate (L353–375); "act." is actual lines.

| Pkg / wave | Modules | Design deps | Status (21:55) | Branch | Audit report(s) | Notes |
|---|---|---|---|---|---|---|
| N11-A / 1 | Setting, Coordinates | frozen defs, Weighted | merged; on GitHub main | inp-n11a | N11-A-audit-1 PASS WITH NOTES | wfield, ext-class, s-nf#data gaps (§4) |
| N11-B / 1 | Constants | frozen exponents | merged; GitHub | inp-n11b | audit-1 FAIL (short name) + `N11-B-audit-1-ruling.md` | accepted by ruling 18:50 |
| N11-C / 2 | Bracket, VectorField | A | merged; GitHub | inp-n11c | PASS WITH NOTES | |
| N11-D / 2 | RealSystem, Continuation | A, ODE, Part 7 | merged; GitHub | inp-n11d | PASS WITH NOTES | |
| N11-E1 / 3 | Flow, SymplecticLinear, Symplectic | C, D | merged on inp; in local main `d4d95536` (push UNVERIFIED) | inp-n11e1 | PASS WITH NOTES | signed `flow` → `ext_flow` |
| N11-E2 / 3 | Lie, Adjoint | A, C | **audit-2 PASS WITH NOTES (21:47); merging into inp now (not yet on inp at 21:56)** | inp-n11e2 | audit-1 FAIL; audit-2 PASS WITH NOTES (both on branch, `b4ca71f4`) | round 2 adds unsigned `ext_taylor_second` |
| N11-E3 / 3 | Domain, Hessian | A, B | merged on inp 21:53 | inp-n11e3 | audit-1 FAIL; audit-2 PASS WITH NOTES | Domain.lean 862 lines (est. 450) |
| N11-F1 / 4 | Composition, CompositionCoeff, Transform, TransformIntegral | C, E1, E2, F2's ExtFlow | **prover done, not audited, not merged** | inp-n11f1 | none yet; handoff `.drafts/handoff-N11-F1.md` (untracked) | 1503 lines act. (est. 1050) |
| N11-F2 / 4 | ExtFlow, CanonicalMap | C, E1 | **audit-1 FAIL for consumer-complete integration (21:43); not merged** | inp-n11f2 | audit-1 and handoff committed on branch (`56668d70`) | see F2-C1 below |
| N11-F3 / 3 | Homological | A, Part 6 | merged; GitHub | inp-n11f3 | PASS WITH NOTES | |
| N11-G / 4 | BlockData | B, E3, Part 8 | merged on inp 21:53 | inp-n11g | PASS WITH NOTES | built on E3 round-1 commits; Part-8 reconciliation checked (audit L64ff) |
| N11-H / 5 | Iterative | C, F1, F2, F3 | **not started** | — | — | est. 650; needs the F2-C1 decision |
| N11-J1 / 5 | Preimage | A, E1 | merged on inp 21:53 | inp-n11j1 | PASS WITH NOTES | |
| N11-J2 / 6 | Transfer | D, E1, J1 | merged on inp 21:53 | inp-n11j2 | PASS WITH NOTES | conditional helper; T3 must be proved at each call |
| N11-K1 / 6 | NormalFormInduction | H | not started | — | — | est. 650 |
| N11-K2 / 7 | NormalForm | K1, telescope | not started | — | — | est. 550 |
| N11-L1 / 4 | EnergyIdentity | C, D | merged; GitHub | inp-n11l1 | audit-1 FAIL + ruling (accepted 21:01) | ef-C internal to L2 |
| N11-L2 / 5 | Energy | L1 | merged; GitHub | inp-n11l2 | PASS WITH NOTES | `energy_free` |
| N11-M1 / 8 | Nonresonant | K2, J2 | not started | — | — | est. 350 |
| N11-M2 / 8 | Resonant | K2, J2, L2, E3 | not started | — | — | est. 450 |
| N11-N / 9 | Block | G, M1, M2, E3 | not started | — | — | est. 450 |
| N11-O / 2 | Threshold | B | merged; GitHub | inp-n11o | PASS WITH NOTES | final-mu/time gaps filled by GAP-A |
| GAP-A (N11-O2) | ThresholdExplicit (+ lane-P `KAM/Planetary/PlanarTorsion/Homological/Reality.lean`) | O | merged on inp 21:53 | inp-gapa | PASS WITH NOTES | fills final-mu and final-time |
| N11-P / 10 | `KAM/Provider/Nekhoroshev/PartialConvexNekhoroshev.lean` | N, O, Coordinates, Hessian | not started (stub) | — | — | est. 300; seal (§3) |

Modules on `inp` now: 20 files, 6470 lines. Pending on branches: E2 505, F2 365 and F1 1503 lines.

**N11-F1 handoff summary** (`/root/code/KAM-inp-n11f1/.drafts/handoff-N11-F1.md`, untracked). Paused
cleanly; last commit `adc0f148` "N11-F1: wrap long lines" (21:45), with `transform` and `transform_integral`
proved (`b6f01429`).

- **Files:**
  - `CompositionCoeff.lean` (218): independent-dimension `*_ext` helpers.
  - `Composition.lean` (590): `ExtCompose`, `extGauge`, `composition_domain`, `composition`,
    `composition_real` and the Lie-series engine.
  - `TransformIntegral.lean` (315): ParamHyp/Fubini engine, `ExtCompose.integral_inClass`, `integral_bound`,
    `coeff_integral_ext`.
  - `Transform.lean` (380): `transform`, `transform_integral`, the remainder series and `transform_identity`.
- **Signed declarations** are copied verbatim. `extFlow` is imported from F2's `ExtFlow.lean`, not redefined.
- **Nodes:**
  - co-field, co-series, co-remainder and composition: `composition*`.
  - tr-taylor: `ext_taylor_second`, used inside `transform`.
  - tr-int: `transform_integral`.
- **Approach:** a port of Part 5 to EC n k with adjoint constant q = e²η/8.
- **Prover-reported checks** (not re-run here; **UNVERIFIED**):
  - The gate build of the four modules is clean (no warnings, no sorry).
  - The axioms of the five main results are [propext, Classical.choice, Quot.sound].
  - Lint passes except the expected "KAM.lean is out of date".
  - No heartbeat signals and no statement changes.
- **Pause status:** "nothing remaining in this package". Next steps are the independent audit, the merge, a
  `KAM.lean` regeneration, then N11-H. The READY marker was removed at the pause; `.drafts/PAUSED-N11-F1` is an
  empty marker.

**Branch topology to respect when merging**

- `inp-n11f1` contains the tips of `inp-n11e2` and `inp-n11f2`. Merging F1 therefore also brings in F2's
  `CanonicalMap.lean`, whose integration audit failed.
- Suggested order: E2, then F2 (once F2-C1 is resolved), then F1 (after its audit).
- **UNVERIFIED**: that these merge cleanly; no merge was attempted.

**F2-C1** (`N11-F2-audit-1.md` §"F2-C1")

- **What passed.** The two F2 modules match the amended signatures, and no soundness defect was found.
- **The gap.** The signed `iterative` (signatures L367–379 premises; statement to L410) takes an arbitrary `PartialBlock` and must conclude
  `ExtCanonical b.c … Φ` (L396). Nothing in its premises forces `0 < b.c`, so H cannot discharge
  `canonical_map`'s new `hc`.
- **Counterexample.** b.w = 0 gives c = 0, and `slowLoss` is automatic at c = 0.
- **The auditor's options.**
  - (a) Authorize a positivity premise in `iterative` and propagate it to its callers.
  - (b) Prove a degenerate c = 0 canonicity branch, so that the types stay unchanged.

## 6. Critical path to sealing `partialConvex_nekhoroshev`

Remaining design estimate, H through P: **about 3400 lines.** For calibration, completed packages ran 0.75–1.65×
their estimates; E3 was 1313 lines against 800, and F1 1503 against 1050.

```
(resolve F2-C1) ─► F2 merge ─┐
E2 merge ────────────────────┼─► F1 audit+merge ─► H (650) ─► K1 (650) ─► K2 (550) ─┬─► M1 (350) [+J2] ─┐
                             │                                                       └─► M2 (450) [+J2,L2,E3] ─┤
                             │                       N (450) [+G,E3] ◄──────────────────────────────────────────┘
                             └──────────────────────► P provider (300) [+O, GAP-A, Coordinates, Hessian]
                                                      ─► seal-key audit ─► seal (orchestrator) ─► unblocks P: E11, E12
```

1. **Immediate.**
   - Finish the E2 merge (in progress per the orchestrator).
   - Get an owner or design decision on F2-C1 (§10, Q1), then merge F2.
   - Run the independent audit of F1, using the "Common to all" focus in §8 plus a whole-library clash check,
     then merge it.
   - Regenerate `KAM.lean` and sync the graph (§4).
2. **N11-H `iterative`** (wave 5). It consumes `ExtCompose`, `composition`, `transform`,
   `transform_integral`, `canonical_map` and `hom`/`homGenerator`. It must export holomorphy, the image, integer
   equivariance and the flow left inverse (design Revision 2, F2).
3. **N11-K1 then K2** (`nf`, waves 6–7). K2 generalizes the Part-6 telescope locally, as the design (L152)
   requires.
4. **N11-M1 and N11-M2** (wave 8) can run in parallel.
   - M2 must apply `FastConvex.toRealFastConvex` before `energy_free`.
   - Both must prove T3 before using `transfer_conditional`.
5. **N11-N `block`** (wave 9).
6. **N11-P provider** (wave 10): assemble it binder by binder (design L393–420), including the empty-G branch
   and the σ = −1 time reversal.
7. **Seal** (§3).
8. **Afterwards (lane P).** E11 is parked on `inp-p14-e11` (2 merge commits, no Lean). It is relaunched after
   the seal by first merging `inp` into it (offload tracker note); E12 follows.

## 7. Rulings and amendments touching N

Quoted from `docs/campaign/OVERNIGHT.md` on `main`; all times are UTC, 2026-10-27/28.

- **21:15 (L208), route.** "N-PARTIAL-CONVEX proof = Pöschel-type normal form with slow parameters (blueprint-N
  Part 11 …), not Nekhoroshev 1977's own route (its §10 lemma proofs are in the unpinned Part II)."
- **18:47 (L387), signed declarations vs literal nodes.** "signed declarations follow the signature file; the
  literal-node rule applies to unsigned exports only, and for a deliberately narrowed signed export the audit
  checks that every consumer's needs are met."
- **18:50 (L395), short names.** "the short-name rule governs unsigned helpers only; signed names follow the
  signature file. N11-B accepted without re-audit." The audit focus now reads "every SIGNED declaration =
  signature file" (19:08, L411).
- **19:27 (L415), critical path.** E11 "applies the N root `partialConvex_nekhoroshev`, a DRAFT_SORRY frozen
  anchor … N11 is the critical path for two frozen theorems."
- **20:50 (L434), `ext_flow`.** "Part 5's `KAM/Nekhoroshev/Averaging/Flow.lean` already owns that constant …
  the signed name is renamed to `ext_flow` (statement unchanged); `flow_real` does not clash." Applied in
  signatures L213, commit `c198ff11`, and design node table L191 / note L294–297 (`eedc66fe`).
- **20:55 (L440), GAP-A node gaps.** The landing of N11-O "only [gave] an existential mu0, not the explicit
  mu_a..mu_f formulas or the closed form of T_P … one follow-up package GAP-A fills the N11-O and T8 gaps as
  appended exports (no signed statement changes)."
- **21:01 (L446), N11-L1 accepted.** "Audit 1 failed L1 because `transverse_pairing` keeps the four bounds of
  stepN:p11:ef-C as premises. The design maps ef-C to the inside of L2's `energy_free` … N11-L1 accepted"
  (`N11-L1-audit-1-ruling.md`).
- **21:15 (L450), canonical_map positivity premise (owner to review).**
  - The ruling: "add `(hc : 0 < b.c)` after `φ` (a source positivity premise; consumers have it from
    `ExtNFHyp.radius_pos`/`slow_width_pos`)."
  - **Superseded in part.** Audit F2-1 found the consumer claim too broad for `iterative`.
- **Earlier general rules that apply to N.**
  - **09:00 (P45) and 13:08 (P810).** Proof cuts without signatures become internal helpers: distinct names,
    blueprint-node citations, no premise added to any signed declaration.
  - **14:05.** A whole-library name-clash check runs before every audit.
  - **16:05 and 17:00.** Signed renames `closure` → `amd_closure` and `avg` → `pg_avg` set the precedent for
    `ext_flow`.
  - **D29.** No new freezes overnight.

## 8. How the work was run (conventions to keep)

**The owner's two hard rules, verbatim:**

> 1. Never use `set_option maxHeartbeats` (or any heartbeat-budget override). A default-heartbeat elaboration
>    failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a
>    proof will not elaborate at default heartbeats, report it as a design signal.
> 2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules,
>    preserving public import paths as cheap facades.

`AGENTS.md` lists these as hard rules 1–2 among eleven. Rules 3–11 also bind: modules, no `axiom`/`sorry`
outside frozen drafts, frozen files read-only, no conclusion-shaped hypotheses, ambient types, builds,
quarantined providers, generated files, errata.

**Further conventions**

- Never use `EuclideanSpace`: use `Fin n → ℝ/ℂ` with max norms.
- No public helper may reuse a short name already used anywhere in KAM. Signed names are exempt (ruling 18:50).
- Never shadow a root Mathlib name that KAM uses.
- Import signed declarations (grep the fully qualified and short names first); never redefine them.
- Lines are at most 100 columns.
- One Lean process at a time, with `LEAN_NUM_THREADS=1` and `nice -n 5`, builds through the compile gate only.
  Never `lake clean`, `lake update` or `lake exe cache get` in a worktree.
- Never edit frozen files or the manifest. A frozen anchor is sealed only by changing its body to a short exact
  application of an audited provider (§3).

**Package workflow**

1. **One package = one worktree and branch off `inp`:** `/root/code/KAM-inp-<sfx>` on `inp-<sfx>`. Upstream
   branches still in audit may be merged in when they are needed.
2. **The prover brief** is `offload-main/<PKG>.md` plus `inp-prover-common.md`.
   - It names the design row, the node table and both design audits.
   - It requires the signed declarations to be copied **verbatim** from the signature file.
   - It summarizes the slice: "implement EVERY SIGNED declaration … AND every graph proof step the node table
     maps to them".
   - Provers stop and report on a statement that looks false.
3. **The prover's deliverables.**
   - It commits with `git -C <abs path>`.
   - It writes `.drafts/handoff-<PKG>.md` (files, nodes, approach, gate build, lint, `#print axioms`, errata)
     and touches `.drafts/READY-<PKG>`.
   - The orchestrator copies the handoff to `docs/tracks/N/audits/<PKG>-handoff.md` with an appended
     `AUDIT FOCUS:` line.
4. **Pre-audit checks:** reused short names, root shadows and whole-library name clashes.
5. **Independent audit.** A different model (GPT-6.1-Sol medium, D24) works refute-first under
   `inp-audit-package.md` and writes `docs/tracks/N/audits/<PKG>-audit-<R>.md`. Fixes get a delta round-2
   audit. The handoff and audit are committed on the branch ("handoff and independent audit (VERDICT)").
   **Audit focus, "Common to all" (verbatim):**

   > Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node
   > the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export
   > named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the
   > signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof
   > soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful
   > root shadow, lines <= 100.

6. **Landing.** The sub-orchestrator (never the prover) merges into `inp` ("Merge inp-<sfx>: … (audit …)"),
   regenerates `KAM.lean` with `scripts/gen_root_imports.py`, syncs the graph, and lands with
   `scripts/land-branch.sh inp` (merge, full build, lint, push).
7. **Graph status records only the literal node conclusion.** A node becomes PROVED only when its literal
   `SOURCE_CONCLUSION` is established, per the audit table, with `LEAN_REF` and `LEAN_NOTE` citing the
   declarations and the audit. Partial coverage stays NOT_STARTED with a note.
8. **Models used.** Provers were Claude Sonnet 5.5 in tmux, auditors GPT-6.1-Sol medium, orchestrators Opus
   5.5.

## 9. Known pitfalls seen on lane N

1. **Name clash.** The N11 signed `flow` collided with Part 5's `KAM.Nekhoroshev.flow`
   (`KAM/Nekhoroshev/Averaging/Flow.lean:228`); only the root import exposes such clashes. Run the whole-library
   clash check before every audit. The same kind of clash broke a landing at 14:05.
2. **Lean division by zero.** `PartialBlock.c = 2*Real.pi/(b.w/b.rB)^2` (`Setting.lean:79–80`) is 0 when w or
   rB is 0, and nothing in `PartialBlock` or `slowLoss` excludes that.
   - `preimage` and `transfer_conditional` therefore carry `(hbR : 0 < b.rB) (hbw : 0 < b.w)` (signatures L477,
     L531).
   - `ExtNFHyp` carries `radius_pos` and `slow_width_pos` (L347–348).
   - `canonical_map` now needs `hc`, while `iterative` has none: this is F2-C1.
   - Check positivity premises along every consumer edge.
3. **Literal-node completeness failures** cost a round each:
   - E2 audit-1: the combined Taylor display `et-taylor` was missing.
   - E3 audit-1: the dm-field transport and analyticity, and the real-Hessian identification, were missing.
   - L1 audit-1: ef-C was kept as premises.
   - F2 audit-1: a consumer edge.

   Briefs must list every node mapped to the modules, not only the signed declarations.
4. **The shared ExtFlow module.** The signed `def extFlow` lives in `Partial/ExtFlow.lean`, a module not in the
   design's module list. F1 imports it and must not redefine it.
   - F1 also adds a public `extGauge` (`Composition.lean:66`). F2 has a different **private** `extGauge`
     (`CanonicalMap.lean:46`) in the same namespace.
   - **UNVERIFIED** whether this trips the short-name or name-clash checks. The F1 audit should check it.
5. **Unsigned helpers versus nodes.** Conditional or partial helpers need distinct names:
   `canonical_map_core` (all clauses except canonicity), `transfer_conditional` (premise T3), `uniform_data_periodic`.
   They never stand in for the node theorem. A conditional `canonical_map_of_pos` was renamed to the signed name
   only after the ruling.
6. **Branch noise.** Branches merged other in-audit branches, so `git diff inp...HEAD` shows inherited files
   and "multiple merge bases" warnings. Scope every audit with "Audit ONLY <files>".
7. **Size overruns.** Domain.lean reached 862 lines against an estimate of 450, and lane P's P11A-P2 needed
   several thousand lines against 750 (ruling 20:40). Split at theorem boundaries well before the 1500-line cap.
8. **Lint noise.** "KAM.lean is out of date" is expected in worktrees; only the integrator regenerates it.
9. **Memory.** A landing was OOM-killed at 17:02 by stacked Lean processes. Keep to one Lean process per agent.

## 10. Open questions for the owner and the new team

1. **F2-C1 / `hc`** (blocks N11-H). Does the owner accept the 21:15 `hc` premise on `canonical_map`? And how
   does `iterative` obtain positivity?
   - (a) Add a source positivity premise to `iterative` (for example `0 < b.rB`, `0 < b.w`) and check its
     K1/K2 callers, which have `ExtNFHyp.radius_pos`/`slow_width_pos`.
   - (b) Prove a c = 0 canonicity branch and keep both types unchanged. The F2 prover believes c = 0 holds,
     because q and p are frozen, but needs a separate proof (**UNVERIFIED**).
2. **The shared `ExtFlow.lean` module.** Keep it and add it to the design's module table, or fold it into an
   existing module? Either way, update design Appendix A for `hc` (§2) and publish
   `docs/tracks/N/design/N11-SIGNATURES.md`.
3. **The integration branch for lane N.** Keep using `inp`, which lane P also uses and the main orchestrator
   lands, or a new lane-N branch off `main`? Who runs `scripts/land-branch.sh` for N work?
4. **The A/B literal-node gaps** (wfield, constants, ext-class, s-nf#data). Fill them with a GAP-style package,
   or accept them as non-blocking for the seal? Sealing needs only the provider; the graph's closure needs the
   nodes.
5. **The F1 audit scope.** Besides "Common to all", confirm the helper names (`extGauge`, `cubeE`,
   `mem_Dom_of_scaled_le`, `q_facts_ext`) and that the `ext_taylor_second` use matches `tr-taylor`.
6. **Publication.** Push the local-only branches and worktree reports. Decide whether the off-repo briefs and
   tools (`.drafts/briefs/`, `orchestrator-tools/`) go into the repo for a team on another machine.
