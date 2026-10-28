# N12-07 independent package audit 1

Overall verdict: **PASS WITH NOTES** for `bpN:p12:lambda`, `stepN:p12:la-inj`, and `stepN:p12:la-cpt`. No blocking mathematical, statement-fidelity, definition, or hygiene finding. The sole check exception is the explicitly permitted stale generated root. This is infrastructure approval for Rank; no frozen theorem is proved or declared seal-ready by this package.

## Scope and authority

Audited 2026-10-28 in `/root/code/KAM-inp-n1207` at HEAD `41b6f5170f8610bda2030f5bf847762ca4625cc2`, comparing with `inp` at `ef8fc426c638557035e6101216aad4ef8b8a570e` using `git diff inp...HEAD`.

Read AGENTS, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the local handoff, design row N12-07 and its signature/proof plan, both design audits, track-N statement, the relevant frozen definitions, blueprint Part 12 and its rank-node packet. The two design audits live under `/root/code/KAM-inp/docs/tracks/N/design/`; the signatures live at `/root/code/KAM-inp/.drafts/design/N12Signatures.lean`. Those paths were read only. The report destination follows the user's explicit override of the generic brief.

`git diff --stat inp...HEAD` reports Setting (112 lines), Field (219 lines), and Rank (186 lines), 517 insertions total. Per AUDIT FOCUS, only `KAM/Nekhoroshev/Averaging/Rank.lean` is audited as new package code; Setting, Norms, and frozen definitions were inspected for its prerequisites. No independent re-audit of Field or all of N12-01 is claimed. The initially untracked handoff was preserved.

Relevant snapshot SHA-256:

| Input | SHA-256 |
|---|---|
| Rank.lean | `359a449532d1ca3b3b4981f982cd72787158c399b0985abc9e35029235913cce` |
| N12-LEAN-DESIGN.md | `d66059fe35c7b3f76307ae60df90aa3da66ea089cd3ec073b39cbe2ffd1b6370` |
| N12Signatures.lean | `0ad9cf0f84ffc435f1d85360516ad94f5ec100ff4a53c76d410f9e7d3b028369` |
| blueprint-N/parts/p12-averaging.tex | `dd549dc5c3069e1a185767b5fa580d979963fa920a4b9e7939529047d13ebbfc` |

## Declaration and node ledger

Names in the table are under `KAM.Nekhoroshev`. Line numbers refer to Rank. Every new public declaration has a row.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| la-cpt regularity | `AvgRank.contDiffOn_freq` :30 | PASS | Genuine frozen frequency map is C² on the real action domain, derived from the frozen real C³ clause; no extra regularity premise. |
| Rank domain | `AvgRank.avgG_subset_actionBall` :39 | PASS | Closed max-norm ball of radius 3R/4 lies inside the rank domain B(0,R), using R>0. |
| Continuity domain | `AvgRank.avgG_subset_domain` :45 | PASS | Same compactum lies inside the genuine real complex-neighborhood slice, using s>0. |
| Matrix identification | `AvgRank.fderiv_apply_eq` :52 | PASS | Exact coordinate expansion of Dω with `avgM`; unconditional linear-map identity, no transpose or index reversal error. |
| Euclidean conversion | `AvgRank.euclid_sq` :60 | PASS | Exact sum-of-real-squares identity, all real vectors and all dimensions. |
| la-inj algebra | `AvgRank.false_of_orth` :66 | PASS | General surjection/orthogonality contradiction for a unit vector. Conditional auxiliary is separately named; its orthogonality premise is discharged in gap_pos. It even permits arbitrary surjective g without linearity. |
| Auxiliary definition | `AvgRank.gap` :79 | PASS | Literal finite sum of squared transposed-matrix coordinates plus squared frequency pairing. |
| `stepN:p12:la-inj` | `AvgRank.gap_pos` :82 | PASS | Derives positivity on G × sphere from each disjunct of the literal frozen rank predicate; no frequency lower bound or extra rank premise. |
| `stepN:p12:la-cpt`, continuity | `AvgRank.gap_continuousOn` :121 | PASS | Derives continuity from C² frequency regularity on an open neighborhood of G. |
| `stepN:p12:la-cpt`, compactness | `AvgRank.isCompact_sphere` :152 | PASS | Euclidean unit sphere is closed and lies in the max-norm closed unit ball; finite-dimensional compactness applies to the Pi carrier. |
| `bpN:p12:lambda`, completion of la-cpt | `«lambda»` :165 | PASS | Exact design signature; compact positive minimum and its positive square root give the uniform squared bound. |

There is no provider export or frozen theorem anchor assigned to N12-07. Provider/frozen-type and proposed seal-body probes are therefore inapplicable. Instead, a fresh theorem with the literal design signature was elaborated with body `by exact KAM.Nekhoroshev.«lambda» d`; a separate text comparison confirmed the production signature equals N12Signatures:264–267 exactly before its proof body. Design:756–761 and blueprint p12:135–142 agree on the carriers, quantifiers, Euclidean gauge, squared lower bound, and rank alternatives.

## Definition and premise audit

The only new def/abbrev/structure is `AvgRank.gap`. Its body is the intended algebraic expression for every h and pair (I,e), with finite sums and no choice, division, conditional fallback, or supremum. Existing `fderiv` is totalized, but positivity and continuity are asserted only under the genuine analytic/rank premises on the valid domain. No off-domain derivative value is used to establish a source conclusion. The exposed noncomputable public section exposes its body.

The imported `AveragingData` contains n≥1, R,s>0, the frozen analytic h/f predicates, and the exact frozen global rank disjunction. It contains no desired estimate or transversality field. `avgG` is the closed maximum-norm ball of radius 3R/4, `avgM` is entry (i,j) of the real derivative of the frozen frequency map, and `euclid` is sqrt of the sum of coordinate norm squares. All ambient vectors are Pi types.

If gap were zero, its nonnegative summands force Mᵀe=0 and e·ω=0. The proof expands Dωv via avgM, obtains orthogonality to its full range, and invokes surjectivity to choose a preimage of e. Branch A uses only Dω being onto and permits ω=0. Branch B uses the augmented onto map (v,c)↦Dωv+cω. Its nonzero-frequency clause need not be used for this weaker algebraic consequence. Neither alternative is strengthened or replaced.

Continuity is established on an open real action neighborhood before restricting to G × sphere. Compactness and a genuine attained minimum then supply positive lam. The empty-product branch chooses 1 only when the universal target is vacuous; it supplies no junk value at a nonempty carrier. Although the interface carries f through standing data, the minimized function and compact set depend only on n,R,h; continuity/rank proofs use h's standing premises. There is no new dependence on ε, a direction e, or an action I. The graph's n,R,s,h constant scope is respected.

## Independent checks

All commands below ran from `/root/code/KAM-inp-n1207`, sequentially with no overlapping auditor-owned Lean/Lake invocations. No heartbeat, recursion-depth, or synthesis-budget override was used.

### Targeted compile gate

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1207 KAM.Nekhoroshev.Averaging.Rank
[inp-gate] slot 1 acquired 08:04:50 for KAM.Nekhoroshev.Averaging.Rank
Build completed successfully (2903 jobs).
exit 0
```

### Signature probe and all theorem axioms

Temporary probe `.lake/abi-scratch/N1207Audit.lean` imported only Rank, elaborated the fresh signature theorem described above, and issued #print axioms for every new public theorem. Command and complete output:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N1207Audit.lean
'KAM.Nekhoroshev.AvgRank.contDiffOn_freq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgRank.avgG_subset_actionBall' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgRank.avgG_subset_domain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgRank.fderiv_apply_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgRank.euclid_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgRank.false_of_orth' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgRank.gap_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgRank.gap_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgRank.isCompact_sphere' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.lambda' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

### Kernel replay

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Averaging.Rank
replaying KAM.Nekhoroshev.Averaging.Rank
exit 0
```

Rank is the package's only new lemma module; there is no provider module to add to this invocation.

### Lint and repository integrity

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (469 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The nonzero exit is exactly the brief's allowed generated-root exception; no root regeneration was attempted. An initial invocation of `sh scripts/lint_sources.sh` omitted the explicit resource environment/niceness, so it was rerun as shown above after it finished; it produced the same output and exit. This invocation mistake is an auditor execution deviation, not a package finding.

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(no output; exit 0)
git diff --check inp...HEAD
(no output; exit 0)
git diff --check
(no output; exit 0)
```

Rank is 186 total lines and has the copyright header, module command, public imports, module docstring, and exposed public section. A token scan found no sorry/admit/axiom/unsafe/opaque/set_option/EuclideanSpace token in Rank. Its project import closure contains 37 KAM modules, including 18 frozen definition modules and no provider or frozen theorem module. Thus no imported DRAFT_SORRY theorem or provider quarantine violation occurs. The frozen ABI and source guards also pass.

## Findings, limits, and closeout

No suspected new blueprint or pinned-source defect was found in the scoped transversality argument. In particular, blueprint p12:140 says to choose z with Az=e and deduce |e|²=0 under orthogonality; the Lean proof implements precisely that argument for both matrix shapes. Blueprint p12:141 says the positive continuous function has a positive minimum on G × sphere; the Lean proof establishes those premises and handles the vacuous empty case explicitly.

The prior design audit's wreg omission and hash-label correction are resolved in design audit 2 and concern other scope; no reopening or proof certification of those modules is implied. No public source erratum or formalization deviation is proposed for Rank. The only remaining package note is the permitted stale generated root. This report establishes the scoped helper/node result, not averaging-root closure, a source-PDF audit, or seal readiness of either frozen averaging theorem.

Only this report was added as repository content by the auditor. The temporary probe was removed after checks. No production, frozen, manifest, generated file, or git state was changed.
