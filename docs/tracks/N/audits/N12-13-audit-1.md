# N12-13 independent package audit 1

**Verdict: PASS WITH NOTES for N12-13 (`avgCell`, `transport`).** No mathematical or statement-fidelity defect found. The targeted build, exact-design signature probe, permitted-axiom checks, and kernel replay passed. Source lint has only the explicitly permitted stale generated-root failure. This is an infrastructure package: it contains no provider export and seals no frozen anchor. Neither `averaging_mean` nor `averaging_most` is certified seal-ready by this audit.

## Scope and evidence

Audited worktree: `/root/code/KAM-inp-n1213`, HEAD `1dfeb813f0180bcc118acd04c0017cdcd7aa0677` (`1dfeb81 N12-13: Transport (avgCell, transport)`). Read the supplied AGENTS instructions, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and `docs/tracks/N/audits/N12-13-handoff.md`. The user's explicit report destination overrides the generic brief's main-worktree destination.

`git diff --stat inp...HEAD` and `git diff inp...HEAD --numstat` show exactly one source change: `KAM/Nekhoroshev/Averaging/Transport.lean`, 196 insertions. The `inp` ref inspected was `05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2`. The focus comparison `git diff inp-n1210b...HEAD -- KAM/Nekhoroshev/Averaging/Transport.lean` is the same complete new module; the comparison base is `921475c33cb76dba47b677e348fce29127afa7b2`. Other differences against that older branch are outside the expressly limited Transport audit.

Statement authorities: `docs/tracks/N/design/N12-LEAN-DESIGN.md` rows 189–193 and 288, proof plan 359–366, signatures 869–878; `/root/code/KAM-inp/.drafts/design/N12Signatures.lean:376–384`; `blueprint-N/parts/p12-averaging.tex:218–230`; and the averaging section of `docs/tracks/N/statement.md`. Also read `/root/code/KAM-inp/docs/tracks/N/design/DESIGN-N12-design-audit-1.md` and `DESIGN-N12-design-audit-2.md`. These two design audits and the signature file are absent at their handoff-relative locations in this package worktree; the named main-worktree copies were used explicitly. Revision 2 closes the earlier corrector-derivative issue, which is outside this package.

Source SHA256 (`Transport.lean`): `dfd6c71a64c0b8f10e4fa616d50e46545f3d81ede380dffc19bda2df1f0a9936`.
Design SHA256: `d66059fe35c7b3f76307ae60df90aa3da66ea089cd3ec073b39cbe2ffd1b6370`.
Signature-file SHA256: `0ad9cf0f84ffc435f1d85360516ad94f5ec100ff4a53c76d410f9e7d3b028369`.

## Declaration and node review

All short declaration names below are in `KAM.Nekhoroshev`; locations are in `KAM/Nekhoroshev/Averaging/Transport.lean`.

| Node / role | Lean declaration | Verdict | Reason / location |
|---|---|---|---|
| `bpN:p12:s-trans#data`, cell definition | `avgCell` | PASS | L36–37: exact design definition, half-open unit angle cube, unrestricted actions. The finite count for compact K belongs to downstream `stopped`, as the design row specifies. |
| Product-volume infrastructure | `avgPhase_isAddHaar` | PASS WITH NOTES | L40–41: standard `Measure.prod.instIsAddHaarMeasure`; exported instance, contrary to handoff wording “Local instance”. No new measure or norm. |
| Cell Borelness | `measurableSet_avgCell` | PASS | L45–52: finite-coordinate Borel inequalities; no extra premises. |
| Cell covering | `mem_avgCell_floor` | PASS | L54–55: coordinatewise floor supplies a cell for every phase point. |
| Cell uniqueness | `avgCell_unique` | PASS | L57–66: integer endpoints and strict upper bounds force identical indices. |
| Cell partition | `disjoint_avgCell` | PASS | L68–70: distinct cells are disjoint by uniqueness. |
| `stepN:p12:tr-cells`, translated piece | `cellPiece` | PASS | L77–78: preimage under addition of `(k,0)` is exactly translation back by `(k,0)` of `S ∩ avgCell k`. |
| Piece Borelness | `measurableSet_cellPiece` | PASS | L80–82: measurable translation preimage of the measurable intersection. |
| Fundamental-cell inclusion | `cellPiece_subset` | PASS | L84–93: subtracts the cell index and preserves the action coordinate; arbitrary G. |
| Translation of integrals | `lintegral_cellPiece` | PASS | L95–100: Haar-preserving translation and measurable embedding; valid for arbitrary ENNReal g and arbitrary S, a legitimate strengthening. |
| `stepN:p12:tr-sum`, conditional measure helper | `lintegral_le_of_disjoint_cellPieces` | PASS | L103–128: explicitly conditional, separately named helper for arbitrary S/G. Disjointness is proved, not assumed, at the transport application. |
| `bpN:p12:transport` | `transport` | PASS | L137–190: exact signature, including d, arbitrary real ε, t, nonnegative-time guard, measurable g/D, one initial cell, local domain inclusion, and endpoint actions in G. No new constant or premise. |
| `stepN:p12:tr-cov` | `transport`, L143–160 | PASS | C¹ on open Ω gives derivatives on D; inverse gives injectivity; determinant one removes the Jacobian factor. Image Borelness is justified by Lusin–Souslin. |
| `stepN:p12:tr-cells` | `transport`, L164–190 | PASS | Periodicity places shifted initial points in Ω. Injectivity makes shifted preimages equal; common initial half-open cell forces integer difference zero. |
| `stepN:p12:tr-sum` | `transport` via `lintegral_le_of_disjoint_cellPieces` | PASS | Translated pieces are disjoint, lie in `[0,1)^n × G`, and have unchanged integrals. Product volume and Tonelli remove the unit-volume angle cube. |

The auxiliary lemmas refine the blueprint proof steps; they do not replace its main statement. In particular, the only disjointness premise is on the generic measure helper, and `transport` discharges it using flow properties. `hDO` also implies the blueprint's initial action-ball restriction because `avgOmega` includes `avgDomain = univ ×ˢ actionBall n R`. No conclusion-shaped hypothesis or assumed change-of-variables identity appears. The arbitrary-real-ε strengthening is already part of the approved design. The unused `ht` is retained to preserve the exact interface.

## Definitions, carriers, and imports

New definitions: `avgCell` is literally the intended half-open cube times unrestricted actions over its entire carrier; `cellPiece` is literally the translated image piece over its entire carrier. No new abbrev or structure. Both are in an `@[expose] public noncomputable section`. The new instance `avgPhase_isAddHaar` supplies a proof for existing canonical product Lebesgue volume. It does not alter the measure or max-norm instances, but is globally exported rather than local; this is a minor handoff description discrepancy, not a mathematical failure.

Read the upstream standing-data and flow definitions and the relevant frozen definitions/averaging anchors. `AvgPhase n` is `(Fin n → ℝ) × (Fin n → ℝ)`. The standing `AveragingData` fields are analytic source premises, positive radii, dimension, and rank; no transport estimate is bundled. `avgG` is the closed max-norm action ball of radius `3*R/4`. `avgFlow` comes from the existing maximal-solution representation. Its off-domain default is never used: every differentiability, inverse, determinant and equivariance application is guarded by Ω membership, including the shifted points.

A recursive source-import check of all 58 project modules in Transport's closure found 26 frozen definition modules, all in the manifest, **zero frozen theorem modules and zero provider modules**. Hence no `DRAFT_SORRY` anchor or other provider is imported, even transitively. Provider-versus-frozen ABI and proposed seal-body tests are not applicable: no provider or anchor body is supplied or changed by N12-13. The relevant frozen averaging anchors remain outside this package's completion claim.

## Independent checks

Lean/Lake audit invocations were serialized. The targeted build, signature/axiom probe and replay were run with `LEAN_NUM_THREADS=1` and `nice -n 5`; no heartbeat or recursion-budget changes were made. An initial lint invocation used plain `sh scripts/lint_sources.sh`; a final repeat uses `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh` so its ABI subprocess also inherits those settings.

### Targeted build

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1213 KAM.Nekhoroshev.Averaging.Transport
```

The inspected gate runs `nice -n 5 lake build` and was allowed to wait. Exit **0**. Key output:

```text
[inp-gate] slot 1 acquired 10:19:31 for KAM.Nekhoroshev.Averaging.Transport
⚠ [2968/2968] Replayed KAM.Nekhoroshev.Averaging.Transport
warning: KAM/Nekhoroshev/Averaging/Transport.lean:137:27: Variable name `ht` is not explicitly referenced.
Build completed successfully (2968 jobs).
```

Also replayed pre-existing unused-variable/section-variable/style warnings in `PicardFamilies` and `LocalDependence`; no error or resource-limit failure.

### Signature and axiom probe

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N1213Audit.lean
```

Exit **0**. The probe copied the complete `transport` telescope and conclusion directly from the external signature file, replaced only the declaration name with `example`, and used:

```lean
by
  exact transport d ε ht g hg ell hD hDO hcell hDG
```

A separate `rfl` example checked the exact `avgCell` body. All nine new public theorems and the instance were printed:

```text
'KAM.Nekhoroshev.measurableSet_avgCell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.mem_avgCell_floor' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgCell_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.disjoint_avgCell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.measurableSet_cellPiece' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.cellPiece_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.lintegral_cellPiece' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.lintegral_le_of_disjoint_cellPieces' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.avgPhase_isAddHaar' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Averaging.Transport
```

Single invocation, exit **0**. Complete output:

```text
replaying KAM.Nekhoroshev.Averaging.Transport
```

There is exactly one new lemma module and no provider module to add to this invocation. Upstream packages are dependencies, not independently re-audited here.

### Source lint and protected paths

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, with only the permitted generated-root issue:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (552 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No root regeneration was performed. No forbidden proof escape, resource override, forbidden ambient type, module-format defect, oversized source, or line-width error was reported. Transport has 196 total lines.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check
```

Both exit **0**, no output. The first confirms no protected-path changes. The pre-existing untracked handoff was preserved. The only repository file written by this audit is this report; its temporary Lean probe is removed after use. No git mutation or commit.

## Uncertainties, errata, and deviations

No suspected blueprint or pinned-source defect was exposed by this Transport proof; no source repair is proposed. The already documented Nei76 maximum/integral issue is outside this transport package, and this proof uses only fixed-time transport. No global flow domain, global off-domain regularity, image angle-box bound, finite-integrability premise, or trajectory-confinement estimate is inserted. ENNReal integrals allow infinite values without requiring finiteness assumptions.

Notes are limited to the allowed stale generated root, the harmless unused nonnegative-time argument, and the handoff's inaccurate “Local instance” description at `Transport.lean:40`. The independent review covers the Transport implementation and its use of upstream interfaces, not the full proofs of upstream flow modules or final frozen averaging providers.
