# Independent audit 1: N89-P3

Overall verdict: **PASS WITH NOTES** for the scoped infrastructure package. No mathematical, signature, definition, or proof blocker was found. The only scoped implementation notes are unused binders in `local_field`; the generated-root lint exception is explicitly permitted by the audit brief. No frozen anchor is implemented or sealed by this package, so a provider/frozen-type comparison and seal-body probe are **not applicable**. This verdict does not establish `block_stab`, `thm1`, or headline closure.

## Scope and authority

Audited on 2026-10-28 in `/root/code/KAM-inp-n89p3`, HEAD `8ef61bd2421488a298342d89254c62f221d1a585` (`N89-P3: block_hyp`). Read AGENTS.md, PLAN.md, DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the supplied handoff, the current N89 design (especially row N89-P3, line 314, and proof plan, lines 371–374), track-N statement, relevant frozen definitions and theorem context, and blueprint Part 9.

The handoff's AUDIT FOCUS restricts proof auditing to `KAM/Nekhoroshev/Poschel/BlockHypotheses*.lean`. There is exactly one such file: `BlockHypotheses.lean`, 375 lines, SHA-256 `af9e628c2b335ed044b74f73a6222455867630ffe66ed5b8e85943778e40cfa4`.

Both requested comparisons were performed:

```text
git diff --stat inp...HEAD
 KAM/Nekhoroshev/Poschel/BlockHypotheses.lean    | 375 +...
 KAM/Nekhoroshev/ResonanceGeometry/Covering.lean | 250 +...
 2 files changed, 625 insertions(+)

git diff inp-n89g7...HEAD --numstat -- 'KAM/Nekhoroshev/Poschel/BlockHypotheses*.lean'
375	0	KAM/Nekhoroshev/Poschel/BlockHypotheses.lean
```

`inp` resolved to `05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2`; `inp-n89g7` resolved to `958496d70cc9dc5ef25068aba9ffe0b9b5a18efa`. The unrestricted three-dot comparison with `inp-n89g7` includes unrelated branch-history changes; the scoped comparison above is the requested implementation boundary. `Covering.lean` is a consumed dependency, not a second independently audited package in this report.

The design audit reports are at `/root/code/KAM-inp/docs/tracks/N/design/DESIGN-N89-design-audit-{1,2}.md`; the signatures are at `/root/code/KAM-inp/.drafts/design/N89Signatures.lean`. The handoff's local `.drafts` location is absent in this worktree. Read the main-worktree evidence directly. Signatures SHA-256: `01270a67c964001a1f6f86a2416ce572fee94f326c34cec43fcef7de0fea4b88`, matching design audit 2. Earlier design-audit F1/F2 concern projection coverage and early parameter ownership, not outstanding P3 signature defects.

## Declaration-by-declaration verdicts

Public names below have namespace `KAM.Nekhoroshev`. Private helpers are listed by their source names, not their generated private names. Line numbers refer to the audited implementation.

| Node / component | Lean declaration and line | Verdict | Reason |
|---|---|---|---|
| `stepN:p9:t1-b#full-rank-zone` | `full_rank_zone`, 130 | PASS | Exact design type. Proves top maximality, radius and delta identities, projector identity, and the strict threshold equivalence for every I in P. |
| `bpN:p9:block-stab#frequency-size` | `block_frequency_radius`, 256 | PASS | Exact design type. Nonnegative half-radius and strict half-radius < r0 follow from Valid and r0 > 0, including top rank. |
| `bpN:p9:block-stab#frequency-size` | `blockBall`, 266 | PASS | Exact design type and body; genuine guarded ball at I0 with radius rLambda/2. |
| `bpN:p9:block-stab` data only | `blockAdm`, 275 | PASS | Exact design body, constants 5 and 288, period-one exponent, full-rank disjunct and multiplicative zero-frequency branch. Does not claim block stability. |
| `bpN:p9:block-stab#local-field` | `local_field`, 281 | PASS WITH NOTES | Exact design type. Both local field identities use open-neighbourhood equality. S and hr are unused, as permitted by the fixed signature. |
| `bpN:p9:block-hyp`, parts (a)–(f), steps `bh-dom/eps/rad/nr/lip/small` | `block_hyp`, 303 | PASS | Exact design type, all conjuncts retained, no extra premise or wider constant dependence. |
| Tube restriction | private `polyNbhd_single_sub`, 40 | PASS | Explicit subset witnesses; radius comparison preserves strict tube membership. |
| Tube restriction | private `realNbhd_single_sub`, 47 | PASS | Same witness on the real max-norm tube. |
| Tube restriction | private `realStrip_single_sub`, 54 | PASS | Product inclusion from real tube inclusion. |
| Tube restriction | private `Dom_single_sub`, 58 | PASS | Unchanged angle strip and smaller action tube. |
| Analytic-class restriction | private `inClass_single`, 62 | PASS | Restricts holomorphy and periodicity, without assuming their desired conclusions. |
| Reality restriction | private `realOn_single`, 67 | PASS | Restriction to the smaller domain. |
| `bh-lip` analysis | private `fderiv_freq_bound`, 79 | PASS | Holomorphy on an open set supplies derivative regularity; Hessian symmetry identifies D(freq); Euclidean output to max and max input to Euclidean cost sqrt(n) once. |
| Real frequency bridge | private `im_eq_zero_single`, 109 | PASS | Evaluates source reality at angle zero using s > 0; no global reality assertion. |
| Pairing bridge | private `dotC_realInclusion`, 115 | PASS | Complex pairing is exactly the complex cast of the real integer dot product. |
| Cover prerequisites | private `cover_valid`, 125 | PASS | Extracts the already-proved final conjunct of elementary; Valid is not an added premise. |
| `bh-eps/rad/small` numerics | private `block_arith`, 182 | PASS | Derives radius positivity, exact numerical identities, epsilon smallness, Mr bound and bottom-lattice smallness from standing/source data. |

## Refutation checks and definitions

Compared the **entire** types of all four new public theorems against the design signatures after whitespace normalization, including the conclusions after every `let`. All four match. Both new definition types and complete bodies match. Elaborated fresh theorems copying the four design signatures and applying the implementation with exactly the design's explicit binders:

```lean
full_rank_zone S heps heps0
block_frequency_radius S heps heps0 Λ hΛ
local_field S hI hr hrr
block_hyp S heps heps0 hfb Λ hΛ I0 hI
```

Also elaborated `example : @audit_blockBall = @blockBall := rfl` and `example : @audit_blockAdm = @blockAdm := rfl`, where each audit definition copies the design body. These checks use actual production imports, not the design's placeholder proofs or copied upstream excerpts.

Definition classification (exhaustive: two defs, no new abbrev/structure):

- `blockBall`: exact constructor of the upstream `FrequencyBall S`; center I0, source membership, radius c.radius Lambda / 2 and proved guards. Its inherited points are the closed **Euclidean** ball, with the existing attained-supremum API. There is no new supremum, chosen maximum, fallback point, or replacement norm.
- `blockAdm`: total proposition on its full declared carrier, exactly the design's disjunction and multiplication inequalities. For arbitrary signed parameters it means those literal inequalities; the physical infinite-time reading is used under the proved positive setting. Full rank admits every time directly. For intermediate rank and Om=0, nonnegative right-hand side under the setting makes every time admissible. No division by Om or eps appears.

`block_hyp` uses action-block membership only for I0 in P and frequency block membership. It restricts the original h, f, complex Hessian bound, quasi-convexity, reality, periodicity and WBound to the singleton tube. Nonresonance uses `freq_realInclusion`, the literal complex/real dot identity, and `cutoffs` at Ka <= K. Closeness uses the attained orthogonal complement point from `projection_distance`; bottom rank is covered by the positive auxiliary delta, without inventing a lambda-zero zone identity. Numerical epsilon control uses rBottom <= r and the exact elementary identity eps = m rBottom^2 / 2^10. The Mr <= ell/2 step uses the existing source-route radius premise, not an assumed block bound.

`full_rank_zone` proves lattice top = real top by dimension, projector = id by its fixed-point property, and the n+1 stratum empty by its dimension guard. The open zone gives `< m*r0/8`, not `<=`. `local_field` proves the zero extension equals the total Hamiltonian in a neighbourhood of each interior point, then uses `EventuallyEq.fderiv_eq`; there is no false global equality or boundary derivative assertion. The unused S and hr show a stronger local fact is available; they do not weaken the fixed export.

The setting was inspected: its fields are source/standing positivity, dimension, analytic/reality/class/bound and quasi-convexity data. No block estimate, orbit confinement, normal form, or final conclusion is hidden in a field, instance or extra premise.

## Independent validation

All Lean-related commands below were run sequentially with `LEAN_NUM_THREADS=1` and `nice -n 5`. No heartbeat, recursion-depth or synthesis-budget override was used. No clean, update, cache fetch, full-library target or dependency-package mutation was requested.

Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n89p3 KAM.Nekhoroshev.Poschel.BlockHypotheses
```

Exit 0; output included:

```text
[inp-gate] slot 2 acquired 10:47:46 for KAM.Nekhoroshev.Poschel.BlockHypotheses
Build completed successfully (3235 jobs).
```

The target was replayed. Exact warning locations/names: inherited `Stability/Gradient.lean:168:5` hgr; `ResonanceGeometry/Maximal.lean:249:25` hK; `ResonanceGeometry/Blocks.lean:34:30` hK and `:35:5` hlam; scoped `Poschel/BlockHypotheses.lean:281:21` S and `:282:44` hr. Each warning says `Variable name ... is not explicitly referenced.` No error or resource-budget failure.

Signature/body/axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N89P3Audit.lean
```

Exit 0. Exact axiom output:

```text
'KAM.Nekhoroshev.full_rank_zone' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.block_frequency_radius' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.blockBall' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.blockAdm' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.local_field' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.block_hyp' depends on axioms: [propext, choice, Quot.sound]
```

Here Lean prints `choice` for the permitted classical choice axiom. No sorryAx or additional axiom occurs.

Kernel replay, one invocation for the sole scoped module (there is no provider module or separate scoped lemma module):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Poschel.BlockHypotheses
```

Exit 0; exact output:

```text
replaying KAM.Nekhoroshev.Poschel.BlockHypotheses
```

Static checks: 375 lines, required copyright/module/public imports/module docstring/`@[expose] public noncomputable section`; both defs are exposed. Forbidden-token/resource-override scan found zero matches. No ambient EuclideanSpace, unsafe axiom mechanism, or local option override. The recursive KAM import closure contains 77 modules, no provider and no frozen theorem module; all 27 imported frozen definition modules are manifest SEALED. Therefore no imported DRAFT_SORRY anchor is used.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check
git diff inp...HEAD --check
```

All exit 0 with empty output. Repository changes by the auditor are limited to this report; the scratch probe is removed after validation. The pre-existing untracked handoff is preserved.

Lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, with exactly the brief-permitted stale-root failure and no other diagnostic:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (553 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

This is not an unconditional lint exit-0 claim. The root was not regenerated; the orchestrator owns that operation.

## Source/blueprint defects, deviations and remaining limits

No new suspected mathematical source or blueprint defect was found in the scoped implementation. No statement or source deviation was introduced by this auditor. The following **inherited, explicitly disclosed** qualifications matter to P3 and qualify the handoff's unqualified “Uncertainties / deviations. None” and “Suspected errata. None”. These are observations from the pinned blueprint/design, not a fresh PDF audit:

1. `blueprint-N/parts/p9-poschel-theorem1.tex:146`, and design lines 276–279, record Pos93 p.190/p.204 as printing `r0 <= 4l/m` and “The stability estimates now apply to all blocks simultaneously, if we have r0<=4l/m”. That bound does not imply `M*r0 <= ell/2` on the full-rank block. This route intentionally uses the stronger standing premise `r0 <= ell/(2*M)`; `block_arith` derives `M*r <= ell/2` from it. This is the existing proof-gap repair/strengthened source premise, not a new premise added by P3 or a claimed numerical misprint. The frozen statements were not changed.
2. Blueprint line 147 and design lines 280–282 disclose the norm adaptation: geometric cutoff K, analytic cutoff K/sqrt(n), max/ell-one norms and period-one exponent `2*pi*(K/sqrt(n))*s/6`. P3 retains that factor in both `blockAdm` branches and the sqrt(n)*M derivative bound. It does not claim the printed Euclidean-framework exponent unchanged.
3. Blueprint line 149 and design lines 283–285 quote the printed exceptional condition “except when ||omega(I0)||<=mr0/8” and radius r0. The design's strict `<` zone threshold and later r0/2 estimate are the disclosed sharper route; `full_rank_zone` uses exactly the strict threshold. No endpoint was silently moved by the implementation.
4. Design lines 273–275 explain zero-rank auxiliary closeness: the resonance space at bottom is all space and auxiliary delta is positive. P3 relies on the correct `cutoffs` result, not a false bottom-rank identity with a zone parameter lambda(0).

There is no requested frozen anchor export here, so no per-anchor seal verdict is asserted. The four public theorems and two definitions are ready for their designed downstream use subject to the notes above. Later stopped stability, headline conversion and all other packages remain outside this audit's closure claim.
