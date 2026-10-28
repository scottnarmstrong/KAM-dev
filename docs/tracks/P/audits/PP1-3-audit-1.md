# PP1-3 independent package audit 1

Verdict: **PASS WITH NOTES** for `bpP:p1:torus-union` and all PP1-3 public exports.
The package is valid infrastructure. It seals no frozen theorem and does not prove
P-G, P-PLANAR, or P-FIXED. The notes concern inherited generated-file differences
and already documented proof-plan issues; no PP1-3 implementation repair is required.

## Scope, authority, and immutable inputs

Tier 2, refute-first statement/definition/proof audit, performed independently of
the prover on 2026-10-28. Only `KAM/Planetary/Hamiltonian/TorusUnion.lean` is in scope.
The prompt's exact worktree report path overrides the generic brief's main-worktree
output instruction. No source, frozen file, manifest, generated file, or git state
was changed. Temporary checks live under `.lake/abi-scratch/` and their Lean sources
are deleted after use. No delegation or external messages were used.

Read the supplied brief, AGENTS.md, PLAN, DECISIONS, handoff and AUDIT FOCUS,
Part 1 design and design audit, source blueprint, relevant track-P conventions,
frozen Phase definition, and the three original frozen track-P theorem surfaces.
There is no provider or frozen theorem implemented by this package, so provider/type
and seal-body probes are **N/A**, not successful anchor seals. The six exact design
statements were instead copied into temporary `example` declarations and proved by
applying the six implementation exports with their explicit binders in order.

Frozen-v1 inputs:

| Input | Revision / SHA-256 |
|---|---|
| Worktree HEAD | `cdf9b359852c6623869e0d392deadef9ffcad2b0` |
| `inp` at initial comparison | `cd23a4d1097be186cd5c5703bf8687af6373121d` |
| Package boundary before its two commits | `f04df2e` (design merge); commits `48d21df`, `cdf9b35` touch only TorusUnion |
| TorusUnion.lean | `249f6eb512a55534fec4fb41eec271978939a8bd7eb6aa2091a7e356550e2bf9` |
| PART1-LEAN-DESIGN.md | `f88dab2f934cdbb1f2d398da3c8a3413f6ebdfe502a9c763cfa14b74c4fa8be4` |
| Original `/root/code/KAM-inp/.drafts/design/PPart1Signatures.lean` | `78f21690c9e2623e9d9a9b6087bf32d1477434618c3089d98d0d0b99d5d098f7` |
| DESIGN-P1-design-audit-1.md | `4f722da6ba8a6805a63b403f1df4a6a86c3bf29511821b47778479ab7d8a31e6` |
| blueprint-P/parts/p1-hamiltonian-tools.tex | `71125916b1c5316e440916dd15e22d267a891c2d2b97188a7afb46ba2ff6af33` |
| Frozen Phase.lean | `ce1c7a4127866a19c0ec6dcc0f3588dc059cd0ce08ef97a06f4d91901cb11a47` |
| KAM/Measure/Lipschitz.lean | `75997ffe53cefd3813dcc40e7f1193b0d976b666f9f9af39503c6443351474a6` |
| KAM/ODE/Basic.lean | `13db29f548ae82d220360578a408ab147a6d1bc666fac9df881491019260090e` |

All implementation line locators below refer to frozen-v1 HEAD. Design and blueprint
locators refer to the corresponding frozen-v1 hashes above. `inp` advanced during
this audit; its initial pinned revision is the comparison authority recorded here.

## Declaration and node ledger

Names are in `KAM.Planetary`. All six public blueprint theorem signatures match the
original design Section G **textually**, including binder order and implicitness.
The body of `unitCube` also matches exactly. There are 17 declarations: one definition
and 16 theorems. Helpers add general reusable statements, not assumptions to the six
source exports. All helpers were read, axiom-checked and included in kernel replay.

| Node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| torus-union, cell | `unitCube` (42) | PASS | Literal half-open product `[0,1)^d`. |
| product measurability | `measurableSet_unitCube` (44) | PASS | Finite product of Borel intervals. |
| cell normalization | `volume_unitCube` (47) | PASS | Pi Lebesgue volume, including empty product. |
| product volume | `volume_prod_unitCube` (50) | PASS | Product outer measure identity; factor one. |
| product completion | `nullMeasurableSet_prod_unitCube` (53) | PASS | Correct product measure and completion API. |
| B1 cell helper | `isSigmaCompact_unitCube` (58) | PASS | Exhaustion by compact boxes; common finite-coordinate bound. |
| B1 product helper | `isSigmaCompact_prod_unitCube` (87) | PASS | Countable union of compact products. |
| Borel helper | `measurableSet_of_isSigmaCompact` (104) | PASS | Compact sets closed in T2 spaces; countable Borel union. |
| continuity helper | `lipschitzOnWith_of_bound` (110) | PASS | `toNNReal` dominates the real bound for every sign. |
| tu-meas helper | `exists_isSigmaCompact_subset_null` (119) | PASS | Finite-measure ball pieces and compact inner approximation. |
| tu-meas helper | `nullMeasurableSet_image_of_lipschitzOn` (142) | PASS | Borel compact-image union plus outer-measure-null image. |
| torus-union / tu-meas / tu-bounds | `torus_union` (167) | PASS | Exact completed measurability and sharp upper bound. |
| torus-union / tu-borel B1 | `torus_union_measurableSet_of_sigmaCompact` (175) | PASS | Sigma-compact image and Borelness, no injectivity premise. |
| torus-union / tu-borel B2 | `torus_union_measurableSet_of_injOn` (184) | PASS | Borel injective continuous-image theorem. |
| torus-union / tu-bounds | `torus_union_lower` (192) | PASS | Lower bound, positivity iff, and finiteness iff all retained. |
| torus-union / lattice identity | `torus_union_saturation` (237) | PASS | Exact equality with countable integer translates. |
| torus-union / saturated measurability | `nullMeasurableSet_torus_union_saturation` (258) | PASS | Completed union and separate Borel implication. |
| tu-ext proof step | no separate export | BYPASSED | On-set Lipschitz estimates suffice; no extension is consumed. |

## Binder audit

SOURCE means blueprint premises (or the stated helper's mathematical premises);
TYPING means data/types needed to state that result. There are no project-owned
Prop bundles hiding hypotheses. Every `Phase d` expands to the frozen product of
Pi real spaces, every lattice vector is `Fin d → ℤ`, and `angleShift k` is exactly
`(fun i => (k i : ℝ), 0)` from ODE/Basic:122. All nested quantifiers in `hF`, `hlow`
and `hper` are the source's universal point/membership/vector quantifiers. They do
not assume image measurability, an inverse, an extension, or a measure estimate.
The logical argument in the *conclusion* of the saturation measurability theorem
is an asserted Borel implication, not an extra premise on its completed result.

Each row below classifies one exported binder; shared names are repeated per
declaration. Inherited `d` is listed explicitly. Mathematical helper premises are
identified as such and never substituted for source theorem premises.

| Declaration | Binder | Bin / authority |
|---|---|---|
| `measurableSet_unitCube` | `d` | TYPING; carrier/data convention |
| `volume_unitCube` | `d` | TYPING; carrier/data convention |
| `volume_prod_unitCube` | `d` | TYPING; carrier/data convention |
| `volume_prod_unitCube` | `E` | TYPING; carrier/data convention |
| `nullMeasurableSet_prod_unitCube` | `d` | TYPING; carrier/data convention |
| `nullMeasurableSet_prod_unitCube` | `E` | TYPING; carrier/data convention |
| `nullMeasurableSet_prod_unitCube` | `hE: completed measurability` | SOURCE; helper contract, Part 1:217–219 proof ingredients |
| `isSigmaCompact_unitCube` | `d` | TYPING; carrier/data convention |
| `isSigmaCompact_prod_unitCube` | `d` | TYPING; carrier/data convention |
| `isSigmaCompact_prod_unitCube` | `E` | TYPING; carrier/data convention |
| `isSigmaCompact_prod_unitCube` | `hE: sigma-compactness` | SOURCE; helper contract, Part 1:217–219 proof ingredients |
| `measurableSet_of_isSigmaCompact` | `X` | TYPING; carrier/data convention |
| `measurableSet_of_isSigmaCompact` | `TopologicalSpace X` | TYPING; carrier/data convention |
| `measurableSet_of_isSigmaCompact` | `MeasurableSpace X` | TYPING; carrier/data convention |
| `measurableSet_of_isSigmaCompact` | `OpensMeasurableSpace X` | SOURCE; helper contract, Part 1:217–219 proof ingredients |
| `measurableSet_of_isSigmaCompact` | `T2Space X` | SOURCE; helper contract, Part 1:217–219 proof ingredients |
| `measurableSet_of_isSigmaCompact` | `s` | TYPING; carrier/data convention |
| `measurableSet_of_isSigmaCompact` | `hs: sigma-compactness` | SOURCE; helper contract, Part 1:217–219 proof ingredients |
| `lipschitzOnWith_of_bound` | `d` | TYPING; carrier/data convention |
| `lipschitzOnWith_of_bound` | `S` | TYPING; carrier/data convention |
| `lipschitzOnWith_of_bound` | `F` | TYPING; carrier/data convention |
| `lipschitzOnWith_of_bound` | `Λ` | TYPING; carrier/data convention |
| `lipschitzOnWith_of_bound` | `hF: on-set Lipschitz inequality` | SOURCE; helper contract, Part 1:217–219 proof ingredients |
| `exists_isSigmaCompact_subset_null` | `d` | TYPING; carrier/data convention |
| `exists_isSigmaCompact_subset_null` | `t` | TYPING; carrier/data convention |
| `exists_isSigmaCompact_subset_null` | `ht: Borel measurability` | SOURCE; helper contract, Part 1:217–219 proof ingredients |
| `nullMeasurableSet_image_of_lipschitzOn` | `d` | TYPING; carrier/data convention |
| `nullMeasurableSet_image_of_lipschitzOn` | `S` | TYPING; carrier/data convention |
| `nullMeasurableSet_image_of_lipschitzOn` | `hS: completed measurability` | SOURCE; helper contract, Part 1:217–219 proof ingredients |
| `nullMeasurableSet_image_of_lipschitzOn` | `F` | TYPING; carrier/data convention |
| `nullMeasurableSet_image_of_lipschitzOn` | `Λ` | TYPING; carrier/data convention |
| `nullMeasurableSet_image_of_lipschitzOn` | `hF: on-set Lipschitz inequality` | SOURCE; helper contract, Part 1:217–219 proof ingredients |
| `torus_union` | `d` | TYPING; carrier/data convention |
| `torus_union` | `E` | TYPING; carrier/data convention |
| `torus_union` | `hE: completed measurability` | SOURCE; blueprint-P Part 1:213 |
| `torus_union` | `F` | TYPING; carrier/data convention |
| `torus_union` | `Λ` | TYPING; carrier/data convention |
| `torus_union` | `hF: on-set Lipschitz inequality` | SOURCE; blueprint-P Part 1:213 |
| `torus_union_measurableSet_of_sigmaCompact` | `d` | TYPING; carrier/data convention |
| `torus_union_measurableSet_of_sigmaCompact` | `E` | TYPING; carrier/data convention |
| `torus_union_measurableSet_of_sigmaCompact` | `hE: sigma-compactness` | SOURCE; blueprint-P Part 1:213 |
| `torus_union_measurableSet_of_sigmaCompact` | `F` | TYPING; carrier/data convention |
| `torus_union_measurableSet_of_sigmaCompact` | `Λ` | TYPING; carrier/data convention |
| `torus_union_measurableSet_of_sigmaCompact` | `hF: on-set Lipschitz inequality` | SOURCE; blueprint-P Part 1:213 |
| `torus_union_measurableSet_of_injOn` | `d` | TYPING; carrier/data convention |
| `torus_union_measurableSet_of_injOn` | `E` | TYPING; carrier/data convention |
| `torus_union_measurableSet_of_injOn` | `hE: Borel measurability` | SOURCE; blueprint-P Part 1:213 |
| `torus_union_measurableSet_of_injOn` | `F` | TYPING; carrier/data convention |
| `torus_union_measurableSet_of_injOn` | `Λ` | TYPING; carrier/data convention |
| `torus_union_measurableSet_of_injOn` | `hF: on-set Lipschitz inequality` | SOURCE; blueprint-P Part 1:213 |
| `torus_union_measurableSet_of_injOn` | `hinj: on-set injectivity` | SOURCE; blueprint-P Part 1:213 |
| `torus_union_lower` | `d` | TYPING; carrier/data convention |
| `torus_union_lower` | `E` | TYPING; carrier/data convention |
| `torus_union_lower` | `hE: completed measurability` | SOURCE; blueprint-P Part 1:213 |
| `torus_union_lower` | `F` | TYPING; carrier/data convention |
| `torus_union_lower` | `Λ` | TYPING; carrier/data convention |
| `torus_union_lower` | `lam` | TYPING; carrier/data convention |
| `torus_union_lower` | `hF: on-set Lipschitz inequality` | SOURCE; blueprint-P Part 1:213 |
| `torus_union_lower` | `hlam: lam > 0` | SOURCE; blueprint-P Part 1:213 |
| `torus_union_lower` | `hlow: on-set lower Lipschitz inequality` | SOURCE; blueprint-P Part 1:213 |
| `torus_union_saturation` | `d` | TYPING; carrier/data convention |
| `torus_union_saturation` | `E` | TYPING; carrier/data convention |
| `torus_union_saturation` | `F` | TYPING; carrier/data convention |
| `torus_union_saturation` | `hper: integer equivariance` | SOURCE; blueprint-P Part 1:213 |
| `nullMeasurableSet_torus_union_saturation` | `d` | TYPING; carrier/data convention |
| `nullMeasurableSet_torus_union_saturation` | `E` | TYPING; carrier/data convention |
| `nullMeasurableSet_torus_union_saturation` | `hE: completed measurability` | SOURCE; blueprint-P Part 1:213 |
| `nullMeasurableSet_torus_union_saturation` | `F` | TYPING; carrier/data convention |
| `nullMeasurableSet_torus_union_saturation` | `Λ` | TYPING; carrier/data convention |
| `nullMeasurableSet_torus_union_saturation` | `hF: on-set Lipschitz inequality` | SOURCE; blueprint-P Part 1:213 |
| `nullMeasurableSet_torus_union_saturation` | `hper: integer equivariance` | SOURCE; blueprint-P Part 1:213 |

Counts: SOURCE = 24, TYPING = 47. STANDING = 0, RULED = 0, EXCESS = 0.
There are no existential numerical constants with hidden or widened dependence:
upper/lower factors are exactly `Λ^(2*d)` and `lam^(2*d)`.

## Definition classification

The only new def/abbrev/structure is `unitCube d`, a **literal definition**:
`Set.pi univ (fun _ => Ico (0 : ℝ) 1)`. Its entire carrier is the intended
`Fin d → ℝ`; no selected witness, fallback or characterization theorem is involved.
For `d = 0` the definition is the singleton empty function, with volume one.
The inherited `@[expose] public noncomputable section` exposes the definition body.
A temporary defining-equation example was checked by `rfl`.

```text
BODY_MATCH: OK
PUBLIC_CARRIER: OK
WELL_DEFINEDNESS: N/A_LITERAL
CHARACTERIZATION: N/A_LITERAL
CHOICE_INDEPENDENCE: N/A
DEFINITION_VERDICT: PASS
```

`Function.invFunOn` in the lower proof is a Mathlib auxiliary function, not a new
public definition. Its values are used only on `F '' A`, where injectivity gives
`hinj.leftInvOn_invFunOn`; arbitrary off-image values cannot affect the argument.
The compact approximants selected by `choose` need not be unique: the public result
is their proved existence with all required properties, not a purported canonical
source object.

## Proof review and adversarial checks

- **Product/Fubini normalization.** Lines 47–56 use `Real.volume_pi_Ico`,
  `Measure.volume_eq_prod` and `Measure.prod_prod`. The cube has volume one, so the
  outer measure of `E × cube` is `volume E`, with no finite-volume assumption or
  missing normalization. The separate null-measurable product proof uses its
  actual measure instances. No unproved Fubini interchange is assumed.
- **Completed measurability.** Lines 119–139 approximate measurable `t` on each
  closed ball by compact `K n m` with error below `m⁻¹`. Closed balls have finite
  measure, and `m⁻¹ → 0`; a countable union over `(n,m)` exhausts `t` modulo a null
  remainder, even for infinite-volume `t`. Lines 145–164 start with a measurable
  subset `t ⊆ S` equal a.e. to `S`, derive `volume (S \ B) = 0`, and split the
  image into the sigma-compact Borel image and a null image. This proves
  `NullMeasurableSet`, without claiming all Lipschitz images are Borel.
- **Borel cases.** B1 explicitly proves sigma-compactness of the half-open cube
  and product, then takes a continuous image. B2 uses exactly
  `MeasurableSet.image_of_continuousOn_injOn`. Thus a non-Borel subset of a null
  parameter set is no counterexample to either Borel theorem's actual premises.
- **Sign and dimension.** `KAM.lip_image_prod` accepts arbitrary real `Λ` and
  uses an explicit sign split in `measure_image_le_of_hausdorffMeasure_eq`.
  Its negative case treats dimension zero separately. `lipschitzOnWith_of_bound`
  supplies continuity by relaxing to `max Λ 0`. No PP1-3 premise `0 ≤ Λ` is added.
  Tested conceptually: empty `E`; `Λ = 0`; `Λ < 0`; and `d = 0`, where nonempty
  images have volume one and the exponent is zero. All agree with the statements.
- **Lower bound.** Lines 200–230 derive injectivity from `lam > 0`, prove the
  inverse is `lam⁻¹`-Lipschitz on its image, apply the same outer-measure estimate,
  and multiply by the positive finite factor `ofReal (lam^(2*d))`. The image/source
  positivity and finiteness equivalences use both bounds and valid ENNReal
  zero/top rules; there is no illicit cancellation of zero or infinity.
- **Whole-torus saturation.** Lines 237–255 use `Int.fract` and `Int.floor` to
  decompose every angle, and use affine equivariance in both directions.
  Lines 267–275 install the actual product Haar instance, identify translates as
  inverse images by the opposite translation, and take the countable lattice
  union. Whole ranges are retained; there is no parameter deletion or torus
  truncation. The output shift is in the first phase block; input `(ω,ϑ)` merely
  names parameter and angle slots, with no claimed symplectic meaning for them.

Candidate objections were challenged against their point-of-use hypotheses and
resolved as above. No unrefuted mathematical blocker remains. This was a separate
adversarial pass by the auditor, not a second-agent review.

## Findings, existing blueprint issues, and deviations

**N1 — inherited generated-root differences; not a PP1-3 edit.** The required
`git diff inp...HEAD` warns:

```text
warning: inp...HEAD: multiple merge bases, using 2e0825e206cf3230e980da464c07603862236f3c
```

It includes unrelated earlier packages and 11 added import lines in `KAM.lean`.
Consequently the literal four-path empty-diff check in brief §5 does **not** pass
for `KAM.lean`. Frozen paths, manifest and README are unchanged. Refutation of
package attribution: `git diff f04df2e HEAD --name-only` returns only
`KAM/Planetary/Hamiltonian/TorusUnion.lean`; `KAM.lean` at `f04df2e` and HEAD has
the same SHA-256 `3108caa531951d556d0a391c18221fa732a61345f9058b9b0ecac36d576593d1`.
The prover's claim that this package did not touch the generated root is verified.
Lint's expected stale-root complaint remains for the orchestrator to regenerate.

**N2 — known proof-plan issue, successfully bypassed.** Design lines 193–195 say
“for `Λ < 0` ... image measure `0`”, and lines 285–291 propose a McShane extension.
The blueprint at line 216 says McShane “gives a `Λ`-Lipschitz” extension without
stating a sign case. The negative case is not a standard nonnegative Lipschitz
constant, and the design's zero-measure shorthand needs `d > 0`: at `d = 0` the
nonempty cell and image have measure one. The existing design audit's
“Dropped-premise verdict” already states this qualification. These are proof-plan
wording issues, not false theorem signatures. Refutation against implementation:
the imported image estimate handles the zero-dimensional case explicitly; continuity
uses `toNNReal Λ`; no McShane extension is constructed or needed. The approved
on-set conclusions remain unchanged. No new pinned-paper erratum was identified.

The dropped McShane import and direct local product-Haar instance are valid
implementation choices. The latter follows design Decision 10 and avoids an
unnecessary dependency on the undelivered Liouville package. No new global
instance, conclusion-shaped hypothesis, or source-law deviation was introduced.

## Verification evidence

1. Required targeted build (after the gate wait):

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-pp13 KAM.Planetary.Hamiltonian.TorusUnion
   ```

   Exit **0**. The wrapper runs `nice -n 5 lake build` and printed:

   ```text
   [inp-gate] slot 1 acquired 05:55:41 for KAM.Planetary.Hamiltonian.TorusUnion
   Build completed successfully (9053 jobs).
   ```

   This was the single targeted cached-dependency build, not a clean rebuild.
   No warnings or default-heartbeat failures were reported.

2. Repository lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, solely the allowed generated-root complaint. Exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (413 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   The module is **281 lines**, maximum Unicode line length **98**; zero lines
   exceed 100 characters. It has the required copyright, `module`, public imports,
   module docstring, public section and exposed definition. The forbidden-token
   scan found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, resource overrides,
   or `EuclideanSpace`. `git diff --check` passes for the module and report.

   Process note: an initial lint invocation was stopped after its ABI subprocess
   was found not to inherit `LEAN_NUM_THREADS=1`; it is not evidence for this audit.
   Its pending build wrapper was also stopped before obtaining a gate slot. The
   completed lint above and all subsequent Lean checks use the requested thread
   setting and niceness, with no concurrent audit-owned Lean jobs.

3. Exact-statement and axiom probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/PP13Audit.lean
   ```

   Exit **0**, with no warnings or errors. The six exact-type examples and the
   literal `unitCube` equation elaborate. A text comparison also returned `True`
   for each of the six signatures against original Section G. Exact axiom output:

   ```text
   'KAM.Planetary.measurableSet_unitCube' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.volume_unitCube' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.volume_prod_unitCube' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.nullMeasurableSet_prod_unitCube' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.isSigmaCompact_unitCube' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.isSigmaCompact_prod_unitCube' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.measurableSet_of_isSigmaCompact' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.lipschitzOnWith_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.exists_isSigmaCompact_subset_null' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.nullMeasurableSet_image_of_lipschitzOn' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.torus_union' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.torus_union_measurableSet_of_sigmaCompact' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.torus_union_measurableSet_of_injOn' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.torus_union_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.torus_union_saturation' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.nullMeasurableSet_torus_union_saturation' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   All 16 lists are exactly `[propext, Classical.choice, Quot.sound]`; there is no
   `sorryAx` or project axiom.

4. Required kernel replay, one invocation for the only in-scope module:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Hamiltonian.TorusUnion
   ```

   Exit **0**. Complete output:

   ```text
   replaying KAM.Planetary.Hamiltonian.TorusUnion
   ```

   This replays the package definition and all 16 public theorem bodies, together
   with any generated private declarations in the module.

5. Import/manifest checks: direct imports are `Mathlib`, frozen `Phase`, ODE/Basic,
   and Measure/Lipschitz. A project-import traversal finds seven project modules,
   with **zero** provider or frozen theorem imports, including transitively. Its
   four frozen imports are SEALED definitions: `Phase`, `IsDiophantine`,
   `HamiltonianVectorField`, and `SymplecticForm`. The frozen Phase file hash equals
   its manifest `planetary.Phase.v1` hash; its recorded ABI is
   `0b8db62a1a83c34b9c3562bd1bb6043b1db7174c9222df403355844422056af8`.
   The completed guard and full ABI lint confirm the frozen closure.

6. Diff checks: executed `git diff inp...HEAD`, scoped module diff and `--check`,
   the four-path protected-file diff, and the independent package-boundary diff
   `git diff f04df2e HEAD`. Their generated-root exception is recorded under N1.
   Final implementation and original-signature hashes were rechecked unchanged. The handoff was already
   untracked on entry; this report is the only new repository artifact.

## Closeout and limits

All 17 public declarations are classified and audited. All six source-facing
statements and the literal definition were checked against the original signature
file and the blueprint, and all 16 public theorems have standard-foundation-only
axiom closure. PP1-3 is acceptable with notes N1–N2. No repair was applied.

No downstream P3/P4/P5/P12/P13 application, physical wrapping chart, root provider,
frozen theorem proof, or other diff module is certified here. In particular, a lower
Lipschitz bound for a wrapped Cartesian torus is not produced by this module.
This report certifies the supplied infrastructure, not the planetary headlines.
