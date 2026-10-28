# S7-1 independent implementation audit 1

**Overall verdict: PASS WITH NOTES.** The two S7-1 modules implement the binding v2
interfaces. No blocking mathematical, statement-fidelity, definition, or hygiene defect
was found. This is approval of helper infrastructure, not a frozen-anchor seal or a
proof of N-HEAD-C, N-QC, or any I/P headline.

## Scope and authority

Audited on 2026-10-28 in `/root/code/KAM-inp-s71`, HEAD
`6e9abddc57d65d22116649e8c9d1d8be4c254d7d`, compared using `git diff inp...HEAD`
against `inp = f45c6617a5e134742856494cfee2a6f95ea2d1b6`.
The user's exact worktree report destination overrides the common brief's main-worktree
destination. No delegation, source edits, or state-changing git commands were used.

Read AGENTS.md, PLAN, DECISIONS, the supplied package-audit brief and S7-1 handoff,
the v2 design and design audits 1–2 (especially F1), the standalone v2 signatures,
the Part 7 setting/real-system/exit-ball statements and proofs, the track-N statement,
and the frozen definitions used by these modules. The standalone and embedded v2
S7 signature region is byte-identical. Binding design SHA-256:
`9376271a6f311a2fa9bdf530680433ae2b759a84747a05aa1aa8ad07d2e53be2`;
standalone signature SHA-256:
`c588818b1772d3f7e106aac256b8207623c8a142cf40ef0e778f0507b1945c9f`.

Owned implementation scope:

| File | Lines | SHA-256 |
|---|---:|---|
| `KAM/Nekhoroshev/Stability/Setting.lean` | 249 | `94190572990d617ad434dceba428460a2a81b8a1bbe16ada4e49a941bc3011fa` |
| `KAM/Nekhoroshev/Stability/RealSystem.lean` | 120 | `b90d823c6a11e1ad758eb0f6f2324f7c6fe5d6a89f20e6e0ebdf5b00c27be5be` |

The diff also contains the 179-line N6-1 `NormalForm/Setting.lean`. As required by
AUDIT FOCUS, its implementation is outside this audit. Its blob is identical to
`inp-n61:KAM/Nekhoroshev/NormalForm/Setting.lean`:
`0bcc6a8c50b375b65bd05ebe645a0bbbd9636d06`. Its imported `freq` definition was
checked for the real-frequency bridge; this is not an independent N6-1 audit.

**Frozen anchors: none in this package.** Provider/frozen-type equality and a seal-body
probe are therefore not applicable. Instead, nine fresh examples copied the exact
v2 theorem signatures and supplied their explicit binders to the implementation
theorems. All elaborated. No frozen declaration or manifest entry was changed.

## Declaration and node review

Names below are in `KAM.Stability`. Locations are in `Setting.lean` unless marked RS
(`RealSystem.lean`). All eight definition bodies, the structure fields, and all nine
public theorem headers match the design mechanically after whitespace normalization.
The structure-instance proofs use `where` instead of the draft's `:= sorry`.

| Blueprint node | Declaration / line | Verdict | Reason / note |
|---|---|---|---|
| p7:setting | `cpx`, 42 | PASS | Image under the genuine real inclusion. |
| p7:setting | `realNbhd`, 45 | PASS | Existential max-norm tube, open strict radius. |
| p7:setting | `realStrip`, 48 | PASS | Full real angles times the real action tube. |
| p7:setting | `realH`, 52 | PASS WITH NOTES | Exact v2 total real restriction; documented extension choice, N1 below. |
| p7:setting | `IsOrbit`, 56 | PASS | Genuine two-sided derivative equation and membership in the real strip. |
| p7:setting | `reMap`, 61 | PASS | Coordinatewise real part after real inclusion. |
| p7:setting | `thetaGradR`, 66 | PASS | Real derivative in the angle coordinate, correct slot. |
| p7:setting | `hessR`, 70 | PASS | Iterated real Fréchet derivative, correct order and directions. |
| p7:setting | `isOpen_realNbhd`, 72 | PASS | Union of open max-norm balls; no positivity or nonempty-set premise needed. |
| p7:setting | `realNbhd_mono`, 79 | PASS | Correct radius order; valid for all real radii. |
| p7:setting | `realInclusion₂_mem_Dom_iff`, 84 | PASS | Exact real slice; `s > 0` supplies real-angle strip membership. |
| p7:setting / p10:hypotheses-check | `realHamiltonian_eq_realH`, 97 | PASS | Definitional equality to the frozen Hamiltonian, globally. |
| p7:setting / p10:hypotheses-check | `freq_realInclusion`, 101 | PASS | Holomorphy and reality on an open real tube identify the complex frequency with the frozen real gradient. |
| p7:transfer / p7:exit-ball | `IsActionNorm`, 132 | PASS | Exact revised six fields; genuine norm dominating the max norm, excludes shifted norms. |
| p7:transfer / p7:exit-ball | `isActionNorm_norm`, 140 | PASS | All six properties of the Pi max norm. |
| p7:transfer / p7:exit-ball | `isActionNorm_euclid`, 148 | PASS | Euclidean formula on function coordinates; triangle by Cauchy–Schwarz, exact homogeneity. |
| p7:exit-ball | `exit_ball`, 220 | PASS | First boundary hit and closed-ball bound, in both time directions; exact v2 statement. |
| p7:real-system | `real_system`, RS 69 | PASS | All smoothness, full integer periodicity, real/complex field identity, C1 field, and interval energy clauses retained. |

Private implementation declarations were also inspected:

| Node / role | Private declaration / line | Verdict | Reason |
|---|---|---|---|
| p7:exit-ball | `first_hit`, 186 | PASS | Infimum of nonempty closed level-superlevel set in a compact time segment; continuity gives equality. |
| p7:setting | `isOpen_realStrip`, RS 34 | PASS | Product openness. |
| p7:setting | `realStrip_mono`, RS 37 | PASS | Product inclusion. |
| p7:real-system(a) | `realH_contDiffOn`, RS 41 | PASS | Finite-dimensional holomorphic regularity, restriction of scalars, real inclusion and real part. |
| p7:real-system(a) | `realH_periodic`, RS 52 | PASS | Derives all integer shifts from the analytic class's unit-coordinate shifts. |

No binder-order change, widened constant dependence, changed norm/carrier, or
conclusion-shaped premise was introduced. There are no existential estimate constants
in this package. Elementary neighborhood assertions hold without the blueprint's
positive-radius and positive-dimension standing restrictions; this is harmless extra
generality. `IsActionNorm.norm_le` is the binding design's restriction to norms dominating
the max norm, including both advertised instances; the standalone exit theorem is not
an export for every arbitrarily scaled norm.

## Definition classification and refutation attempts

All eight new definitions are direct intended objects, with no branch, fallback,
choice of surrogate dynamics, or assumed estimate. `cpx`, `realNbhd`, and `realStrip`
remain correct for empty sets and nonpositive radii. `realH` is the genuine total
real-part restriction, and `reMap` is a total real-part map even when the complex map
does not preserve real points. Reality hypotheses are needed only where equality to
complex dynamics is asserted. `IsOrbit` unfolds to `KAM.ODE.IsSolutionIn`, with
ordinary two-sided `HasDerivAt` at every time in the supplied set.

`thetaGradR` and `hessR` deliberately use Mathlib's total `fderiv`. Their interpretation
as classical derivatives requires differentiability; no S7-1 theorem exploits the
default derivative at a nonsmooth point. `real_system` proves differentiability on
the relevant open domain. `freq_realInclusion` obtains differentiability from
holomorphy and openness before comparing derivatives. Its result uses the literal
frozen `frequencyMap`, not an assumed identification.

The new structure `IsActionNorm` is a property bundle of source norm laws, not a
bundle of proof conclusions. `norm_le` implies nonnegativity and definiteness;
`smul` supplies absolute real homogeneity and `add_le` the triangle inequality.
The old shifted norm `N(a) = ‖a‖ + 1` fails `map_zero`. In the implemented exit proof,
`N(I(0)-I(0)) = 0 < ϱ` is established explicitly at Setting:229. The infimum proof
establishes an attained level, rather than assuming the existence of an exit time.
For negative `t₁`, it applies the same scalar first-hit argument to `z(-t)` and maps
the full preceding segment back. `t₁=0` cannot satisfy the exit premise. No dynamical
equation or future confinement premise is smuggled into this continuous-curve lemma.

For `real_system`, the real/complex field equality uses the frozen signs and slots
`(∂I G, -∂θ G)`. C1 regularity follows from proved C2 regularity of the Hamiltonian.
The strip is invariant under all integer angle shifts. Energy is proved for every
supplied actual orbit on every order-connected time set; no compactness, chosen flow,
or pre-existing conservation hypothesis is added. Existence/uniqueness are not
restated as new conclusions: the design explicitly records that the proved C1 and
periodicity facts are the inputs to Part 3's existing results.

## Independent validation receipts

All audit Lean invocations were serial, with `LEAN_NUM_THREADS=1`; no heartbeat,
recursion-depth, or synthesis-budget override was used. The build used the compile
gate, and the explicit Lean/checker commands used `nice -n 5`. Lint's ABI-check
process and its descendants were set to niceness 5 while running. No clean, update,
cache fetch, or library-wide build was performed.

### Targeted build

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s71 KAM.Nekhoroshev.Stability.RealSystem
[inp-gate] slot 1 acquired 06:14:02 for KAM.Nekhoroshev.Stability.RealSystem
Build completed successfully (3182 jobs).
exit 0
```

`RealSystem` depends on `Setting`, so this targeted invocation checks both modules.
No warnings were emitted.

### Exact design-type probes and axioms

Auditor-created `.lake/abi-scratch/maud-s71-1.lean` imported `RealSystem`, copied the
nine theorem signatures directly from the design, and discharged each by `exact`
the corresponding implementation applied to precisely its explicit binders.
The two norm instances used `(n := n)`. This probes the binding interfaces without
importing any of the signature file's placeholder theorem bodies.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/maud-s71-1.lean
exit 0
'KAM.Stability.isOpen_realNbhd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.realNbhd_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.realInclusion₂_mem_Dom_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.realHamiltonian_eq_realH' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.freq_realInclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.isActionNorm_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.isActionNorm_euclid' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.exit_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.real_system' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Stability.RealSystem KAM.Nekhoroshev.Stability.Setting
replaying KAM.Nekhoroshev.Stability.Setting
replaying KAM.Nekhoroshev.Stability.RealSystem
exit 0
```

### Source lint, imports, and protected paths

```text
LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (418 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole failure is the generated-root freshness check explicitly excepted by the
audit brief. No source-line, module-format, forbidden-token, size, frozen-file, or
ABI complaint was emitted. Independent scans found no lines over 100 characters
in either S7-1 file, no forbidden escape or resource-option tokens, and no
`EuclideanSpace`. Both files have copyright, `module`, public imports, module
docstring, and an exposed public noncomputable section.

An import-closure walk found 50 project modules, no provider, and 19 frozen modules,
all definition anchors marked SEALED. No DRAFT_SORRY frozen theorem is imported,
directly or transitively. The axiom receipts independently exclude `sorryAx` from
every public theorem.

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(empty output; exit 0)
git diff --check inp...HEAD
(empty output; exit 0)
```

## Notes, deviations, and suspected errata

**N1 — documented totality choice, nonblocking.** Blueprint
`blueprint-N/parts/p7-stability.tex:28` says “`G^ℝ(x)=0` otherwise”.
`Setting.lean:52–53` instead uses `Re G ∘ ι` everywhere, exactly as directed by
design §5 item 1 (`PART67-LEAN-DESIGN.md:184`, “instead of `G` on `W_r`, `0` off it”).
These are different global functions but agree on the open working real strip,
so their derivatives, fields, and orbit predicates there agree. The global frozen
Hamiltonian bridge is intentionally exact for the selected extension. This is an
already declared design deviation, not a newly introduced fallback or a false
on-domain theorem. Do not describe the two total functions as globally equal.

**N2 — valid proof-route substitution, nonblocking.** The design proof plan
(`PART67-LEAN-DESIGN.md:328`) proposes `gen_exit`. The implementation proves a
private scalar first-hit lemma from closed-set infima instead. It establishes the
same public conclusion using only continuity and the norm's zero value, in both
time directions. No public target is bypassed or assumed.

**N3 — merge/landing boundary.** Land the N6-1 dependency consistently with its
owner, and regenerate the generated root through the orchestrator. This audit does
not independently approve N6-1 or authorize any frozen seal. There is no unresolved
S7-1 mathematical obligation or source defect identified here.

No new suspected pinned-source erratum was found; no pinned source was changed.
No implementation deviation beyond N1–N2 was found. The report is the only retained
auditor edit; the scratch probe was removed after validation.
