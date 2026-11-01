# LP-PS independent package audit 1

**Package verdict: PASS WITH NOTES.** No blocking statement-fidelity, definition-carrier, or conclusion-shaped-input defect found. This accepts the bounded, non-frozen planar package; it is not a freeze approval or a new audit of its ingredient proofs.

Audited HEAD: `eaefacb443be5f0c29ea3a83356c84861aa644a4`.
Comparators at inspection: `inp=687eeddd6ca20620946910ef8d1b48aaf1237c6a`,
`inp-lp=0fac4488bd15ede6fd2bebc49488f4a51a4ae40a`.
Read AGENTS.md, PLAN.md, DECISIONS.md, the general package-audit brief, LP-PS handoff and AUDIT FOCUS,
the bounded brief `/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP-PS.md`, SPEC, MAIN and normative AMENDMENTS,
draft-2 FREEZE-PROPOSAL and its verification text. Compared `git diff inp...HEAD`; mathematical/code scope is
`git diff inp-lp...HEAD -- KAM`: five new PlanarSafety modules (809 lines), plus five generated imports in
`KAM/Root/Planetary.lean`. Ingredients were inspected only at the interfaces used by this assembly.
There are no LP frozen anchors/providers to compare or seal-copy probes to run.

## General LP1 — PASS

`Main.lean:43`, `lp1_planar_strongAMD_safety`, implements MAIN Theorem 15 with Lemmas 14 and 16,
using Lemma 13 as the sole stopped-drift supplier (N7). Its only deliberate generalization of the
normalized target is omission of `hνmax` and `hνle`: arbitrary positive fixed masses are allowed, and μ
is a mass scale rather than necessarily the largest planet/star mass ratio. No rescaling of the equation
or time is silently introduced.

The statement preserves all nonzero integer modes, ℓ¹ `modeSize`, the radian frequency `ν³/Λ³`,
the exact exponential horizon with real exponent `1/(2(τ+1))`, physical time, both closed endpoints,
and all 13 per-time clauses. In particular, it exports negative osculating energy, positive axis,
eccentricity below one, containment of the current radius, the **sum** of axis and eccentricity-vector
errors, both endpoint errors, and both half-gaps. Physical lengths use `planeLength`; action/axis drifts
use the Pi maximum norm. Reconstruction uses masses `actualMasses 1 ν μ` and the actual barycentric
position/velocity maps on the same interval.

The telescope contains source data, positivity, compactness, ordered axes, Diophantine data and the
initial AMD margin only. `hch` types the source threshold and follows from positive masses, physical
initial data and ordered axes (`mem_strongLSet_actionVector`, `strongLSet_subset_chamber`). No safety,
chart-lift, normal-form, stopped-drift, uniqueness or prograde conclusion is assumed by LP1.

The proof derives nonzero total momentum from the strong threshold's star bound and δ>0, then
splits its sign. The negative case applies the same constants to `reflectPhase z₀`, preserving physical
data, axes, frequencies, chamber and absolute AMD. Reflection back preserves the entire conclusion.
Newtonian reconstruction is applied to the transported moving solution, avoiding any unproved
Newtonian reflection step.

## Normalized LP1 — PASS

`Main.lean:136`, `lp1_planar_strongAMD_safety_normalized`, has the draft-2 LP1 type, up to definitional
unfolding of `ecc` and irrelevant binder names. Both normalization assumptions occur in their original
position and are unused by the direct application of general LP1. The verification file's two theorem
signatures were independently compared with the proposal's two code blocks after whitespace
normalization: both equal. The requested verification was then elaborated successfully, closing the
proposal declarations by the package exports with exactly the displayed explicit arguments.

## Half-integer LP1 — PASS

`Main.lean:189`, `lp1_planar_strongAMD_safety_halfInteger`, specializes τ to `n−1/2`, which strictly
exceeds `n−1`. `scaleExponent_planar` rewrites precisely to `1/(2n+1)`. All hypotheses, constants,
N10 restrictions and conclusion clauses otherwise agree with general LP1. This corollary inherits
the valid mass-scale generalization.

## LP0 — PASS

`Main.lean:254`, `lp0_planar_barrier`, is full MAIN Lemma 5 in the source-complete draft-2 form:
the deficit-list assertion includes endpoints `e∈[0,1]^n`; the physical assertion includes all-pair
separation, compact containment, negative energy throughout the compact set, and the angular-momentum
magnitude/sign margin. Its draft-2 verification elaborated successfully.

The compact witness is **not** the larger collision-free barrier compact alone. At lines 278–291 the
proof intersects that compact with the preimage of `{x | ∀ i, x i ≤ −c}`, where `c>0` comes from
`strongBarrier_physical`. Energy is continuous on the barrier compact because it excludes zero star
radius; relative closedness gives a compact intersection. Every point of the intersection has
`E_i≤−c<0`. Every admissible state lies in it by the barrier compact containment and uniform energy
bound. Thus neither taking a closure across zero energy nor relying on continuity of energy at a
collision is involved. The positive witnesses work also when U or the admissible family is empty;
the state assertions are then vacuous, as expressly permitted by MAIN L5.

## Internal prograde assembly — PASS

`Prograde.lean:43`, `planar_safety_of_prograde`, is an explicitly named intermediate theorem with
`0<totalMomentum z₀`; general LP1 discharges this orientation by reflection. It does not assume any
individual prograde momentum, secular stability or confinement estimate.

All constants precede μ and z₀. The choices are from `(n,ν,A,δ,γ,τ)` only:
shared tube U, NRR's constants with `D₀=1`, barrier/OSC constants at margin δ/2, budget radius r₁,
and the uniform action bound C on U. The proof chooses
`r₂=min(r₁,r_g)`, `AΛ=1/2`, `Aa=(max C 0+1)(Σν_i⁻²+1)`, `Aelem=A₂` from OSC,
`dStar=min(dS₁,dS₂)`, `dPair=min(dP₁,dP₂)`, and
`μ₀=min(min(min μ₁ μ₂) r₂²) (min(dS₁/(2Aosc),dP₁/(4Aosc)))`.
OSC's μ₂ already pays the inequalities for dS₂,dP₂; the extra restrictions pay them for dS₁,dP₁.
Therefore N10 holds for the **minimum** constants actually exported. No constant is chosen after the
initial state or μ. The output Aelem is OSC's constant, not the input architecture set A.

The `hstop` construction at lines 135–154 is the required interface discharge:

- `StoppedOn` unfolds literally to CONF's strict antecedent; no improved action bound is inserted.
- `LiftData` is constructed from physical initial data, U, the budget, the closed action ball,
  the initial AMD margin and orientation. The level-set membership follows from nonnegative AMD.
- `lpChartLift_premises (wS := w)` uses the **same** NRR slow width w. Its chart ODE,
  rescaled real-domain membership, centre identity and slow-ball membership are all outputs.
- `lpStoppedBlock` and NRR's `lpBlock` both unfold to
  `⟨I0,secularBall ν δ I0,r,w⟩`; the equality argument passed to NRR is `rfl`.
- NRR is applied on `J := uIcc 0 t`, with both endpoints included, so the negative-time case
  receives the same premises. `scaleExponent τ` unfolds to `1/(2(τ+1))`, and its absolute-time
  bound is the exact CONF bound. The resulting drift is r/2.

CONF then supplies the moving solution, uniqueness, physical validity, half-radius drift, AMD margin
and barrier membership. GEOMOD and OSC are applied to that barrier membership. The axis estimate
uses bounded actions in U and a harmless enlargement of its constant; AMD drift follows from exact
momentum conservation and the sum of component action differences. This closes the previously
conditional LIFT/NRR-to-CONF edge for this package without promoting their conditional statements.

## Declaration-by-declaration review

All names are relative to `KAM.Planetary.StrongAMD`. Line references are within PlanarSafety parts.

| Node / location | Declaration | Verdict | Reason |
|---|---|---|---|
| L14, Constants:35 | `exists_budget_radius` | PASS | Uniform positive radius; pays `nr+Ω≤δ/4` for every smaller positive r. |
| L2 dictionary, Constants:55 | `keplerAxis_eq_action_sq` | PASS | Physical guards and positive masses justify Λ²/ν². |
| L14 axes, Constants:64 | `norm_axis_sub_le` | PASS | Sup drift and bounded actions give the displayed sum bound; no denominator can vanish. |
| L14 centre, Constants:96 | `mem_strongLSet_actionVector` | PASS | Positive square-root branch and orbital identities give membership from axes. |
| T15 reflection, Orientation:38 | `reflectPlane_sum` | PASS | Linear finite-sum identity, including empty sums. |
| L16 reflection, Orientation:46 | `oscVelocity_reflectPhase` | PASS | Reflects both canonical velocity and the full μΣp contribution. |
| L16 reflection, Orientation:51 | `oscEnergy_reflectPhase` | PASS | Squared length and radius invariant. |
| L16 reflection, Orientation:56 | `oscAxis_reflectPhase` | PASS | Same parameter and energy. |
| L16 reflection, Orientation:61 | `oscEccVector_reflectPhase` | PASS | Vector covariance, including its dot product and parameter division. |
| L16 reflection, Orientation:67 | `oscEcc_reflectPhase` | PASS | Euclidean length invariant, including circular states. |
| L16 reflection, Orientation:72 | `oscPeri_reflectPhase` | PASS | Axis and eccentricity invariant. |
| L16 reflection, Orientation:77 | `oscApo_reflectPhase` | PASS | Axis and eccentricity invariant. |
| T15 reflection, Orientation:82 | `keplerPeri_reflectPhase` | PASS | Canonical axis and eccentricity length invariant. |
| T15 reflection, Orientation:87 | `keplerApo_reflectPhase` | PASS | Same canonical invariances. |
| T15 reflection, Orientation:93 | `actionVector_reflectPhase` | PASS | Pointwise action invariance; no norm substitution. |
| statement bundle, Orientation:100 | `PlanarSafeState` | PASS | Literal 13-clause output predicate; carrier analysis below. |
| solution bundle, Orientation:126 | `PlanarSafeSol` | PASS | Initial value, moving equation, uniqueness and timewise output only. |
| T15 transport, Orientation:131 | `PlanarSafeState.of_reflectPhase` | PASS | Transports every clause, including vector error and dependent threshold witness. |
| T15 transport, Orientation:156 | `PlanarSafeSol.of_reflectPhase` | PASS | Reflects each competing local solution and uses involutivity to transfer MovingUniqueOn. |
| L14/T15, Prograde:43 | `planar_safety_of_prograde` | PASS | Constructed constants and hstop; scoped orientation input discharged by Main. |
| T15, Main:43 | `lp1_planar_strongAMD_safety` | PASS | Orientation-free source theorem with authorized mass generalization. |
| draft-2 LP1, Main:136 | `lp1_planar_strongAMD_safety_normalized` | PASS | Exact normalized target verified by elaboration. |
| §1 corollary, Main:189 | `lp1_planar_strongAMD_safety_halfInteger` | PASS | Correct exponent and unchanged clauses. |
| L5/draft-2 LP0, Main:254 | `lp0_planar_barrier` | PASS | Full deficit/physical/compact/negative-energy/momentum output. |

## Definition classification and carrier checks

There are exactly two new definitions and no new abbrevs, structures, selected optimizers or fallback values.
Both definitions are exposed in the public noncomputable section.

- `PlanarSafeState` is a proposition bundling the explicit LP1 per-time conclusions. It accepts arbitrary
  real μ, δ and bound constants and arbitrary phases, with `hn:2≤n`. This is an algebraic predicate,
  not a declaration that every such input is a physical ellipse. Its first clause guards canonical
  physical interpretation; its osculating clause explicitly supplies negative energy, positive axis
  and e<1. Its threshold receives an existential chamber witness, so it never supplies an off-chamber
  physical minimum. At μ≤0 the ordinary real square-root expression has its Lean meaning; the predicate
  makes no existence claim there, and all existence consumers require μ>0. Circular states remain
  included, with no derivative of the eccentricity norm or perihelion angle required.
- `PlanarSafeSol` is exactly initial equality, moving solutionhood, frozen local-overlap uniqueness and
  `∀t∈[-T,T], PlanarSafeState ...`. It intentionally omits Newtonian reconstruction, which Main adds.
  For negative T, the interval is empty and its interval clauses have the corresponding vacuous meaning;
  it does not assert global physical behavior. The existence theorem constructs T>0 before use.

The reflection lemmas are valid even on algebraically totalized inputs (zero mass, radius or parameter):
they are exact covariance identities, not physical interpretation theorems on those inputs. No existence
consumer relies on those values. `norm_axis_sub_le` also covers n=0 as an auxiliary algebraic estimate;
main results have n≥2. Conditional reflection-transport inputs are appropriately explicit for those
transport helpers, not assumptions substituted for proving a source theorem.

## Checks and exact evidence

Every Lean/Lake invocation performed here was serial and used the binding D53 wrapper:

```text
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 <command>
```

1. Fresh draft-2 verification and all-public-theorem axiom check:

```text
<D53 wrapper> lake env lean .lake/abi-scratch/LPPSAudit1.lean
exit 0
```

The scratch file was the supplied `freeze/verification-draft-2.lean.txt` verbatim, followed by
`#print axioms KAM.Planetary.StrongAMD.<name>` for each of the 22 new theorem names in the table.
For every one, output was exactly (up to line wrapping):

```text
'KAM.Planetary.StrongAMD.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The three supplied prints also passed: proposal `planar_strongAMD_exponentialSafety`, proposal
`planar_strongAMD_barrier`, and general `lp1_planar_strongAMD_safety`, with that same axiom set.
No sorryAx or additional axiom appeared. The scratch file is deleted after checks.

2. Fresh targeted build through the compile gate (inside the D53 scope):

```text
<D53 wrapper> /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-lp-thr KAM.Planetary.StrongAMD.PlanarSafety
[inp-gate] slot 2 acquired 05:16:39 for KAM.Planetary.StrongAMD.PlanarSafety
Build completed successfully (9314 jobs).
exit 0
```

This targeted dependency-closure build reused the existing build snapshot; no clean, default-library
or application build was run. Output replayed existing dependency warnings (unused binders/tactics
and deprecated names); no diagnostic named a PlanarSafety file.

Authorized lint, only through the requested wrapper:

```text
/root/code/KAM-inp/.drafts/LP/lp_lint.sh /root/code/KAM-inp-lp-thr
check_lean_modules: PASS (3707 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
exit 0
```

The wrapper runs `sh scripts/lint_sources.sh` inside the exact D53 scope. No stale-root exception
was needed. Final read-only comparison confirmed all six audited Lean paths byte-identical to HEAD;
`git status --short` contains only this new report.

3. Launcher replay/name evidence was recovered read-only from
`/root/code/KAM-inp/.drafts/LP/audit-LP-PS-1.log`; it is not a fresh replay by this auditor:

```text
KAM.Planetary.StrongAMD.PlanarSafety.Orientation replay exit 0
KAM.Planetary.StrongAMD.PlanarSafety.Constants replay exit 0
KAM.Planetary.StrongAMD.PlanarSafety.Prograde replay exit 0
KAM.Planetary.StrongAMD.PlanarSafety.Main replay exit 0
KAM.Planetary.StrongAMD.PlanarSafety replay exit 0
name-clash check OK (5 package modules + every built KAM module; 0 base clash(es) skipped)
shadow check OK (no package name shadows a root constant)
short-name check OK (no reused public short name)
```

The launcher script runs each replay as capped `timeout 1200 lake env leanchecker <module>`.
The user explicitly allowed reliance on these launcher checks; no duplicate replay was needed.

4. Static checks:

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
- `git diff --check inp...HEAD` and `git diff --check inp-lp...HEAD -- KAM`: empty, exit 0.
- No forbidden escape, sorry, resource override, EuclideanSpace, provider import or direct frozen
  theorem import in the five new files. Frozen imports are definitions, not unproved theorem gates.
- File lengths: facade 22, Constants 109, Main 298, Orientation 176, Prograde 204. All below 1500.
  Four declaration-bearing parts have copyright, module header, public imports, module docstring and
  exposed public section. The import-only facade has all except a literal public section (note H1).
- Root delta is exactly five public imports, an existing generated producer change; the auditor
  did not regenerate or edit any root, frozen file, manifest, source, or implementation.

## Notes, uncertainties, errata and deviations

**H1 (minor literal hygiene deviation):** `KAM/Planetary/StrongAMD/PlanarSafety.lean:6–22` is an import-only
facade without `public section`. AGENTS hard rule 3 explicitly lists that marker for every Lean module.
This has no declaration visibility or mathematical effect, since the file declares nothing, but is a
literal style deviation even if lint passes. Add the marker in an authorized implementation follow-up
or record an explicit import-only-facade exception; no code was changed by this auditor.

**D1 (handoff documentation):** the handoff cites `freeze/STATEMENT-REVIEW-2.md` and claims its PASS;
that file is absent in this worktree. Its purported review result is not independently attested here.
The actual proposal/verification text and fresh elaboration were reviewed directly, so this does not
leave the target's type unverified. The handoff's 779-line count is also stale: current files total 809.
Main's overview still refers to draft 1 although its implemented statement includes the draft-2 delta.

No new suspected mathematical erratum in MAIN or AMENDMENTS was found. The N6 half-radius change and
N7 alternative-supplier ruling, rather than the unamended Lemma-12/r/4 prose, control this assembly.
The accepted generalization and literal unfolding of `ecc` are reported above; neither changes the
normalized target. Existing total physical-expression freeze choices remain outside this package's
scope. No unresolved mathematical invoice remains for the five reviewed main statements under their
audited ingredient interfaces. Only this report is retained from the audit.
