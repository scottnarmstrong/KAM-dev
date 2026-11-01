# LP-W3C independent package audit 1

Date: 2026-11-01. Worktree: `/root/code/KAM-inp-lp-thr`.
Reviewed HEAD: `0d42d416c20d8df856def8673484dc6b0ac7ba4d`.
Bases: `inp = d02d874dc6aa384ad71a1db1b529c9da20ee80bb`,
`inp-lp = cd90623d95ef75230401fbed51efa9d12f3d6e60`.

Scope: read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the independent package audit brief,
LP-W3C AUDIT FOCUS, SPEC, MAIN as amended, all three component briefs and handoffs.
Compared `git diff inp...HEAD` and audited the exact package surface of
`git diff inp-lp...HEAD -- KAM`: 15 files, +1364/-5, including the generated root imports.
Nothing here is frozen; provider/frozen type equality and seal-body probes are inapplicable.
The requested `/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP-W3C.md` does not exist.
The combined handoff and the existing LP-LIFT, LP-DOMX and LP-THR2 briefs supply the bounded targets;
this missing aggregate brief is a documentation note, not an inferred mathematical premise.

Pinned local source hashes (SHA-256):

- MAIN: `68e9167f04e4a04689ea163c74e02ffcaea657b252726080abdbe37bdba48c1b`.
- AMENDMENTS: `c887d1e27354a3db7fb8a20d8bf3e33a9ef95ff3173f925ba5ebfab192651881`.

## LP-LIFT — PASS WITH NOTES

The exact bounded target is L14's chart lift and D1 premises, not L14/T15 closure.
`StoppedOn` (Stopped:58–63) is literally LP-CONF's antecedent
(Confinement:180–183), including `uIcc 0 t`, strict action radius and strict AMD margin.
`LiftData` contains standing/initial premises, the shared compact action set, budget and positive
orientation. None is the desired stopped drift or first-exit conclusion.

The proof obtains positive individual angular momenta using conservation of total momentum and
`cross_sign_and_margin`; it then constructs a maximal chart solution through a chart inverse,
projects it, and uses ODE uniqueness only on its intersection with the stopped interval.
Continuation uses the compact zero-angle set and the derived margin `n*r > 0` to establish chart
safety. It does not assume that the lift already exists on the queried interval.
The resulting maximal interval is open and contains both endpoints of `uIcc 0 t`, so the lift has
two-sided derivatives there, also for negative t and t=0. Restriction of the physical solution is
by the literal `IsSolutionIn.mono` interface. No extension of the physical curve beyond J is assumed.

All names below have namespace `KAM.Planetary.StrongAMD`.

| Node | Declaration | Verdict | Reason |
|---|---|---|---|
| L14 data | `LiftData` | PASS | Source/typing/initial premises only; orientation belongs to T15's prograde reduction. |
| L14 stop | `StoppedOn` | PASS | Exact strict antecedent, with both time directions. |
| L14 budget | `LiftData.n_mul_r_pos` | PASS | Derived from n≥2 and r>0. |
| L14 localization | `LiftData.actionVector_mem` | PASS | Closed-ball premise applied directly. |
| L14 modulus | `LiftData.abs_threshold_sub_le` | PASS | Uniform modulus on the same U; budget retains n*r. |
| L14 collar | `LiftData.threshold_ball_le` | PASS | Correct sign of threshold comparison. |
| L14 whole ball | `LiftData.strongAMD_le_of_stopped` | PASS | C≤B(I0)−δ/4 derived from stopped conditions and budget. |
| L14 orientation | `LiftData.prograde_of_stopped` | PASS | Conservation supplies orientation along the interval; no prograde conclusion assumed. |
| restriction | `lpMovingSolutionOn_mono` | PASS | Subset restriction of the ODE/domain predicate. |
| continuation data | `lpStoppedBox` | PASS WITH NOTES | AMDBox used solely as data for liftQ; see definition classification. |
| continuation | `LiftData.zeroAngle_mem_liftQ` | PASS | Closed action box and whole-ball AMD bound. |
| continuation | `LiftData.mem_chartSafe_of_liftQ` | PASS | Derives Γ_i<I_i and collision-freeness from the positive n*r margin. |
| L14 lift | `LiftData.lpChartLift_of_stopped` | PASS | Open chart ODE interval, exact projection and initial action. |
| L13 block | `lpStoppedBlock` | PASS | Exactly the whole secular ball, centre and radii. |
| D1(ii) | `lpRescale_mem_realDom` | PASS | Strict fast action bound, real strip, exact slow base witness. |
| D1(i)–(iii) | `lpChartLift_premises` | PASS | Lift, outer localization, initial action and slow membership all derived. |
| conditional adapter | `lpStopped_drift_of_chartData` | PASS | Explicitly conditional, distinct name and docstring; ExtNFHyp/trace not claimed proved here. |

Definition classification:

- `LiftData`: proposition bundling source premises; inconsistent inputs simply have no witness.
- `StoppedOn`: literal predicate for every real t; t=0 includes the initial point, and negative t reverses
  no inequalities. No fallback or selected witness.
- `lpStoppedBox`: literal auxiliary record for arbitrary ν,I0,δ,r. Zero fields are unused AMDBox metadata,
  not asserted admissibility. `liftQ` reads only the bounds and outerAMD; `liftQ_isCompact` requires no
  AMDBox admissibility. This is a justified implementation variation from the brief's reuse warning:
  no AMDBox safety/stopped theorem supplies a source conclusion. The proof establishes `hQW` itself.
- `lpStoppedBlock`: literal PartialBlock, even for nonpositive widths. The localization theorem is valid
  for arbitrary wS (including zero, with Lean's total division), because the scaled slow witness matches
  exactly. This is a stronger algebraic statement, not an invertible physical rescaling at zero;
  physical use through `ExtNFHyp` has positive widths. No proof uses a zero-width inverse.

Note: MAIN:480's −7δ/16 estimate uses Ω≤δ/16. This package deliberately proves the weaker −δ/4
bound requested by its brief from the N6 stopped budget; it suffices for secularBall. It does not
claim the literal −7δ/16 statement without that extra source bound. Reflection and hstop discharge
remain outside LP-LIFT. Missing freeze-proposal wording in the new module docstrings is a minor
SPEC §4 documentation deviation; the modules do identify their package, source and non-frozen status.

## LP-DOMX — PASS WITH NOTES

The missing L8 clauses are now proved on a uniform tube. Positions AND momenta are the two components
of Ψc; the Fréchet derivative bound controls both in the Pi/product sup norm. `cDot` is the bilinear
sum of squares, not a Hermitian norm. The coordinatewise estimate `2ε²+4Qε` is a valid sup-norm
version of the source's Euclidean estimate. The pair perturbation correctly allows two position
errors (each ≤ε/2). Positive real parts keep every radicand inside the principal slit plane.
The proofs establish holomorphy of the principal square root before taking its inverse, and establish
real trace as the physical Euclidean length, including the zero-vector algebraic identity.
The physical denominator results themselves require dS,dP>0, hence exclude zeros.

| Node | Declaration | Verdict | Reason |
|---|---|---|---|
| Cauchy | `norm_fderiv_le_cauchyBall` | PASS | Positive radius; restricts to complex lines and bounds operator norm by M/ρ. |
| tube | `complexTube_mono` | PASS | Correct for all radii, including empty nonpositive tubes. |
| tube | `isOpen_complexTube` | PASS | Union of open balls. |
| tube | `complexTube_add_shift` | PASS | Exact integer fast-shift invariance. |
| tube | `closedBall_subset_complexTube` | PASS | Triangle inequality; negative σ gives an empty closed ball. |
| tube bound | `exists_norm_le_halfTube` | PASS | Compact thickened cell and periodicity; empty K is harmless. |
| derivative | `norm_fderiv_le_quarterTube` | PASS | Quarter-radius closed ball lies in the half tube. |
| Lipschitz | `norm_sub_le_of_quarterTube` | PASS | Convex ball inside quarter tube, ordinary derivative bound. |
| coordinates | `cBody` | PASS | Same finite product indexing as real bodyVector on its full carrier. |
| bilinear square | `cDot` | PASS | Literal sum of two complex squares. |
| trace | `cBody_ofReal` | PASS | Definitional equality. |
| trace | `cDot_ofReal` | PASS | Real planeSq, no norm substitution. |
| branch trace | `cDot_cpow_ofReal` | PASS | Principal half-power equals nonnegative real Euclidean length. |
| perturbation | `re_cDot_ge` | PASS | Coordinatewise estimate implies nonnegativity of relevant bounds when inhabited. |
| reciprocal | `norm_inv_sqrt_le` | PASS | d>0 and Re≥d²/2 give √2/d. |
| branch | `differentiableOn_inv_sqrt_cDot` | PASS | Slit-plane cpow, then nonzero inverse. |
| chart data | `IsChartExtension` | PASS | Output specification; real trace, safety and periodicity, no existence assumed. |
| restriction | `IsChartExtension.toSmallerTube` | PASS | Restriction retains real trace and shift invariance. |
| L8 chart/momenta | `exists_strongChart` | PASS | Coordinate extensions with a common positive radius; uniform half-tube bound. |
| denominator helper | `exists_tube_re_cDot_ge` | PASS | Explicit conditional estimate from chart and derivative data. |
| L8 denominators | `exists_strongDenominatorTube` | PASS | Real separation supplied by GEOMOD on core with margin 3δ/16. |
| chart coordinate | `differentiableOn_chart_coord` | PASS | Continuous linear projections. |
| L8 data | `StrongTubeData` | PASS | Output bundle containing all newly required estimates and traces. |
| L8 assembly | `exists_strongTubeData` | PASS | Constructs the bundle; does not assume its difficult fields. |
| L8 containment | `lemma8_complete` | PASS WITH NOTES | Uniform data plus (22) containment; existing D0/D1/D6 provide setup and exact split. |

Definition classification:

- `cBody` and `cDot`: literal finite formulas for all complex inputs, no choices/fallbacks.
- `IsChartExtension`: proposition defining an extension on its specified tube; outside the tube Ψc is
  unconstrained, appropriately for a local extension. Nonpositive radius yields empty-tube conditions;
  existence/use theorems supply positive radii.
- `StrongTubeData`: proposition defining output data, with positive R,ρ,dS,dP and ρ≤R/4. It does not
  encode an input hypothesis hiding L8: `exists_strongTubeData` constructs every field. M,M' need not be
  positive in this interface; one can inflate them and combine M,M',M/(R/4),M'/(R/4),1 to obtain the
  source's single positive bound. Empty core/level-set cases are vacuous, as in MAIN:257.

Bookkeeping: **the previous L8 missing-clause invoice is paid**. L8 may count PROVED using the existing
D0 (`strongLSet`), D1 (`exists_isSharedTube`), D6 (`movingHamiltonian_poincareProd_split`) together with
`lemma8_complete`, not by pretending its `hg` argument was unconditional. The constants/functions precede
I0 and no μ occurs. Its explicit widths are rStar=min(4r,ρ/2), s=b=ρ/8; rStar≤4r is N3, and (22)
lies in the denominator tube ρ⊆R/4, where all derivative bounds hold. The source's positive common M is
an elementary enlargement of the displayed separate bounds; the exact real Hamiltonian split is the
existing D6 theorem, not a truncation. Initial secular states of AMD≤B(I0)−δ lie inside the whole
B(I0)−δ/4 ball with positive squared-radius slack 3δ/4. No new dynamical assumption is needed.
This bookkeeping conclusion concerns L8, not the remaining L13 analytic/Fourier adapter inputs or T15.
Module docstrings again omit SPEC §4's exact freeze-proposal phrase (documentation only).

## LP-THR2 — PASS

| Node | Declaration | Verdict | Reason |
|---|---|---|---|
| F3 carrier | `orderedCrossThreshold` | PASS | hn:2≤n excludes empty adjacent families at n=0,1. |
| F3 carrier | `orderedStrongThreshold` | PASS | Threads hn to cross threshold; star family is also nonempty. |
| compatibility | `orderedCrossThreshold_eq` | PASS | Literal rfl. |
| compatibility | `orderedStrongThreshold_eq` | PASS | Remains literal rfl. |
| pair minimum | `orderedPairThreshold_isLeast` | PASS | Attained least value from existing pairThreshold_isLeast; no witness selection. |
| pair value | `orderedPairThreshold_existsUnique_value` | PASS | Uniqueness of the scalar least value, not uniqueness of the optimizer. |
| positivity | `orderedStrongThreshold_pos` | PASS | Existing proof still applies definitionally, with positive masses. |
| continuity | `continuous_orderedStrongThreshold` | PASS | Existing proof still applies on OrderedActions. |
| first action | `orderedStrongThreshold_eq_min_first` | PASS | Only the required hn argument changed. |

The two changed definitions remain literal finite infima/minimum on OrderedActions, not guarded
fallbacks. hn is typing data, not a conclusion-shaped premise. For n=2 the adjacent family has one
member; for larger n it is finite and nonempty. Positive masses are needed for the physical reading
and positivity results, and are explicit in those consumers; the least-value characterization is
valid even more generally. Raw total threshold helpers retain their previous off-carrier behavior;
the package does not certify them as source physical minima outside the source carrier.
Repository-wide search finds orderedCrossThreshold/orderedStrongThreshold uses only in
Threshold/{Defs,Strong}.lean; no missed external caller. F3's implementation repair is complete;
changing a future freeze inventory remains the orchestrator's separate task.

## Checks and evidence

All Lean/Lake calls below were serial and inside the binding D53 scope:

```text
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 <command>
```

1. Lint, only through the authorized wrapper:

```text
/root/code/KAM-inp/.drafts/LP/lp_lint.sh /root/code/KAM-inp-lp-thr
check_lean_modules: PASS (3702 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
exit 0
```

2. Targeted builds through the serial compile-gate/capped LP driver (its actual Lake calls use the
exact D53 wrapper above):

```text
/root/code/KAM-inp/.drafts/LP/lp_build.sh /root/code/KAM-inp-lp-thr KAM.Planetary.StrongAMD.ChartLift KAM.Planetary.StrongAMD.AnalyticDomain KAM.Planetary.StrongAMD.Threshold
Build completed successfully (9270 jobs).
Build completed successfully (9179 jobs).
Build completed successfully (9051 jobs).
exit 0
```

These are targeted dependency-closure builds using the existing snapshot, not a clean/core-library
rebuild. Existing dependency warnings were replayed (unused variables/tactics, deprecated dif_pos).
No resource override or application build was introduced.

3. Single temporary probe, run as the D53-wrapped command:

```text
lake env lean .lake/abi-scratch/LPW3CAudit.lean
exit 0
```

The probe imported ChartLift, AnalyticDomain and Threshold. It checked all 41 new/changed public
theorem exports and affected compatibility/consumer theorems listed below. Each output was exactly
`'<fully qualified name>' depends on axioms: [propext, Classical.choice, Quot.sound]`
(up to line wrapping). No sorryAx or additional axiom appeared.

```text
KAM.Planetary.StrongAMD.LiftData.n_mul_r_pos
KAM.Planetary.StrongAMD.LiftData.actionVector_mem
KAM.Planetary.StrongAMD.LiftData.abs_threshold_sub_le
KAM.Planetary.StrongAMD.LiftData.threshold_ball_le
KAM.Planetary.StrongAMD.LiftData.strongAMD_le_of_stopped
KAM.Planetary.StrongAMD.LiftData.prograde_of_stopped
KAM.Planetary.StrongAMD.lpMovingSolutionOn_mono
KAM.Planetary.StrongAMD.LiftData.zeroAngle_mem_liftQ
KAM.Planetary.StrongAMD.LiftData.mem_chartSafe_of_liftQ
KAM.Planetary.StrongAMD.LiftData.lpChartLift_of_stopped
KAM.Planetary.StrongAMD.lpRescale_mem_realDom
KAM.Planetary.StrongAMD.lpChartLift_premises
KAM.Planetary.StrongAMD.lpStopped_drift_of_chartData
KAM.Planetary.StrongAMD.norm_fderiv_le_cauchyBall
KAM.Planetary.StrongAMD.complexTube_mono
KAM.Planetary.StrongAMD.isOpen_complexTube
KAM.Planetary.StrongAMD.complexTube_add_shift
KAM.Planetary.StrongAMD.closedBall_subset_complexTube
KAM.Planetary.StrongAMD.exists_norm_le_halfTube
KAM.Planetary.StrongAMD.norm_fderiv_le_quarterTube
KAM.Planetary.StrongAMD.norm_sub_le_of_quarterTube
KAM.Planetary.StrongAMD.cBody_ofReal
KAM.Planetary.StrongAMD.cDot_ofReal
KAM.Planetary.StrongAMD.cDot_cpow_ofReal
KAM.Planetary.StrongAMD.re_cDot_ge
KAM.Planetary.StrongAMD.norm_inv_sqrt_le
KAM.Planetary.StrongAMD.differentiableOn_inv_sqrt_cDot
KAM.Planetary.StrongAMD.IsChartExtension.toSmallerTube
KAM.Planetary.StrongAMD.exists_strongChart
KAM.Planetary.StrongAMD.exists_tube_re_cDot_ge
KAM.Planetary.StrongAMD.exists_strongDenominatorTube
KAM.Planetary.StrongAMD.differentiableOn_chart_coord
KAM.Planetary.StrongAMD.exists_strongTubeData
KAM.Planetary.StrongAMD.lemma8_complete
KAM.Planetary.StrongAMD.orderedCrossThreshold_eq
KAM.Planetary.StrongAMD.orderedStrongThreshold_eq
KAM.Planetary.StrongAMD.orderedPairThreshold_isLeast
KAM.Planetary.StrongAMD.orderedPairThreshold_existsUnique_value
KAM.Planetary.StrongAMD.orderedStrongThreshold_pos
KAM.Planetary.StrongAMD.continuous_orderedStrongThreshold
KAM.Planetary.StrongAMD.orderedStrongThreshold_eq_min_first
```

The same invocation elaborated three `example ... := rfl` checks: StoppedOn equals the literal
LP-CONF antecedent, orderedCrossThreshold equals crossThreshold, and orderedStrongThreshold equals
strongThreshold. No diagnostics. The scratch file was removed after the successful check.

4. Kernel replay and short-name checks were not rerun: the user explicitly supplied them as
launcher checks already performed, and requested economical statement/carrier review. Their raw
output/exit codes are not visible in this session, so this report does not invent a fresh
leanchecker exit code or independently attest those launcher logs. The fresh axiom probe and targeted
builds above are independent checks performed here.

5. Static checks:

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
- `git diff --check inp-lp...HEAD -- KAM`: empty, exit 0.
- `git diff --check inp...HEAD`: exit 2, exactly
  `docs/tracks/LP/freeze/STATEMENT-REVIEW-1.md:477: new blank line at EOF.`
  This is a pre-existing documentation-only whitespace note; the handoff's unqualified clean claim
  does not hold for the full branch diff. The audited KAM diff is clean.
- No forbidden proof escape/resource override, EuclideanSpace, provider import or direct frozen
  theorem import found in the new modules; global lint passed. Source-escape and dependency hygiene
  are also supported by all 41 standard-only axiom sets.
- New source files have module headers, public imports, docstrings and public sections; definitions
  are in exposed sections. All changed hand-written Lean files are at most 229 lines. The generated
  root gained exactly ten imports, an already-present producer/orchestrator change, not an auditor edit.
- The new DOM facade import is acyclic: Bounds imports DOM parts, not its facade.
- `rg -n 'orderedCrossThreshold|orderedStrongThreshold' KAM --glob '*.lean'`: only Defs and Strong;
  Pair's new characterization exports are separately reviewed above.


## Combined verdict — PASS WITH NOTES

No blocking source-fidelity, carrier or conclusion-shaped-hypothesis defect found in the bounded
package. LP-LIFT derives D1's geometric premises; LP-DOMX pays L8's omitted bounds/denominators;
LP-THR2 implements the specified carrier repair. This is package acceptance, not a seal audit or
closure of L14/T15 or the analytic adapter.

Notes: missing aggregate package brief; deliberate auxiliary AMDBox data reuse; stronger arbitrary-wS
localization with positivity restored by the consuming analytic data; source/documentation accounting
as specified above. No new suspected mathematical erratum in MAIN or AMENDMENTS. No code was changed
by the auditor. Only this report is retained; temporary probes are removed after checking.
