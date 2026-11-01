# LP-W5C independent package audit 1

Audited 2026-11-01 at `fe922018f230e59bb98ad8769b5b834ea6299f33` in `/root/code/KAM-inp-lp-w5c`.
Baseline `inp`: `5090562d4826c933407f5140aa2ea3e2fb32f5bc`; package baseline `inp-lp`:
`a2dc16709f099a41d331030c0a1dde4628b9457c`.

Read the common package-audit brief, AGENTS, PLAN, DECISIONS (including current-main D53, D58–D59),
LP-W5C and its three component briefs, SPEC, MAIN and AMENDMENTS, LP3-PLAN, and the combined/component
handoffs. No LP declaration is frozen. Verdicts below concern this bounded package and exact statement
surface; they do not authorize a freeze or re-audit the previously audited suppliers.

## LP3-PS — PASS

| Node | Declaration (`KAM.Planetary.StrongAMD`) | Verdict | Reason |
|---|---|---|---|
| Generic state | `nekPlanarState` | PASS | Literal 13-clause state predicate, three drift scales replaced by `s`. |
| Generic solution | `nekPlanarSol` | PASS | Initial value, moving solution, uniqueness, all per-time clauses; reconstruction added in Main. |
| Reflection/state | `nekPlanarState.of_reflectPhase` | PASS | Transports every clause, including osculating vector error and annulus gaps. |
| Reflection/solution | `nekPlanarSol.of_reflectPhase` | PASS | Reflects solution back; uniqueness transported using involutivity. |
| Oriented assembly | `nek_planar_safety_of_prograde` | PASS | Explicitly named internal oriented helper; supplier discharges stopped drift. |
| LP3-1 | `lp3_planar_strongAMD_safety` | PASS | Full LP1 type with exactly the three authorized changes. |
| Normalized LP3-1 | `lp3_planar_strongAMD_safety_normalized` | PASS | Same comparison; retains `_hνmax`, `_hνle`. |

`Nek/PlanarSafety/Prograde.lean:62–63` obtains the shared tube and uniform supplier constants from
`lp_stopped_drift_nek_hstop`; the later `hstop := hdr z₀ hI0 hd` is passed to
`strongFirstExit_of_stopped_drift`. Neither stopped confinement nor an analytic estimate is assumed by
the headline. Membership in the sharp level set is derived from architecture membership, nonnegative AMD,
and the initial margin. The closed radius ball lies in the shared tube by the supplied `r ≤ 4rg`.

The supplier witnesses (`StrongAMD/Nek/Drift.lean:175`) choose `c = B₀^(−a_n)`, `T₀ = 1`.
The assembly takes `AΛ = B₀^b_n/2`,
`Aa = B₀^b_n (max C 0 + 1)(Σ ν_i^(−2) + 1)`. For positive `B₀, μ`, `Real.mul_rpow`
gives `r = B₀^b_n μ^b_n`; the first-exit improvement `r/2` gives the advertised action bound.
The axis estimate is paid by the displayed `Aa`, and conservation of angular momentum bounds AMD drift
by the sum of the `n` action errors.

Main derives `totalMomentum z₀ ≠ 0` from `C ≤ B−δ < B ≤ Λ₀`, using `δ > 0` and `n ≥ 2`.
The negative case is reflected, the positive case uses the oriented helper. Newtonian reconstruction is
then applied to the returned moving solution. There is no prograde or arithmetic premise in either headline.

## LP3-SP-SAFE — PASS

| Node | Declaration (`KAM.Planetary.Spatial`) | Verdict | Reason |
|---|---|---|---|
| Generic state | `SpatialNekSafeState` | PASS | LP2 state predicate with `ρ` in exactly the three drift positions. |
| Generic solution | `SpatialNekSafeSol` | PASS | LP2 solution predicate with the generic state predicate. |
| Rotation/state | `SpatialNekSafeState.transport_rotate` | PASS | Orthogonal proper rotation preserves all physical and osculating clauses. |
| Rotation/solution | `SpatialNekSafeSol.transport_rotate` | PASS | Inverse rotation `Rᵀ` preserves solutions and transports uniqueness. |
| Aligned assembly | `spatial_nek_safety_of_aligned` | PASS | Internal aligned helper; stopped estimate discharged by audited supplier. |
| LP3-2 | `lp3_spatial_strongAMD_safety` | PASS | Full LP2 type with exactly the three authorized changes. |
| Normalized LP3-2 | `lp3_spatial_strongAMD_safety_normalized` | PASS | Same comparison; retains `_hνmax`, `_hνle`. |

`Nek/SpatialSafety/Aligned.lean:68` obtains `B₀ ≥ 1`, its positive threshold and drift statement from
`spatial_stopped_drift_nek`. The proof builds `SpatialLiftData`, derives the initial level membership,
and passes `hstop := hdrift z₀ hz₀L hd` to `spatialStrongFirstExit_of_stopped_drift`.
The alignment field is confined to this separately named helper.

Here `c = B₀^(−a_n)`, `T₀ = 1`, `Bb = B₀^b_n`, `AΛ = Bb/2`,
`Aa = (Bb/2)(2 max C 0 Σ ν_i^(−2) + 1)`. The `hrad` and `hhor` equalities use positive-base
`Real.mul_rpow`, with no physical-time or period conversion. The exponents use the fast dimension `n`.

Main derives `angularMomentum3 z₀ ≠ 0` by the same sharp-threshold contradiction before choosing a proper
rotation to `e₃`; positivity of its length justifies the inverse scalar. It rotates the obtained solution
back, transports uniqueness, and reconstructs the Newtonian solution. There is no inclination, nonzero
momentum, alignment, secular or arithmetic premise in either headline.

Both assemblies choose
`μ₀ = min (min μsupplier μosc) (min (dS₁/(2 Aosc)) (dP₁/(4 Aosc)))`,
`dStar = min dS₁ dS₂`, `dPair = min dP₁ dP₂`.
The new threshold gives `Aosc μ₀ ≤ dS₁/2` and `2(Aosc μ₀) ≤ dP₁/2`;
`μ₀ ≤ μosc` and the existing osculating receipt give the corresponding inequalities for `dS₂,dP₂`.
The `min_choice` branches therefore prove both N10 inequalities for the actual exported minima.
Every constant is chosen before `μ,z₀`; dependence is only on `(n,ν,A,δ)`.

## LP3-SRC — PASS

| Node | Declaration | Verdict | Reason |
|---|---|---|---|
| Planar/general | `StrongAMD.lp3_planar_strongAMD_safety_source_general` | PASS | Exact §3b template with the three LP3 changes; obtained from LP3-1. |
| Planar/normalized | `StrongAMD.lp3_planar_strongAMD_safety_source` | PASS | Exact normalized template; normalization premises retained. |
| Spatial/general | `Spatial.lp3_spatial_strongAMD_safety_source_general` | PASS | Exact post-SRCB2 §3d template; canonical elements use `spatialSource*`. |
| Spatial/normalized | `Spatial.lp3_spatial_strongAMD_safety_source` | PASS | Exact normalized template; directly consumes normalized LP3-2. |

Names in this table are under `KAM.Planetary`. The planar statement deliberately keeps the raw canonical
action/axis/eccentricity formulas as specified by §3b; the spatial statement uses the source restrictions
throughout as specified by §3d. The canonical `h₀` binders merely repeat physical/mass data already assumed;
they are constructible from those assumptions. At later times, the proof constructs `hs` from returned
physicality and `ho` from positive masses, positive `μ`, nonzero positions, and returned osculating ellipticity.
Thus the existential guards are proved conclusions, not premises smuggling in safety.

## Combined verdict — PASS WITH NOTES

All three components PASS. No blocking mathematical or statement-fidelity issue found. Notes are the
explicit generated-root exception and the scope of the launcher checks below; no frozen statement is sealed.

### Independent full-signature comparison

Compared each entire declaration type, including everything after `let T :=`, to its corresponding landed
LP1/LP2 `Main.lean` or `Source.lean` template. Removed only the `γ τ`, `hγ hτ` binders and the complete
Diophantine arrow; substituted the time exponent once and the drift expression three times. Ignoring whitespace
and the declaration name, the resulting strings are identical for **all eight** types:

| LP3 suffix | Planar | Spatial |
|---|---|---|
| `safety` | PASS | PASS |
| `safety_normalized` | PASS | PASS |
| `safety_source_general` | PASS | PASS |
| `safety_source` | PASS | PASS |

Each comparison independently counted one deleted Diophantine premise, one time-exponent replacement,
and exactly three drift replacements. Full new type lengths before whitespace removal were, respectively,
planar 2982/3033/4589/4640 and spatial 3324/3375/5195/5240 characters (excluding theorem names).
This checks all binders, quantifier/constant order, N10, `let T`, and the complete conclusion, rather than
just the type prefix. In particular all 13 per-time clauses survive.

MAIN §1 and T15/T19 are the nonresonant source, not themselves a proof of LP3: MAIN line 616 explicitly
leaves the resonance-tolerant upgrade separate. The component briefs and LP3-PLAN §1–§4 authorize replacing
that supplier with the sealed partial-convexity route. The retained geometric, first-exit, osculating and
reconstruction claims agree with MAIN as amended (especially N2, N6 and N10). Precisely the advertised tradeoff
remains: no arithmetic hypothesis and whole-sublevel uniformity, with time exponent
`2/(6n²−3n+14)` and drift exponent `3/(6n²−3n+14)` instead of the nonresonant time exponent and `√μ`.
Nothing else in the headline type changes. General-mass statements are stronger than MAIN's normalized
mass assumption; normalized/source forms retain that assumption under D59/OD-3.

### Definition classification and edge cases

Independent body comparisons also returned `True` for all four predicates after substituting the generic scale and predicate names.

The four definitions in the two Orientation modules are **logical packaging**, not newly totalized physical
objects: `nekPlanarState`, `nekPlanarSol`, `SpatialNekSafeState`, `SpatialNekSafeSol`. Their bodies are literal
conjunctions of the intended clauses on their whole declared carriers. There is no choice, fallback, division
or fabricated value in any new definition. The state predicates require current physicality and chamber
membership explicitly. Solution predicates intentionally omit reconstruction, which Main supplies.

The generic scale `s`/`ρ` is an arbitrary real; at zero it demands zero action/axis/AMD error, and at negative
values it retains the literal inequalities (possibly unsatisfiable), with no fallback. The transport lemmas
remain meaningful for every scale. Their LP3 uses have positive scale from `μ > 0`; `μ = 0` and negative `μ`
are excluded at the headline. `hn : 2 ≤ n` excludes empty/single-planet threshold indexing. Empty `A` or an empty
admissible sublevel leaves a vacuous initial-state assertion without adding a nonemptiness assumption.
Equality `C(0) = B(I⁰)−δ` is retained. Circular and coplanar states are not excluded. At zero total angular
momentum the headline premises contradict the positive margin, as proved before any orientation choice.
For arbitrary `T`, solution predicates use exactly the stated closed interval; the headline produces positive `T`.

No new structure, instance or bundled field assumes a proof obligation. The transport helpers assume the
state they transport, and the oriented/aligned helpers have distinct names; neither substitutes its internal
orientation premise for the source-facing theorem.

### Checks and exact validation scope

All Lean/Lake calls in this audit use D53: `systemd-run --user --scope --quiet -p MemoryMax=4G
-p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 <command>`. Calls were serialized; LP wrappers
also check available memory and the build wrapper acquires a compile-gate slot.

1. Lint (the only lint invocation):

   ```sh
   /root/code/KAM-inp/.drafts/LP/lp_lint.sh /root/code/KAM-inp-lp-w5c
   ```

   Exit **0**, output:

   ```text
   check_lean_modules: PASS (3798 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
   ```

   The application exception is explicitly file-hash-only; this does not claim a fresh lunar application build.

2. Targeted builds (one module per call, in this order, through the D53 LP compile-gate wrapper):

   ```sh
   /root/code/KAM-inp/.drafts/LP/lp_build.sh /root/code/KAM-inp-lp-w5c \
     KAM.Planetary.StrongAMD.Nek.PlanarSafety \
     KAM.Planetary.StrongAMD.Nek.PlanarSafety.Source \
     KAM.Planetary.Spatial.Nek.SpatialSafety \
     KAM.Planetary.Spatial.Nek.SpatialSafety.Source
   ```

   Exit **0**. The four final success lines were, respectively:

   ```text
   Build completed successfully (9368 jobs).
   Build completed successfully (9369 jobs).
   Build completed successfully (9428 jobs).
   Build completed successfully (9429 jobs).
   ```

   Builds reused the existing snapshot, replaying dependency linter warnings (unused variables/section
   variables/simp arguments); no compilation failure occurred. The two facade and two Source targets cover
   all ten new modules by their import closure.

3. Independent axiom and definitional-equality probe, importing the two new Source modules, under
   the project options:

   ```sh
   /root/code/KAM-inp/.drafts/LP/lp_lean.sh /root/code/KAM-inp-lp-w5c .lake/abi-scratch/LPW5CAudit1.lean
   ```

   Exit **0**, no errors. `#print axioms` for **all fourteen new public theorems** listed in the
   three declaration tables printed exactly `[propext, Classical.choice, Quot.sound]` for each export.
   These include both internal oriented/aligned assemblies and all four transport lemmas, not only the
   eight headline/source theorems. Four additional `example ... := rfl` checks verified that specializing
   each new state/solution predicate at `Real.sqrt μ` is definitionally equal to its LP1/LP2 counterpart.
   The temporary probe was deleted after successful elaboration.

4. Kernel replay and short-name checks: **not rerun**, as the audit prompt explicitly states that the
   launcher already ran them. The launcher's detailed output and numeric replay exit code are not visible
   to this auditor; no locally observed replay receipt is claimed. The fresh builds/probe above are separate
   checks, not a substitute claim of independent kernel replay. Frozen-provider type/seal probes are
   inapplicable: this package defines no provider or frozen export.

5. Source inspection of all ten new modules found no proof escapes, `sorry`, forbidden declarations,
   resource overrides, or `EuclideanSpace`; module headers/imports/docstrings/public sections are present.
   Four new definitions, fourteen new theorems; no other new declaration kind. Largest new file:
   spatial `Source.lean`, **238 lines**. Module-level imports contain no provider or draft frozen anchor.
   The sealed partial-convexity theorem is consumed through the previously audited suppliers under D58/OD-13.
   `git diff --check inp-lp...HEAD`: exit **0**, no output.


### Files, deviations, errata and uncertainty

The package diff is exactly ten new modules (1513 inserted lines including the root delta):
`StrongAMD/Nek/PlanarSafety.lean` and its `Orientation`, `Prograde`, `Main`, `Source` parts;
`Spatial/Nek/SpatialSafety.lean` and its `Orientation`, `Aligned`, `Main`, `Source` parts;
plus ten generated imports in `KAM/Root/Planetary.lean`.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.
The generated part `KAM/Root/Planetary.lean` does change, so the literal broad generated-root prohibition
has the disclosed package-authorized exception; no source root was regenerated by this auditor.
The parallel drift-scale predicates are the other explicitly authorized engineering deviation; LP1/LP2
files are unchanged. No new MAIN/AMENDMENTS defect, blueprint contradiction, heartbeat/default-elaboration
failure or memory design signal was found. Previously audited supplier proofs remain outside this bounded audit.
Only this report is a persistent auditor edit; temporary probes are deleted. No state-changing git command ran.
