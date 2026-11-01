# LP-OSC independent package audit 1

Verdict: **PASS WITH NOTES**, for the planar, non-frozen package and its exact statements. No blocking mathematical or hypothesis defect found. This is not approval of a frozen anchor or a spatial/dynamical extension.

Audited HEAD `9ed9490ed7a68dccedbfbf0eb6c431d816261770`; `inp` = `9dacd25fb9b1a0390123599c68caed715926d347`; `inp-lp` = `7a36432eb1f89066bcd06335ef88495c9c1adb5f`. Read AGENTS.md, PLAN.md, DECISIONS.md, the independent audit brief, LP-OSC handoff/AUDIT FOCUS, the package brief at `/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP-OSC.md`, SPEC.md, MAIN Lemma 16 and AMENDMENTS.md (especially N10).

Compared `git diff inp...HEAD` and scoped the Lean review to `git diff inp-lp...HEAD -- KAM`: four new Osculating modules (1006 lines) and four generated import additions in `KAM/Root/Planetary.lean`. Also checked the directly consumed existing GEOMOD, orbital and Hamilton-field statements, without reopening those packages. No provider/frozen-type seal probes apply: there are no new frozen anchors.

## Main conclusions and source fidelity

| Intended node | Export | Verdict | Result |
|---|---|---|---|
| MAIN (42), velocity (10) | definitions and `oscVelocity_eq_movingField` | PASS | Literal unit-mass formulas; exact q-block of the physical moving Hamiltonian. |
| L16 item 1, (43) | `exists_osc_estimates` / `OscEstimate` | PASS WITH NOTES | Uniform summed axis/vector error and both endpoint errors, plus strict eccentricity and negative specific energy; see mass note. |
| L16 item 2 | `specAxis_tangency`, `osc_tangency` | PASS | Precisely the radial-inequality formulation requested by the package brief. |
| L5 → L16 | `barrier_osc_data` | PASS | All uniform input bounds proved from GEOMOD, with the same canonical peri/apo gaps. |
| L16 item 3 / N10 | `osculating_barrier` | PASS | Explicit smallness restrictions and half star/adjacent-annulus gaps. |

1. **Mass and energy.** MAIN:28 and SPEC distinguish specific energy E from `keplerEnergy = νᵢ E`. Basic:115 proves this exact identity. Therefore `OscEstimate` uses `oscEnergy ≤ −(c/νᵢ)/2` when the input is total `keplerEnergy ≤ −c`. The package brief item 1 literally says “`oscEnergy ≤ −c/2`”; this is a documentation scale mismatch outside the normalized source domain. On MAIN/SPEC's domain `max ν = 1`, every νᵢ ≤ 1, so the implemented bound actually implies that literal bound. For arbitrary positive masses the implementation correctly states the specific scale. No source result was weakened on its intended domain. Record this wording discrepancy for the later freeze proposal; do not silently identify the two c's.
2. **Mass upper bound.** The proof chooses `M = 1 + ∑ ν`, `m0 = min ν` when indices exist, `D = n P`, `Pv = P/m0`, `c1 = c/M`, `s = M μ`. Thus `kᵢ − 1 ≤ M μ`, with no mass-normalization hypothesis. Constants are explicit functions of masses, dimension and bound data; no dependence on z, i or μ is introduced. `s0` is the minimum of 1 and two positive numerical thresholds; μ0 = s0/M. The relative energy bound follows from E ≤ −c/νᵢ and the error allowance c1/2 ≤ (c/νᵢ)/2.
3. **Exact (43).** The axis and eccentricity-vector errors are summed, with A = M(Aa + Ae). Both endpoint errors use Aosc = M(2 Aa + amax Ae). The vector division is scalar multiplication by 1/k, and all lengths are Euclidean `planeLength`, not Pi sup norms. Circular eccentricity causes no differentiation problem: the proof uses the reverse triangle inequality.
4. **Bridge.** From a(2 KE) = −ν, KE ≤ −c and ν ≤ M, obtain 2ca ≤ M. GEOMOD gives dS ≤ a(1−e), hence 2c dS ≤ M(1−e), so `e ≤ 1 − 2 c dS/M < 1`. This proof does not assume a uniform eccentricity margin as a new barrier premise. Position separation from GEOMOD also supplies `NoCollision` for the velocity identity.
5. **N10.** The final threshold is `min μ1 (min (dS/(2 Aosc)) (dP/(4 Aosc)))`. Both `Aosc μ0 ≤ dS/2` and `2(Aosc μ0) ≤ dP/2` are exported. One endpoint error pays the star gap and two endpoint errors pay the adjacent gap. The existential c, dS and dP are sourced from the same GEOMOD bounds used in the proof.
6. **Hypotheses and scope.** No new conclusion-shaped hypothesis or bundled unpaid osculating claim occurs. The numerical perturbation helpers are distinctly named and conditional; their hypotheses are discharged explicitly in the main proof. `hK` consists of the source physical/bounded-set data. Compactness of K is unnecessary once those bounds are supplied (a valid strengthening). `n ≥ 2` is required at the barrier interface; the generic estimates also work for n = 0 or 1. No trajectory-level tangent ellipse or `IsMovingSolutionOn` corollary is exported; the radial formulation is exactly the package's approved bounded target. No claim of a spatial version is audited.

## Every new public theorem

All names below are in `KAM.Planetary.StrongAMD`. Locations are in `KAM/Planetary/StrongAMD/Osculating/`, except `Osculating.lean` in its parent.

| Location | Declaration | Verdict | Reason |
|---|---|---|---|
| `Estimates.lean:49` | `planeSq_two` | PASS | Exact coordinate expansion; all planar vectors. |
| `Estimates.lean:52` | `planeDot_two` | PASS | Exact coordinate expansion; all planar vectors. |
| `Estimates.lean:55` | `planeSq_sub_planeSq` | PASS | Polarization identity on the full carrier. |
| `Estimates.lean:59` | `planeLength_sub_le` | PASS | Euclidean triangle inequality, no domain restriction. |
| `Estimates.lean:64` | `abs_planeSq_sub_le` | PASS | Cauchy–Schwarz and triangle inequality. |
| `Estimates.lean:70` | `planeLength_sum_le` | PASS | Finite Euclidean triangle inequality, including the empty sum. |
| `Estimates.lean:84` | `planeSq_specEccVector` | PASS | Lagrange identity with positive k and radius; correct k² denominator. |
| `Estimates.lean:109` | `planeDot_specEccVector` | PASS | Radial identity with positive k and radius. |
| `Estimates.lean:136` | `specAxis_tangency` | PASS | Item 2 radial formulation; negative energy yields positive axis. Allows radial e = 1; does not assert strict ellipticity. |
| `Estimates.lean:169` | `planeLength_le_of_sub` | PASS | Triangle inequality from explicit velocity bounds. |
| `Estimates.lean:176` | `abs_planeSq_sub_le'` | PASS | Small velocity perturbation and 0 ≤ μ ≤ 1; direct bound. |
| `Estimates.lean:191` | `abs_specEnergy_sub_le` | PASS | Energy expansion; k − 1 controlled by μ and radius bounded below. |
| `Estimates.lean:210` | `specEccVector_eq` | PASS | Definitional equality, including singular arguments. |
| `Estimates.lean:214` | `planeLength_F_sub_le` | PASS | Expanded numerator difference, using genuine position/velocity bounds. |
| `Estimates.lean:263` | `planeLength_specEccVector_sub_le` | PASS | Controls 1/k and its difference from 1 using k ≥ 1; no circular norm assumption. |
| `Estimates.lean:299` | `abs_specAxis_sub_le` | PASS | Conditional reciprocal estimate; energy-error premise is discharged by the preceding energy expansion in osc_core. |
| `Basic.lean:87` | `oscVelocity_eq_movingField` | PASS | MAIN (10); uses movingField_blocks with G = m₀ = 1 and NoCollision. |
| `Basic.lean:96` | `oscEnergy_eq_spec` | PASS | Exact definitional dictionary. |
| `Basic.lean:100` | `oscAxis_eq_spec` | PASS | Exact definitional dictionary. |
| `Basic.lean:103` | `oscEccVector_eq_spec` | PASS | Exact definitional dictionary. |
| `Basic.lean:107` | `planeSq_smul_eq` | PASS | Exact scalar homogeneity on all real scalars. |
| `Basic.lean:110` | `planeDot_smul_right_eq` | PASS | Exact bilinearity on all real scalars. |
| `Basic.lean:115` | `keplerEnergy_eq_spec` | PASS | νᵢ Eᵢ total/specific dictionary; νᵢ ≠ 0 is essential. |
| `Basic.lean:122` | `keplerAxis_eq_spec` | PASS | Exact axis dictionary for νᵢ ≠ 0, even when energy is zero under Lean division. |
| `Basic.lean:131` | `keplerEccVector_eq_spec` | PASS | Exact vector dictionary for νᵢ ≠ 0. |
| `Basic.lean:145` | `osc_tangency` | PASS | Item 2; μ ≥ 0 and νᵢ > 0 imply kᵢ > 0; radius and negative energy supplied. |
| `Core.lean:50` | `oscAE_pos` | PASS | Positivity under numerical bound data. |
| `Core.lean:53` | `oscAF_pos` | PASS | Positivity under numerical bound data. |
| `Core.lean:57` | `oscB_pos` | PASS | Positivity for dS > 0, any Pv. |
| `Core.lean:59` | `oscAe_pos` | PASS | Positivity under numerical bound data. |
| `Core.lean:63` | `oscAa_pos` | PASS | Positive denominator c1² and numerator. |
| `Core.lean:70` | `oscAperi_pos` | PASS | Positivity under numerical bound data. |
| `Core.lean:79` | `abs_peri_apo_sub_le` | PASS | Endpoint product expansion; conditional axis/eccentricity errors supplied by osc_core. |
| `Core.lean:111` | `osc_core` | PASS | Pointwise (43); explicit smallness conditions on s are numerical and discharged by s0 in the uniform theorem. |
| `Osculating.lean:58` | `exists_pos_bounds_mass` | PASS | Finite positive masses; n = 0 handled with witnesses m0 = M = 1. |
| `Osculating.lean:74` | `exists_osc_estimates` | PASS | Item 1; summed axis/vector error, common endpoint constant, positive constants, all states and indices; mass-scale note below. |
| `Osculating.lean:216` | `barrier_osc_data` | PASS | GEOMOD bridge; derives eStar = 1 − 2 c dS/M and collision-freeness rather than assuming them. |
| `Osculating.lean:268` | `osculating_barrier` | PASS | Item 3 and assembly: both N10 restrictions in the conclusion; all barrier states, velocities, estimates and half-gaps. |

## Definition classification and edge cases

All 21 new definitions are exposed literal arithmetic/vector formulas or an explicit proposition; there are no new abbrevs/structures, optimizer choices, branches, arbitrary extension values or hidden fields.

| Declaration | Classification and whole-carrier behavior |
|---|---|
| `specEnergy` | Literal specific energy; at q = 0, the division term is zero under Lean's field convention. Physical uses exclude q = 0. |
| `specAxis` | Literal −k/(2E); at E = 0 it is zero, without an elliptic interpretation. Tangency requires E < 0. |
| `specEccVector` | Literal (42) at parameter k; at k = 0 it is the zero vector, at q = 0 it is also zero. No physical theorem relies on these values. |
| `oscVelocity` | Literal finite vector sum and p/ν. νᵢ = 0 invokes ordinary division by zero; physical theorems have νᵢ > 0. μ = 0 recovers p/ν. |
| `oscParam` | Literal 1 + μνᵢ, for every real argument; physical estimates establish k ≥ 1. |
| `oscEnergy` | `specEnergy` with actual V and k, including the same zero-radius convention. |
| `oscAxis` | `specAxis` specialization, with the same zero-energy convention. |
| `oscEccVector` | `specEccVector` specialization, including k = 0 convention. |
| `oscEcc` | Euclidean length of the literal eccentricity vector, including zero at a circular orbit. |
| `oscPeri` | Literal a(1−e); physical perihelion interpretation only under elliptic conditions. |
| `oscApo` | Literal a(1+e); same qualification. |
| `keplerPeri` | Literal canonical a(1−e), retaining inherited Kepler definitions on all inputs. |
| `keplerApo` | Literal canonical a(1+e), same. |
| `oscAE` | Explicit arithmetic energy-error coefficient; 1/dS is totalized at dS = 0; uses require dS > 0. |
| `oscAF` | Explicit arithmetic numerator-error coefficient; same dS condition. |
| `oscB` | Explicit arithmetic energy-size coefficient; same dS condition. |
| `oscAa` | Explicit (AE+B)/c1², zero at c1 = 0 by field division; uses require c1 > 0. |
| `oscAe` | Explicit AF+1; physical positivity proved from bound data. |
| `oscAmax` | Explicit 1/(2c1); valid axis-bound interpretation requires c1 > 0. |
| `oscAperi` | Explicit 2Aa + amax Ae; no fallback beyond those literal arithmetic subexpressions. |
| `OscEstimate` | Transparent conjunction of exactly eight requested/strengthened clauses; no existential witness, theorem field, or hidden hypothesis. Outside positive physical inputs it remains that literal proposition, without an elliptic interpretation. |

These singular values are the standard totalization of the displayed rational formulas, not a replacement model on the physical carrier. The main theorems exclude every relevant singular denominator. At μ = 0 the dictionary recovers canonical elements for positive masses; main uniform results deliberately quantify 0 < μ. The tangency helper permits radial states with e = 1; it never asserts strict ellipticity there. Strict e < 1 in `OscEstimate` is proved separately from the uniform margin. Empty K/U yield legitimate vacuous assertions; no nonemptiness is assumed or needed. For n = 0 the finite mass-bound lemma chooses (1,1) and all planet clauses are vacuous. If eStar < 0, the hypotheses permit no indexed nonempty physical state, since eccentricity lengths are nonnegative; this is not used to evade a nonempty barrier.

## Hygiene and independent checks

Every Lean/Lake invocation made for this audit used the binding D53 wrapper:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 <command>
```

Checks were serial, including lint. No library-wide rebuild, replay, name-check rerun, heartbeat/recursion override, or state-changing git command was requested.

Targeted build (the prescribed driver holds the compile gate and invokes the above wrapper):

```sh
/root/code/KAM-inp/.drafts/LP/lp_build.sh /root/code/KAM-inp-lp-thr KAM.Planetary.StrongAMD.Osculating
```

Exit 0; terminal output `Build completed successfully (9129 jobs).` This is the targeted import closure, not a plain-library build. Cached `KAM.Kepler.Energy:106` replay emitted existing unused-variable warnings for `hm` and `hκ`; no LP-OSC error.

A generated temporary `.lake/abi-scratch/LP-OSC-audit-1.lean` imported the facade and issued `#print axioms` for every one of the 38 public theorems in the table, in declaration/file order. Command:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean .lake/abi-scratch/LP-OSC-audit-1.lean
```

Exit 0. Every output line had exactly this form (with its corresponding fully qualified name):

```text
'KAM.Planetary.StrongAMD.exists_osc_estimates' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.barrier_osc_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.osculating_barrier' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All other 35 outputs had the identical three-element axiom list, including every helper and tangency/dictionary theorem. The temporary probe was deleted after the check.

Lint (only the owner-prescribed route):

```sh
/root/code/KAM-inp/.drafts/LP/lp_lint.sh /root/code/KAM-inp-lp-thr
```

Exit 0, with the following output (no stale-root exception needed):

```text
check_lean_modules: PASS (3685 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

The application-anchor qualification is the lint tool's exact scope; this audit did not build the opt-in application.

Kernel replay and short-name checks were explicitly reported by the user as already run by the launcher. Their actual output/exit codes are unavailable in this audit turn; they were not rerun or independently asserted. The prover handoff separately reports its short-name check exit 0. The successful independent build/axiom checks above are the live receipts collected here.

Static checks: new files have 338, 153, 194 and 321 lines, all below 1500; copyright, `module`, public imports, module docstrings, exposed public noncomputable sections present. Reviewed all four full files; no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, heartbeat/recursion/synthesis overrides, provider imports, DRAFT_SORRY imports or root imports in these modules. `git diff --check inp-lp...HEAD -- KAM` exited 0 with no output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` was empty. `KAM/Root/Planetary.lean` does change: exactly four imports of these modules, reported by the prover as generator-produced. Record this generated-file deviation explicitly; this audit did not edit or regenerate it.

## Errata, deviations and limits

- **Package-brief wording note (item 1):** “`oscEnergy ≤ −c/2`” uses the same c as the total-energy input. Exact implementation is `≤ −(c/νᵢ)/2`. On normalized source masses it implies the brief's bound; for unnormalized masses the scale distinction must remain explicit. This is a documentation correction to carry to the freeze proposal, not an unpaid proof step.
- **No new suspected MAIN defect.** MAIN:527 says “`|k_i−1| ≤ μ`”, correctly under MAIN:11's “`max_i ν_i=1`”. The implementation removes that normalization and uses Mμ; this is a valid generalization, not source errata.
- **Reported implementation deviations:** four focused modules rather than a single file (the brief allows a split); four generated root imports; extra positivity, radial containment and strict eccentricity clauses in `OscEstimate`; specific-energy scale made explicit. All have been reviewed.
- No frozen surface is approved or sealed here. Spatial elements and a dynamical tangency statement remain outside the requested package scope. No implementation changes were made; the only persistent audit edit is this report.
