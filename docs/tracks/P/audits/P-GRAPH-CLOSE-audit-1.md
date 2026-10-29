# P-GRAPH-CLOSE independent audit 1

**Verdict: FAIL for closing all 28 records.** The existing sealed results checked here pass their type, seal-body and axiom probes; this is not a refutation of a frozen theorem. There are 7 OWNER rows, 5 NEEDS-LEAN rows, 4 BYPASSED rows, 9 PROVED rows and 3 definition-confirmed rows. Some remaining work is small statement packaging, but compilation does not supply the missing exported statements.

Audit snapshot: `HEAD fc903094802c29288e118b9aa3e38cf4fa9c49b8`, `inp 32090afa8790d0dc33e1df1a18c3093313898a1d`. `git diff inp...HEAD` consists exactly of 35 added lines in `docs/tracks/P/audits/P-GRAPH-CLOSE-handoff.md`. No Lean implementation is introduced by this branch. The user's explicit absolute report destination overrides the generic brief's main-worktree destination. Only this report and temporary `.lake/abi-scratch/` files were written; no graph, Lean, frozen file, manifest, generated file or Git state was changed.

Read: AGENTS, PLAN, DECISIONS, the audit brief, handoff, all 28 NOT_STARTED records (including SOURCE fields, locators, DEPS, EDGEs and notes), their local blueprint passages, track P statement, P14 design and relevant earlier definitions receipts, with fresh code inspection taking precedence. This review uses local pinned blueprint text; it does not assert a new independent transcription check of the original published PDFs.

## Node decisions

Names are in `KAM.Planetary` unless qualified. `AMD/`, `Exponential/`, `Preparation/`, `SecularBox/`, `Poincare/` and `Averaging/` below are under `KAM/Planetary/`. Line ranges refer to this checkout. PROVED for internal steps invokes the handoff's ruling (b), identifying the proved parent and actual proof block; it does not invent a public theorem. BYPASSED describes the full source route or omitted clause, with the used part explicitly retained.

| Node | Proposed status | Lean declarations and locator | Justification |
|---|---|---|---|
| `bpP:p0:totality` | OWNER | Frozen definitions; `blueprint-P/parts/p0-conventions.tex:306–329`; `docs/campaign/OVERNIGHT.md:646–653` | This is a multi-clause guard convention, not one proved Lean claim. Decide whether to classify it as administrative/definition-audit material, retaining its guarded measure and domain obligations at consumers, or require explicit lemmas for the literal summary. A remark label cannot certify all these facts. |
| `bpP:p1:order` | OWNER | Frozen `hamiltonianVectorField`, `symplecticForm`; `blueprint-P/parts/p1-hamiltonian-tools.tex:40–42`; `Averaging/Direct.lean:88–184` | The implemented equations use positions first; no standalone coordinate-swap theorem realizes this entire source convention. Decide whether the coordinate dictionary is an accepted convention or must be a proved pullback/field-conjugacy identity. No silent graph re-kind is authorized. |
| `bpP:p3:conv#data` | OWNER | `KAM.Weighted.coeff`, `modeWeight`, `wsum`, `WSummable`, `WBound`, `wnorm`, `KAM/Weighted/Norm.lean:48–83` | Period-one coefficients and geometric-width conversion are explicit, but real `tsum`/`iSup` totalizations are not the source extended norm on the whole carrier. Accept guarded finite-norm predicates as the source interface, or require an extended-valued/restricted-carrier object. |
| `bpP:p7:conv#data` | OWNER | `KAM.Kepler.delaunay`, `KAM/Kepler/Orbit.lean:45`; `keplerLong`, `KAM/Kepler/Equation.lean:117–124`, `eccAnom:272`; `delaunay_symplectic`, `KAM/Kepler/DelaunaySymplectic.lean:447–483` | The intended map and sign convention hold on `deDom`. Its public total carrier includes the Kepler-solver `else 0` branch; decide whether domain-restricted fidelity is sufficient, rather than calling that fallback the physical map everywhere. |
| `bpP:p11:sec-conv#data` | OWNER | `KAM/Weighted/Norm.lean:48–83`; `Preparation/Basic.lean`; `docs/tracks/P/audits/DEFS-P11-audit-1.md:23–36` | Same whole-carrier norm issue as Part 3: `WBound` supplies summability and a finite bound but is a predicate, not the literal possibly infinite norm. Strip/period and polydisc notation do not resolve that distinction. |
| `bpP:p11:sec-D#data` | OWNER | `p11K2`, `p11s2`, `Preparation/SlowData.lean:36–39`; `p11SlowH0`, `p11SlowF2`, `SlowAverageF2.lean:54–66`; `p11SlowData`, `SlowSigned.lean:102–106` | The selected record is choose-or-default, and the h0/f2 helpers have a free correction Z. Decide whether proved local specifications can replace unconditional source-object definitions; independently, the exact polar-shell object and direct source average/formula identifications still need the work listed below. |
| `bpP:p11:sec-E#data` | OWNER | `p11Rescale`, `p11PreparedBox`, `Preparation/SlowData.lean:31–35`; `p11SecE`, `p11Rescale_polydisc_iff`, `SecEDefs.lean:25–99`; `p11PreparedCoreOf`, `PreparedBasic.lean:39–52`; `p11PreparedData`, `PreparedData.lean:107–108` | The older missing-E and mapping-iff findings are now repaired; do not repeat them as current gaps. The selector ruling remains, together with identification of the full complex H2 pullback, domain table and normalized-frequency source formulas, not merely arbitrary fields satisfying a local output contract. |
| `bpP:p14:geometry` | NEEDS-LEAN | `geometry`, `AMD/Geometry.lean:74–171`; `elements`, `AMD/Elements.lean:134ff`; `amd_compact`, `Geometry.lean:174ff` | The public geometry conclusion omits `a_i(1-e_i) ≤ |q_i| ≤ a_i(1+e_i)`. These inequalities are genuinely supplied by `elements` and used at Geometry:111–128, so this is a missing literal combined statement, not an analytic gap or a valid bypass of the radial argument. |
| `stepP:p14:geo-b` | NEEDS-LEAN | `AMD/Geometry.lean:108–131`; `elements`, `AMD/Elements.lean:134ff` | The proof obtains both exact radial inequalities from `hel i` and derives d/R bounds, but its exported `hrlow`/`hrup`-based conclusion only retains the box bounds. Export the radial-and-box conjunction under the source hypotheses; this also repairs the preceding row. |
| `stepP:p14:cl-b` | BYPASSED | `amd_closure`, `AMD/Closure.lean:166–192` | The sealed route uses energy `E_i ≤ -m_i^3/(2 u_i²)` and angular momentum `C_i ≥ l_i-(A0+n delta)+delta > 0`. It never needs the source's sharper denominator `(u_i-delta)²` or the particular `(l_i+delta)sqrt(1-e_*²)` margin. Do not label those precise bounds proved by this alternate argument. |
| `stepP:p14:cl-c` | PROVED | `amd_closure`, `AMD/Closure.lean:193–227` | Internal to the PROVED closure parent: continuity passes the alternate strict-negative/positive margins to the limit, then the action interval and AMD bound, producing membership in the collar and outer region. No ellipticity of the limit is assumed. |
| `bpP:p14:moving-ode` | BYPASSED | `moving_ode`, `AMD/MovingODE.lean:28–47`; `amd`, `AMD/Confinement.lean:168–198`; `stopped_isSolutionOn_reverse`, `Exponential/Stopped.lean:215–240` | The positive-H portion is proved and used. The full source lemma's separate physical -H equivalence is not used: confinement applies generic ODE confinement to the original field, while E11 reverses a lifted chart curve directly into the negative N-Hamiltonian. This bypass does not claim the missing physical -H conjunct is a theorem. |
| `stepP:p14:mo-reg` | PROVED | `moving_ode`, `AMD/MovingODE.lean:36–39`; `analyticOnNhd_movingHamiltonian`, `KAM/Planetary/Newtonian/Models.lean`; `KAM.ODE.ham_smooth_c1` | The open collision-free domain and analytic Hamiltonian give C-infinity regularity and C1 field regularity, independently of mu's sign. The moving_ode proof explicitly applies the smooth-field theorem to that analytic input. |
| `stepP:p14:mo-eq` | BYPASSED | `AMD/MovingODE.lean:40–47`; `AMD/Confinement.lean:168–187`; `Exponential/Stopped.lean:227–240` | Positive equivalence is exactly proved by unfolding the two predicates. The negative physical equivalence in this full node is bypassed by the same direct chart time-reversal route as the preceding parent row; it must not be inferred just from the positive equivalence. |
| `stepP:p14:pt-input` | PROVED | `isCompact_perturbationCore`, `Exponential/Perturbation.lean:48–87`; `perturbation`, `Perturbation.lean:238–244` | Internal to PROVED perturbation: the fundamental cell is compact, included in the enlarged cylinder and chartSafe by real_domain, and tube supplies fc, real trace, holomorphy and shifts. The analytic chart premise is proved at :41–45, not assumed as a new input. |
| `stepP:p14:pt-rho` | PROVED | `perturbation`, `Exponential/Perturbation.lean:245–285`; `exists_shift_mem_core`, :148–185 | The proof chooses rho = min(kappa,r/2), forms the compact closed-rho neighborhood, bounds fc there, and sets B0=max(1,B'). Lattice reduction proves F is contained in T and the uniform bound on F; F uses open fast/slow sets and strict imaginary-coordinate inequalities, and shifts preserve those conditions. These choices precede mu. |
| `stepP:p14:pt-def` | PROVED | `perturbation`, `Exponential/Perturbation.lean:286–288` | Literal local definition `P z := if z ∈ T then fc z / B0 else 0`. The following hP records equality on T, and hFT has already put all analytic uses there. |
| `stepP:p14:pt-p12` | PROVED | `perturbation`, `Exponential/Perturbation.lean:289–298` | Internal to PROVED perturbation: differentiability transfers by congruence on F; B0 positivity and hFT prove norm ≤1. Neither property is a hypothesis or a record field supplied without proof. |
| `stepP:p14:pt-p3` | PROVED | `perturbation`, `Exponential/Perturbation.lean:299–302,308–319` | Real trace is supplied by tube and rewritten through hP, proving the real-valued clause for every real point in F. The final block proves the literal normalized fMov trace on the working cylinder; its openness is independently established by E11. |
| `stepP:p14:pt-p4` | PROVED | `perturbation`, `Exponential/Perturbation.lean:303–307` | The actual hper witness gives shifted membership in T and equality of fc. Rewriting hP at both points proves P4, with the frozen complexified fastShift. |
| `bpP:p14:hnu` | PROVED | `hnu`, `Exponential/Hamiltonian.lean:50–72`; `differentiableAt_hnu_field`, :89–113; `hamiltonianVectorField_neg`, :116–119; `stopped_hamiltonian_neg`, `Exponential/Stopped.lean:180–188`; `isOpen_workingCylinder`, :64–71; consumers :208–209,231–239 | The old openness qualification is discharged at the actual PROVED stopped consumer: take U=workingCylinder with E11's explicit openness and subset_rfl. Equality, differentiability and both field comparisons are all supplied there; this certifies that use of the node, not a nonexistent new monolithic theorem named hnu. |
| `bpP:p14:sec-domain#data` | definition-confirmed | `chartAMD`, `chartSafe`, `Exponential/Setting.lean:32–38`; `planetBlock`, `poincareProd`, `poincareProdDom`, `Poincare/Product.lean:41–51`; `isOpen_poincareProd_preimage`, :300–303; `chartSafe_shift_iff`, `Exponential/Perturbation.lean:207–215`; `sec_domain_chart_facts`, `Exponential/Dictionary.lean:64–79` | These are the fast-first chart, quadratic Gamma sum, safe-domain intersection, physical pullbacks and 2pi fast translations. Openness and shift invariance are proved on the intended chart domain; fastBox/slowBall alone would not suffice for this node. |
| `bpP:p14:sec-stopped#data` | definition-confirmed | Frozen `degenerateHamiltonian`, `KAM.Nekhoroshev.realPart`, `complexifyPhase`; `Exponential/Hamiltonian.lean:50–58,122–127`; `Exponential/Stopped.lean:180–188,245ff` | The expressions instantiated in stopped are exactly Re h(fast I)+nu Re P(cx w), with constant-in-coupling perturbation, and the same expression for (-h,-P). stopped_hamiltonian_neg proves the sign identity; the two sets of N hypotheses are discharged in stopped, not fields masquerading as definitions. |
| `bpP:p14:sb-cov` | NEEDS-LEAN | `sb_cov`, `SecularBox/Covariance.lean:101–120`; private `sbCov_root`, :91–94; local hax, :111–112 | sb_cov exports Gamma, eccentricity-vector, Jacobian, position and momentum covariance, but not the root/axis and scalar-x clauses of the literal node. The root and axis identities are already proved internally; bundle the remaining scalar identity and full source conjunction rather than treating unfolding as an exported conclusion. |
| `stepP:p14:sb-cv-1` | NEEDS-LEAN | `SecularBox/Covariance.lean:43–61,72–94,111–112` | Fast actions, Gamma, eccentricity vector, root and axis identities are proved privately/internally; the source ratio rho=Gamma/Lambda also follows. Since the full parent node is not yet certified PROVED, do not use ruling (b) circularly to close its missing complete slow-data conjunction. Export it with the parent repair. |
| `stepP:p14:sb-cv-2` | NEEDS-LEAN | `sbCov_jac`, `SecularBox/Covariance.lean:96–99`; `sb_cov`, :104–120 | J covariance is literal, but scalar x=v dot c covariance is only a rewrite inside the q/p proof. The source conjunction `(x-shift equality) and (J-shift equality)` needs to be exported with the preceding repair; no new analytic estimate is involved. |
| `bpP:p14:sb-smooth#data` | definition-confirmed | Frozen `jupiterSaturnWeights`; `sb_smooth_prop`, `SecularBox/Smooth.lean:317–323`; `sb_safety`, `SecularBox/Safety.lean:156ff` | m=(1,saturn), saturn in the exact rational interval. Smoothness actually allows every real mu, stronger than the subsection's positive-mu convention; the safety theorem retains mu>0. This is parameter setup, not a new dynamical claim. |
| `bpN:p6:iterative-special` | BYPASSED | `direct_step`, `Averaging/Direct.lean:88–184`; `KAM.NormalForm.iterative_direct_a` through `_e`, `KAM/Nekhoroshev/NormalForm/{IterativeMap,IterativeRemainder,IterativeReal}.lean`; `Averaging/FiniteStep.lean:130–191` | The P-owned remark's full general-p, g=0 and lattice-zero contract is not an exported theorem. P's route builds the original IterHyp and directly invokes general N results, choosing p=2 and alpha_N=2 alpha/q; finite averaging continues on that same generator/flow. This bypass does not certify the literal general-p specialization as PROVED or reclassify it as an N external. |

## Remaining Lean work

The 5 NEEDS-LEAN rows correspond to two small groups, not five independent analytic gaps:

1. **Geometry / geo-b:** export, from admissible B and z in amdOuter B, for every i,
   `keplerAxis B.mass z i * (1 - planeLength (keplerEccVector B.mass z i)) ≤ planeLength (bodyVector z.1 i)` and
   `planeLength (bodyVector z.1 i) ≤ keplerAxis B.mass z i * (1 + planeLength (keplerEccVector B.mass z i))`, together with the d/R bounds and the existing geometry conclusion. The exact radial inequalities are already projections of `elements`; a fresh distinct wrapper can combine them with geometry without changing any frozen statement. Estimate: 15–35 Lean lines. They are used in Geometry:111–128, so a claim that the radial argument is unused would be false.
2. **Covariance / cv-1 / cv-2:** export the full source conjunction under the elliptic hypotheses (or stronger whole-carrier theorem if valid): invariance of Gamma, k=secularRoot, rho=Gamma/Lambda, a=secularAxis; covariance of v, q, p; and `planeDot (secularEccVector (secularRotation theta w) i) (orbitalUnit F) = planeDot (secularEccVector w i) (orbitalUnit (F-theta))`, with the J identity. Reuse sb_cov and the existing internal root/axis proofs; do not assume these identities. Estimate: 30–60 lines total. Current sealed sb_rot uses the q/p/J projections (Rotation:77ff); this row requests the complete literal parent declaration, not a repair to that sealed consumer.

There are also **missing source objects/identifications within OWNER nodes**, independent of the acceptability of choice:

- `sec-D#data`: define the exact shell `{(zeta,rho) : |Im zeta|∞ < sigma_F/6 and forall j, |rho_j-2*pi*eps| < pi*eps}` and identify Pi, raw zeta average, h0 and f2 with the source formulas (including any correction Z used by the implementation). Related action boxes include different fast restrictions and do not by themselves define this shell. Estimate: 25–80 lines for explicit objects and basic characterizations, plus identification work; no estimate of that proof work is certified here.
- `sec-E#data`: E and its iff now exist. Still supply a literal complex H2/H-hat pullback identification and complete source-domain/frequency formula coverage for the chosen datum, or an exact audit mapping to existing statements. `p11PreparedCoreOf.N/P` are explicit formulas, while its chain is real-projected and does not itself assert the full complex identity. Estimate: 50–150 lines for statements/bridges if the necessary existing identities cover the full source domains; otherwise this requires a separate design audit. An owner ruling about selectors cannot prove a missing identity.

No physical -H wrapper is required by the observed sealed route. If the orchestrator wants that blueprint lemma proved rather than bypassed, the missing statement is C1 regularity of -X_H on W and `(IsHamiltonianSolutionOn (-H) univ J z and forall t in J, NoCollision (z t).1) iff KAM.ODE.IsSolutionIn (-X_H) W J z`; the positive equivalence and `hamiltonianVectorField_neg` suggest a 15–30 line wrapper. This is optional route completion, not an additional NEEDS-LEAN row.

## Owner questions

1. For totality and coordinate order, accept reviewed conventions with individual consumer guard proofs, or demand theorem nodes? If conventions are accepted, specify a supported graph-schema representation; the existing claim/NOT_STARTED status must not silently become PROVED.
2. For both weighted-norm nodes, approve the interface consisting of WSummable/HasFiniteWNorm/WBound and a real totalized norm on its finite locus, or require the literal extended-valued norm/restricted carrier. This is the same question for Part 3 and Part 11.
3. For Part 7, approve faithfulness on deDom with a totalized solver outside it, or require a restricted-domain chart object. No conclusion here endorses the solver fallback as the source map off-domain.
4. For sec-D and sec-E, accept choose-or-default records only under proved local specification guards, or require direct source-object definitions throughout their claimed carriers. Either answer leaves the explicit missing shell/complex-identity work above to be discharged.

## Anchor and hygiene results

The four anchors directly relevant to the P14 route—`amdConfinement`, `planetaryExponentialSafety`, `secularBoxSafety`, `secularBoxAtCitedMasses`—are **PASS WITH NOTES**: already SEALED, exact provider types and literal existing seal bodies pass fresh probes, and axiom/kernel checks are recorded below. Notes concern graph/source completeness above. The other three planetary anchors are unchanged and SEALED in the manifest; this audit does not represent a fresh complete re-audit of their proofs. The imported `KAM.Nekhoroshev.partialConvex_nekhoroshev` is SEALED too.

No new public definition, helper, premise or instance is introduced by the diff. Existing source-object classifications used here: chartAMD, chartSafe, fastBox, slowBall, enlargedCylinder, workingCylinder and perturbationCore are explicit intended sets/functions; EnlargedData contains geometric source inequalities; local P's zero extension outside T is exactly the source extension, and hFT excludes it from all analytical uses. SecularRotation is the literal linear rotation of the slow pairs. The weighted norms, Kepler solver and P11 selectors have the whole-carrier qualifications in their OWNER rows; those qualifications must not be erased by successful compilation. Imported frozen theorems in the reviewed provider dependency closure are SEALED; production providers import no other provider directly. The frozen anchor's import of its own provider is the allowed seal edge.

All Lean/Lake commands launched by this auditor were serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`; source reads occurred while a check ran. No resource overrides, cache operations, clean, update or generated-root regeneration were used.

### Fresh commands and receipts

1. Targeted compile gate (exit **0**):

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-pclose KAM.Provider.Planetary.PlanetaryExponentialSafety KAM.Provider.Planetary.AmdConfinement KAM.Provider.Planetary.SecularBoxSafety KAM.Provider.Planetary.SecularBoxAtCitedMasses KAM.Planetary.Averaging.Direct
```

Final output: `Build completed successfully (9362 jobs).` The build replayed existing linter warnings (unused-variable and style suggestions); no compiler error. The compile-gate receipt reports slot 1 acquired. Dependencies were reused/replayed; no clean or whole-library rebuild was requested.

2. Source lint (exit **0**, complete output below):

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

```text
check_lean_modules: PASS (1339 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The lint includes forbidden proof escapes and resource overrides, 1500-line caps, module structure, generated-root consistency, frozen-anchor integrity and elaborated ABI verification. No stale-root exception was used.

3. Exact provider/seal and axiom probe (exit **0**, no errors or warnings):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/PcloseProbe.lean
```

For each of the four anchors, the scratch file imported its frozen and provider modules and elaborated `example : type_of% @KAM.Planetary.<name> := @KAM.Provider.Planetary.<name>`. It also copied the literal frozen declaration header under a fresh `auditSeal_<name>` and retained its existing proof body. The applications were:

```lean
by exact KAM.Provider.Planetary.amdConfinement hn B hB mu T delta hmu hT hdelta hmargin hAMD z0 hz0 hstop
by exact KAM.Provider.Planetary.planetaryExponentialSafety hn B hB
by exact KAM.Provider.Planetary.secularBoxSafety saturn mu hsaturn hmu w0 hw0
by exact KAM.Provider.Planetary.secularBoxAtCitedMasses w0 hw0
```

The probe then printed axioms of the four frozen exports, four provider exports, and the following audited supporting results. Complete output:

```text
'KAM.Planetary.geometry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.elements' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.amd_closure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.moving_ode' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_workingCylinder' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fastBox_eq_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hnu' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiableAt_hnu_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hamiltonianVectorField_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stopped_hamiltonian_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.perturbation' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isCompact_perturbationCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chart_perturbation_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stopped' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stopped_isSolutionOn_forward' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stopped_isSolutionOn_reverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sb_cov' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sb_smooth_prop' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.direct' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.direct_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rescale_polydisc_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.amdConfinement' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.amdConfinement' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.planetaryExponentialSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.planetaryExponentialSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.secularBoxSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.secularBoxSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.secularBoxAtCitedMasses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.secularBoxAtCitedMasses' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every printed result has exactly `[propext, Classical.choice, Quot.sound]`; none has sorryAx or a custom axiom. There are no new public theorems in the branch diff requiring additional new-export probes.

4. One kernel replay invocation (exit **0**, complete output below):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Provider.Planetary.PlanetaryExponentialSafety KAM.Provider.Planetary.AmdConfinement KAM.Provider.Planetary.SecularBoxSafety KAM.Provider.Planetary.SecularBoxAtCitedMasses KAM.Planetary.AMD.Geometry KAM.Planetary.AMD.Closure KAM.Planetary.AMD.MovingODE KAM.Planetary.Exponential.Perturbation KAM.Planetary.Exponential.Hamiltonian KAM.Planetary.Exponential.Stopped KAM.Planetary.SecularBox.Covariance KAM.Planetary.SecularBox.Smooth KAM.Planetary.Averaging.Direct KAM.Planetary.Preparation.SecEDefs
```

```text
replaying KAM.Planetary.Preparation.SecEDefs
replaying KAM.Planetary.Averaging.Direct
replaying KAM.Planetary.SecularBox.Smooth
replaying KAM.Planetary.SecularBox.Covariance
replaying KAM.Planetary.Exponential.Stopped
replaying KAM.Planetary.Exponential.Hamiltonian
replaying KAM.Planetary.Exponential.Perturbation
replaying KAM.Planetary.AMD.MovingODE
replaying KAM.Planetary.AMD.Closure
replaying KAM.Planetary.AMD.Geometry
replaying KAM.Provider.Planetary.SecularBoxAtCitedMasses
replaying KAM.Provider.Planetary.SecularBoxSafety
replaying KAM.Provider.Planetary.AmdConfinement
replaying KAM.Provider.Planetary.PlanetaryExponentialSafety
```

5. Protected-path and whitespace checks:

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
git diff --check
```

All exit **0**, no output. A source import-closure walk from the four providers found just one imported frozen theorem, `KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev`, with manifest state `SEALED`, and no direct provider import outside frozen anchors. The four reviewed planetary anchor entries themselves are SEALED. Scratch probe and logs were removed after recording these receipts.

## Defects, deviations and limits

No new suspected defect in a published pinned source or frozen statement was established. The source-versus-Lean discrepancies retained above are exact omissions/representation questions, not counterexamples to the source mathematics:

- `blueprint-P/parts/p14a-amd-expsafe.tex:78–79`: “a_i(1-e_i) ≤ |q_i| ≤ a_i(1+e_i)” is not a conjunct of the public geometry theorem, although elements supplies it and the proof uses it.
- `blueprint-P/parts/p14b-secular-box.tex:165–171`: “Gamma_i,k_i,a_i unchanged” and the scalar x shift identity are not all conjuncts of sb_cov. Internal algebra is not a full exported parent statement under the one-declaration rule.
- `blueprint-P/parts/p14a-amd-expsafe.tex:111,115`: the “for -H” physical equivalence is absent from moving_ode; its observed consumer route is bypassed as documented, not silently treated as present.
- The literal sharper uniform constants in `p14a:102` are replaced by different positive/negative margins in AMD/Closure; the exact source inequalities are not certified. The replacement is sufficient for the limit conclusion and is the reason for the BYPASSED row.
- The literal weighted norm, polar-shell and full prepared-data concerns are retained at their source locators in the OWNER rows and remaining-work list. The SecEDefs additions repair the old E/iff findings only.

No deviation was introduced by this audit. Line estimates are planning estimates, not proof guarantees. No proof or graph status was changed; the orchestrator must apply any accepted recommendations and resolve the remaining literal statements/owner rulings before claiming complete graph closure.
