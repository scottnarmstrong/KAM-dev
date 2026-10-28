# S8-D independent package audit 1

Verdict: **PASS WITH NOTES** for the internal S8-D helper package. No frozen anchor is proved or seal-ready by this package; provider/frozen-type and seal-body probes are **not applicable**. All 30 new public theorems pass statement and proof review. Notes concern the explicitly retained consumer obligations, generated-root lint exception, and documentation provenance.

## Scope and authority

Audited HEAD `aff048b7e4ec66d1eb3f7ac45e5b03552f95434e` against `inp` `e5df64700d49778f5a16b13c87fb6e7a5237ea4d`, using `git diff inp...HEAD` (merge base `81bb576d2ebe1ee5c4cb309059b68d4b24148218`). Only the following five files are audited:

- `KAM/Planetary/SecularForm/DiagonalJet.lean`: 165 lines.
- `KAM/Planetary/SecularForm/DiagonalJet/Radial.lean`: 256 lines.
- `KAM/Planetary/SecularForm/DiagonalJet/Orbit.lean`: 161 lines.
- `KAM/Planetary/SecularForm/DiagonalJet/Pair.lean`: 174 lines.
- `KAM/Planetary/SecularForm/DiagonalJet/Mean.lean`: 186 lines.

Total: 942 lines. The three-dot diff also includes seven changes outside these paths; those are not certified by this report. The protected-path diff is empty.

Read the repository rules, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, local handoff and AUDIT FOCUS, Part 8 blueprint, P810 design and track P statement conventions. The user's exact local output path overrides the generic brief's MAIN-worktree destination. No production file was edited.

Authoritative source: `blueprint-P/parts/p8-secular-form.tex`, SHA-256 `413806b9fcc86156e0b241da85668677b44bf142897c7039940504a50ae1febc`, matching the design pin. Relevant locators are qf-scale L161, qf-c0 L162, qf-diag L163–165, quartic(b) L223–224 and q4-b L233. P810 design L430–434 assigns S8-D/S8-Q/S8-4; L454–457 says “DiagonalJet/CrossJet return identities for the literal pair average, Quadratic sums them.” This supports the handoff's internal-helper interpretation. The claimed 13:08 entry itself is absent from this checkout's `docs/campaign/OVERNIGHT.md` (and the live main inp copy checked); the design text and explicit AUDIT FOCUS suffice to establish the present audit scope. No signed-signature fidelity is claimed.

## Declaration review

All names below have prefix `KAM.Planetary.SecularForm.`. File basenames refer to the five audited paths above. Support lemmas are implementation proof cuts, not substitutions for signed results.

| Blueprint node / role | Lean declaration and locator | Verdict | Reason / limits |
|---|---|---|---|
| `qf-diag; quartic(b), q4-b` | `pairSlowSecular_diag_jet` (DiagonalJet.lean:45) | PASS | Literal pair integral; both axis orderings; positive r,C before u; sixth-order bound. Fixed actions. |
| `qf-diag support` | `planeDot_orbitalUnit_polar` (Mean.lean:36) | PASS | Polar reduction including zero vector. |
| `qf-diag; q4-b support` | `integral_cos_pow_period` (Mean.lean:51) | PASS | All six moments k<=5; even means 1,1/2,3/8 and odd means zero. |
| `qf-diag Taylor support` | `powerSeries_diag` (Mean.lean:76) | PASS | Power-series coefficient identity from actual HasFPowerSeriesOnBall data. |
| `qf-diag Taylor support` | `analytic_taylor_bound` (Mean.lean:87) | PASS | Derives local order-six remainder and continuity from analyticity. |
| `qf-diag support` | `integral_cos_pow_shift` (Mean.lean:107) | PASS | Translation-invariant period integral for every natural power. |
| `qf-diag; q4-b` | `circleMean_jet` (Mean.lean:116) | PASS | Derives coefficients h2/4 and h4/64 with O(|v|^6); no Taylor estimate assumed. |
| `qf-diag support` | `planeSq_orbit_vec` (Orbit.lean:37) | PASS | Orbit-vector algebra from source K>0 and |v|^2=1-K^2; no radius conclusion assumed. |
| `qf-diag` | `planeLength_poincare_fst` (Orbit.lean:55) | PASS | Literal chart position radius a*keplerJac on poincareDom. |
| `qf-c0` | `poincare_circular_fst` (Orbit.lean:72) | PASS | Exact circular chart formula, even at totalized degenerate inputs. |
| `qf-c0/diag support` | `planeLength_sub_circle` (Orbit.lean:87) | PASS | Polar distance identity, q=0 included. |
| `qf-c0/diag` | `circle_average` (Orbit.lean:108) | PASS | Literal normalized inverse-distance integral. Unrestricted equality also covers totalized singular integrals. |
| `qf-diag` | `integral_keplerLong_comp` (Orbit.lean:132) | PASS | Correct mean-to-eccentric-longitude Jacobian; |v|<1, continuous periodic integrand. |
| `qf-diag support` | `continuous_keplerJac` (Pair.lean:34) | PASS | Elementary continuous Jacobian for every v. |
| `qf-diag support` | `periodic_keplerJac` (Pair.lean:41) | PASS | Exact 2*pi period for every v. |
| `qf-diag support` | `keplerJac_le` (Pair.lean:44) | PASS | Upper radius factor bound 1+|v| from physical scalar product. |
| `qf-diag support` | `poincareV_congr_fst` (Pair.lean:53) | PASS | Regular eccentricity vector independent of longitude. |
| `qf-diag support` | `mem_poincareDom_congr_fst` (Pair.lean:57) | PASS | Source domain independent of longitude. |
| `qf-diag` | `pair_inner_average` (Pair.lean:63) | PASS | Circular second-planet integration yields literal radialPhi, correct mass and G factors. |
| `qf-diag` | `pairSlowSecular_circular_partner` (Pair.lean:80) | PASS | Literal pair identity on the source separated-orbit domain; no coefficient hypothesis. |
| `qf-c0` | `pairSlowSecular_zero` (Pair.lean:143) | PASS | Positive actions and distinct axes suffice for exact constant term. |
| `qf-scale support` | `radial_base_nonneg` (Radial.lean:29) | PASS | Algebraic radicand nonnegativity for all real a,b,t. |
| `qf-scale` | `radialPhi_comm` (Radial.lean:35) | PASS | Exact symmetry, stronger all-real carrier. |
| `qf-scale` | `radialPhi_smul` (Radial.lean:42) | PASS | Degree -1 for c>0; all real a,b. |
| `qf-scale` | `radialPhi_eq_laplace` (Radial.lean:58) | PASS | Exact normalized Laplace formula for 0<a<b. |
| `qf-scale support` | `analyticAt_laplaceForm` (Radial.lean:78) | PASS | Analytic explicit Laplace expression on 0<p.1<p.2. |
| `qf-scale` | `analyticOnNhd_radialPhi` (Radial.lean:89) | PASS | Joint real analyticity on positive distinct radii. |
| `qf-diag; quartic(b)` | `analyticAt_radialH` (Radial.lean:117) | PASS | Derived analyticity at epsilon=0 for positive distinct axes. |
| `qf-diag inner` | `iteratedDeriv_two_radialH_of_lt` (Radial.lean:143) | PASS | h2=a/b^2 times b_(3/2)^(1)(a/b), using proved identities. |
| `qf-diag outer` | `iteratedDeriv_two_radialH_of_gt` (Radial.lean:196) | PASS | h2=b/a^2 times b_(3/2)^(1)(b/a); no numerical ratio restriction. |

## Definitions, premises and consumer applicability

There are **no new public or private `def`, `abbrev`, or `structure` declarations** in these five files. Nine private theorems provide coordinate expansions or elementary Laplace differentiability; they are proved, not supplied as assumptions. Local `let`/`set` expressions are literal radii, eccentricities, derivatives, Taylor polynomials and bounds, with no fallback replacing a physical object.

The upstream objects were checked at their definitions: `Basic.lean:38` bundles only positive physical data and n>0; `Basic.lean:74` defines the actual iterated normalized Newtonian pair integral using `poincare`, not a coefficient model. `LaplaceIdentities.lean:303–305` defines the literal radial integral and `radialH`. The frozen `planeLength` is sqrt(sum of squares), not the ambient Pi max norm; `planeDot`, `orbitalUnit`, and `secularAverage` retain the physical scalar product and 2*pi convention. No new norm instance, coefficient structure, quadratic matrix, numerical axis ratio, or conclusion-shaped field is assumed.

`pairSlowSecular_circular_partner` legitimately assumes chart membership and separated radii. This is the blueprint's local collision-free regime, also explicit in quartic(a). Crucially, `pairSlowSecular_diag_jet` **discharges** both guards from positive actions, distinct axes and its chosen positive radius; it does not export separation as an additional premise. Its proof uses delta=|a-b|/a and radius at most min(sqrt(I)*delta, sqrt(I)*rH, sqrt(I)). Degenerate values of totalized division/integration in unrestricted auxiliary identities are never used to obtain the physical jet: the assembly establishes strictly positive radii/Jacobian and uniform radial separation first.

For S8-Q, substituting the two proved h'' identities gives respectively
`-G*m_i*m_j*a/(4*I*b^2)*b_(3/2)^(1)(a/b)` for a<b, and
`-G*m_i*m_j*b/(4*I*a^2)*b_(3/2)^(1)(b/a)` for b<a.
On the source increasing-axis carrier these are exactly `-pairA/I` (`Coefficients.lean:31`), with the required factor 1/4. No factor-two mismatch was found.

For S8-4, writing t=|u|^2/I, the proof uses the **exact** eccentricity identity e^2=t-t^2/4. The mean expansion h(0)+h''e^2/4+he^4/64 yields the coefficient `(h/64-h''/16)/I^2` times `-G*m_i*m_j`, exactly quartic(b); the remaining error is bounded by C|u|^6. This is a rigorous local remainder, stronger than the qf-diag second-order calculation.

Consumer notes (not package failures):

1. The exported jet concerns `(u,0)`. S8-Q and S8-4 must prove/use the literal pair-integral argument swap (with the necessary integrability/Fubini justification on their separated domain) for `(0,u)`; merely renaming i,j does not rewrite the original integral. This was explicitly left to consumers in the handoff.
2. r,C may depend on D,i,j,I,J. No uniformity over a neighbourhood of actions follows from this theorem alone. S8-Q must combine it with joint analyticity and its uniform Taylor/assembly argument. The current S8-D interface does not claim that stronger parent result.
3. Cross terms, full coefficient assembly, invariant quartic structure, and mixed quartic coefficients remain outside S8-D. Neither `quadratic_form` nor `quartic`, nor a physical frozen headline, is closed here.

## Hygiene and independent checks

All Lean/Lake checks were run serially with `LEAN_NUM_THREADS=1` and `nice -n 5`; no cache update, clean, library rebuild, frozen edit or state-changing git command was used. The targeted build waited for the prescribed compile gate.

### Build (exit 0)

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s8d KAM.Planetary.SecularForm.DiagonalJet
```

Relevant exact output:

```text
[inp-gate] slot 1 acquired 14:27:41 for KAM.Planetary.SecularForm.DiagonalJet
Build completed successfully (9119 jobs).
```

Replayed dependency unused-variable warnings occurred in `KAM/Kepler/Energy.lean:106`, `KAM/Planetary/Poincare/Chart.lean:212,247`, and `KAM/Kepler/Mass.lean:147,157,500,524`; none occurred in the five audited files. No heartbeat/design failure.

### Axiom probe (exit 0)

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S8DAudit.lean
```

The temporary probe imported the facade and issued `#print axioms` for every public theorem in the table. Exact output:

```text
'KAM.Planetary.SecularForm.pairSlowSecular_diag_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.planeDot_orbitalUnit_polar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.integral_cos_pow_period' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.powerSeries_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.analytic_taylor_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.integral_cos_pow_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.circleMean_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.planeSq_orbit_vec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.planeLength_poincare_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.poincare_circular_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.planeLength_sub_circle' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.circle_average' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.integral_keplerLong_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.continuous_keplerJac' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.periodic_keplerJac' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.keplerJac_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.poincareV_congr_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.mem_poincareDom_congr_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pair_inner_average' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairSlowSecular_circular_partner' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairSlowSecular_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.radial_base_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.radialPhi_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.radialPhi_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.radialPhi_eq_laplace' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.analyticAt_laplaceForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.analyticOnNhd_radialPhi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.analyticAt_radialH' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.iteratedDeriv_two_radialH_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.iteratedDeriv_two_radialH_of_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay (exit 0)

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.DiagonalJet KAM.Planetary.SecularForm.DiagonalJet.Radial KAM.Planetary.SecularForm.DiagonalJet.Orbit KAM.Planetary.SecularForm.DiagonalJet.Pair KAM.Planetary.SecularForm.DiagonalJet.Mean
```

Exact output:

```text
replaying KAM.Planetary.SecularForm.DiagonalJet.Radial
replaying KAM.Planetary.SecularForm.DiagonalJet.Pair
replaying KAM.Planetary.SecularForm.DiagonalJet.Mean
replaying KAM.Planetary.SecularForm.DiagonalJet.Orbit
replaying KAM.Planetary.SecularForm.DiagonalJet
```

### Source lint (exit 1, permitted generated-root exception only)

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (688 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

This is the sole exception explicitly allowed by the audit brief. The generated root was left untouched. Module checks, frozen-anchor guard and all 144 frozen ABI hashes pass.

### Static and quarantine checks

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0. No signed declaration or protected generated file changed.
- `git diff --check inp...HEAD` and `git diff --check`: no output, exit 0.
- `rg -n 'sorry|admit|axiom|unsafe|opaque|set_option|EuclideanSpace|^(def|abbrev|structure) ' KAM/Planetary/SecularForm/DiagonalJet.lean KAM/Planetary/SecularForm/DiagonalJet/*.lean`: no matches, exit 1 (normal no-match result).
- Parsed the KAM import closure recursively: 73 KAM modules, no Provider module, no Frozen theorem module. All 47 imported Frozen modules have manifest state `SEALED` and are definitions. No DRAFT_SORRY dependency.
- Compared the 30 new public declaration names against declaration commands elsewhere under KAM: no duplicate names found. All share their intended SecularForm namespace.
- Counted every audited file, checked module/copyright/public imports/docstrings/public exposed sections. All satisfy module and 1500-line rules.
- No frozen/provider probe or seal copy was fabricated: no such export exists in this scoped package.

## Source defects, deviations and uncertainty

No new defect in a pinned paper or in the audited blueprint formulas was found. Existing Part 8 source-gap/erratum discussions (Fej04r factor 1/2, CP11 quartic formula) are background; this package uses the blueprint's corrected direct radial calculation, not the printed finite-ratio CP11 expression. This audit does not independently certify those papers or the mixed quartic formulas.

Minor introduced documentation defect: `DiagonalJet/Orbit.lean:71` says “radius `Λ²/(mκ)`”; the theorem immediately below correctly states `Λ ^ 2 / (m ^ 2 * κ)`. The handoff inventory repeats the same prose typo. The missing square on m is mathematically incorrect for the actual chart/action normalization. Correct the prose downstream; the checked Lean statement and proof have the correct m^2. No code repair was made during this read-only audit.

The handoff's 13:08 OVERNIGHT locator could not be independently recovered, as recorded above. Current design authority and the user's supplied AUDIT FOCUS are consistent. No new mathematical assumption or source deviation is introduced by these proofs.

The audit created only this report and temporary files under `.lake/abi-scratch/`; all audit-created probes and logs were deleted after embedding the results. The pre-existing untracked handoff was preserved. No production changes, commits or seals were made.
