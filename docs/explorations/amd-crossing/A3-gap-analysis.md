> Source: `RESEARCH/GAP-ANALYSIS.md` in the exploration workspace `/mnt/HC_Volume_106379410/kam-explore/amd-crossing/`. Paths `_sources/…` refer to `RESEARCH/_sources/` in the workspace.
> Date: 2026-10-31.
> Independent analysis produced for the orchestrator; not audited. Copy lightly edited: co-author naming neutralized, internal labels made neutral, cross-references pointed to the appendix files.

# Repository gap analysis against Candidate B

Read-only source inspection at `/root/code/KAM`, main commit `f5625f197c621ccc8045e8392a07e23fe0cb10fc`, on 2026-10-31. Inputs: the research brief, the co-author's message, BRAINSTORM-1 ([A1](A1-brainstorm.md)), the orchestrator's assessment, and the current repository rules, statement registry, source catalogue, dependency graphs and implementations. No repository was edited and no Lean/Lake build was run. “Exists” below means an inspected declaration and implementation, not a fresh kernel/source audit. Key file hashes are in `_sources/repo-source-manifest.json`.

## 1. Main finding

The campaign needs **neither a new Nekhoroshev foundation nor a new fast-angle normal-form engine**. Track N already has an extended normal form with canonical slow pairs on an arbitrary secular set, and an exponential nonresonant stopped-action theorem. The largest missing planar component is the exact strong-LP geometry and its uniform compact analytic domain. Spatial coordinates, the spatial Newtonian dictionary, and actual-velocity osculating elements remain substantial new work.

## 2. Ingredient inventory

All file paths below are relative to `/root/code/KAM`; names after colons are exact declaration locators unless a directory is explicitly named.

| Ingredient | Existing source and actual scope | Required adaptation or gap |
|---|---|---|
| Ambient space | `KAM/Frozen/Planetary/Defs/Phase.lean:Phase`, position/momentum pairs of `Fin d → ℝ` | Reuse `Phase (n*2)` planar and `Phase (n*3)` spatial; physical Euclidean lengths must not be replaced by the ambient max norm |
| Exact moving-Sun Hamiltonian | `Frozen/Planetary/Defs/MovingHamiltonian.lean:movingHamiltonian`; `Planetary/Newtonian/Models.lean:movingHamiltonian_split`, `hamiltonianVectorField_moving` | Existing physical model is planar. With G=m0=1 it has exact form (h+\mu f_{Mov}), including the diagonal recoil and indirect terms. New dimension-three version and equivalence proofs needed |
| Physical masses | `Frozen/Planetary/Defs/ActualMasses.lean:actualMasses` | Reusable: star 1, planet masses \(\mu m_i\). Fix \(\max_i m_i=1\) if \(\mu\) is to mean largest planet/star mass ratio |
| Canonical elements | `Frozen/Planetary/Defs/KeplerEnergy.lean:keplerEnergy`, `KeplerAxis.lean:keplerAxis`, `KeplerAction.lean:keplerAction`, `KeplerEccVector.lean:keplerEccVector`; `Planetary/AMD/Elements.lean:elements`, `eccentricity_deficit`, `ecc_bound` | Planar, with (a=-m/(2E)), \(\Lambda=m\sqrt a\), canonical velocity \(p/m\). New spatial analogues; no silent reinterpretation as actual heliocentric-velocity elements |
| Real chart over non-small eccentricities | `Planetary/Poincare/Chart.lean:poincareDom`, `analyticOnNhd_poincare`, `poincare_periodic`; `Poincare/Product.lean:poincareProd`, `poincareProdDom`; `Exponential/Dictionary.lean:poincareProd_image_prograde` | Existing planar chart is defined on \(0<\Lambda,\ (\xi^2+\eta^2)/2<\Lambda\), not merely a perturbative tiny-eccentricity ball. Reuse onto/symplectic/periodic machinery; spatial regular chart is missing |
| Kepler analytic machinery | `KAM/Kepler/EquationComplex.lean`, `KeplerTube.lean`, `Delaunay.lean` and related files | Planar building blocks. For qualitative uniform analyticity, reuse the generic compact extension theorem rather than demanding explicit complex formulas initially |
| Angular momentum | `Frozen/Planetary/Defs/TotalMomentum.lean:totalMomentum`; `Planetary/AMD/AngularMomentum.lean:ang_mom` | This is scalar **angular** momentum, not linear momentum. Spatial \(L=\sum q_i\times p_i\), conservation and norm invariance are new |
| AMD identity | `Frozen/Planetary/Defs/PhysicalAMD.lean:physicalAMD`; `Exponential/Dictionary.lean:poincareProd_planet_facts`, `sec_domain_chart_facts`; `Exponential/Setting.lean:chartAMD` | Planar prograde identity \(C=\sum\Lambda-L=\sum(\xi^2+\eta^2)/2\). It is normalized AMD; multiply by \(\mu\) for physical angular-momentum units. Spatial \(C=\sum\Lambda-|L|\) and aligned-frame four-square identity are new |
| Sharp LP threshold | No compact pair-threshold/strong-threshold implementation found in inspected P/AMD, Exponential and frozen definitions | New attained minimum, positivity, contact equivalence, continuity, comparison to star thresholds, spatial eccentricity lower bound and radial-separation theorem |
| Existing crude geometry | `Frozen/Planetary/Defs/AMDBox.lean:AMDBox`, `AMDBoxAdmissible.lean:AMDBox.Admissible`; `Planetary/AMD/Geometry.lean:geometry`, `geometry_radial`, `amd_compact`, `geometry_complete`; `AMD/Closure.lean:amd_closure` | Replace common eccentricity/radius/gap budget by a moving sharp threshold. Existing proofs suggest the compactness and exit architecture, but their signatures consume the old box |
| Enlarged safe cylinder | `Planetary/Exponential/Setting.lean:EnlargedData`, `fastBox`, `slowBall`, `enlargedCylinder`, `chartSafe`; `Enlargement.lean:enlarge`; `RealDomain.lean:real_domain`, `original_cylinder_subset` | Rebuild with a family of local action boxes and center-dependent full slow balls. One global slow cutoff at the minimum threshold would unnecessarily remove allowed initial states |
| Uniform complex domain | `Planetary/Exponential/ComplexTube.lean:tube` (line 165) | Compact-safe-set, analytic, periodic extension theorem on `Phase (n+n)` with n fast angles. Reusable for the planar domain; generalize its independent fast/slow dimensions for space. It provides existence, not usable numerical widths |
| Perturbation norm | `Planetary/Exponential/Perturbation.lean:perturbation` (line 226) | Uses compact extension and a normalizing constant B0. Adapt its real-domain hypotheses and uniform family bounds; exact disturbing function survives |
| Fast Kepler Hamiltonian | `Planetary/Exponential/KeplerData.lean:keplerSumGen_fderiv2_apply`, `hess_norm_le`, `real_freq`, `real_hess`, `h_data` | \(h=-\sum m_i^3/(2I_i^2)\), negative definite Hessian. Reusable for convex route (sign reversal) and explicit frequency Lipschitz constants |
| Extended normal form | `Nekhoroshev/Partial/Setting.lean:PartialBlock`, `ExtNFHyp`; `Partial/NormalForm.lean:nf`, `nnf_disp_radius`; `Partial/Preimage.lean:preimage` | Already permits arbitrary `S : Set (Phase k)`, scaled slow variables, complex thickening, and exponential fast Fourier tail. Reuse unchanged |
| Nonresonant fast stability | `Nekhoroshev/Partial/Nonresonant.lean:nonresonant` | Already gives drift \(\le r/2\) through \(sr(5\varepsilon)^{-1}e^{2\pi Ks/6}\), **conditional only on slow membership through the queried time**. Need quantitative parameter choice and AMD discharge of that condition |
| Partial-convex global route | `Frozen/Nekhoroshev/Theorems/PartialConvexNekhoroshev.lean:partialConvex_nekhoroshev` | Source is Nek77 Thm4.4, no Diophantine premise. Exponents \(a_n=2/(6n^2-3n+14)\), \(b_n=3/(6n^2-3n+14)\). Existing slow-domain stopping premise must be eliminated in planetary assembly |
| Lifts and scale conversion | `Planetary/Exponential/Lift.lean:lift`; `UniformData.lean:uniform_data`; `Nekhoroshev/Partial/Domain.lean:domain_field_scaled` | Reuse planar local diffeomorphism/ODE lifting. Period-one angles require \(\theta=\lambda/(2\pi)\), Hamiltonian divided by \(2\pi\), slow scaling and bracket coefficient; physical time is unchanged by the complete conversion |
| First exit and continuation | `Planetary/AMD/MovingODE.lean:moving_ode`; `ConfinementExit.lean:amd_exit_forward`, `amd_exit_backward`; `Confinement.lean:amd` | Generic ODE continuation architecture survives; old named theorems depend on `AMDBox`, so new geometry-specific adapter needed |
| Newtonian export | `Frozen/Planetary/Defs/IsNewtonSolutionOn.lean:IsNewtonSolutionOn`; `BarycentricPositions.lean:barycentricPositions`; `BarycentricVelocities.lean:barycentricVelocities` | Reuse planar functions literally. They output `Fin 2 → ℝ`; new dimension-three versions needed, not just a different `Phase` parameter |
| Actual osculating bridge | Existing `keplerEccVector` does not supply it | New identity \(\dot q_i=p_i/m_i+\mu\sum_jp_j\), and compact \(O(\mu)\) comparison with velocity-defined elements using gravitational parameter \(1+\mu m_i\). Then preserve the radial gaps |

## 3. What P-EXP-SAFE actually does

The frozen declaration `KAM/Frozen/Planetary/Theorems/PlanetaryExponentialSafety.lean:planetaryExponentialSafety` (line 53) is sealed by the provider `KAM.Provider.Planetary.planetaryExponentialSafety`. The latter invokes `planetaryExponentialSafety_of_expsafe` with the implementation `KAM.Planetary.expsafe`. This is not a final theorem assuming an unproved stability oracle: follow the supplied implementation.

The chain is:

1. `Exponential/Enlargement.lean:enlarge` turns strict `AMDBox.Admissible` inequalities into an enlarged fast box and slow AMD ball. These inequalities enforce one eccentricity cap, inner radial bounds and adjacent radial gaps.
2. `RealDomain.lean:real_domain`, `ComplexTube.lean:tube`, and `Perturbation.lean:perturbation` make the actual unaveraged chart Hamiltonian an admissible analytic perturbation. Its norm is bounded after introducing B0; \(\nu=B_0\mu\) is the perturbation parameter fed to N.
3. `KeplerData.lean:h_data` supplies the definite fast Hessian and complex bounds. `UniformData.lean:uniform_data` and `Lift.lean:lift` transfer a stopped physical solution to the canonical chart.
4. `Exponential/Stopped.lean:stopped` (line 247) uses **`partialConvex_nekhoroshev`**, for h/P and the reversed-time signs. It obtains a `StoppedActionBound` through \(\nu^{-1}e^{\nu^{-a_n}}\) with drift \(\nu^{b_n}/2\). It does not use a Diophantine nonresonant theorem.
5. `AMD/Confinement.lean:amd`, via angular momentum, `amd_closure`, `amd_compact` and the two exit lemmas, converts that stopped bound into existence, uniqueness, geometric confinement and a Newtonian solution. Conservation gives \(C(t)-C(0)=\sum(\Lambda_i(t)-\Lambda_i(0))\). Thus the secular ball is justified by the same action estimate being bootstrapped; there is no independent secular stability hypothesis in the headline theorem.
6. `Exponential/Safety.lean:expsafe` combines these steps, discards the harmless prefactor after shrinking the smallness threshold, and translates action drift to axis drift. Its choices include \(c=B_0^{-a_n}\) and \(C=B_0^{b_n}\sum_i\mathrm{upper}_i/m_i^2\). `keplerAxis_eq_action_div_sq` and `keplerAxis_drift_le` justify the last conversion.

The source path is `blueprint-P/parts/p14a-amd-expsafe.tex:bpP:p14:expsafe`, consumed by `docs/graph/P/DEPGRAPH.md:bpP:p0:expsafe`; the frozen declaration identifies the specialization of Nek77 Thm12.3, pp.55–56. Track N implements the abstract Thm4.4 route beneath it. The graph and Lean chain agree on that structure; a graph “reviewed” annotation is not a substitute for new-source audit of the upgraded theorem.

## 4. What survives the sharp-threshold replacement

Unchanged mathematical engines: the moving-Sun split, planar chart, complex-extension theorem, Kepler Hessian, Track N partial-convex theorem, extended normal form, preimage theorem, local ODE existence/uniqueness, and scalar angular-momentum conservation.

Adapted interfaces: enlarged-domain witnesses; compactness; parameter-uniform perturbation bounds; the physical-to-chart lift domain; stopped bound packaging; forward/backward no-exit proofs; final action-to-axis bounds. These are not all drop-in theorem applications because many existing signatures carry an `AMDBox`.

New mathematics/API: attained sharp threshold and its moving-parameter continuity; a strong-LP family of safe cylinders; the explicit nonresonant parameter choice; genuine osculating elements. Spatial additions also require cross-product algebra, vector angular momentum, spatial regular coordinates, symplecticity, onto/analyticity and dimension-three Newtonian reconstruction.

The cheaper Nek77 milestone is consequently **substantial but bounded**, not immediate. A single old AMDBox can lose correlations between eccentricities and exclude legal states. Taking sufficiently many local fast boxes with center-dependent full slow balls preserves the complete prescribed sublevel. Compactness makes constants uniform. The same approach supplies either dynamical route.

## 5. Track N answers the analytic question

`PartialBlock.base` is the complex embedding of \(\{I_c\}\times(S/\ell)\), \(\ell=w/r\). `Weighted.Dom` thickens that arbitrary base by r and gives fast angles an s strip. `ExtNFHyp` explicitly demands:

* a holomorphic real-on-real fast h and perturbation f, weighted Fourier bound \(\varepsilon\);
* central nonresonance to cutoff K, frequency Lipschitz bound L and \(KLr\le\alpha/p\);
* \(64\pi ksr\le w^2\), \(2\pi Ks\ge6\), and \(\varepsilon\le\alpha r/(2^7qK)\).

The conclusion includes symplecticity for the weighted bracket, periodicity, realness, an exponential tail and **slow-coordinate displacement**. These are precisely the terms a parameter-only application would miss. `nonresonant` already pays the inverse-map and action-transfer costs. With \(S\) the full center-dependent AMD ball, the remaining difficulty is producing a fixed physical collar w and norm bound uniformly, then excluding slow exit with the original angular momentum. The paper argument in PROOF-PLAN ([A4](A4-proof-plan.md)) does that qualitatively. No global secular flow estimate or secular action-angle coordinates are required.

## 6. Size calibration

Counts were obtained by passing all `.lean` files in each listed directory to **`wc -l`**. They include comments and blank lines; these are directory-level hand-written-development proxies, not token/proof-step counts. Generated root imports and certificate `Data` trees outside these directories are excluded. The listed N/P implementation directories contain no `Data` subtree. Overlapping rows must not be added twice. Reproducible totals: `_sources/repo-line-counts.json`.

| Directory | Files | Lines |
|---|---:|---:|
| `KAM/Nekhoroshev` | 136 | 34,055 |
| `KAM/Frozen/Nekhoroshev` | 26 | 1,199 |
| `KAM/Provider/Nekhoroshev` | 6 | 395 |
| `KAM/Planetary` | 761 | 147,974 |
| `KAM/Frozen/Planetary` | 74 | 3,603 |
| `KAM/Provider/Planetary` | 7 | 462 |
| `KAM/Kepler` | 14 | 5,116 |
| N `Partial` subset | 36 | 12,472 |
| N `NormalForm` subset | 20 | 3,927 |
| P `AMD` subset | 8 | 1,322 |
| P `Exponential` subset | 13 | 2,852 |
| P `Poincare` subset | 10 | 3,957 |
| P `Newtonian` subset | 10 | 2,836 |

N including anchors/providers: **35,649** lines. P including anchors/providers: **152,039**; with the separate Kepler library: **157,155**. A 5–9k-line planar sharp-threshold upgrade is credible relative to the 4,174-line existing AMD/exponential implementation and the available 12,472-line partial engine. Budgeting a second normal-form foundation would be a major overestimate. Conversely, a spatial chart/export package is not a few hundred lines: 9–17k additional lines across geometry, charts and dynamics is a reasonable planning range, not a measured prediction.

## 7. Launch constraints inherited from the repository

Preserve frozen declarations and hashes; add new anchors instead of editing P-EXP-SAFE. Current conventions include `Fin n → ℝ`, the module system, explicit physical versus max norms, and period-one versus radian conversion. No conclusion-shaped assumptions in final statements; stopped premises are internal and must be discharged. The campaign should first approve source text and exact signatures, then generate/review a direct dependency graph. Future proof tasks must obey the repository's current ownership and serialized build rules; no builds were authorized by this research brief.
