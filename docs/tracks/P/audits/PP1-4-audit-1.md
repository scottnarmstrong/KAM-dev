# PP1-4 independent proof audit 1

Audited file: `KAM/Planetary/Hamiltonian/Chart.lean` (248 lines), HEAD
`1178f45b0c98c4aa05bd1a789ae0890d404a651a`. Scope is ONLY PP1-4/Chart, as the
handoff's AUDIT FOCUS directs. No delegation, production edits, or state-changing git commands.
Report destination follows the user's explicit worktree-path override of the generic brief.

## Verdict and scope

**PP1-4: PASS WITH NOTES**. No material
statement or proof defect found. This is an infrastructure package: it exports no provider and
seals no frozen anchor. Accordingly provider/frozen-type comparison, proposed seal-body probes,
and per-anchor seal readiness are **not applicable**. No I/N/P headline theorem is certified here.

Read AGENTS.md, PLAN, DECISIONS, the assigned package audit brief and handoff, Part 1 design row
P1-4/proof plan/Appendix B, DESIGN-P1-design-audit-1, the Kepler design's Part 1 interface and
risk discussion, Track P statement, the relevant Part 1 blueprint, the four directly imported
frozen definitions and their imported IsDiophantine definition, and the delivered Kepler and
Poincaré interfaces. No external source result needs to be replaced or assumed for this package.

## Findings and notes

- **N1, resolved design concern:** `volume_angleScale_image` at Chart:205–217 installs
  `Measure.prod.instIsAddHaarMeasure _ _` locally. DESIGN-P1-design-audit-1's N1 explicitly permits
  this alternative. The named Haar helper remains owned by PP1-7; no Chart → Liouville edge or
  duplicate declaration is introduced. No correction requested.
- **N2, comparison provenance:** the requested `git diff inp...HEAD` warns
  `multiple merge bases, using bd23fdf193a0f771879dfd4fdbfdfe00570288e5`.
  Both merge bases are `bd23fdf193a0f771879dfd4fdbfdfe00570288e5` and
  `ca8a6683f2e6fe6e275d17b746066c70bcb68d26`. At the recorded comparison, `inp` was
  `d030f8799fbc9a4c5e23582162b9bd844fa49574`. The broad diff contains 29 files,
  including three inherited generated-root imports (Transform, TransformSeries, Poincare.D25).
  Thus the brief's literal empty-diff check for `KAM.lean` does **not** pass on this comparison.
  Frozen files, manifest and README have an empty diff. The package's commits `3746243` and
  `1178f45` touch only Chart, and `git diff --name-only c7d5689..HEAD` outputs only Chart.
  The generated-root delta is inherited branch history, outside the explicitly assigned scope;
  it is not silently described as an empty broad diff or attributed to this package.
- **N3, expected generated root:** lint's only accepted exception is the out-of-date generated
  `KAM.lean` receipt below. Regeneration remains with the orchestrator.

No blocking finding, added source hypothesis, widened constant dependence, changed norm/carrier,
source substitution, or conclusion-shaped premise was found. No heartbeat design signal occurred.

## Declaration fidelity

Every name below is in `KAM.Planetary`. All 21 public theorem signatures match design Appendix B
(lines 450–554) exactly after whitespace normalization. The independent elaboration probe also
checks those design types with all original binders explicitly quantified. All five definitions
match the design bodies. Blueprint labels abbreviate `bpP:p1:*`, with `li-det` a `stepP:p1:*` label.

| Node | Lean declaration | Verdict | Reason / note |
|---|---|---|---|
| chart | `IsChart` | PASS | Exact conjunction of analytic-at-neighbourhood and the delivered Kepler predicate. |
| chart | `isChart_iff` | PASS | Definitional equivalence; no hidden premise. |
| chart | `IsChart.analyticOnNhd` | PASS | Projection of the first defining clause. |
| chart | `IsChart.symplectic` | PASS | Projection to the original Kepler symplectic predicate. |
| chart | `IsChart.mono` | PASS | Both clauses restrict to an arbitrary subset. |
| chart | `chartPullback` | PASS | Exactly the total function c inverse times H composed with Ψ. |
| chart | `IsChart.bijective_fderiv` | PASS | Positive factor implies nonzero; uses PP1-1 nondegeneracy in the same dimension. |
| li-det | `IsChart.abs_det_fderiv` | PASS | Absolute determinant c^d, with the phase dimension 2d. |
| chart-field / cf-diff | `chart_field_differentiableAt_iff` | PASS | Both implications; reverse direction uses a proved local inverse. |
| chart-field / cf-field | `chart_field` | PASS | Unconditional frozen-field identity, including the nondifferentiable branch. |
| chart-orbit | `chart_orbit` | PASS | Retains differentiability and HasDerivAt; stronger arbitrary-set J formulation. |
| typical (3) | `IsChart.comp` | PASS | Correct MapsTo guard, composition order and c₁*c₂. |
| typical (3) | `chartPullback_comp` | PASS | Both inverse scale factors; valid also for zero factors by total inverse. |
| typical / helper | `isChart_continuousLinearEquiv` | PASS | Actual conformally symplectic CLE; no theorem conclusion assumed as data. |
| conv#data | `angleScale` | PASS | Exactly (c • z.1, z.2), on the full carrier. |
| conv#data | `angleScaleCLM` | PASS | The same scaling as a continuous linear map, including c=0. |
| conv#data | `angleScaleCLM_apply` | PASS | Definitional equality of scaling implementations. |
| conv#data | `fullShift` | PASS | Exactly (2π k, 0), uniformly for all d. |
| period-convert (d) | `fullShift_eq_angleScale` | PASS | Correct full lattice and factor 2π. |
| typical (2) / period-convert (a) | `isChart_angleScale` | PASS | Global chart for positive c; original designed hc binder retained. |
| period-convert (a) | `angleScale_add_angleShift` | PASS | Full integer position lattice; momenta unchanged. |
| period-convert (a) | `abs_det_fderiv_angleScale` | PASS | Correct c^d Jacobian for any phase point. |
| period-convert (a) / measure-use | `volume_angleScale_image` | PASS | Exact volume scaling for arbitrary sets, stronger than measurable-set restriction. |
| period-convert (b) | `chartPullback_angleScale` | PASS | Exactly c inverse times H(c z₁,z₂); no time rescaling. |
| period-convert (b) | `angleScale_hamiltonianVectorField` | PASS | Unconditional field transport with the frozen sign convention. |
| period-convert (d) | `fastShift_eq_angleScale` | PASS | Correct append/coercion; slow positions and all momenta zero. |

## Definition classification and proof review

- `IsChart`: exposed Prop-valued predicate, exactly `AnalyticOnNhd ℝ Ψ O ∧
  KAM.Kepler.IsSymplecticOn c Ψ O`. Neither injectivity nor any hard analytic theorem is bundled
  as extra chart data. Positivity and openness are standing conditions at blueprint use sites;
  proofs only require positivity where needed and work without openness because analyticity is
  at a neighbourhood of each point.
- `chartPullback`: exposed total real function `fun z => c⁻¹ * H (Ψ z)`. At zero c this is Lean's
  specified total inverse, not an arbitrary fallback used to prove positive-c transport.
- `angleScale`: exposed total linear position scaling `(c • z.1, z.2)` for all real c.
- `angleScaleCLM`: exposed CLM implementing exactly that scaling; no alternate object.
- `fullShift`: exposed total integer-lattice translation `(fun i => 2 * π * (k i : ℝ), 0)`
  for every d, including dimension zero. No junk values or hidden extension.

The four private helpers (`linearField_smul`, `linearField_zero`, `angleScale_eq_clm`,
`angleScale_symplectic`) are elementary proved identities, not extra assumed inputs.

The local inverse proof (Chart:78–104) derives strict differentiability from analyticity and
constructs a CLE from PP1-1's bijectivity. It uses the genuine local right inverse to recover H
near Ψ(z); no global inverse or injectivity is assumed. The field proof (107–126) has the correct
c inverse cancellation and proves the nondifferentiability equivalence before using total
fderiv=0. The orbit proof is the actual derivative chain rule and keeps H differentiability.
Composition has the correct scalar order (commutativity only rearranges real factors). The
Jacobian and Haar argument give c^d, not c^(2d), with product Lebesgue volume on the frozen max-norm
carrier. No measurability premise is needed for an invertible linear map's outer-measure formula.

The delivered `poincareProdCast` supplies exactly `analyticOnNhd_poincareProdCast` and
`poincareProdCast_symplectic`; their conjunction constructs `IsChart 1` directly for arbitrary n.
Thus the existing phaseCast bridge handles `n+n` versus `n*2` without changing Chart's carrier.
The successful lightweight probe checks `fullShift` at `Fin (n+n) → ℤ`. The Poincaré conjunction
was reviewed at source level; its optional heavy-import elaboration attempt was terminated
(exit 143) before diagnostics, so no successful consumer-probe elaboration is claimed. This is
an interface review, not an audit of
Poincaré proofs or the later PP1-6/PP1-7 packages.

## Hygiene and independent validation

All Lean invocations were serialized and used `LEAN_NUM_THREADS=1`, at niceness 5. No heartbeat,
recursion-depth, synthesis-budget or linter overrides were introduced.

**Targeted build** (exit 0):

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-pp14 KAM.Planetary.Hamiltonian.Chart
```

```text
[inp-gate] slot 2 acquired 05:57:09 for KAM.Planetary.Hamiltonian.Chart
⚠ [9054/9055] Replayed KAM.Planetary.Hamiltonian.Algebra
warning: KAM/Planetary/Hamiltonian/Algebra.lean:146:39: Variable name `hc` is not explicitly referenced.
⚠ [9055/9055] Replayed KAM.Planetary.Hamiltonian.Chart
warning: KAM/Planetary/Hamiltonian/Chart.lean:193:36: Variable name `hc` is not explicitly referenced.
Build completed successfully (9055 jobs).
```

The omitted warning hints suggest renaming unused binders or disabling their linter; neither was
done. Chart's positive-factor binder is part of the required design signature. The build replayed
up-to-date artifacts; the independent kernel replay below supplies the separate proof check.

**Exact design-type and axiom probe** (final exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/PP14Audit.lean
```

The probe imports Chart and checks 21 explicit Pi types transcribed from Appendix B using
`example : ∀ <all original binders>, <original conclusion> := @KAM.Planetary.<name>`.
It also checks the exposed chart/pullback bodies by `rfl` and fullShift at dimension n+n.
Only unused-binder warnings occurred in the final run. Exact axiom output:

```text
'KAM.Planetary.isChart_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.IsChart.analyticOnNhd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.IsChart.symplectic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.IsChart.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.IsChart.bijective_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.IsChart.abs_det_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chart_field_differentiableAt_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chart_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chart_orbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.IsChart.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chartPullback_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isChart_continuousLinearEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.angleScaleCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fullShift_eq_angleScale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isChart_angleScale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.angleScale_add_angleShift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.abs_det_fderiv_angleScale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.volume_angleScale_image' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chartPullback_angleScale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.angleScale_hamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fastShift_eq_angleScale' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Attempt history is retained for accuracy: an initial probe importing Poincare.Product was
terminated (exit 143, no diagnostics; cause unconfirmed). The first lightweight attempt returned
all 21 clean axiom reports, then exited 1 because the audit generator truncated its last signature
at the named argument `b := b`. This was an audit-harness parsing error, not a package error.
Correcting that final probe signature gave exit 0 with every example elaborated; no production
file changed.

**Kernel replay** (one invocation, exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Hamiltonian.Chart
```

```text
replaying KAM.Planetary.Hamiltonian.Chart
```

Chart is the sole in-scope lemma module; there is no provider module to include.

**Lint**:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (417 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Exit code **1**, solely because the generated root is stale. This is the exact exception allowed
by the audit brief. There were no forbidden-token, line-length or file-length diagnostics.
The module system, frozen-anchor guard and all 144 frozen declaration ABI hashes passed.


**Static checks and import quarantine**:

```text
Public theorems: 21
All 21 theorem signatures: whitespace-normalized exact match with Appendix B
IsChart MATCH
chartPullback MATCH
angleScale MATCH
angleScaleCLM MATCH
fullShift MATCH
Lines: 248 maximum characters: 100
Forbidden tokens: []
Transitive KAM modules: 9
Providers: []
Frozen theorem imports: []
Frozen definition imports: 5
```

A recursive source-import walk found only the frozen definitions SymplecticForm,
HamiltonianVectorField, Phase, IsDiophantine and FastShift. There are no frozen theorem imports
whose SEALED/DRAFT_SORRY state could affect this package, and no provider imports.
`git diff --check inp...HEAD -- KAM/Planetary/Hamiltonian/Chart.lean` exits 0 (only the documented
multiple-merge-base warning). `git diff --name-only inp...HEAD -- KAM/Frozen manifest README.md`
prints no paths (same warning). The separate `KAM.lean` diff is nonempty as documented in N2.


## Uncertainties, suspected errata, and deviations

No new suspected defect in a pinned source or the assigned blueprint statements. No mathematical
or Lean-signature deviation. Harmless strengthening: arbitrary O and J rather than open O/interval
J where the proof only uses pointwise neighbourhood analyticity and two-sided derivatives; exact
linear volume scaling for all sets. These strengthenings are already in the audited design.
The local Haar-instance choice is the recorded, explicitly approved design alternative N1.

The branch-history/generated-root notes above are the only hygiene qualifications. No frozen
file, manifest, README or generated root was edited by this audit. Only this report persists;
Lean probes are removed after the checks.
