# GAP-P9dict independent package audit 1

Auditor: maud-gp9d-1. Date: 2026-10-29 UTC.
Worktree: `/root/code/KAM-inp-gp9d`.
Audited HEAD: `ee06ef0f620cc167afe719215197228b1553dc95`.
Comparison ref `inp`: `747706c70a08f2e1e2610dd82dc38cbdfeed2bfd`.

## Verdict

**PASS WITH NOTES** for the complete assigned `bpP:p9:dict` slice. The mathematical exports pass; the only hygiene exception is the permitted stale generated root. This is infrastructure, with no frozen theorem anchor or provider to seal. No assertion of headline theorem closure is made.

Scope is exclusively the new `KAM/Planetary/SecularSpectrum/DictNodes.lean`; dependencies were read to identify its objects and premises, not re-audited as separate packages. The full `git diff inp...HEAD` is exactly this file, 98 inserted lines. The pre-existing untracked handoff was left untouched. The explicit user report destination overrides the generic brief's main-worktree destination.

Read: `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the supplied audit brief and focused handoff; `docs/tracks/P/statement.md` (relevant conventions and averaged expansion); `docs/graph/P/DEPGRAPH.md:17190–17218`; `blueprint-P/parts/p9-secular-spectrum.tex:155–160`; the P810 design node table at line 175; frozen `HasSecularBirkhoffForm` and `OscillatorAction`, and the spectral/physical adapters below.

## Declaration and node table

All four declarations are in `KAM.Planetary.SecularSpectrum`. These are unsigned exports; no signed declaration is changed or replaced. The older design maps this node to `diagonalize (oscillatorAction identity)`; this gap package additionally exports the literal matrix-spectrum dictionary. No other design node is assigned to `DictNodes.lean`.

| Node / role | Declaration (file line) | Verdict | Reason |
| --- | --- | --- | --- |
| Spectral helper | `charpoly_smul_eq_prod_sorted` (33) | PASS | For every real scalar, including zero and negative scalars, characteristic polynomial of `c • A` factors over `c * sorted A`. No assertion that multiplication by a negative scalar preserves sorting. |
| Sorted spectral helper | `sorted_smul` (52) | PASS | For `c > 0`, both lists are monotone with identical root products, so equality follows from `eq_of_monotone_prod`. Hermitian proof of `c • A` is typing data derivable from `hA`, not a mathematical extra premise. |
| `bpP:p9:dict`, items (1), (2), (4) | `p9_dict` (63) | PASS | For all physical `Data n`, `n ≥ 2`, admissible axes: sorted spectrum of `2 • Q_h` equals `2σ`, its characteristic polynomial has exactly these roots, and both `σ` and `2σ` are strictly negative. The separate `n = 1` branch gives `Q_h = 0`, zero sorted spectrum, and `2σ = 0` for every axis vector. |
| `bpP:p9:dict`, actual frozen-frequency expression | `p9_dict_planar` (85) | PASS | On valid planar data and admissible axes, identifies the spectrum above with `fun j => 2 * p11c_sigma p a j`; proves negativity of both lists. The exact expression supplied to the landed Birkhoff predicate specializes directly to this result. |
| `bpP:p9:dict`, sign and labelling conventions | Handoff convention accounting | PASS | Increasing eigenvalue labelling is implemented by `sorted`; the CP10 absolute-value sign observation is honestly described as a convention, not a proved CP10 nonresonance declaration. No claim is made outside the admissible patch. |

## Fidelity, proof and completeness

`SecularForm.Mat n` is literally `Matrix (Fin n) (Fin n) ℝ` (`Basic.lean:34`). `Data` fields (`Basic.lean:38–46`) contain only positive physical constants/masses and `0 < n`; there is no spectral conclusion bundled into an input. `axes` means positive, strictly increasing axes. `coeffs` is the existing normalized secular matrix (`Coefficients.lean:42–43`), and `sigma` is definitionally its sorted spectrum (`Coefficients.lean:121`). `sorted` uses the actual Hermitian eigenvalues in increasing order (`Norms.lean:34–35`; `LocalAnalytic/Sorted.lean:33–60`). Thus neither list is an invented frequency definition or a replacement matrix.

The characteristic-polynomial proof conjugates the real diagonal spectrum by the eigenvector unitary, moves factors using `Matrix.charpoly_mul_comm`, cancels `star U * U`, and uses the diagonal characteristic polynomial. The permutation product identity preserves multiplicities. `sorted_smul` additionally uses positivity precisely where preservation of monotonicity needs it. These arguments work without simple-spectrum or invertibility assumptions.

The `∀ h` clauses are nonvacuous. An independent elaborated probe constructed each Hermitian proof by `(coeffs_hermitian D a).smul (by simp [IsSelfAdjoint])`, and likewise for arbitrary real Hermitian `A`. No spectral step is assumed. Negativity is discharged by the existing `sigma_neg`, and the one-planet calculation by `coeffs_one` and `sigma_one` (`Nondegeneracy/SymmetricRelation/Limits.lean:36–51`). The one-planet result is stronger than the source in dropping axis admissibility. `Data.hn` excludes `n = 0`; `n ≥ 2` together with the explicit `n = 1` clause exhausts the source's positive dimensions. It is a faithful case split, not a loss of the one-planet case or an assertion of negativity there.

The frozen normalization is literal: `OscillatorAction.lean:37–38` is `(p² + q²)/2`; `HasSecularBirkhoffForm.lean:55` multiplies it by `Omega`. `PlanarTorsion/Birkhoff/FhatClause.lean:63–65` supplies `fun _ I j => 2 * p11c_sigma p (p.axes I) j`. `SpectralAdapter.lean` identifies `p11c_Q` with `coeffs` and `p11c_sigma` with `sigma`. The planar export therefore identifies the actual expression used by the existing construction, under the same admissible-axis guard. It does not assert that arbitrary input `Omega` to the frozen predicate has these values. The source's quadratic rewrite into oscillator actions already appears in `SecularSpectrum/Diagonalize.lean:124–132,155–159`; this package need not repeat that analytic theorem.

For item (2), the source says “which is insensitive to the overall sign” (`p9-secular-spectrum.tex:157`). Algebraically `|Σ (-Ω_j) k_j| = |Σ Ω_j k_j|`; an independent scratch example proved precisely this identity. That is not a proof of the positive CP10 lower bound. The package and handoff do not claim such a proof. Under the explicit orchestrator ruling, the sign/index/labelling convention clauses are accounted for without demanding a new production CP10 declaration. The stated general matrix dictionary and the concrete planar specialization cover the assigned mathematical gap. Existing graph consumers use the factor-two normalization (`DEPGRAPH.md:18794,18805,21204,21218`); these exports do not narrow it to a model or add consumer hypotheses.

## Definition classification and imports

No new `def`, `abbrev`, `structure`, instance, or public carrier is introduced. Local `U` and `d` at lines 38–39 are exactly the eigenvector unitary and diagonal eigenvalue matrix. They have no fallback branch. The global `sigma` and sorted eigenvalue operations are inherited definitions; the new proof relies only on their intended eigenvalue meaning. Off-patch continuation of frozen frequencies is not asserted by these exports.

A transitive KAM import traversal found 152 modules, no provider imports, and 55 frozen imports, all manifest-state `SEALED` definitions. There are no imported frozen theorems, hence no imported `DRAFT_SORRY` anchors. The relevant frozen oscillator/Birkhoff definitions are also `SEALED`. Full qualified names remain under `KAM.Planetary.SecularSpectrum`; a declaration-name scan of all production `KAM/**/*.lean` found each of the four new short names exactly once. No reused public helper name or harmful root shadow was found.

## Independent checks

All Lean/Lake commands were sequential, with `LEAN_NUM_THREADS=1` and niceness 5; the build wrapper itself supplies `nice -n 5`. Lint was run only after kernel replay finished, because its ABI phase invokes Lean. No source, manifest, generated root, README, or git state was changed.

1. Targeted compile gate:

   ```text
   env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp9d KAM.Planetary.SecularSpectrum.DictNodes
   [inp-gate] slot 2 acquired 03:56:33 for KAM.Planetary.SecularSpectrum.DictNodes
   Build completed successfully (9198 jobs).
   exit 0
   ```

   Only inherited dependency warnings were replayed (unused variables, deprecated tactics, one style suggestion); none came from `DictNodes.lean`.

2. Axiom and usability probe:

   ```text
   env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/maud-gp9d-1.lean
   'KAM.Planetary.SecularSpectrum.charpoly_smul_eq_prod_sorted' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.sorted_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.p9_dict' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.p9_dict_planar' depends on axioms: [propext, Classical.choice, Quot.sound]
   exit 0
   ```

   Besides these four `#print axioms` commands, the probe checked derivability of the Hermitian typing arguments, the unrestricted one-planet projection, the exact landed frequency expression at `a = p.axes I`, and the sign identity above. No frozen-provider type/seal-body probes apply: this package has no provider or frozen theorem anchor (`FROZEN_DECL: -` in the graph).

3. Kernel replay, one invocation for the sole new module:

   ```text
   env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularSpectrum.DictNodes
   replaying KAM.Planetary.SecularSpectrum.DictNodes
   exit 0
   ```

4. Lint:

   ```text
   env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1247 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1 (only the explicitly permitted generated-root mismatch)
   ```

5. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty. `git diff --check inp...HEAD` and `git diff --check`: exit 0, no output. Direct scan of the new module found no forbidden tokens, resource overrides, or `EuclideanSpace`. It has 98 lines, maximum 100 Unicode characters per line, and the required copyright, `module`, public imports, module docstring and public section. Scratch probes and temporary check logs were removed after completing the report.

## Notes, uncertainties, errata and deviations

No new mathematical defect, source erratum, or implementation deviation found. Blueprint line 156 already identifies the factor-half issue as “suspected erratum E-P-Fej04r-3”; this audit checks consistency with that declared normalization, not a fresh transcription audit of Fej04r or CP10. Nothing here upgrades that source erratum's status. The descriptive opening of the track statement is historical; current frozen definitions and D20 control its approved meaning.

The graph still says `LEAN_STATUS: NOT_STARTED` for this node (`DEPGRAPH.md:17215–17217`); updating graph status and regenerating `KAM.lean` belong to the orchestrator, not this report-only audit. No frozen theorem is sealed by this result. The report is the only persistent file written by the auditor.
