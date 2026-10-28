# P23-10 independent package audit 1

Overall verdict: **PASS WITH NOTES** for P23-10 (`bpP:p2:split`). No mathematical, definition, signature, or consumer-applicability defect found in the scoped implementation. No frozen theorem is assigned to this infrastructure package, so provider/frozen-type equality and a frozen seal body are **not applicable**. This verdict does not close P-G or the finite averaging construction.

Audited HEAD: `4b34dcea9164aba1b968170d582126ba5f739f26`.
Scoped file: `KAM/Planetary/Averaging/Splitting.lean`, **348 lines**,
SHA-256 `cdb2ce2f9566e1530ec60807690f5a7c108b9e63d830cb4bd5074cdecd78a77b`.
Report destination follows the user's explicit worktree override:
`/root/code/KAM-inp-p2310/docs/tracks/P/audits/P23-10-audit-1.md`.

## Authority and comparison boundary

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package audit brief, the P23-10 handoff/AUDIT FOCUS, the P23 design revision 2 (package row at L274, exact appendix signatures at L505–530), both design audits, the relevant track-P statement conventions, and Part 2 blueprint L22–74. Checked the split/step graph records and finite-averaging consumers at blueprint Part 2 L99–125. Read the relevant frozen field, strip, action-neighbourhood, phase and block definitions and the actual Weighted/Canonical/NormalForm dependency contracts.

The shared signature file is absent at this worktree's `.drafts/design/P23Signatures.lean`; the named file exists at `/root/code/KAM-inp/.drafts/design/P23Signatures.lean`. Compared its `firstGen`, `directMap`, and `split` directly with both the design appendix and implementation: all three signatures match after whitespace normalization, and both definition bodies match as well. The shared file was read only; its fixtures and `sorry` bodies were never imported into the proof.

`git diff inp...HEAD` reports multiple merge bases and selects
`313c5e7e5854640055fcd8089ff18446da1fe5c3`: exactly `Direct.lean` (186 lines) and `Splitting.lean` (348 lines) are added. The requested scoped comparison
`git diff inp-p2305...HEAD -- 'KAM/Planetary/Averaging/Splitting*.lean'`
is exactly the new splitting module. `Direct.lean` is byte-identical between `inp-p2305` and HEAD. P23-05 is used as an upstream dependency, not independently re-audited here.

The unfiltered comparison against `inp-p2305` also contains inherited unrelated packages and generated-root changes. The other `inp` merge base,
`beddbc6fca7c5cdcc05bb4178fe7576a3bfe730f`, similarly exposes those inherited differences, including 11 added root imports. They are outside the explicit Splitting-only focus; they are not hidden by claiming every possible merge-base diff is empty. The brief's literal protected-path command with Git's selected merge base is empty, and the P23-10 HEAD commit changes only `Splitting.lean`. No frozen/manifest change appears against either merge base.

## Declaration and node verdicts

All names below have namespace `KAM.Planetary`. Private declarations are included to make the complete local proof inventory reviewable.

| Node / obligation | Declaration and source line | Verdict | Reason |
|---|---|---|---|
| `bpP:p2:split`, generator | `firstGen`, L30 | PASS | Exact projection of the unchanged `homGen K {0} h f` onto nonzero first-block modes. |
| `bpP:p2:split`, same map | `directMap`, L33 | PASS | Exact time-one flow on the one-loss domain; definitionally N `iterMap` with `Λ={0}`. |
| `sp-coef`, finite cutoff | private `finite_zBall'`, L41 | PASS | Embeds the cutoff in a finite natural-ceiling cutoff; arbitrary real K allowed. |
| `sp-coef`, coefficient formula | private `genC`, L47 | PASS | Exact cutoff indicator times the divided Fourier coefficient. |
| `sp-coef`, representation | private `homGen_eq_series`, L51 | PASS | Unconditional equality of the actual generator and that Fourier series. |
| `sp-coef`, summability | private `summable_genC`, L58 | PASS | Finite support gives genuine summability; no junk-zero sum inference. |
| `sp-coef`, coefficient extraction | private `coeff_homGen`, L64 | PASS | Torus Fourier orthogonality recovers the specified coefficient. |
| `sp-coef`, small divisor | private `norm_div_divisor_le`, L69 | PASS | Uses positive α, q≥1, and the actual divisor lower bound to give q/(2πα). |
| `sp-field`, character invariance | private `character_add_smul_single`, L94 | PASS | A zero jth Fourier index gives invariance along the jth complex-angle line. |
| `sp-field`, vanishing derivative | private `dtheta_eq_zero_of_modes`, L108 | PASS | Fourier reconstruction and local line invariance imply zero derivative on the open domain. |
| `stepP:p2:sp-coef` | `firstGen_class_bound`, L153 | PASS | Returns class and qδ/(2πα₁) bound without width-loss/smallness hypotheses; stronger helper applicability. |
| `stepP:p2:sp-coef`, support | `split_coeff`, L196 | PASS | All coefficients of the complement with nonzero first block vanish, on every allowed action. |
| `stepP:p2:sp-field`, first block | `dtheta_firstGen_eq`, L216 | PASS | Equality of actual first-block angle derivatives of φ and φ¹ on the original domain. |
| `stepP:p2:sp-int`, MVT | private `component_mvt`, L248 | PASS | Derived from the real mean-value theorem for a continuous linear image of an exhibited solution on [-1,1]. |
| `bpP:p2:split`, `sp-field`, `sp-int` | `split`, L260 | PASS | Exact design conjunction: weighted generator bound, coefficient independence, both block action bounds and angle bound on the three-halves-loss domain. |

## Statement fidelity, proof and consumers

`DirectHyp` contains only source positivity/typing data, holomorphy of h, the full-neighbourhood divisor lower bound, class of f, and its weighted bound. `TwoDiv` is the explicit two-scale divisor predicate. No solution, transformed map property or hard proof conclusion is assumed. Its stronger α₁ branch is actually used at L175–180; α₂ is not substituted for it.

The source's δ equal to the norm is generalized to an arbitrary nonnegative numerical upper bound via `WBound`. This is a stronger applicable theorem, and agrees with the audited design. `H.div` at α₂ is implied by `TwoDiv` and α₂≤α₁; its presence is redundant source data rather than a new mathematical restriction. No frequency Lipschitz bound, dimension lower bound, realness requirement, or conclusion-shaped premise is introduced. Empty D, zero-dimensional blocks, K=0, δ=0, and q=1 remain allowed.

The coefficient proof identifies `homGen` with a finitely supported series, recovers its coefficients by torus orthogonality, and compares each projected weighted summand against q/(2πα₁) times the corresponding f summand. It separately proves summability before comparing sums. `split_coeff` uses class-backed coefficient linearity and the exact projection formula. Independence is the blueprint's explicitly declared Fourier-mode notion (Part 2 L34); it also yields pointwise derivative equality through Fourier reconstruction and eventual line constancy. No unjustified differentiation of an infinite series is used.

The field/integration part constructs `CanonData` with Φ=qδ/(2πα₂). The exact smallness premise gives Φ/(ρσ)≤1/4, which implies the canonical requirement ≤1/2. `flow_a` and `gaugeInterior_half` supply an actual solution on [-1,1] contained in `Dom D (r-ρ) (s-σ)`. `vf_bound` for φ¹ and `dtheta_firstGen_eq` then give the α₁ bound for every first-block component along this solution. The real continuous linear projection and `component_mvt` integrate that bound at t=1. The last block is bounded by the full Pi max norm; the remaining displacement estimates are projections of `canonical_map_a` on the same domain and same flow.

The full-generator class and α₂ weighted bound from blueprint clause (a) remain available as `(direct H).1` and `(direct H).2.1`. They are not omitted proof obligations concealed by the selected `split` conjunction. This is the design-audited selected-view convention. The forthcoming P23-12 consumer can use the returned displacement bounds on its smaller step domain with the exact N map: the probe proves `directMap = iterMap ... {0} ...` by `rfl`. Finite iteration, telescoping, reality and lattice transport remain P23-12/upstream obligations; this audit does not claim those later constructions exist.

## Definition classification and imports

- `firstGen`: intended Fourier projection, exactly the approved body on its total carrier. The inherited projection uses a total `tsum`; class and bounds are established under source hypotheses. All generator coefficients have finite cutoff support, and no theorem exploits the nonsummable-sum default.
- `directMap`: intended existing total flow, with no additional choice/default wrapper. The inherited `flow` chooses a solution if one exists and otherwise returns the initial point (`Canonical/Flow.lean` L54–55). On every point where `split` asserts a displacement, `flow_a` proves existence and the solution equation, so the fallback cannot supply the theorem. No assertion is made that arbitrary off-domain inputs have a dynamical meaning.
- Private `genC`: intended finite-cutoff divided coefficient. Total complex division away from the guarded domain is conventional; under theorem hypotheses the used denominators have positive lower bounds. There is no added `abbrev`, `structure`, instance, witness-selection device, or alternative norm.

The three direct imports are `Averaging.Direct`, `Canonical.TransformSeries`, and `Canonical.Adjoint`. A recursive source import inventory has 82 local modules, no provider import, and no frozen theorem import. Its 12 frozen imports are definitions, all `SEALED` in the manifest: ActionNbhd, ComplexStrip, both Hamiltonian fields, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, SymplecticForm, and Planetary Fast/Phase/Slow. Thus there is no DRAFT_SORRY dependency or provider-quarantine violation. Coordinates and norms remain the prescribed Fin-function Pi max norm and angle-first product.

## Independent validation

Commands run from `/root/code/KAM-inp-p2310`. All explicit audit build/probe/kernel commands below use `LEAN_NUM_THREADS=1` and `nice -n 5` (the build wrapper supplies nice).

1. Targeted compile gate:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2310 KAM.Planetary.Averaging.Splitting
   [inp-gate] slot 2 acquired 07:50:53 for KAM.Planetary.Averaging.Splitting
   Build completed successfully (9128 jobs).
   exit 0
   ```

   This was the targeted overlay build; the job count is Lake's dependency accounting, not a clean build invocation. No `lake clean`, update, cache get, or library-wide build was run.

2. Probe `.lake/abi-scratch/P2310Audit.lean`:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2310Audit.lean
   'KAM.Planetary.firstGen_class_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.split_coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.dtheta_firstGen_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.split' depends on axioms: [propext, Classical.choice, Quot.sound]
   exit 0
   ```

   The probe copies the exact design `split` declaration under the fresh name `AuditP2310.split_signature`, with body
   `by exact KAM.Planetary.split H hα hd hρ hρr hσ hσs hsmall`.
   Thus the assigned statement elaborates with exactly the explicit source binders in order. Two `rfl` examples check the `firstGen` body and `directMap = iterMap ... {0} ...`. No frozen seal was simulated because there is no assigned frozen anchor.

3. Kernel replay, one invocation for the only new scoped module (there is no separate new helper module):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Averaging.Splitting
   replaying KAM.Planetary.Averaging.Splitting
   exit 0
   ```

4. Source lint, final serialized invocation:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (460 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The only failure is the brief's explicitly permitted stale generated root. No generated file was regenerated. Forbidden-proof/resource scans, 100-character lines, module form, 1500-line cap, frozen guard and elaborated ABI checks pass. The scoped module has copyright, `module`, public imports, module documentation and an exposed public noncomputable section. A separate token/line inventory found no forbidden tokens or overlong lines. The handoff says 343 lines; the audited file actually has 348, safely below the cap.

5. `git diff --check inp...HEAD`: exit 0 (only Git's multiple-merge-base warning). `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty diff, exit 0, with the same warning; alternate-base qualification is recorded above. No state-changing git operation was used.

Audit-process deviation: the initial `sh scripts/lint_sources.sh` invocation was launched while the targeted build command was pending, without explicitly setting `LEAN_NUM_THREADS` or nice. Lint internally invokes `lake env lean` for ABI validation; the first probe was also started before that initial lint had completed. This did not follow the requested serialized resource protocol. The initial lint returned the same sole generated-root failure and ABI success. Final validation corrects the scheduling: after the initial checks finished, kernel replay ran alone; then lint was rerun alone with the required environment/priority, followed by a serialized rerun of the probe. No other worker's process was interrupted. This note is an audit-execution deviation, not a defect in the submitted proof.

## Suspected errata, uncertainties and write boundary

No new blueprint contradiction or pinned-source erratum was found. The comparison here certifies the assigned design/blueprint proof contract; CP10 (70)–(71), p.565 is the blueprint's source attribution, not a fresh PDF verification in this audit. No statement repair or mathematical deviation was introduced. There was no default-heartbeat failure or resource-budget override.

Only this report was written outside the authorized `.lake/abi-scratch/` probe area. The probe and captured kernel log were deleted after checking. The pre-existing untracked `P23-10-handoff.md` was left untouched. No production Lean, frozen declaration, manifest, generated root, README, blueprint, graph or shared signature was edited.
