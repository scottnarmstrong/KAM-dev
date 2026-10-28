# B01 independent package audit 1

**Verdict: PASS WITH NOTES for B01 (data infrastructure).** No blocking implementation or source-fidelity finding. No frozen theorem/provider belongs to B01; provider-type equality, seal-body substitution and per-anchor seal readiness are not applicable. This report does not close P-FIXED, any other frozen anchor, or any downstream P11B proof obligation.

Audited 2026-10-28 in `/root/code/KAM-inp-p11b-b01`, HEAD `25caaf5f1d6b939a84b0b32a47067d647c7e7124`, against `inp` at `dca5e7e3ee3a8b0d8f0f2b53a377bf87ac1fc024`. `git diff inp...HEAD` contains only the new 116-line `KAM/Planetary/WeakKAM/Data.lean`. The handoff was already untracked and is preserved. The explicit user report destination overrides the generic brief's main-worktree destination.

Read the package brief, AGENTS.md, PLAN, DECISIONS, track P statement, P11B design/package row B01 and Appendix A, both design audits (under `docs/tracks/P/design/`), the canonical signature, and the relevant blueprint/frozen definitions. Scope is exclusively the Data module.

## Declaration and definition classification

Names below are in `KAM.Planetary`. Blueprint labels abbreviate `bpP:p11a:`. All 15 declaration blocks, including structure fields and `sel_data`, are byte-identical to canonical signature lines 38–112 and the corresponding Appendix A block. A Python comparison of the full block from `abbrev SelectionR` through `sel_data` returned `EXACT SIGNATURE/APPENDIX MATCH; 15 declarations; NO OTHER DECLARATION NAME COLLISIONS`.

| Node | Declaration (Data.lean line) | Verdict | Classification / reason |
|---|---|---|---|
| sel-data; domain-def | `SelectionR` (40) | PASS | Carrier abbreviation `Fin n → ℝ`; existing max norm. |
| sel-data; domain-def | `SelectionC` (41) | PASS | Carrier abbreviation `Fin n → ℂ`; existing max norm. |
| domain-def | `SelectionPhaseC` (42) | PASS | Product `(theta, eta)` in the source order. |
| domain-def | `SelectionPoint` (43) | PASS | Product `((theta, eta), b)`; parameter separate from dynamical phase. |
| sel-data | `selectionReal` (45) | PASS | Coordinatewise real inclusion on the entire carrier. |
| sel-data | `selectionRe` (46) | PASS | Coordinatewise real part on the entire carrier. |
| sel-data; index-def | `selectionLength` (47) | PASS | Explicit Euclidean length, square root of sum of squares; no norm instance change. |
| sel-data; index-def | `selectionThick` (48) | PASS | Euclidean Minkowski thickening by a closed radius ball. For source compact nonempty K, equals the closed distance thickening. |
| domain-def | `selectionDomain` (50) | PASS | Frozen angular strip, strict max-norm action ball, unrestricted supplied parameter set B. |
| sel-data; index-def | `selectionScalar` (52) | PASS | Literal `(c · ω(y))^ρ`, with no change of scalar convention. |
| sel-data; index-def | `selectionDG` (55) | PASS WITH NOTES | Scalar diagonal Euclidean tensor seminorm; source-domain qualifications below. |
| sel-data; index-def | `selectionDGVector` (58) | PASS WITH NOTES | Same diagonal seminorm with explicit Euclidean target length. |
| sel-data (a)–(d) | `SelectionData` (64) | PASS | Standing input structure, not a construction-output assumption. Detailed field review below. |
| sel-data (c) | `SelectionPerturbation` (105) | PASS | Separate Prop structure containing exactly holomorphy, period-one periodicity, reality, and pointwise ε bound. |
| sel-data | `sel_data` (114) | PASS WITH NOTES | Transparent identity definition `d ↦ d`; packages the supplied data and proves no additional analytic theorem. |

`SelectionData` includes the literal integer/exponent restrictions, compact positive-volume K, positive strip/thickening/loss bounds, C₁≥1, 0<β≤M, holomorphy/reality, induced max-norm Hessian bound, pointwise existential finite derivative order, and full multilinear top derivative bounds. Its `h` is the source Hamiltonian, not an assumed solution. No iteration, selected set, frequency limit, torus, displacement, or Lipschitz conclusion is assumed. Perturbation f and ε occur only in the separate perturbation predicate, preserving the intended later quantifier order for constants.

The Hessian expression differentiates the complex gradient into the existing Pi max norm, giving the induced max-to-max operator norm, rather than a maximum matrix entry. Finite type allows order zero, as the source maximum over 0≤j≤μ requires. `top_bounds` uses Euclidean unit-ball arguments; this is equivalent to the source unit-sphere operator bound for positive multilinear order, by scaling and multilinearity. The pointwise existential finite-type clause matches the lower bound on the infimum of the finite maximum, since the finite maximum is attained.

The open collar is exactly frozen `actionNbhd K (2*ϑ)`. Holomorphy there supplies smoothness on its real slice; the Euclidean ϑ-thickening lies inside it because max length ≤ Euclidean length ≤ϑ<2ϑ. Consequently omitting a separate smoothness field does not assume a proof step or weaken the input object. Downstream proofs still need to establish and use these elementary analytic bridges.

## Totality and scope notes

There are no custom fallback branches, arbitrary selected witnesses, or replacement norm instances. All bodies are literal source formulas or input structures. Total library `fderiv`/`iteratedFDeriv` values away from differentiability are not claimed to represent source derivatives there. For n≥1 the Euclidean unit sphere is nonempty compact, and each fixed continuous multilinear derivative gives a continuous, bounded diagonal evaluation on it; its real supremum therefore has the intended meaning. At order zero this is the value's absolute value or Euclidean length, as required.

At n=0 the unit sphere is empty, so the scalar order-zero expression can give the empty-supremum value instead of |g(y)|. This is the inherited total-library boundary already discussed in design audit 1, paragraph “Definitions/structures” (line 284); it is outside the source's N≥1 domain and excluded by `SelectionData.n_pos`. Likewise the closed-distance interpretation of `selectionThick` uses compact source K, not an arbitrary nonclosed set. No B01 theorem consumes either out-of-source case. These are qualifications on interpretation, not a reliance on junk values or a newly introduced source defect. Future standalone lemmas must retain the relevant source restrictions.

The handoff's “sel_data proved” is read literally as an implemented identity definition: `example {n : ℕ} (d : SelectionData n) : sel_data d = d := rfl` elaborates. It is not a proof that arbitrary scalar data satisfy the standing assumptions. B01 contains no new public theorem, so there is no omitted theorem proof to audit.

## Independent verification

All completed Lean commands below were serial, with `LEAN_NUM_THREADS=1` and `nice -n 5`. The waiting compile-gate request was paused while direct probes/kernel replay/lint ran, to prevent overlapping checks. No clean, update, cache fetch, heartbeat override, or generated-root rewrite was used.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11b-b01 KAM.Planetary.WeakKAM.Data
   ```

   Exit 0. Exact output:

   ```text
   [inp-gate] slot 2 acquired 15:03:26 for KAM.Planetary.WeakKAM.Data
   Build completed successfully (9079 jobs).
   ```

   This is the targeted overlay build, not a library rebuild from scratch. No warnings or errors were emitted.

2. Axiom and identity probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B01Audit.lean
   ```

   Exit 0. For each of `SelectionR`, `SelectionC`, `SelectionPhaseC`, `SelectionPoint`, `selectionReal`, `selectionRe`, `selectionLength`, `selectionThick`, `selectionDomain`, `selectionScalar`, `selectionDG`, `selectionDGVector`, `SelectionData`, `SelectionPerturbation`, `sel_data`, exact output was:

   ```text
   'KAM.Planetary.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   The identity example above and `example : type_of% @sel_data := fun {n} d => d` elaborated. The latter produced only an unused-binder warning in the probe. An earlier probe attempt incorrectly attached `(n := n)` to `type_of% @sel_data` and exited 1 with `Invalid argument name n for function`; the corrected probe passed. This was a scratch syntax error, not a package failure. Scratch is removed at closeout.

3. Kernel replay, one invocation for the only package module (no provider or lemma module exists):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.Data
   replaying KAM.Planetary.WeakKAM.Data
   ```

   Exit 0.

4. Lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1, solely for the explicitly permitted generated-root exception. Exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (766 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   This independent result differs from the handoff's claimed lint exit 0; the permitted exception explains exit 1. The root was not regenerated. An initial lint invocation was terminated before its ABI Lean subprocess, then rerun with the explicit thread/nice settings above; that partial run is not counted as completed validation.

5. Hygiene and frozen boundary:

   - `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, empty output.
   - `git diff --check inp...HEAD`: exit 0, empty output.
   - Source has copyright/authors/license, `module`, public imports, module docstring, and exposed public noncomputable section; 116 total lines, below 1500.
   - No forbidden proof escape, resource override, or EuclideanSpace carrier in the module.
   - Declaration-name scan over other KAM sources found no duplicate of any of the 15 names.
   - Recursive project import scan: no provider and no DRAFT_SORRY frozen theorem. All 12 reachable frozen definition modules are SEALED in the manifest: ActionNbhd, ComplexStrip, FrequencyMap, HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, RealHamiltonian, SymplecticForm, Planetary.Phase. No frozen theorem is imported by the project import closure.

Snapshot SHA256:

```text
d7b17ec35cca4caa4c2884d2e6d2670a52074c7b1c45c752b1e60382ef1ef381  KAM/Planetary/WeakKAM/Data.lean
6800132b3e98b3badc215d5cb1cccc6b016e2f14ec976b661519e436cbf39596  /root/code/KAM-inp/.drafts/design/P11BSignatures.lean
8b3fd811a8c13414699fb79dc55e7b1b74e90cebf697f89e76a053ecb52c0bdd  docs/tracks/P/design/P11B-LEAN-DESIGN.md
```

## Blueprint/source defects, deviations and remaining obligations

No suspected pinned-source erratum or new blueprint contradiction found in scope. Relevant checked text is p11a3 lines 30–41 (“Data of the selection theorem”), p11a1 lines 17–26 (dimensions, Euclidean thickening, diagonal/operator tensors), and p11a2 lines 23–27 (domains and norms). The implementation preserves these conventions and distinguishes max norm from explicit Euclidean lengths.

The earlier design findings F1 (extension-prefix premise) and F2 (fixed-key uniformity) concern later packages and are resolved at design level by design audit 2; neither is implemented or discharged by B01. Its inherited N1 bridges and later release gates remain open outside this audit. No claim of an iteration, selection theorem, physical transport, or frozen proof closure follows from this data package.

Only this report is a repository deliverable; temporary files belong under `.lake/abi-scratch/` and are removed. No source, frozen file, manifest, generated file, handoff or git state was changed.
