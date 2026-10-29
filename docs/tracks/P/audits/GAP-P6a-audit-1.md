# GAP-P6a independent audit 1

**Verdict: PASS WITH NOTES for the package; PASS for all eight assigned graph nodes.**
No frozen theorem anchor is provided or sealed by this package. “Seal-ready” is therefore
not applicable. The eight unsigned graph exports establish their assigned conclusions.
The notes are the permitted stale generated root, inherited build warnings, and the
source's already-recorded arbitrary-real-ε bridge. No blocking finding was found.

## Scope, authorization, and frozen inputs

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-gp6a`.
Report-only, focused tier-2 audit; no code repairs, graph edits, commits, or root regeneration.
The user's explicit absolute report path overrides the generic brief's main-worktree destination.
The handoff's AUDIT FOCUS narrows implementation review to
`KAM/Planetary/Newtonian/HamiltonNodes.lean`.

Snapshot v1:

- HEAD: `fa91c8ee9f9f8cfbd1af677f2bbbc7902f99ce38`.
- `inp`: `3c67c4e953df9ee8aa6e50f89bf935f63764fe3e`.
- `git diff inp...HEAD`: one new file, 544 insertions, no other changes.
- HamiltonNodes SHA256:
  `0dcefa522bdce89adfbb3244960c355a34bb334f5bcac2ae2cbe27b971310693`.
- `docs/graph/P/DEPGRAPH.md` SHA256:
  `8fc6c0139d2d39fa7f4d137189dad1c8689fa1e9a51a56a5ded64d5612a34525`.
- `blueprint-P/parts/p6-newtonian-models.tex` SHA256:
  `b6885887ba6dfd181e79925cb4584b4b5590d0debc3bc205a2c49aa86b634899`.
- Handoff SHA256:
  `354579809d70e04b4a8cb296c2afb5c7347b84f9231e3c0d65634e81b12279da`.

Read: AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, handoff,
GAP-PLAN-P.md lines 467–478, track P statement conventions, every assigned NODE's
SOURCE_HYPOTHESES / SOURCE_QUANTIFIERS / SOURCE_CONCLUSION, and all cited blueprint
lines. Read the frozen phase, body-vector, collision, moving/fixed Hamiltonian, and
Hamiltonian-vector-field definitions, plus the landed definitions and lemmas used here.
The full three-dot source diff and every new proof were inspected.

All source locators below refer to this snapshot. Lean names are in `KAM.Planetary`.
No SIGNED declaration or signature-file obligation belongs to this unsigned slice;
provider/frozen-type equality and trial seal-body probes are not applicable.

## Per-node source-correspondence ledger

| Graph node; DEPGRAPH lines; blueprint lines | Lean declarations; HamiltonNodes lines | Verdict | Source hypotheses, quantifiers, and conclusion |
|---|---|---|---|
| `bpP:p6:hamilton-eqs`; 11465–11479; 82–100 | `hamilton_eqs_moving` 112, `hamilton_eqs_fixed` 130; `movingField_blocks` 36, `fixedField_blocks` 54 | PASS | Both position and momentum block formulas on all collision-free phase points, followed by the pointwise curve iff. Data precede phase point / curve / time / body index. Arbitrary real μ and ε strengthen the default nonnegative scope. |
| `stepP:p6:he-dir`; 11501–11517; 94–97 | `fderiv_movingHamiltonian_dir` 407, `fderiv_fixedHamiltonian_dir` 435 | PASS | For every collision-free z and every phase direction d, the kinetic restriction, literal i<j potential pair sum, and DH=DV+DT. No derivative formula is assumed. DT and DV are represented by DH on (0,δp) and (δq,0); the proved shape split identifies these with the source's T and V derivatives. |
| `stepP:p6:he-coef`; 11532–11546; 98 | `fderiv_movingHamiltonian_partials` 150, `fderiv_fixedHamiltonian_partials` 167; block exports 36, 54 | PASS | At arbitrary z∈W and Cartesian index (i,c), both partials have the required coefficients and signs. The block exports give the stated consequence for X_H. Partial order p then q in a conjunction changes neither quantification nor conclusion. |
| `stepP:p6:he-curve`; 11592–11606; 100 | `hasDerivAt_iff_bodyVector` 75, `hasDerivAt_movingField_iff` 89, `hasDerivAt_fixedField_iff` 101 | PASS | Genuine iff, both directions. An ambient real curve and one collision-free evaluation point suffice; restricting the theorem to t∈J and curves lying in W recovers the source. Source curve-before-time order retained; no openness or connectedness premise on J is added. |
| `stepP:p6:rc-coords`; 11790–11804; 170–171 | `rc_coords_moving` 187 | PASS | Exactly R1/R2 over arbitrary J are taken as input; then t∈J, all body indices, and all scalar coefficient arrays w. Position and momentum derivatives a_i,b_i and their weighted sums are proved. Mass / G positivity and μ≥0 are unnecessary and omitted, a strengthening. |
| `bpP:p6:reconstruction-fixed#real-eps`; 12775–12789; 191 with 184 | `fixedField_equations` 212 | PASS | R1/R2 for H_fix imply both q_i′ and p_i′ at every t∈J, for every body and every real ε. There is no ε≥0 premise. All data are universal before the curve hypothesis and time; grouping ε with G,m0 ahead of m only permutes independent universal data, with no changed dependence. |
| `stepP:p6:rf-eq`; 12076–12090; 191 | `fixedField_rf_eq` 225 | PASS | Positivity for all individual and pair lengths; q′, p′, and V′ for every t∈J and every i. Only source mass positivity and R1/R2 are assumed. G positivity and n≥1 are omitted. The conjunction of universal clauses is equivalent to the source's time-indexed conjunction. gKernel and fKernel expand to exactly the displayed force. |
| `stepP:p6:sp-alg`; 11376–11390; 69 | `sp_alg` 509 | PASS | All phase points, including the total-function extension outside W. Literal frozen kinetic expression equals Σ|p_i|²/(2m_i)+(μ/m0)|P|²/2; subtracting those kinetic parts gives potential agreement at ε=μ; full difference equals μ|P|²/(2m0). No positivity or collision premise is required. |

All eight assigned nodes are covered, accounting for all 15 new public theorems.
The additional `he-fix` dependency at DEPGRAPH 11562–11591 / blueprint 99 is also
realized by the fixed-model derivative, partial, and block exports. It is not a ninth
assigned node. No other node is assigned to this module by GAP-P6a's design table.

## Definitions and proof review

There are four new definitions, all private; no public def, abbrev, structure,
instance, or bundled premise is introduced.

| Definition; lines | Classification over its entire carrier |
|---|---|
| `hnPos`; 251–256 | Continuous linear projection to body's two position coordinates; exact on every phase point. |
| `hnMom`; 258–263 | Continuous linear projection to body's two momentum coordinates; exact on every phase point. |
| `hnDot`; 269–270 | Finite sum of coordinate projections weighted by v; exactly w↦planeDot v w, for all v,w. |
| `hnShape`; 297–298 | Genuine common expression H_Kep+c(b|Σp_i|²−pairPotential), using the same total real inverse conventions as the frozen Hamiltonians. No fallback or branch. |

The private definitions are unfolded internally; no public consumer needs their bodies exposed.
The equalities to the moving/fixed Hamiltonians are proved at 300–312. The local
HasFDerivAt construction at 314–352 differentiates sums of genuine quadratic and
inverse-length terms; nonzero position and separation vectors follow from NoCollision.
Thus the public fderiv evaluations are actual derivatives, not uses of fderiv's
nondifferentiable fallback. The fixed velocity cancellation uses only m_i≠0,
derived from source mass positivity.

Refutation pass: checked reversed force signs, index orientation q_j−q_i versus q_i−q_j,
missing pair contributions, possible one-way curve statements, evaluation only at a
special time, illicit ε≥0 restrictions, and dependence on an assumed dependency output.
None survives: explicit derivatives and finite sums have the expected signs and
coefficients; the coordinate iff is proved using both projections and reconstruction
via finProdFinEquiv surjectivity. `fixedField_rf_eq` invokes proved
`reconstruction_fixed` internally for positivity and constructs the derivative clauses;
it does not take reconstruction's conclusion as a hypothesis. The he-coef proof uses
landed Hamilton-field formulas internally, an alternative proof route with the same
literal partial-derivative conclusion. No reused public helper short name or harmful
root shadow was found; all new public declarations are under `KAM.Planetary`.

The project-local transitive import scan found no provider and no frozen theorem
module. Every encountered frozen definition has manifest state SEALED. Direct imports
are Mathlib, Models, Reduction, Reconstruction. The 15 public axiom checks below also
exclude indirect sorry dependence.

## Independent verification

All Lean-bearing commands were run sequentially, with `LEAN_NUM_THREADS=1` and
`nice -n 5`; lint's ABI subprocess inherits both. No library clean, update, cache fetch,
root regeneration, resource-budget override, or package-directory modification was requested.

Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp6a KAM.Planetary.Newtonian.HamiltonNodes
```

Exit 0. Output:

```text
[inp-gate] slot 2 acquired 02:05:23 for KAM.Planetary.Newtonian.HamiltonNodes
⚠ [9087/9098] Replayed KAM.Kepler.Energy
warning: KAM/Kepler/Energy.lean:106:35: Variable name `hm` is not explicitly referenced.
warning: KAM/Kepler/Energy.lean:106:48: Variable name `hκ` is not explicitly referenced.
Build completed successfully (9098 jobs).
```

The unused-variable diagnostic also printed standard rename/removal hints. These
warnings are in an unchanged dependency; no diagnostic was issued in HamiltonNodes.
The job count is Lake's target closure, not a requested clean rebuild.

Axiom probe: `.lake/abi-scratch/GAPP6aAudit1.lean` imported only
`KAM.Planetary.Newtonian.HamiltonNodes` and contained `#print axioms` for every
name below. Command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPP6aAudit1.lean
```

Exit 0. Exact output:

```text
'KAM.Planetary.movingField_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fixedField_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hasDerivAt_iff_bodyVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hasDerivAt_movingField_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hasDerivAt_fixedField_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hamilton_eqs_moving' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hamilton_eqs_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_movingHamiltonian_partials' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_fixedHamiltonian_partials' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rc_coords_moving' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fixedField_equations' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fixedField_rf_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_movingHamiltonian_dir' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_fixedHamiltonian_dir' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sp_alg' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay, one invocation for the sole new module:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Newtonian.HamiltonNodes
```

Exit 0. Exact output:

```text
replaying KAM.Planetary.Newtonian.HamiltonNodes
```

Repository lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the expected generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1197 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

This exception is expressly permitted by the audit brief and handoff; KAM.lean was not edited.

Other mechanical checks:

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
- `git diff --check inp...HEAD`: empty, exit 0.
- Forbidden-token and resource-option search in HamiltonNodes: no matches.
- 544 physical lines, maximum Unicode line width 100; required copyright, module,
  public imports, module docstring, and public section present.
- All 15 public short names were searched against other project Lean declaration
  headers; no duplicate was found. Private helpers have private names.
- Probe removed after use; final report-only change inspection recorded below.

## Source issues, limitations, and disposition

No new suspected pinned-source erratum or implementation deviation was found.
The existing source gap is explicit: blueprint line 20 says
“μ,ε≥0 unless said otherwise”, while line 184 allows “ε∈R” and line 191 invokes
Hamilton equations. DEPGRAPH 12801 records this as SOURCE_GAP and requires preserving
the arbitrary-real-ε contract. This package supplies that extension by a proved
arbitrary-real formula, including negative ε. This resolves the assigned Lean bridge;
it does not edit or silently reinterpret the blueprint or graph status.

The proof route for he-coef reuses landed block formulas rather than repeating the
pair-sum regrouping; the conclusion is still the node's literal one. sp-alg uses
planeSq, equal to planeLength squared, and the explicit frozen kinetic expression.
These are faithful representations, not weakened contracts.

No full headline theorem, external PDF proof, unrelated module implementation, or
campaign graph-status update is certified here. No source-network retrieval was needed:
the assigned literal contracts and cited blueprint text are present in the checkout.
No finding requires a repair before these unsigned exports can be integrated. Root
regeneration remains the orchestrator's permitted merge task.

Closeout: eight of eight assigned nodes and fifteen of fifteen public theorems checked;
all four definitions classified; build, axiom probe, kernel replay, protected-path
comparison and source hygiene completed. The report is the only repository edit made
by this audit; the pre-existing untracked handoff is preserved.
