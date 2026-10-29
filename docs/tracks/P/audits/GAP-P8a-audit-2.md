# GAP-P8a independent audit 2

**Overall verdict: PASS WITH NOTES. All nine unsigned node exports PASS.** The statement-completeness failures F1–F3 in audit 1 are repaired at the audited HEAD. The targeted build, kernel replay and all nine axiom probes pass. Lint exits 1 solely for the expressly permitted stale generated root. No frozen anchor is a target of this package, so this is package/node certification, not an anchor seal or campaign theorem closure.

Audited worktree: `/root/code/KAM-inp-gp8a`. Date: 2026-10-29 UTC.

- HEAD: `d45b25b28d382716cdcf15c9653b6bb82083eb8d`.
- Comparison ref `inp`: `5d2c928069e3d3bcea1f688373decd8fda061515`.
- Selected three-dot merge base: `537fc2a837002555fbe2766678b1c8454274228f`.
- Repair commits: `06980833` (F1–F3), `d45b25b2` (private-helper lint cleanup).
- Sole audited implementation: `KAM/Planetary/SecularForm/ModelTransferNodes.lean`, 748 lines.

## Authority and scope

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, GAP-P8a-handoff.md including AUDIT FOCUS, audit 1, GAP-PLAN-P.md's GAP-P8a section, the relevant P810 design node table/conventions/departures, track P statement P7 item 4, and all nine NODE records' SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS and SOURCE_CONCLUSION with their cited blueprint statements/proofs. The blueprint is `blueprint-P/parts/p8-secular-form.tex`.

Compared `git diff inp...HEAD`. The live inp ref advanced during the audit (final observed value `d6fa120cc475a689316bdbf716406c2fcc856747`); the final repeat warned about multiple merge bases and selected the same base pinned above. A byte-for-byte comparison confirmed the initial pinned-ref diff, final live-ref diff, and explicit base-to-HEAD diff are identical (SHA256 `c3b333b0fda19fe677d584e4d4a1bcb63d0793df35e9c313861669a8911fca4f`). Its four-file inventory is AnalyticNodes.lean (+435), ModelTransferNodes.lean (+748), audit-1.md (+159), handoff.md (+46). Read the entire audited implementation and its proofs. AnalyticNodes is an imported dependency expressly excluded from this audit; its independent source fidelity is not certified here. No other implementation is independently re-audited. The user's exact worktree report path controls over the generic brief's main-worktree wording.

There are no SIGNED declarations, providers, or frozen theorem targets in this slice. Signature-file/provider-type equality and proposed seal-body probes are therefore not applicable. Relevant frozen definitions inspected include assemble, secularAverage, HasSecularBirkhoffForm, hamiltonianVectorField, movingHamiltonian, fixedHamiltonian and secularEccVector. The recursive KAM import closure has 160 modules, no provider and no frozen theorem; every imported frozen module is a manifest-SEALED definition. No DRAFT_SORRY import is used.

## Per-node verdicts

All declaration names below are in `KAM.Planetary.SecularForm`. Implementation locators are in ModelTransferNodes.lean; graph locators are in docs/graph/P/DEPGRAPH.md.

| Node | Declaration / line | Verdict | Literal source comparison |
|---|---|---|---|
| `stepP:p8:id-diff` | `identification_diff`, 35 | PASS | Graph 15942; blueprint 191. Pointwise squared-total-momentum difference, continuity of individual own-angle momenta, their assembly identity and continuity of the difference. Dependency outputs built internally. |
| `stepP:p8:id-avg` | `identification_avg`, 67 | PASS | Graph 15972; blueprint 192. Correct radian average and both delta formulas, with kappa=G*m0. Physical/chart premises only. |
| `stepP:p8:id-int` | `identification_int`, 95 | PASS | Graph 16001; blueprint 193. Integrability iff on slowDom, subtraction guarded by actual integrability, both integrable on an internally obtained positive real polydisc. |
| `bpP:p8:identification` | `identification_full`, 167 | PASS | Graph 15910; blueprint 182–189. Includes the previously missing pointwise difference at 177–179, continuity, average, integrability iff, guarded secular identity and unconditional local averaged-Hamiltonian identities for all couplings. |
| `bpP:p8:same-jets#jets` | `same_jets_jets`, 537 | PASS | Graph 16059; blueprint 197–201, 206. All positive-order slow tensors and all action derivatives; common quadratic form, uniform quartic remainder and analytic remainder; now explicit Hamiltonian vector-field equations, zero action components and mu-scaled fast-frequency difference at 556–581. |
| `bpP:p8:same-jets#transfer` | `same_jets_transfer_full`, 589 | PASS | Graph 16091; blueprint 202, 206. Exact frozen HasSecularBirkhoffForm iff with P0-delta and unchanged Omega/beta; whole oscillator-disc containment is sourced; composition for any action-preserving map into the real polydisc strengthens the symplectic case. |
| `bpP:p8:same-jets` | `same_jets_full`, 433 | PASS | Graph 16030; blueprint 196–204. Bundles all-order jets, common quadratic remainder, transfer, composition and the explicit averaged-Hamiltonian dynamics at one common radius. Both named subexports are projections of this bundle. |
| `stepP:p8:q4-c` | `quartic_c_node`, 607 | PASS | Graph 16247; blueprint 234. Both diagonal coefficients equal G*m_i*m_j*radialR1/(2*Lambda^2) on positive separated actions. Specializes to source units G=m0=1; does not assert agreement with the unrepaired printed CP11 coefficient. |
| `bpP:p8:quartic` | `quartic_full`, 683 | PASS | Graph 16121; blueprint 216–229. Joint six analytic pair coefficients, actual fixed/moving fourth jets, exact radial diagonals, physical pair scaling, separated-domain analyticity and sufficient subdomain. Now includes the actual centered dimensionlessPair expansion and its conversion for the same coefficient family (700–716), plus every Taylor tensor's analyticity on all alpha in (0,1) (731–732). |

## Refutation checks and repair assessment

**F3 closed:** identification_full now literally includes the formula `f_mov-f_fix=(2*m0)^(-1)*planeSq(sum momentum)` in its conclusion, not merely in an adjacent export or docstring. Its proof constructs this from perturbation_diff. Average subtraction remains correctly guarded outside the collision-free analytic neighbourhood.

**F2 closed:** same_jets_full and same_jets_jets now state the frozen hamiltonianVectorField components of the actual averaged physical Hamiltonians: xi-dot=mu*partial_eta S, eta-dot=-mu*partial_xi S, Lambda-dot=0 in both models, equal slow components, and lambda-dot_moving=lambda-dot_fixed+mu*partial_Lambda delta. These claims hold for arbitrary fast angles and all real mu, with the same coupling in both models. This is the requested secular-equation statement; no ODE existence claim is being substituted for it.

The Hm/Hf equality binders (462–467, 557–562) only name the displayed, fully specified averaged Hamiltonians; the z equality names the assembled phase point. They do not assume a dependency's output or a dynamical conclusion. All can be discharged by reflexivity after substitution. An independent Lean probe instantiated the Hamiltonian aliases with the literal functions using `hD (1 : ℝ) _ _ rfl rfl`; it succeeded. The private dynamics proof obtains integrability, differentiability and averaged-H identities internally, transfers local identities through the continuous phase projection, then applies the frozen vector-field definition. The derivative signs and Fin.castAdd/Fin.natAdd blocks agree with assemble's `(phi,q;I,p)` order.

**F1 closed:** quartic_full existentially supplies A,A',B,cW for the actual `dimensionlessPair` at the physical axis ratio. Its expansion explicitly subtracts W(0), avoiding the previous unsourced W(0)=0 restriction. Its next conjunct equates the canonical pair polynomial of the same existential `c` used in both total fourth jets to the corrected W4 expression with the physical prefactor and all A,A',B corrections. The proof selects `c=quarticCoeff` and obtains the expansion/conversion from quartic_pair_chart_conversion, without asking the caller for any expansion premise. The old generic arbitrary-W implication is gone.

The final clause states analyticity of the complete order-k slow derivative tensor at v=0, for every k, on the whole interval alpha in (0,1). This gives all Taylor coefficients (factorials and coordinate evaluations are fixed linear operations). The private taylor_analytic_alpha proof differentiates the jointly analytic function on the open separated domain, restricts the slow slots by a fixed continuous linear inclusion, and restricts alpha to the circular slice. No uniform convergence radius as alpha approaches 1 is claimed.

The exact eccentricity carrier in pair scaling is poincareV, whose body at `([0,u0],[Lambda,u1])` is `sqrt((1-planeSq(u)/(4*Lambda))/Lambda) • u`; for positive Lambda this is the source's `sqrt(1-planeSq(u)/(4*Lambda))*u/sqrt(Lambda)`. This is the original Poincare object, not a replacement chart. Unfolding radialR1 gives the diagonal formula (b) as well as (c), including the correct factors 32, 8 and 2. The all-order tensor representation and common `coeffs` are the design's representation of multi-index jets and the common quadratic matrix; its spectrum, hence sigma and Omega=2*sigma, is consequently shared. No separate model-specific spectrum is introduced.

## Hypotheses, definitions, quantifiers and completeness

- Data contains only positive G,m0,m and n>0. Physical and chart premises are retained; none of the nine public theorems assumes a proved analytic, averaging, jet or conversion output. Local private helpers may take those inputs, and their callers discharge them internally.
- The new definition is **private phaseSlow**, 261–272: a continuous linear coordinate projection `(phi,q;I,p) -> (q,I,p)` on its entire phase carrier. Its application and assembly identities are proved at 274–281. It has no fallback, restricted-domain branch or conclusion-bearing field. No new public def/abbrev/structure/instance is introduced. Local F,W,iota in taylor_analytic_alpha are literal regrouping, inverse-image domain and linear-inclusion objects.
- The real polydisc is open. The proofs construct positive radii by minima before choosing points, derivative orders, mu, V,r0,mu0,P0,Omega,beta or chi. Constants depend only on the standing physical data/base axes. The one common same-jets radius serves both models and all bundled clauses; its projections retain that choice. No point-dependent radius or widened constant dependence was found.
- The P810 design expressly uses existential radii (347), full slow tensors (349), and a uniform max-norm quartic bound (348). Shrinking preserves positivity and the source local claim. Radian normalization and the frozen `(I,phi,p,q)=(Lambda,lambda,eta,xi)` dictionary are preserved. The G factor in q4-c and dropping unused symplecticity in composition are valid strengthenings.
- GAP-PLAN-P maps exactly nine nodes to this file: all nine appear above and have their assigned conclusions. The older P810 table's identification/same-jets/quartic proof cuts are covered by these exports and imported landed results. There is no additional handoff list of skipped already-closed nodes. The related quartic cuts q4-str (graph 16154), q4-a (16186), q4-b (16218) are each explicitly PROVED, with LEAN_REF to the landed structure/scaling/pair-conversion/diagonal results. AMENDMENTS.md supplies no conflicting P8 amendment. No unsupported BYPASSED claim was needed.
- The nine target records themselves still say NOT_STARTED in this checkout. This audit does not change graph state or certify closure of the separately audited AnalyticNodes dependency.

## Independent checks

Every Lean/Lake/kernel invocation below ran sequentially, with LEAN_NUM_THREADS=1. No separate Lean operation overlapped lint's internal ABI probe. The build gate itself invokes `nice -n 5 lake build`. No clean/update/cache-get command or package-directory mutation was run.

### Targeted build

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp8a KAM.Planetary.SecularForm.ModelTransferNodes
```

Exit **0**. Exact gate/final lines:

```text
[inp-gate] slot 2 acquired 02:23:26 for KAM.Planetary.SecularForm.ModelTransferNodes
Build completed successfully (9206 jobs).
```

Lake replayed inherited dependency warnings. No diagnostic was attributed to ModelTransferNodes.lean. The job count includes dependency replays against the existing build overlay; no from-scratch library rebuild was requested.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.ModelTransferNodes
```

Exit **0**, complete output:

```text
replaying KAM.Planetary.SecularForm.ModelTransferNodes
```

### Axioms and alias-premise probe

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/maud-gp8a-2-probe.lean
```

Exit **0** on the first run. Imported ModelTransferNodes and ran #print axioms for every new public theorem, then the alias-instantiation example described above. Complete output:

```text
'KAM.Planetary.SecularForm.identification_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.identification_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.identification_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.identification_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.same_jets_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.same_jets_jets' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.same_jets_transfer_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.quartic_c_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.quartic_full' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The alias example adds no output and uses no resource overrides. Only the three allowed axioms occur; no sorryAx or frozen theorem axiom occurs.

### Lint and protected paths

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1196 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The sole failure is expressly allowed generated-root staleness; regeneration belongs to the orchestrator. No other lint failure was suppressed or excused.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both initially exited **0**, empty output. At final validation both again exited **0**, with only the git diagnostic `warning: inp...HEAD: multiple merge bases, using 537fc2a837002555fbe2766678b1c8454274228f`; no protected-path diff or whitespace defect appeared. The identical-diff check above resolves the moving-ref ambiguity. Independent static inspection: 748 lines, maximum width 100 Unicode characters; copyright, module, public imports, module docstring and public noncomputable section present. No forbidden proof escape, EuclideanSpace or option override. A scan of KAM declarations found no other occurrence of any of the nine new public short names. All public names are inside KAM.Planetary.SecularForm, with no harmful root shadow. The recursive import scan found no providers and only SEALED frozen definitions, as checked against manifest/frozen-anchors.json.

## Notes, errata and limits

The handoff still names 783cc445 and approximately 470 lines. Its deviation 3 says vector-field equations are not stated, which is stale after the repair commits: they are now stated explicitly in both exports. Treat this report's pinned HEAD and locators as the current audit receipt. Audit 1 remains an accurate historical FAIL for its own earlier HEAD; its four node failures do not persist here.

No new suspected defect in a pinned source or frozen declaration was discovered. The known CP11 (B.6) issue is already recorded in blueprint p8, remark at 237–238: “the printed ... alpha^4 ... must be ... alpha^3”. Its stated reason is the spurious odd alpha^9 contribution and the independent integral/numerical comparison. This audit neither rederives that external certificate nor asserts the unrepaired formula. The package uses the exact radial derivative definition. Explicit mixed c3–c6 values remain the source's Part 11b forward obligation.

The literal source representation choices above are documented; no new weakening, source hypothesis, normalizer substitution or unpaid dependency premise was found. PASS is limited to this unsigned node slice, with the stated imported-dependency boundary; no claim of P-G/P-PLANAR/P-FIXED sealing follows.

Only this report was written in the repository. Scratch probe/log files were removed after recording their output. No implementation, frozen file, manifest, graph, generated root or README was edited; no git state-changing command or commit was run.
