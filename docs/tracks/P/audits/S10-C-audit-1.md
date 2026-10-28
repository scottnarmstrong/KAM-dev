# Independent S10-C package audit 1

Overall verdict: **PASS WITH NOTES** for S10-C's finite-type/index/CP09 infrastructure. No blocking mathematical or implementation defect found. All five main exports pass their exact design contracts. **Frozen anchors: none supplied or proved by this package; seal readiness is not applicable.** This report does not certify P-G, P-PLANAR, P-FIXED, the planetary R-nondegeneracy construction, stability, or later consumers as closed.

Audited HEAD: `45970cd33524133a103ef3d72997a8fdd97b5031`, worktree `/root/code/KAM-inp-s10c`, 2026-10-28. Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, S10-C handoff/AUDIT FOCUS, P810 design and both design audits, Part 10's finite-type/index/CP09 text and proof plan, track-P statement, the relevant frozen theorem interfaces and imported frozen definitions. Production review is restricted to `KAM/Planetary/Nondegeneracy/FiniteType.lean` (450 lines), as specifically directed.

## Scope and nonblocking notes

1. The requested `git diff inp...HEAD` was inspected. Git warns `multiple merge bases, using 9cdbdacf00986d1fe22a572b8fdbafdffe224355`. At audit time `inp` is `05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2`. That diff includes inherited unrelated packages and four added imports in generated `KAM.lean`; therefore the broad protected-path command is **not empty**. No frozen/manifest/README difference appears. These root edits are absent from both `git diff inp-s10j...HEAD -- KAM/Frozen manifest KAM.lean README.md` and `git diff cda8ceb..HEAD -- KAM/Frozen manifest KAM.lean README.md`. The actual S10-C commit range `cda8ceb..HEAD` changes only FiniteType.lean. Do not attribute the broad inherited root delta to S10-C.
2. Comparison against `inp-s10j` (`68fff7a9ed132b8a319c134f4d00116ee8f0a9a2`) also includes S10-Z's AnalyticZeros and its reports. Those inherited proofs are not re-audited here; their uses were inspected and their dependencies checked.
3. `.drafts/design/P810Signatures.lean` is absent in this worktree. The retained P810 design Appendix A contains the signatures; both design audits identify that appendix as the signature source. A whitespace-normalized comparison finds **MATCH** for all ten assigned definitions/signatures. Full definition bodies were checked, including betaFamily and betaMu. Five additional Lean probes copy the Appendix A theorem signatures verbatim and apply the implementation exports.
4. `finite_type` keeps unused `hB`; `index_amount` keeps unused `hC`, `hK`, `hCont`, exactly as in the design. Their proofs establish stronger facts without these inputs; no premise was added. `h` in `index_amount` is the designed guard for a defined least index, supplied by finite_type in analytic applications, not a substitute proof of finite type.
5. The proof bypasses `f_pol`: `HasFPowerSeriesOnBall.factorial_smul` identifies the diagonal coefficients directly. This is a valid proof-plan variation, not an unpaid polarization assumption. The handoff's prose “Imports: DiagonalTensor, AnalyticZeros only” omits the literal additional `public import Mathlib` at line 8; this harmless inventory omission does not affect quarantine or axioms.

## Declaration-by-declaration assessment

Names below are in `KAM.Planetary.Nondegeneracy`. Nodes refer to `bpP:p10:*` / `stepP:p10:*`; helper rows describe their role rather than claiming a separate published blueprint node. Every new public declaration is included.

| Node / role | Lean declaration | Verdict | Reason / note |
|---|---|---|---|
| `index-def` | `betaFamily` | PASS | Literal infimum; nonnegative bounded-below image; attained under the design guards. |
| `index-def` | `sphere` | PASS | Euclidean length2=1, not ambient Pi norm=1. |
| `cp09-lemma1` | `squaredForm` | PASS | Literal square of the scalar dot product. |
| `index-def` | `betaMu` | PASS | Exact squared-family specialization. |
| `index-def` | `index_def` | PASS | Nat.find of positive-order/positive-amount existence; no fallback. |
| `ft-cover helper` | `scalarJet_nonneg` | PASS | Absolute values and nonnegative real supremum. |
| `ft-cover helper` | `norm_le_one_of_length2` | PASS | Correct Euclidean-to-Pi comparison, including vacuous dimension zero. |
| `ft-cover helper` | `jetOp` | PASS | Diagonal sphere supremum of the actual continuous multilinear tensor. |
| `ft-cover helper` | `abs_diag_le` | PASS | Multilinear operator bound and unit-vector Pi norm at most one. |
| `ft-cover helper` | `bddAbove_jetOp` | PASS | Explicit operator-norm upper bound. |
| `ft-cover helper` | `jetOp_nonneg` | PASS | Nonnegative supremum, including empty sphere. |
| `ft-cover helper` | `jetOp_le_add` | PASS | Triangle inequality and bounded supremum. |
| `ft-cover helper` | `jetOp_lipschitz` | PASS | One-Lipschitz in tensor operator norm; no norm substitution in the amount. |
| `ft-cover` | `scalarJet_continuousOn` | PASS | Zero-order evaluation norm; positive-order composition with jetOp. |
| `ft-cover helper` | `jetMax_zero` | PASS | Singleton order set. |
| `ft-cover helper` | `jetMax_succ` | PASS | Finite bounded image and insertion/max identity. |
| `ft-min helper` | `jetMax_nonneg` | PASS | Nonnegative scalar jets. |
| `ft-cover helper` | `scalarJet_le_jetMax` | PASS | Valid bounded finite supremum inclusion. |
| `ft-cover` | `jetMax_mono` | PASS | Successor max gives monotonicity. |
| `ft-cover` | `jetMax_continuousOn` | PASS | Finite recursion of continuous maxima. |
| `index-def helper` | `betaFamily_nonneg` | PASS | Every jet maximum is nonnegative. |
| `ft-min helper` | `betaFamily_le` | PASS | Infimum bounded below by zero; product membership explicit. |
| `index-def` | `betaFamily_mono` | PASS | Nonempty product and monotone jets; no regularity premise needed. |
| `ft-min` | `betaFamily_attained` | PASS | Actual minimum by compactness, nonemptiness and continuity. |
| `index-def` | `index_amount` | PASS | Exact design signature; Nat.find minimality and monotonicity. Regularity inputs unused. |
| `ft-pt` | `eventuallyEq_zero_of_scalarJet` | PASS | Normalize arbitrary directions; factorial derivative/power-series identity kills every diagonal coefficient. |
| `ft-pt` | `exists_scalarJet_pos` | PASS | Analytic identity theorem on connected B contradicts the supplied nonzero value. |
| `finite-type / ft-pt / ft-cover / ft-min` | `finite_type` | PASS | Exact design signature; finite relative-open cover, maximum order plus one, attained positive infimum. |
| `cp09-lemma1 helper` | `analyticAt_fsum` | PASS | Finite analytic sum; no extra source assumption. |
| `cp09-lemma1 helper` | `analyticAt_fprod` | PASS | Finite analytic product, including empty product. |
| `cp09-lemma1 helper` | `expansion` | PASS | Conditional finite expansion helper, used only after proving the algebraic expansion; joint derivative continuity proved. |
| `cp09-lemma1 helper` | `continuous_length2` | PASS | Continuity of square root of sum of squares. |
| `cp09-lemma1 helper` | `isCompact_sphere` | PASS | Closed and Pi bounded in finite dimension. |
| `cp09-lemma1 helper` | `sphere_nonempty` | PASS | Coordinate unit vector; requires positive output dimension. |
| `cp09-lemma1 helper` | `ne_zero_of_mem_sphere` | PASS | Euclidean unit vectors cannot vanish. |
| `cp09-lemma1 helper` | `analytic_coord` | PASS | Actual coordinate projection of an analytic map. |
| `cp09-lemma1` | `cp09_lemma1` | PASS | Exact design signature; squared finite expansion and R-nondegeneracy. |
| `cp09-lemma1` | `cp09_unsquared` | PASS | Exact design signature; linear expansion and the same R-nondegeneracy. |
| `cp09-lemma1` | `cp09_product` | PASS | Exact design signature; compact product spheres and generic common nonzero point. r=0 gives one. |

## Definition classification and proof scrutiny

All six new definitions are intended mathematical objects, without theorem-shaped fields or alternate implementations. `betaFamily` is the literal real sInf of the jet-maximum image of C0 × K; `sphere` uses Euclidean length2; `squaredForm` is the literal squared pairing; `betaMu` is exactly the sphere specialization; `index_def` is guarded Nat.find; `jetOp` is the actual tensor diagonal supremum. No new abbrev, structure, or global instance occurs.

On arbitrary noncompact or empty input, a real sInf need not be an attained minimum (the empty real infimum has its library total value). The code does not advertise or use such a minimum without its guards: `betaFamily_attained` at lines 164–173 proves attainment on the compact nonempty product under continuity, and `finite_type` uses it at lines 306–307. The nonnegative range is always bounded below. The general order-theoretic helpers remain valid on their stated domains; monotonicity explicitly assumes nonemptiness. For every order the relevant jets are continuous under `hCont`, so attainment also holds at `index_def` under the index_amount hypotheses by specializing betaFamily_attained. No fallback is used to obtain positivity.

The dimension-zero input sphere for positive-order jets is empty, giving jetOp zero as intended for the zero-dimensional multilinear tensor; order zero remains |g|. Positive output dimensions are guarded by `hm` in CP09. For the product variant, each output dimension is positive and r=0 is harmless: the parameter product is inhabited and the scalar product is identically one on nonempty B.

The pointwise proof (lines 195–268) uses actual derivatives and analytic power-series coefficients: all unit diagonal derivatives zero implies all diagonal derivatives zero by scaling; the zero direction follows by positive-order multilinearity; nonzero factorials force every power-series diagonal term zero. Local vanishing propagates by the analytic identity theorem on connected B. This supplies the pointwise cover without assuming the desired lower bound.

The compactness proof (lines 270–307) uses ambient open representatives of relatively open positivity sets on C0 × K. A finite subcover yields a single positive order (finite supremum plus one), monotonicity preserves positivity, and an attained minimum supplies a uniform positive amount. The constants/orders depend only on the data bound before the existential. Norm comparison is only used to bound jets in the ambient Pi operator norm; the amount remains the literal Euclidean diagonal norm.

For CP09, `expansion` proves both analyticity and joint continuity of the actual iterated derivatives. Squared, unsquared and product expansions are algebraically proved at their call sites. The product proof uses `generic` to obtain a single common point of nonvanishing for all factors, rather than multiplying unrelated point witnesses. No extra premise or instance hides a hard step.

## Independent validation

All auditor-controlled Lean/Lake commands were serialized and used `LEAN_NUM_THREADS=1`, `nice -n 5`. No resource overrides were introduced. Commands ran from `/root/code/KAM-inp-s10c`.

### Targeted build

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s10c KAM.Planetary.Nondegeneracy.FiniteType
```

Exit **0**. Relevant output:

```text
[inp-gate] slot 2 acquired 10:31:00 for KAM.Planetary.Nondegeneracy.FiniteType
Build completed successfully (9113 jobs).
```

Only replayed unused-variable warnings in inherited `KAM.Kepler.Energy`, `KAM.Planetary.Poincare.Chart`, `KAM.Kepler.Mass`; no FiniteType warning. The job count is Lake's dependency accounting, not 9113 concurrently launched Lean processes.

### Exact signatures and axioms

The five Appendix A theorem signature probes use fresh names `audit_finite_type`, `audit_index_amount`, `audit_cp09_lemma1`, `audit_cp09_unsquared`, `audit_cp09_product`, with bodies applying the corresponding exports to the explicit binders in order. No frozen-provider type equality/seal-body probe applies: this package has no provider or anchor.

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S10CSignatures.lean
```

Exit **0**, no output. All five exact copied design signatures elaborate at default resource settings.

The second scratch file contains `#print axioms KAM.Planetary.Nondegeneracy.<name>` for every one of the 33 new public lemmas/theorems:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S10CAudit.lean
```

Exit **0**. Exact output:

```text
'KAM.Planetary.Nondegeneracy.scalarJet_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.norm_le_one_of_length2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.abs_diag_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.bddAbove_jetOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.jetOp_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.jetOp_le_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.jetOp_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.scalarJet_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.jetMax_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.jetMax_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.jetMax_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.scalarJet_le_jetMax' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.jetMax_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.jetMax_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.betaFamily_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.betaFamily_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.betaFamily_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.betaFamily_attained' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.index_amount' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.eventuallyEq_zero_of_scalarJet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.exists_scalarJet_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.finite_type' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.analyticAt_fsum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.analyticAt_fprod' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.continuous_length2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.isCompact_sphere' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.sphere_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.ne_zero_of_mem_sphere' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.analytic_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.cp09_lemma1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.cp09_unsquared' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.cp09_product' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Nondegeneracy.FiniteType
```

Exit **0**. Exact output:

```text
replaying KAM.Planetary.Nondegeneracy.FiniteType
```

One invocation replays the sole module owned by S10-C. The inherited DiagonalTensor/AnalyticZeros modules were not added as separate audit targets.

### Source lint, imports and protected files

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely for the brief-permitted stale generated root. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (527 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

All other lint checks pass. The generated root was not regenerated.

The source has copyright/author/license header, `module`, three public imports, module docstring, exposed public noncomputable section, and the required Pi carriers. All 450 lines satisfy the 1500-line cap; no forbidden tokens or set_option occur. The package's transitive local import traversal covers 67 KAM modules and finds **no provider or frozen theorem import**; imported frozen definitions do not contain proof placeholders. Thus no DRAFT_SORRY theorem or provider is imported, directly or indirectly.

```sh
git diff --check inp-s10j...HEAD -- KAM/Planetary/Nondegeneracy/FiniteType.lean
git diff cda8ceb..HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff inp-s10j...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

All exit **0**, no output. The broader inp comparison's inherited KAM.lean delta is disclosed above. No production file was edited. Both audit scratch probes were removed after use. The pre-existing untracked S10-C-handoff.md was preserved.

## Source/blueprint defects, deviations, uncertainties

No new suspected mathematical source or blueprint defect was found in the audited contracts. Part 10 lines 199–220 supply the finite-type, minimum, least-positive-index and all three CP09-family statements; the implementation preserves the squared convention, dimensions, compactness, nonemptiness and dependencies. The power-series route and unused premises are the proof-plan variations described above. No pinned-source repair, frozen statement change or errata-ledger edit is requested. This audit checks the local blueprint/design contracts and does not claim a new independent review of the original CP09/Rus01 PDFs or unrelated inherited packages.

The missing standalone draft and inherited root diff are provenance limitations, not silently repaired inputs. The current report is written at the user's exact worktree path, overriding the generic brief's main-worktree output instruction.
