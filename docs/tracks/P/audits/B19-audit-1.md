# B19 independent package audit

Overall verdict: **PASS WITH NOTES** for the B19 `evaluation_bilipschitz` infrastructure slice. All signed declarations and all assigned graph steps pass. No frozen theorem is sealed by this package. The notes are the permitted stale generated root and inherited protected-path comparison noise, not missing evaluation mathematics.

Audited 2026-10-29 in `/root/code/KAM-inp-p11b-b19`, HEAD `bd587502d193103a0ad6239cb442a76b003487ae`. Scope is ONLY `KAM/Planetary/WeakKAM/Evaluation.lean`. The exact user-specified report destination overrides the brief's generic main-worktree destination. Used the lean-statement-audit method; read AGENTS, PLAN, DECISIONS, the package brief, B19 handoff, P11B design row B19 and node table, both design audits, canonical signatures, track-P statement, and relevant blueprint statements/consumers. No source or frozen files were edited.

## Snapshot and comparison

- Evaluation SHA256: `fe55f2b029e7dbec6c09914b21ce67b2ac0938797b56f9b56dabbcd5877cce5a`.
- Canonical `/root/code/KAM-inp/.drafts/design/P11BSignatures.lean` SHA256: `e5ae0f3f6c134280acd184e6130e2c39bac49485097647cd36f52f7dbf87ef63`.
- Observed `inp`: `3fcfb654e1e10a82cc4ab57401156fc446225ce1`.
- `git diff inp...HEAD` warns: `multiple merge bases, using 1f061eb1e60db1c82bd8d9c2c64483a08da1cebe`. Both merge bases are `1f061eb1e60db1c82bd8d9c2c64483a08da1cebe` and `68928d00aa4d02c9b2a11f2b9673d8bd47616645`.
- The full three-dot diff was inspected: Evaluation (377 added lines), KAM.lean (7 inherited import additions), two graph files (21 additions/21 deletions each), and B16/B17 audit/handoff files. No inherited package proof is newly certified here.
- `git show --stat HEAD` identifies the owned B19 commit as Evaluation alone. `git diff HEAD^ HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.
- The literal protected-path three-dot requirement is **not empty**: KAM.lean has seven inherited B16/B17 imports (Displacement and six Tori modules). Frozen, manifest and README diffs are empty. The root changes precede B19; this is recorded explicitly rather than claiming the literal check passed.

## Signed declarations and complete graph slice

All six signed commands match the canonical signature exactly after removing theorem proof bodies and surrounding comments; binder order, implicitness, types, structure parent, field order and all definition bodies agree. An independent source-type application probe checks the theorem with every explicit binder in order. Literal definition equations are checked by `rfl`. There is no provider/frozen seal correspondence in this infrastructure package.

All names below have prefix `KAM.Planetary`; `D.` abbreviates the `EvalExtData` namespace. Line numbers refer to Evaluation.

| Node / role | Declaration / lines | Verdict | Reason |
|---|---|---|---|
| half-open cell | `selectionHalfCell`, 32 | PASS | Exact signed body, angle Ico and parameter H in phase order. |
| closed cell | `selectionClosedCell`, 34 | PASS | Exact signed body, angle Icc. |
| quotient | `selectionQuotient`, 36 | PASS | Exact signed period-one AddCircle quotient; action block unchanged. |
| conditional extension data | `EvalExtData`, 43 | PASS | Explicit implementation input package; constructed inside source theorem. |
| extension formula | `D.E`, 58 | PASS | Literal id plus Phi on all Phase. |
| extension continuity | `D.continuous_E`, 60 | PASS | D.lip gives continuity of Phi. |
| eb-bounds helper | `D.bounds`, 66 | PASS | Literal two-sided estimate with 1-lam and 1+lam. |
| inverse helper | `D.bij_inv`, 70 | PASS | Bijectivity and inverse inequality from lipeo_onto. |
| image transfer | `D.ev_image`, 73 | PASS | Agreement only used on H contained in Kinf. |
| eb-meas lower helper | `D.measure_lower_aux`, 77 | PASS | Inverse map, exponent 2*n; multiplication cancels positive inverse factor. |
| eb-meas upper helper | `D.measure_upper_aux`, 98 | PASS | Forward lip_image_prod with 1+lam. |
| product cell | `selectionHalfCell_eq`, 106 | PASS | Literal equality to angle cube times H. |
| closed product cell | `selectionClosedCell_eq`, 112 | PASS | Same for closed cube. |
| cell volume | `volume_selectionHalfCell`, 118 | PASS | Unit cube has volume one; product measure, arbitrary H. |
| cell projection | `selectionHalfCell_subset`, 123 | PASS | Parameter membership projection. |
| closed projection | `selectionClosedCell_subset`, 126 | PASS | Parameter membership projection. |
| inner boxes | `selectionInnerBox`, 130 | PASS | Closed cubes ending at 1-1/(j+1). |
| compact boxes | `selectionInnerBox_compact`, 133 | PASS | Finite product of compact intervals times compact H. |
| exhaustion | `selectionHalfCell_eq_iUnion`, 137 | PASS | One common finite maximum index; endpoint 1 remains excluded. |
| compact domain | `selectionClosedCell_compact`, 157 | PASS | Finite closed cube times compact H. |
| image exhaustion | `D.compact_union`, 167 | PASS | Continuous E sends each inner box to compact image. |
| F-sigma | `D.closed_union`, 173 | PASS | Compact images are closed in Phase. |
| sigma compact | `D.sigma_compact`, 178 | PASS | Countable union of compact images. |
| Borel image | `D.measurable`, 184 | PASS | Countable union of closed sets is measurable. |
| closed image | `D.closed_image_compact`, 190 | PASS | Agreement with continuous E on compact closed cell. |
| lattice saturation | `D.lattice_union`, 195 | PASS | Floor decomposition and ev equivariance; both inclusions. |
| quotient lattice invariance | `selectionQuotient_add_lattice`, 222 | PASS | Integer translations disappear in AddCircle 1. |
| quotient continuity | `continuous_selectionQuotient`, 227 | PASS | Coordinatewise continuous quotient and action projection. |
| quotient image | `D.quotient_compact`, 238 | PASS | Quotient of full image equals quotient of closed-cell image. |
| common output | `SelectionEvaluationOutput`, 258 | PASS | Exact signed parent and all fields, one inherited witness. |
| bpP:p11a:evaluation-bilipschitz | `evaluation_bilipschitz`, 301–369 | PASS | Constructs output from raw data, admissible positive epsilon and perturbation. |
| stepP:p11a:eb-bounds | 324–334, 345–353 | PASS | Bounds/inverse restricted from E using agreement on Kinf fibres. |
| stepP:p11a:eb-ext | 304–323, 332–335, 354–358 | PASS | McShane defect extension, global bijection, exact defect Lipschitz constant; retained equivariance inherited. |
| stepP:p11a:eb-meas | 77–100, 118–188, 336–341, 359–369 | PASS | Closed exhaustion, measurability, lower/coarse/upper measures all populated. |
| stepP:p11a:eb-cpt | 190–251, 342–344 | PASS | Closed image, lattice union and quotient compactness all populated. |
| bpP:p11a:situation | `situation`, 372 | PASS | Exact signed output alias; never assumed by evaluation theorem. |

The design node table at P11B-LEAN-DESIGN.md:153–157 maps all four eb steps to the theorem; no separate node-named export has a weakened conclusion. Row B19 at line 245 assigns precisely this slice. `bpP:p11a:situation` has its signed alias here; upstream iteration/selection construction remains inherited.

## Definitions, hypotheses and consumer adequacy

Definition classification:

| Declaration | Classification | Body/carrier/well-definedness/characterization/choice |
|---|---|---|
| selectionHalfCell | Literal set predicate | BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; PASS. |
| selectionClosedCell | Literal set predicate | Same statuses; closed rather than half-open angle intervals; PASS. |
| selectionQuotient | Literal quotient map | Same statuses; period one on the full Phase carrier; PASS. |
| EvalExtData.E | Literal formula | Same statuses; E z = z + Phi z globally; PASS. |
| selectionInnerBox | Literal compact exhaustion | Same statuses; j=0 is the zero-angle box and every j has endpoint strictly below one; PASS. |
| situation | Literal type alias | Same statuses; exactly SelectionEvaluationOutput; PASS. |
| EvalExtData | Conditional implementation structure | Raw Phi, 0<=lam<1, Lipschitz bound, retained agreement and equivariance; honest input to distinct conditional helpers, constructed at 311–323; PASS. |
| SelectionEvaluationOutput | Source result structure | Exact signed extension of SelectionLipschitz; all new fields populated by proof, not supplied as assumptions; PASS. |

No arbitrary chosen map is exported as a canonical source object: the source asks for existence of an extension. McShane supplies that witness, and its defining bounds/agreement are proved. Uniqueness of this existential extension is not a source requirement. Equivariance is only required for evaluation on retained fibres; the proof never assumes the arbitrary McShane extension is periodic globally.

Expanded binder audit for the source theorem follows. TYPING includes numerical/function data; STANDING cites the literal source assumptions p11a3:32–40; SOURCE cites p11a4:30–34. No instances or extra assumptions are hidden in the new output structure.

| Binder / expanded field | Bin | Authority |
|---|---|---|
| implicit n : Nat | TYPING | Number of angles/actions. |
| d : SelectionData n (carrier/data) | TYPING | Source selection data. |
| d.mu | TYPING | Integer order. |
| d.rho | TYPING | Integer index. |
| d.tau | TYPING | Real exponent. |
| d.theta | TYPING | Real geometric width (Lean ϑ). |
| d.strip | TYPING | Real strip width. |
| d.C1 | TYPING | Real Hessian bound. |
| d.beta | TYPING | Real finite-type bound. |
| d.M | TYPING | Real tensor bound. |
| d.loss | TYPING | Real measure loss. |
| d.K | TYPING | Parameter set. |
| d.h | TYPING | Integrable Hamiltonian. |
| d.n_pos | STANDING | sel-data (a): n>=1. |
| d.mu_pos | STANDING | sel-data (a): mu>=1. |
| d.rho_mem | STANDING | sel-data (a): rho=1 or 2. |
| d.tau_nonneg | STANDING | sel-data (a). |
| d.tau_gap | STANDING | sel-data (a): tau>n*mu/rho-1. |
| d.compact | STANDING | sel-data (b). |
| d.positive_measure | STANDING | sel-data (b). |
| d.theta_pos | STANDING | sel-data (b). |
| d.theta_le | STANDING | sel-data (b). |
| d.strip_pos | STANDING | sel-data (b). |
| d.strip_le | STANDING | sel-data (b). |
| d.hessian_normalized | STANDING | sel-data (b): C1>=1. |
| d.beta_pos | STANDING | sel-data (d). |
| d.beta_le | STANDING | sel-data (d): beta<=M. |
| d.loss_pos | STANDING | sel-data (b). |
| d.loss_lt | STANDING | sel-data (b). |
| d.holo | STANDING | sel-data (c). |
| d.real | STANDING | sel-data (c). |
| d.hessian | STANDING | sel-data (c), whole complex collar. |
| d.finite_type | STANDING | sel-data (d), pointwise existential derivative order. |
| d.top_bounds | STANDING | sel-data (d), Euclidean unit-ball tensor inputs. |
| epsilon | TYPING | Perturbation upper bound. |
| he | SOURCE | situation: epsilon>0. |
| hsmall | SOURCE | situation: epsilon<=selectionAdmissible d. |
| f | TYPING | Perturbation function. |
| hf.holo | SOURCE | sel-data (c), on strip times action neighbourhood. |
| hf.periodic | SOURCE | sel-data (c), integer angle periodicity. |
| hf.real | SOURCE | sel-data (c), reality on real points. |
| hf.bound | SOURCE | situation: norm f<=epsilon on the whole domain. |

Counts in this explicit expansion: TYPING 15, STANDING 21, SOURCE 6, RULED 0, EXCESS 0 (42 rows). Parent record carriers and witnesses are outputs constructed by `lipschitz_family`; no conclusion is assumed by `evaluation_bilipschitz`. The conditional helpers take D, compact H, H subset Kinf, or cell membership exactly when needed; these premises are supplied inside the theorem.

Consumer check: p11a5:105 (qt-k4), p11a5:128 (pi-a) and Part 11's K4 need the image of the parameter cell, its measure, injectivity and quotient compactness. `SelectionOutput.compact_H` and `H_subset` (SelectionRecord:42–43) supply H=Hinf. Fresh term probes apply `o.measure_lower o.Hinf o.compact_H o.H_subset` and `o.quotient_compact` with those same witnesses. The inherited periodic defect proves evaluation equivariance. The bilipschitz lower bound with positive 1-2^-10 implies injectivity, and agreement with continuous global E gives continuity on the retained set. These are mathematically available even though not separately named fields. All fields retain the same d/f/epsilon, chain, Kinf/Hinf, defect and frequencies. Zero epsilon is outside this positive-epsilon source theorem, as explicitly specified in p11a4:34; B19 does not claim the p11a5 zero-case assembly.

## Validation

The final validation commands are run serially with `LEAN_NUM_THREADS=1`; build uses the prescribed compile gate and its `nice -n 5 lake build`. Scratch is `.lake/abi-scratch/B19Audit.lean`, removed after checking. An initial lint attempt was superseded because lint internally invokes Lean for ABI hashing; only the serialized rerun is the final lint receipt.

1. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11b-b19 KAM.Planetary.WeakKAM.Evaluation`

   Exit 0. Output: `[inp-gate] slot 1 acquired 00:29:10 for KAM.Planetary.WeakKAM.Evaluation`; `Build completed successfully (9216 jobs).` Replayed upstream unused-variable warnings occur; no warning originates in Evaluation.

2. `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`

   Exit 1, solely the permitted generated-root exception. Exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1156 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

3. `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B19Audit.lean`

   Exit 0. Exact-type theorem application, four literal definition equations and two Hinf consumer probes elaborate without diagnostics. All 24 public theorem axiom results follow verbatim:

   ```text
   'KAM.Planetary.EvalExtData.continuous_E' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.EvalExtData.bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.EvalExtData.bij_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.EvalExtData.ev_image' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.EvalExtData.measure_lower_aux' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.EvalExtData.measure_upper_aux' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.selectionHalfCell_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.selectionClosedCell_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.volume_selectionHalfCell' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.selectionHalfCell_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.selectionClosedCell_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.selectionInnerBox_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.selectionHalfCell_eq_iUnion' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.selectionClosedCell_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.EvalExtData.compact_union' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.EvalExtData.closed_union' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.EvalExtData.sigma_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.EvalExtData.measurable' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.EvalExtData.closed_image_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.EvalExtData.lattice_union' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.selectionQuotient_add_lattice' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.continuous_selectionQuotient' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.EvalExtData.quotient_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.evaluation_bilipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

4. `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.Evaluation`

   Exit 0. Exact output: `replaying KAM.Planetary.WeakKAM.Evaluation`.

5. `git diff --check inp...HEAD`: exit 0, only the multiple-merge-base warning. Owned protected-path diff empty; literal three-dot protected-path diff has the inherited KAM.lean change described above.

6. Static checks: 377 lines total, no line over 100 characters; module/copyright/public imports/module docstring/public exposed section present. No forbidden proof escapes, heartbeat/recursion/synthesis overrides or EuclideanSpace. Comment-masked declaration scan of all KAM sources found no reused helper short names. There are no root-namespace declarations or new instances. The first unmasked scan matched the words “lemma bounds” in a PolarAverage docstring; that is not a declaration and was discarded.

7. Recursive project import scan: 170 modules, 14 frozen definition modules, zero provider imports and zero frozen sorry imports. The imported frozen objects are definitions, not DRAFT_SORRY theorem anchors. Frozen guard/ABI results are recorded in the lint receipt.

## Source defects, deviations and limits

No substantive suspected pinned-source defect, blueprint contradiction, unauthorized deviation, unpaid B19 node or added source premise was found. The source p11a4:229 writes the inner boxes once as H times angle cube while defining A in phase order (angle, parameter). This is a harmless notational block swap in the exposition; the implementation consistently uses angle cube times H and product volume, with no hidden Jacobian. It does not affect the claim or require a changed theorem.

Using the global inverse of E for the lower measure estimate is equivalent to the source's inverse restricted to the image. Both apply lip_image_prod with exponent 2*n and produce the positive lower factor (1-lam)^(2*n), not its reciprocal. The exhaustion begins at j=0 (m=1), adding a redundant zero-angle compact box to the source's m>=2 union; the proved union is unchanged. These are implementation choices, not deviations of the signed statements.

Regenerating KAM.lean is left to the orchestrator as the brief requires. This audit certifies only B19 and its exact positive-epsilon signature, not any frozen anchor, the whole P11B campaign, or the later quantitative/physical theorem.
