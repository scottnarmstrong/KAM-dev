# Independent audit: P11A-P8e (tracks I/N/P)

**Verdict: PASS WITH NOTES for each signed export `prepared`, `amount`, and `data_star`.** Their signatures match literally, their proofs have no extra premise, and every clause of the signed preparation specification is assembled. This is acceptance of the signed preparation slice, not a frozen-anchor seal or closure of the physical headline. The remaining notes concern the expressly deferred Part11a5 typed bridge and the permitted stale generated root.

## Scope and authority

Audit date: 2026-10-29. Worktree: `/root/code/KAM-inp-p11ap8e`; HEAD: `bbf064fa2bd7259455c072dfa7168fed25c5e6b4`.
Read AGENTS.md, PLAN, DECISIONS, the requested package audit brief, the entire P8e handoff/AUDIT FOCUS, track-P statement, design node table and revision-2 reconciliation, blueprint preparation/amount/data-star nodes, relevant source specifications and frozen definitions. The user-specified worktree report destination overrides the generic brief's main-worktree destination.

Signed authority: `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`, SHA256 `fd2c245ea48f1b99f36beb02bba0095e9a55b070be0eae178198fdf20011b9e9`; `prepared` 1124–1131, selector 1133–1134, `amount` 1135–1143, `data_star` 1282–1301.

Initial `git diff inp...HEAD` used inp `9ffcb3343be139ca6f003a42f0cab4ab6027fbb6`: 15 files, 4946 insertions, including 13 Lean files and inherited P8D handoff/audit documents. This contains earlier P8b/P8b2/P8b3/P8D work as well as P8e. All 13 Lean modules received independent axiom and kernel checks; detailed assembly review follows the explicit six-module AUDIT FOCUS. Earlier dependency packages are not represented as newly authored P8e proofs.

The shared inp ref advanced externally during this audit to `5d44119d056f2ca5951a84bfccb79e709d730e4e`. A repeated literal `git diff inp...HEAD` warned `multiple merge bases, using af9e74858ebeabe685f5c42392912bbbe760c827`; the two merge bases were that commit and `2526f740b776df512dd67a7d60a6202209cb2eda`. That comparison contains the same 13 Lean paths, 4656 insertions; Datum's existing P8D material and the two P8D documents are now common history. Reproducible initial comparison: `git diff 9ffcb3343be139ca6f003a42f0cab4ab6027fbb6...bbf064fa2bd7259455c072dfa7168fed25c5e6b4`. Protected-path comparisons were empty at both observations.

No provider or frozen theorem is added or sealed. Consequently frozen-provider equality and frozen seal-body tests are inapplicable. Fresh-name copies of the three signed declarations were elaborated with direct bodies `prepared D hnu`, `amount D hnu`, and `data_star D`, followed by exact `type_of%` comparisons in both directions. The full signed statement, including every internal let-binding, was copied from the signature file; no draft proof or sorry body was imported. All three headers are byte-identical, including binder order, to their signed headers.

## Node coverage and proof review

All declaration names below are in `KAM.Planetary`.

| Node | Realization | Verdict | Reason |
|---|---|---|---|
| `bpP:p11:prepared` | Prepared.lean:27 `prepared` | PASS | Exact signed existential thresholds and full specification; no extra source input. |
| `stepP:p11:pr-basic` | Prepared.lean:85–100, `p11_prepared_basic_dom` | PASS | Basic formula/chain, holomorphy, periodicity, reality, and Hamiltonian identity retained. |
| `stepP:p11:pr-a` | Same basic assembly, `b8` | PASS | Perturbation sup bound uses c3 ≥ c2, with the signed exponent. |
| `stepP:p11:pr-in` | PreparedJets/G0 and PreparedDev/Resc feeding pr-b/c/d | PASS | Uses established derivative inputs; does not assume the prepared jet conclusion. |
| `stepP:p11:pr-b` | Prepared.lean:89–90 `hbb` from `p11_pr_b` | PASS | Complex frequency and Hessian bounds on the signed 3/4-neighbourhood. The signed bound is 2L+1; the dependency proof actually bounds the Hessian by 1. |
| `stepP:p11:pr-c` | Prepared.lean:93–96 `hcc` from `p11_pr_c` | PASS | Full unscaled-J diagonal jet closeness, same checkW and exponent; normalization proved by `p11_prep_chk_eq`. |
| `stepP:p11:pr-d` | Prepared.lean:91–100 `hdd` from `p11_pr_d` | PASS | Scalar orders 1 through mu+1, vector orders 0 through mu, and separate scalar order 0; neither zero-order clause is omitted. |
| `bpP:p11:sec-E#data` | Existing PreparedData and Basic/core construction | PASS | Same signed carriers, rescaling and box; no replacement definition. |
| `bpP:p11:amount` | Amount.lean:71 `amount` | PASS | Exact signed lower bound `(1/2)*eps^(mu+2)*beta` for the selected Q. |
| `stepP:p11:am-dir` | Amount.lean:153–169, `amount_transfer` → `amount_dir` | PASS | Stability on original J coordinates; smoothness, compactness, jet bound, nonempty set, and beta comparison all supplied. |
| `stepP:p11:am-scale` | Same call → `amount_scale` | PASS | Directional rescaling pays eps^mu; restricting to r directions is valid for the full amount. |
| `stepP:p11:am-norm` | Same call → `amount_norm`; Amount.lean:178–180 | PASS | Target diagonal scaling pays eps^2; local equality on an open ball transports all jets to the actual prepared frequency. |
| `bpP:p11:data-star` | Datum.lean:158 `data_star` | PASS WITH NOTES | Exact signed conjunction, unconditional application of proved amount. Typed Part11a5 bridge remains deferred by the design. |

`prepared` chooses c3 = max(max(1,c2), Kc(1+c2)) and the minimum of three positive thresholds. The auxiliary M = (Kb+Kd)(1+c2)+c3 controls all three needed smallness bounds from one eventual estimate. Its exponent depends only on fixed tau and mu. c3 and the threshold may depend on D and the already fixed nu, as signed. The bounds 2L+1, M*, and M0* remain independent of nu and epsilon.

Every signed `P11PreparedSpec` clause is wired at Prepared.lean:99–100: basic fields b1–b8; frequency/Hessian hbb; frequency normalization hfr; closeness hcc; positive-order scalar bound hdd.1; Hamiltonian identity b9. The extra FullSpec clauses are, in order, normalized-frequency identity, unscaled-J closeness, full vector jets, and scalar order zero. This exhausts the conjunction rather than merely proving a selected sub-specification.

`amount` establishes FullSpec for the actual `p11PreparedData` by unfolding its existence guard, which is witnessed by `prepared`. It uses compactness on the fixed patch K to obtain a finite diagonal jet bound L1. A shrinking original-action cube lies in K since J0 is interior. Monotonicity gives beta_J ≤ index on that cube. A further positive threshold enforces `2^mu theta (2 L1+theta) ≤ beta_J/2`; there is no assertion of derivative stability from a C0 bound. Smoothness of checkW is derived from the prepared holomorphic frequency and the invertible block scaling for positive eps. The amount is transferred on the open 5/4-ball, then `index_def_congr` replaces diag(1,eps)checkW by the prepared frequency on the box. Pi max-norm geometry and explicit Euclidean tensor gauges are kept distinct.

`data_star` supplies the universal amount premise of the distinct conditional helper with `fun _nu hnu => amount D hnu`. Its proof is therefore unconditional in the signed physical data. The helper shrinks only epsilon, preserves c and the chosen Q, and proves the fixed box/numeric conditions separately. No conclusion-shaped hypothesis remains in any signed theorem.

## Focus declarations

| Declaration (file:line) | Verdict | Reason |
|---|---|---|
| `p11_prep_five_eventually` (PreparedSmall:29) | PASS | Positive logarithmic lower bound for s2 and epsilon-log decay give 5eps ≤ s2. |
| `p11_prep_small` (PreparedSmall:57) | PASS | Simultaneous positive threshold establishes fast/slow specs and numeric guards; selectors use witnessed branches. |
| `p11_prep_eventually_le` (PreparedSmall:106) | PASS | Epsilon times a fixed logarithmic power tends to zero; valid for M=0 and q=0 too. |
| `p11PrepQ_checkW` (PreparedChoice:42) | PASS | Definitional identification of the chosen frequency field. |
| `p11PrepQ_N_formula` (PreparedChoice:45) | PASS | Definitional core formula, valid on the stated action neighbourhood. |
| `p11_prep_pt` (PreparedChoice:52) | PASS | Affine rescaling identity, with exactly the necessary nonzero epsilon guard. |
| `p11_prep_chk_eq` (PreparedChoice:67) | PASS | Proves the normalized-frequency identity for all J and rho; stronger than the bounded-domain use. |
| `p11_prep_ball_mem` (PreparedChoice:75) | PASS | Coordinate clipping to the half cube gives distance ≤3/4<1. |
| `p11_fderiv_pi_one` (PreparedChoice:93) | PASS | Derivative of a one-coordinate Pi-valued scalar function, from differentiability. |
| `p11_prep_freqR_eq` (PreparedChoice:104) | PASS | Uses the order-zero frequency identity and division cancellation for positive eps. |
| `prepared` (Prepared:27) | PASS | Exact signed assembly, as detailed above. |
| `p11_amt_op_bound` (AmountSetup:28) | PASS | Continuous finite jet on compact A times the compact product of Euclidean unit balls; bounds the actual supremum. |
| `p11_amt_jet_bound` (AmountSetup:52) | PASS | Finite sum of nonnegative bounds; diagonal gauge ≤ operator gauge, including order zero. |
| `p11_amt_jet_mono` (AmountSetup:68) | PASS | Restricts the original set; no strength or constant change. |
| `p11HalfCube_compact` (AmountSetup:76) | PASS | Finite product of compact intervals. |
| `p11HalfCube_nonempty` (AmountSetup:79) | PASS | Zero lies in the cube, including dimension zero. |
| `p11HalfCube_norm` (AmountSetup:82) | PASS | Coordinate interval bounds give the Pi max-norm bound. |
| `p11_amt_append_norm` (AmountSetup:88) | PASS | Both blocks bounded by 1/2; no Euclidean/max identification. |
| `p11_amt_box_halfCube` (AmountSetup:95) | PASS | Exact projections of the prepared box into its two half cubes. |
| `p11_amt_chk_contDiff` (Amount:29) | PASS | CheckW smoothness derived from the specified holomorphic frequency, not assumed. |
| `amount` (Amount:71) | PASS | Exact signed assembly, as detailed above. |
| `p11PreparedBox_isCompact` (Datum:30) | PASS | Finite product of compact intervals. |
| `p11PreparedBox_volume` (Datum:33) | PASS | Product Lebesgue volume of unit intervals equals one. |
| `p11PreparedBox_diam` (Datum:38) | PASS | Pi diameter upper bound and opposite constant corners; dimension positivity supplied by D.n_ge. |
| `p11_tau_max_gt` (Datum:58) | PASS | Each component of the right maximum is strictly less by one after casts. |
| `p11_one_le_L` (Datum:68) | PASS | Extracts the proved secular source bound. |
| `p11_one_le_M0` (Datum:73) | PASS | L ≥1 and the positive integer-power factor give M0 ≥1. |
| `p11_beta_bounds` (Datum:82) | PASS | eps^(mu+2) ≤eps and eps beta_J ≤1 yield beta ≤1/2; M ≥2; beta positive. |
| `data_star_of_amount` (Datum:112) | PASS | Explicit conditional helper, with exactly the authorized signed amount output as premise. |
| `data_star` (Datum:158) | PASS WITH NOTES | Signed unconditional application; deferred typed integration noted below. |

## Definition classification

The three new definitions in the focus slice are intended total objects:

| Definition | Classification | Whole-carrier behavior |
|---|---|---|
| PreparedChoice:31 `p11PrepChk` | Normalized derivative field | Derivative of h0+g2 at the rescaled real point; head real part and tail real part divided by eps. Division and fderiv have Lean's usual totalized values outside regularity/positive-epsilon guards; no theorem infers analytic meaning there. |
| PreparedChoice:39 `p11PrepQ` | Concrete prepared core | Uses the established core with exactly p11PrepChk as checkW; no fallback or hidden premise. |
| AmountSetup:73 `p11HalfCube` | Geometric set | Literal product [-1/2,1/2]^n on its whole carrier. |

There is no new structure/instance in the focus slice. The signed selector `p11PreparedData` is unchanged from inp (PreparedData.lean:107–108), with its exact signed `if exists ... then choose else default` body. The only use requiring its specification, Amount.lean:111–115, proves the existence guard first. The fallback is never used to discharge a theorem.

Inherited definitions in the full diff were also classified: `p11DevCenter` is the slow-box center; `p11DevProj` the first-block continuous linear projection; private `opsRe`, `opsExt`, `opsExtR` the real-part map and the two zero-block extensions; `p11DevH` the singleton-vector h0+g2; `p11DevA/G/Z` literal factorial/radius Cauchy majorants; `p11DevOmv` the concatenated omega and Omega/(2pi); `p11CloseFun` the normalized complex frequency defect; `p11CloseDom` the intersection of the slow-box slice and the original secular ball. These implement their stated formulas, not proxy predicates or conclusion fields. Totalized divisions outside positive-radius assumptions are not used as estimates.

## Consumer applicability and limitations

Design node table lines 174–185 maps all preparation/amount substeps to these assemblies; its inherited helper modules provide the derivative inputs and directional transfer. No unsigned graph-node namesake replaces a literal graph conclusion. The actual signed result is the authority where the design deliberately packages a narrower conjunction.

Design lines 856–861 expressly say: “Once Part11a5 delivers its exact admissibility predicate, P8D must prove a typed bridge from these conjuncts into it.” They also say K5/K6 “remain upstream proof obligations”. This checkout has no production consumer of `data_star` or import of Preparation.Datum; the independent `WeakKAM/Data.lean` defines `SelectionData` and `SelectionPerturbation` rather than a completed bridge from these preparation outputs. The signed data retain the same Q, required domains, frequency/Hessian bound, all vector/scalar jets, nonzero amount and fixed geometry for that future bridge. These facts do not establish compatibility with a future API automatically. In particular this audit does not certify the full prose of blueprint data-star (p11-cp09-preparation.tex:243–245), the K5 polynomial lower budget, the K6 displacement constants, the wrapper or a physical theorem. This recorded integration boundary is a note, not an extra hypothesis in the accepted signed theorem.

## Hygiene and independent validation

All auditor-initiated Lean/Lake invocations were serialized, each with `LEAN_NUM_THREADS=1` and `nice -n 5`. Builds used the required compile gate. No clean, dependency update, cache fetch, root regeneration, frozen edit, manifest edit or state-changing git command was performed. Only this report is retained; scratch probes/logs are removed after results are recorded.

1. Protected paths: `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no patch (both initial and later comparisons). `git diff --check 9ffcb3343be139ca6f003a42f0cab4ab6027fbb6...HEAD` exited 0, no output.
2. Targeted build, exit 0:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap8e KAM.Planetary.Preparation.PreparedSmall KAM.Planetary.Preparation.PreparedChoice KAM.Planetary.Preparation.Prepared KAM.Planetary.Preparation.AmountSetup KAM.Planetary.Preparation.Amount KAM.Planetary.Preparation.Datum
   [inp-gate] slot 1 acquired 03:39:23 for KAM.Planetary.Preparation.PreparedSmall KAM.Planetary.Preparation.PreparedChoice KAM.Planetary.Preparation.Prepared KAM.Planetary.Preparation.AmountSetup KAM.Planetary.Preparation.Amount KAM.Planetary.Preparation.Datum
   Build completed successfully (9435 jobs).
   ```

   Replayed warnings were deprecations and unused variables/tactics/simp arguments, including deprecated dif_pos in PreparedSmall/Amount and if_pos in AmountSetup. No elaboration error or default-heartbeat design signal occurred.
3. Signature/body and focus-axiom probe: `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P8eProbe.lean`, exit 0. Six bidirectional exact-type examples and three copied signed declarations passed. Complete axiom output for the 30 focus public theorems:

   ```text
   'KAM.Planetary.p11_prep_five_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_prep_small' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_prep_eventually_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11PrepQ_checkW' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11PrepQ_N_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_prep_pt' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_prep_chk_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_prep_ball_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_fderiv_pi_one' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_prep_freqR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.prepared' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_amt_op_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_amt_jet_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_amt_jet_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11HalfCube_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11HalfCube_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11HalfCube_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_amt_append_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_amt_box_halfCube' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_amt_chk_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.amount' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11PreparedBox_isCompact' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11PreparedBox_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11PreparedBox_diam' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_tau_max_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_one_le_L' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_one_le_M0' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11_beta_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.data_star_of_amount' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.data_star' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

4. Broader axiom probe: `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P8eAllAxioms.lean`, exit 0. All 136 public theorems in the initial full diff were printed: 132 depend on `[propext, Classical.choice, Quot.sound]`; `p11_close_append_cast`, `p11_dev_append_add`, `p11_pd_single_cast`, and `p11_pd_single_nat` depend only on `[propext, Quot.sound]`. No other axiom occurred.
5. Kernel replay, one invocation covering all 13 changed Lean modules:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.PreparedSmall KAM.Planetary.Preparation.PreparedChoice KAM.Planetary.Preparation.Prepared KAM.Planetary.Preparation.AmountSetup KAM.Planetary.Preparation.Amount KAM.Planetary.Preparation.Datum KAM.Planetary.Preparation.PreparedOps KAM.Planetary.Preparation.PreparedDev KAM.Planetary.Preparation.PreparedNum KAM.Planetary.Preparation.PreparedResc KAM.Planetary.Preparation.PreparedFreq KAM.Planetary.Preparation.PreparedClose KAM.Planetary.Preparation.PreparedM
   ```

   Exit 0. Complete output:

   ```text
   replaying KAM.Planetary.Preparation.PreparedM
   replaying KAM.Planetary.Preparation.PreparedClose
   replaying KAM.Planetary.Preparation.PreparedFreq
   replaying KAM.Planetary.Preparation.PreparedResc
   replaying KAM.Planetary.Preparation.PreparedNum
   replaying KAM.Planetary.Preparation.PreparedDev
   replaying KAM.Planetary.Preparation.PreparedOps
   replaying KAM.Planetary.Preparation.Datum
   replaying KAM.Planetary.Preparation.Amount
   replaying KAM.Planetary.Preparation.AmountSetup
   replaying KAM.Planetary.Preparation.Prepared
   replaying KAM.Planetary.Preparation.PreparedChoice
   replaying KAM.Planetary.Preparation.PreparedSmall
   ```

6. Source lint: `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`, exit 1, complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1239 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   The sole failure is the exact generated-root exception permitted by the brief. It was not regenerated. No forbidden token, resource override, EuclideanSpace, overlong line, oversized file or module-system violation was found. The 13 changed Lean files have 103–844 lines (focus: 103,104,123,143,183,185); maximum line width over the full diff is 100, and over the focus modules 99. Definitions needing unfolding sit in `@[expose] public noncomputable section`.
7. Recursive project-import closure from Datum: 389 project modules, no provider import and no frozen theorem import. All 64 imported frozen definition modules match manifest entries in state SEALED. Thus no DRAFT_SORRY dependency is hidden in the assembly, consistently with the axiom output.
8. Public declaration short-name scan against all KAM sources found no reused short name among the full diff's public theorem/def/abbrev additions. All focus exports remain under KAM.Planetary; no root declaration or instance is introduced, and the exact-type probes resolve the intended names.

## Errata, deviations and remaining uncertainty

No new suspected pinned-source defect, false blueprint conclusion, or mathematical deviation was established. The existing CP09 C0-to-amount issue is explicitly repaired here by unscaled-J derivative stability; the proof does not reproduce it. The design's old intermediate pr-b text says Hessian ≤1, while the signed final bound is 2L+1; PreparedFreq.lean:343–350 in fact proves ≤1 before weakening, so no node is lost. The separate signed data-star/Part11a5 integration boundary above remains open and must not be relabelled as full wrapper or headline closure.

No production source was modified by the auditor. The pre-existing untracked P8e handoff was preserved. Final retained change: this exact worktree report.
