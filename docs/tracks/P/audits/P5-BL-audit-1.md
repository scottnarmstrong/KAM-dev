# Independent audit 1: P5-BL

Verdict: **PASS WITH NOTES** for the P5-BL infrastructure contract (`lip_complex`, `complexFast`, `bilip`). No frozen anchor is proved or sealed by this package; frozen P-G remains outside this verdict. No blocking mathematical or signature defect found. Validation receipts are recorded below.

## Scope and authority

Audited HEAD `c33e60fe12450ad27575d794943c245b30c79271`, against `inp` at `05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2`, and the scoped `inp-p5ex...HEAD` diff (`inp-p5ex` at `117d37238a3f0ac1e88dfcfe8718fee28b271823`). Only `KAM/Planetary/PGAssembly/FastComplex.lean` is audited afresh: 491 lines, 18 public theorems and two definitions. The `inp...HEAD` diff also includes ten inherited Extension modules and P5-EX audit/handoff documents; the `inp-p5ex...HEAD` comparison contains unrelated branch divergence, which is not part of this audit.

Read AGENTS.md, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, local P5-BL handoff, P45 design (including package row, source-gap proof plan and revision 4), design audits 1–4, authoritative shared `/root/code/KAM-inp/.drafts/design/P45Signatures.lean:654–668`, P5 blueprint lines 78–94, P5 graph records, and track P statement's nondegeneracy contract. Read the frozen P-G telescope, `HasFastDiffeomorphism`, `FastFrequency`, `ActionNbhd`, and consumed PGData/PGExtension definitions. The exact report destination in the user request overrides the generic brief's main-worktree destination.

There is no provider export in scope. Frozen-provider type equality and seal-body probes are therefore **not applicable**, rather than passed. Instead, a scratch probe reproduces both theorem types from the shared design under fresh names, proves them using the implementation, and checks the reproduced `complexFast` body by `rfl`.

## Declaration-by-declaration findings

All names below are in `KAM.Planetary`; line numbers refer to FastComplex.lean.

| Node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| Cauchy helper for lip-complex | `norm_fderiv_le_of_closedBall` (39) | PASS | Bounded holomorphic vector map on a closed Pi ball; restriction along a complex line gives operator bound A/r. No convexity premise on the original carrier. |
| bpP:p5:lip-complex | `lip_complex` (77) | PASS | Exact design telescope, radii and constant 2NA/rho. Close/far split works on arbitrary X. |
| bpP:p5:bilip definition | `complexFast` (135) | PASS | Exact derivative-coordinate definition from design. |
| Coordinate helper definition | `partialsCLM` (139) | PASS | Actual bounded complex linear coordinate-evaluation map. |
| Coordinate identity | `complexFast_eq` (142) | PASS | Definitional equality; no premise. |
| Coordinate norm | `norm_partialsCLM_le` (145) | PASS | Operator norm at most one in Pi sup norms, including dimension zero. |
| Analytic extension derivative | `analyticOnNhd_fderiv_H0` (156) | PASS | Openness and holomorphy produce analyticity of the derivative on the original tube. |
| Frequency analyticity | `analyticOnNhd_complexFast` (164) | PASS | Composition with partialsCLM. |
| Frequency differentiability | `differentiableOn_complexFast` (168) | PASS | Same tube, no extra premise. |
| Derivative continuity | `continuousOn_fderiv_complexFast` (172) | PASS | Analytic regularity, not an assumed field. |
| Derivative upper bound | `norm_fderiv_complexFast_le` (177) | PASS | Uses proved extension second-derivative bound and norm(partialsCLM) <= 1. |
| Inclusion coordinate helper | `realInclusion_single` (193) | PASS | Exact real basis-vector inclusion identity. |
| Tube membership helper | `mem_actionNbhd_real` (198) | PASS | Positive radius and actual base-set membership suffice. |
| stepP:p5:bl-real attachment | `real_relation` (206) | PASS | Neighborhood equality from h0real justifies differentiating; not merely pointwise equality. Identifies actual frozen fastFrequency. |
| stepP:p5:bl-real derivative | `omega_hasFDerivAt` (243) | PASS | Constructs real derivative and proves complex derivative's action on real vectors. |
| stepP:p5:bl-real inverse | `omega_deriv_injective` (274) | PASS | Differentiates g composed with frequency = id on open W. hT is a distinct conditional helper premise discharged by omega_hasFDerivAt. |
| stepP:p5:bl-real complexification | `fderiv_complexFast_lower` (293) | PASS | Real/imaginary splitting proves complex kernel zero; finite dimensionality supplies positive lower constant. |
| stepP:p5:bl-comp local step | `complexFast_local_lower` (331) | PASS | Derivative continuity and mean value estimate for frequency minus its linearization give the local lower bound. |
| stepP:p5:bl-comp compact step | `lower_lip_of_local` (380) | PASS | Distinct general conditional helper; continuity, injectivity and local estimates are proved at its bilip application, not added to source hypotheses. |
| bpP:p5:bilip | `bilip` (460) | PASS WITH NOTES | Exact design type; data-only witnesses, strict rho < delta/16, full pairwise complex lower bound and derivative upper bound on doubled tube. See interface note below. |

## Proof and hypothesis audit

For close pairs, each segment point is less than rho/2 from the nearer endpoint. The endpoint has a witness in X at distance strictly less than rho, so the **closed** rho/2 ball remains in X_(2rho). The one-variable vector-valued Cauchy estimate along arbitrary complex directions gives the stronger derivative constant 2A/rho; N >= 1 then gives the advertised 2NA/rho. Distant pairs use the two endpoint sup bounds and distance >= rho. No convexity or connectedness of X is required; if X is empty, the pairwise conclusion is vacuous. The A >= 0 fact is derived from an actual evaluation whenever a pair is present.

At real tube points, h0real holds on a real neighborhood, allowing uniqueness of derivatives after restriction of scalars. The proof obtains the true real frequency derivative; it then differentiates the frozen inverse identity on W. Both openness of the frequency image (for differentiability of g) and openness of W (for the eventual inverse identity) are used. Real injectivity of that derivative implies complex injectivity by splitting the complex input into real and imaginary vectors. No analytic inverse or lower singular-value bound is assumed.

The compactness helper chooses pairs at radius r/(m+2) with ratio less than 1/(m+1), extracts a subsequence of their **real base witnesses in K x K**, and transfers convergence to the complex points. Distinct real limits contradict injectivity; equal limits contradict the established local lower bound and eventually small ratio. The proof does not assert compactness of an open tube. In bilip, K is closure V (compact by boundedness and finite dimensionality), r = delta/16, and M0 = max 1 extension.M0. Since 2rho < delta, h0bounds applies throughout the doubled tube.

P5-EX is consumed through the proved selected `pgExtension`, h0holo, h0real and h0bounds. No PGExtension witness is added as a source premise. Although the design package schedule lists P4-LI as a dependency, this implementation needs no selected P4 inverse constants or `lip_inverse` theorem: it uses the explicit C1 inverse already in frozen `d.hfreq` directly, as the bl-real proof plan prescribes. This is a dependency simplification, not a missing assumption or a claim to have reaudited P4-LI.

## Definition classification and import hygiene

- `complexFast`: intended total coordinate derivative of the chosen complex H0 extension, verbatim design body. Off the analytic locus, Mathlib fderiv has its standard totalized behavior. No result relies on those exterior values: derivative and pairwise estimates are restricted to the proved holomorphic tube.
- `partialsCLM`: ordinary continuous complex linear map taking a functional to its basis evaluations, on its whole carrier; no choice, fallback or encoded proof assumption.
- No new structure, abbrev, instance or source-data field. The module-level expose/noncomputable section covers both definitions.
- Recursive inspection of all local KAM imports reaches 52 KAM modules and **zero frozen theorem or provider modules**. Thus no imported DRAFT_SORRY anchor and no provider quarantine breach; manifest theorem-state exceptions are unnecessary.

## Notes, source fidelity and limits

1. Blueprint `bpP:p5:bilip` (p5:89) also says “hence” the inverse derivative has norm at most c0 inverse. The approved design and implementation do not export that continuous-linear-equivalence corollary explicitly. It follows mathematically by differentiating the pairwise lower bound at interior tube points, then using square finite-dimensional injectivity/surjectivity. This is an interface note for P5-FI consumers, not an extra premise or mismatch with the audited design type. This audit does not claim that omitted corollary has already been formalized.
2. The derivative bound 2A/rho is stronger than the printed 2NA/rho; likewise M0 may be enlarged to at least one as the exact design requires. Neither changes the claimed source conclusion or constant dependence.
3. The previously reported revision-4 P5-EX issue about off-cylinder agreement of P is inherited context, not a new P5-BL finding. Here only unchanged H0 agreement is used. No new suspected pinned-paper erratum, blueprint contradiction or deviation was found in the scoped proofs. No remote paper check or full P5-EX re-audit is claimed.
4. This is package verification, not graph-status mutation, full campaign closure, or frozen P-G proof completion.

## Independent checks

All completed Lean commands below ran sequentially with `LEAN_NUM_THREADS=1` and `nice -n 5`. No heartbeat, recursion or synthesis budget override was used.

### Targeted compile

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5bl KAM.Planetary.PGAssembly.FastComplex
[inp-gate] slot 1 acquired 10:52:47 for KAM.Planetary.PGAssembly.FastComplex
Build completed successfully (9098 jobs).
exit 0
```

The reported job count includes cached dependency traversal; no clean, update, cache retrieval or library-from-scratch command was issued.

### Design types, definition and axioms

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5BLAudit1.lean
exit 0
```

The probe imports only FastComplex. It copies the authoritative design telescopes under fresh names, with bodies:

```lean
-- In namespace KAM.Planetary, under noncomputable section:
-- audit_lip_complex has the complete design telescope.
-- Its body is:
@KAM.Planetary.lip_complex _ _ hN X rho A hrho f hf hb
-- audit_bilip has the complete design telescope. Its body is:
KAM.Planetary.bilip d
-- audit_complexFast repeats the design body verbatim.
example : @audit_complexFast = @complexFast := rfl
```

An initial probe run exited 1 solely because its copied definition lacked the surrounding `noncomputable section` from the design. Restoring that scratch-only context gave the successful run above; no production edit or type change was needed. The initial run's axiom output agreed with the successful rerun.

Each line below is the exact successful output of the corresponding `#print axioms`:

```text
'KAM.Planetary.norm_fderiv_le_of_closedBall' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lip_complex' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.complexFast_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_partialsCLM_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.analyticOnNhd_fderiv_H0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.analyticOnNhd_complexFast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiableOn_complexFast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuousOn_fderiv_complexFast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_fderiv_complexFast_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.realInclusion_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mem_actionNbhd_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.real_relation' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.omega_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.omega_deriv_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_complexFast_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.complexFast_local_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lower_lip_of_local' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.bilip' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.FastComplex
replaying KAM.Planetary.PGAssembly.FastComplex
exit 0
```

There is one new implementation module and no separate provider/lemma module to add to this invocation.

### Source lint

An early `sh scripts/lint_sources.sh` attempt was stopped during the source-check phase so that its later ABI subprocess would not overlap the targeted build; it is not used as a complete validation receipt. The final run is sequential, with both the thread limit and nice priority inherited by its ABI subprocess.

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (562 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole failing lint condition is the generated-root freshness notice expressly permitted by the audit brief. The generated root was not regenerated or edited. No other lint failure was reported.

### Integrity

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produces no output. The scoped new file contains no forbidden tokens or resource options, has 491 lines, and its longest line is 99 characters. Copyright, `module`, public imports, module docstring and public exposed noncomputable section are present. No production file was edited. Final cleanup and report whitespace check are recorded below.

The audit probe `.lake/abi-scratch/P5BLAudit1.lean` was deleted after validation. The report has 20 declaration rows and 18 axiom receipts. Final `git diff --check` and `git diff --no-index --check /dev/null /root/code/KAM-inp-p5bl/docs/tracks/P/audits/P5-BL-audit-1.md` exit 0. Status contains only this new report and the pre-existing untracked P5-BL handoff; no tracked file is modified. Source SHA256 for FastComplex.lean: `9f864874947a6203c5c77015e5c719af4a9801b7dbde660ff4fc21d16b162e6b`.

Final disposition: **PASS WITH NOTES** for P5-BL; no repair requested for the scoped file. The inverse-derivative interface note and permitted generated-root lint exception do not establish frozen-anchor or campaign closure.
