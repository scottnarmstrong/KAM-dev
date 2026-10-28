# Independent package audit 1 — P5-EX

Overall verdict: **PASS WITH NOTES** for the revision-4 P5-EX infrastructure contract (`ext`, `complexAverage_real`, `consts`). No frozen anchor is proved by this package; no P-G seal or root-closure verdict is asserted. The notes concern the already declared blueprint correction and scope boundaries, not an unproved premise in these results.

## Scope and authority

Audited `/root/code/KAM-inp-p5ex`, HEAD `0466c50d04c571fb5e9fc7d06e6e2a8d24b21a67`, against `inp` at `05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2`, using `git diff inp...HEAD`. Git reports multiple merge bases and selects `d59d3373956033408a4dc55abe782d89092254f3`; this warning is recorded rather than silently replacing the requested comparison. The diff adds 11 files / 1429 lines: ten `Extension*.lean` files (1275 lines) and the 154-line P5-CG `ComplexGlue.lean`. The handoff explicitly limits this audit to the ten Extension modules. ComplexGlue is an upstream dependency, not an independently audited package here; the axiom checks below cover its transitive logical dependencies, while kernel replay selects the ten modules in scope.

Read AGENTS.md, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the worktree handoff and AUDIT FOCUS, P45 design ownership/proof plan and Revision 4, design audits 1–4, P Part 5 lines 27–47, the track statement, frozen P-G telescope and its relevant definitions. Read the authoritative shared signatures at `/root/code/KAM-inp/.drafts/design/P45Signatures.lean` (not present in this package's `.drafts`). Signature SHA256: `6f3ac05b5f71bca24343c84aa3df51812acac3f518381c5ae9ef645b2355c402`; design SHA256: `fe084af07ac93f216e4f98e0ff5284319c5a544ee6df073af2069e9639d47559`.

The user's exact report destination overrides the generic brief's MAIN-worktree output rule. No repository source, frozen file, manifest, generated root, README or git state was edited. The pre-existing untracked handoff was left untouched. Audit probes live only in this worktree's `.lake/abi-scratch/` and are removed after validation.

## Refutation and statement checks

All eleven interface declarations (`PGComplexPhase`, `assembleComplex`, `extensionDomain`, `PGExtension`, `ext`, `pgExtension`, `pgWidth`, `pgOscRadius`, `complexAverage`, `complexAverage_real`, `consts`) match the shared signatures after whitespace normalization: whole bodies for definitions/structure, and whole telescopes/conclusions for theorems. The revision-4 `agrees` premise is exactly `w ∈ closure (cylinder d.V d.r0)`. No stronger hP/hperiod/hfreq is substituted. PGData is the upstream packaging of the frozen P-G inputs; hP is joint real analyticity on the closed cylinder, hperiod is only on the open cylinder, and hfreq supplies analyticity on W containing closure V. Other PGData fields are standing source data, not newly introduced extension assumptions.

There is no `KAM.Provider.*` export or frozen seal in scope, so a provider/frozen-type seal probe is not applicable. Instead, the scratch probe copies the three interface theorem statements directly from the shared signatures under fresh names, supplies `by exact ext d`, `by exact complexAverage_real d mu hmu I hI p q hx`, and `by exact consts d`, then checks each with `example : type_of% @original := @audit_copy`. This checks binder order and full elaborated type against the authoritative design, without importing the DRAFT_SORRY P-G theorem.

The hard overlap obligation is paid explicitly. `eventually_eq_zero_of_analyticAt_closure` uses a real open subset meeting a connected analytic ball. `exists_delta_shift_eq` intersects finitely many germ identities then uses compactness to thicken the box. In `exists_pg_delta`, the open packed cylinder uses `(0,mu0)`; positivity of mu0 supplies endpoint density, and shifted closure points remain in the source analyticity set. Thus the argument never assumes periodicity of the arbitrary total source at all exterior real angles.

`tube_glue` compares F and its translate on a ball of radius rho1. The second translated ball stays in the original tube by the three-radius triangle bound. Real-slice identity is applied on the real ball, and the finite-shift identity supplies equality there. `PGTube.valid_diff` bounds lattice-coordinate differences by one using rho≤1/2 and the fundamental angle windows. `PGTube.P_eq` consequently removes the chosen-shift dependence. `exists_valid` uses angle floors to place every extension-domain point in a valid translated box; local valid sets are open, giving holomorphy and joint continuity. `pg_period_closure` extends only closed-cylinder periodicity by continuity and density.

The H0 extension is obtained separately from compact complexification on closure V. `tube_fderiv_bounds` puts the closed ball of radius rhoH/2 inside the larger tube when delta≤rhoH/4; genuine holomorphy justifies both fderiv estimates. `pgExtension_exists` chooses a smaller positive common radius and enlarges bounds by maxima. Choice in `pgExtension` selects this proved witness.

For `complexAverage_real`, every integrand point has fast action in V and each oscillator satisfies p_j²+q_j²<r0². It is in the original cylinder and in extensionDomain (zero distance), so the amended agreement field applies. The slow phase order `(q,p)`, assembly order `(I,phi,p,q)`, radian average factor `(2π)^(-a)`, and frozen secularAverage match. Integrability is also available from PGData.hBNF on this domain (and from extension continuity on the compact angle box); no totalized-integral fallback is used as mathematical input.

For `consts`, `strip_mem_extensionDomain` supplies the actual complex domain. The angle map is `phi=2π theta`; a period-one strip delta/(2π) is available. Taking loss delta/(4π) in `summableWeighted_torusCoeff` yields coefficient radius delta/2 and factor coth(delta/4)^a. LP is enlarged to max(1, factor·MP), chosen before mu/I/x. These are the designed constants and dependencies. General helper statements have explicit hypotheses describing their own objects; none is substituted for a source result without discharging those hypotheses.

## Declaration inventory

Every declaration below is public through the exposed public section. All names are in `KAM.Planetary`. The node column uses the suffix of `bpP:p5:*` or `stepP:p5:*`; multiple helper rows implement portions of a node rather than claiming separate source theorems.

| Node | Declaration (file:line) | Verdict | Reason / note |
|---|---|---|---|
| ext / consts | `ext` (Extension.lean:36) | PASS | Exact revision-4 signature/body for definitions; produced existence, real average attachment, or uniform Fourier bound. |
| ext / consts | `pgExtension` (Extension.lean:38) | PASS | Exact revision-4 signature/body for definitions; produced existence, real average attachment, or uniform Fourier bound. |
| ext / consts | `pgWidth` (Extension.lean:40) | PASS | Exact revision-4 signature/body for definitions; produced existence, real average attachment, or uniform Fourier bound. |
| ext / consts | `pgOscRadius` (Extension.lean:42) | PASS | Exact revision-4 signature/body for definitions; produced existence, real average attachment, or uniform Fourier bound. |
| ext / consts | `complexAverage` (Extension.lean:44) | PASS | Exact revision-4 signature/body for definitions; produced existence, real average attachment, or uniform Fourier bound. |
| ext / consts | `complexAverage_real` (Extension.lean:50) | PASS | Exact revision-4 signature/body for definitions; produced existence, real average attachment, or uniform Fourier bound. |
| ext / consts | `consts` (Extension.lean:91) | PASS | Exact revision-4 signature/body for definitions; produced existence, real average attachment, or uniform Fourier bound. |
| consts | `assembleComplex_real` (ExtensionConsts.lean:31) | PASS | Explicit strip inclusion and 2π rescaling; coefficient radius delta/2 and coth(delta/4)^a factor. |
| consts | `strip_mem_extensionDomain` (ExtensionConsts.lean:38) | PASS | Explicit strip inclusion and 2π rescaling; coefficient radius delta/2 and coth(delta/4)^a factor. |
| consts | `differentiable_assembleComplex_smul` (ExtensionConsts.lean:94) | PASS | Explicit strip inclusion and 2π rescaling; coefficient radius delta/2 and coth(delta/4)^a factor. |
| consts | `assembleComplex_shift` (ExtensionConsts.lean:104) | PASS | Explicit strip inclusion and 2π rescaling; coefficient radius delta/2 and coth(delta/4)^a factor. |
| consts | `PGExtension.angle_periodic` (ExtensionConsts.lean:119) | PASS | Explicit strip inclusion and 2π rescaling; coefficient radius delta/2 and coth(delta/4)^a factor. |
| consts | `PGExtension.summable_torus` (ExtensionConsts.lean:128) | PASS | Explicit strip inclusion and 2π rescaling; coefficient radius delta/2 and coth(delta/4)^a factor. |
| ext | `PGComplexPhase` (ExtensionDefs.lean:31) | PASS | Exact revision-4 carrier, formula, domain, or produced witness; closed-cylinder agreement retained. |
| ext | `assembleComplex` (ExtensionDefs.lean:33) | PASS | Exact revision-4 carrier, formula, domain, or produced witness; closed-cylinder agreement retained. |
| ext | `extensionDomain` (ExtensionDefs.lean:36) | PASS | Exact revision-4 carrier, formula, domain, or produced witness; closed-cylinder agreement retained. |
| ext | `PGExtension` (ExtensionDefs.lean:41) | PASS | Exact revision-4 carrier, formula, domain, or produced witness; closed-cylinder agreement retained. |
| ext-H0 / ext | `tube_fderiv_bounds` (ExtensionExists.lean:30) | PASS | Compact H0 complexification; closed-ball Cauchy bounds; smaller common delta; no added source premise. |
| ext-H0 / ext | `exists_H0_tube` (ExtensionExists.lean:53) | PASS | Compact H0 complexification; closed-ball Cauchy bounds; smaller common delta; no added source premise. |
| ext-H0 / ext | `pgExtension_exists` (ExtensionExists.lean:61) | PASS | Compact H0 complexification; closed-ball Cauchy bounds; smaller common delta; no added source premise. |
| ext-loc | `packVec` (ExtensionPack.lean:29) | PASS | Coordinate packing/unpacking, linearity, norm control or regularity; purely algebraic/typing helper. |
| ext-loc | `packVec_zero` (ExtensionPack.lean:32) | PASS | Coordinate packing/unpacking, linearity, norm control or regularity; purely algebraic/typing helper. |
| ext-loc | `packVec_fst` (ExtensionPack.lean:35) | PASS | Coordinate packing/unpacking, linearity, norm control or regularity; purely algebraic/typing helper. |
| ext-loc | `packVec_snd` (ExtensionPack.lean:39) | PASS | Coordinate packing/unpacking, linearity, norm control or regularity; purely algebraic/typing helper. |
| ext-loc | `unpackL` (ExtensionPack.lean:44) | PASS | Coordinate packing/unpacking, linearity, norm control or regularity; purely algebraic/typing helper. |
| ext-loc | `unpackL_packVec` (ExtensionPack.lean:49) | PASS | Coordinate packing/unpacking, linearity, norm control or regularity; purely algebraic/typing helper. |
| ext-loc | `packVec_unpackL` (ExtensionPack.lean:55) | PASS | Coordinate packing/unpacking, linearity, norm control or regularity; purely algebraic/typing helper. |
| ext-loc | `packVec_sub` (ExtensionPack.lean:66) | PASS | Coordinate packing/unpacking, linearity, norm control or regularity; purely algebraic/typing helper. |
| ext-loc | `realInclusion_packVec` (ExtensionPack.lean:74) | PASS | Coordinate packing/unpacking, linearity, norm control or regularity; purely algebraic/typing helper. |
| ext-loc | `norm_packVec_zero_le` (ExtensionPack.lean:83) | PASS | Coordinate packing/unpacking, linearity, norm control or regularity; purely algebraic/typing helper. |
| ext-loc | `differentiable_packVec_sub` (ExtensionPack.lean:94) | PASS | Coordinate packing/unpacking, linearity, norm control or regularity; purely algebraic/typing helper. |
| ext-loc | `continuous_packVec_sub` (ExtensionPack.lean:105) | PASS | Coordinate packing/unpacking, linearity, norm control or regularity; purely algebraic/typing helper. |
| ext-loc | `continuous_packVec_real` (ExtensionPack.lean:116) | PASS | Coordinate packing/unpacking, linearity, norm control or regularity; purely algebraic/typing helper. |
| ext-glue / ext-per | `eventually_eq_zero_of_analyticAt_closure` (ExtensionPeriodic.lean:31) | PASS | Open-set analytic identity, finite-shift uniform thickening, or real-slice continuation; explicit helper premises discharged at use. |
| ext-glue / ext-per | `exists_delta_shift_eq` (ExtensionPeriodic.lean:44) | PASS | Open-set analytic identity, finite-shift uniform thickening, or real-slice continuation; explicit helper premises discharged at use. |
| ext-glue / ext-per | `mem_actionNbhd_iff` (ExtensionPeriodic.lean:68) | PASS | Open-set analytic identity, finite-shift uniform thickening, or real-slice continuation; explicit helper premises discharged at use. |
| ext-glue / ext-per | `tube_glue` (ExtensionPeriodic.lean:72) | PASS | Open-set analytic identity, finite-shift uniform thickening, or real-slice continuation; explicit helper premises discharged at use. |
| ext-per | `PGTube.exists_valid` (ExtensionProps.lean:28) | PASS | Valid shift existence or local/periodic/bounded/real properties; source agreement confined to closed cylinder. |
| ext-per | `PGTube.P_bound` (ExtensionProps.lean:59) | PASS | Valid shift existence or local/periodic/bounded/real properties; source agreement confined to closed cylinder. |
| ext-per | `PGTube.P_periodic` (ExtensionProps.lean:66) | PASS | Valid shift existence or local/periodic/bounded/real properties; source agreement confined to closed cylinder. |
| ext-per | `PGTube.P_holo` (ExtensionProps.lean:82) | PASS | Valid shift existence or local/periodic/bounded/real properties; source agreement confined to closed cylinder. |
| ext-per | `PGTube.P_continuous` (ExtensionProps.lean:97) | PASS | Valid shift existence or local/periodic/bounded/real properties; source agreement confined to closed cylinder. |
| ext-per | `pg_period_closure` (ExtensionProps.lean:112) | PASS | Valid shift existence or local/periodic/bounded/real properties; source agreement confined to closed cylinder. |
| ext-per | `PGTube.P_agrees` (ExtensionProps.lean:134) | PASS | Valid shift existence or local/periodic/bounded/real properties; source agreement confined to closed cylinder. |
| ext-loc | `pgWbox` (ExtensionTube.lean:31) | PASS | Compact fundamental box, genuine packed source, domain topology or cylinder/closure inclusion. |
| ext-loc | `pgX` (ExtensionTube.lean:36) | PASS | Compact fundamental box, genuine packed source, domain topology or cylinder/closure inclusion. |
| ext-loc | `pgF` (ExtensionTube.lean:40) | PASS | Compact fundamental box, genuine packed source, domain topology or cylinder/closure inclusion. |
| ext-loc | `pgF_packVec` (ExtensionTube.lean:43) | PASS | Compact fundamental box, genuine packed source, domain topology or cylinder/closure inclusion. |
| ext-loc | `continuous_blockFast_real` (ExtensionTube.lean:47) | PASS | Compact fundamental box, genuine packed source, domain topology or cylinder/closure inclusion. |
| ext-loc | `continuous_blockSlow_real` (ExtensionTube.lean:52) | PASS | Compact fundamental box, genuine packed source, domain topology or cylinder/closure inclusion. |
| ext-loc | `isClosed_pgWbox` (ExtensionTube.lean:57) | PASS | Compact fundamental box, genuine packed source, domain topology or cylinder/closure inclusion. |
| ext-loc | `isBounded_pgWbox` (ExtensionTube.lean:69) | PASS | Compact fundamental box, genuine packed source, domain topology or cylinder/closure inclusion. |
| ext-loc | `isCompact_pgWbox` (ExtensionTube.lean:98) | PASS | Compact fundamental box, genuine packed source, domain topology or cylinder/closure inclusion. |
| ext-loc | `isCompact_pgX` (ExtensionTube.lean:101) | PASS | Compact fundamental box, genuine packed source, domain topology or cylinder/closure inclusion. |
| ext-loc | `mem_actionNbhd_mono` (ExtensionTube.lean:104) | PASS | Compact fundamental box, genuine packed source, domain topology or cylinder/closure inclusion. |
| ext-loc | `isOpen_actionNbhd` (ExtensionTube.lean:108) | PASS | Compact fundamental box, genuine packed source, domain topology or cylinder/closure inclusion. |
| ext-loc | `cylinder_sub_fastShift` (ExtensionTube.lean:116) | PASS | Compact fundamental box, genuine packed source, domain topology or cylinder/closure inclusion. |
| ext-loc | `closure_cylinder_sub_fastShift` (ExtensionTube.lean:121) | PASS | Compact fundamental box, genuine packed source, domain topology or cylinder/closure inclusion. |
| ext-loc | `isOpen_cylinder` (ExtensionTube.lean:128) | PASS | Compact fundamental box, genuine packed source, domain topology or cylinder/closure inclusion. |
| ext-loc | `pgWbox_subset_closure` (ExtensionTube.lean:145) | PASS | Compact fundamental box, genuine packed source, domain topology or cylinder/closure inclusion. |
| ext-loc / ext-glue | `pgShift` (ExtensionTubeData.lean:31) | PASS | Packed open/closed source domains and finite shifts; tube witness constructed from hP/hperiod and compactness. |
| ext-loc / ext-glue | `pgK` (ExtensionTubeData.lean:35) | PASS | Packed open/closed source domains and finite shifts; tube witness constructed from hP/hperiod and compactness. |
| ext-loc / ext-glue | `pgG` (ExtensionTubeData.lean:40) | PASS | Packed open/closed source domains and finite shifts; tube witness constructed from hP/hperiod and compactness. |
| ext-loc / ext-glue | `packVec_mem_pgK` (ExtensionTubeData.lean:44) | PASS | Packed open/closed source domains and finite shifts; tube witness constructed from hP/hperiod and compactness. |
| ext-loc / ext-glue | `pgX_subset_pgK` (ExtensionTubeData.lean:49) | PASS | Packed open/closed source domains and finite shifts; tube witness constructed from hP/hperiod and compactness. |
| ext-loc / ext-glue | `analyticOnNhd_pgF` (ExtensionTubeData.lean:53) | PASS | Packed open/closed source domains and finite shifts; tube witness constructed from hP/hperiod and compactness. |
| ext-loc / ext-glue | `isOpen_pgG` (ExtensionTubeData.lean:58) | PASS | Packed open/closed source domains and finite shifts; tube witness constructed from hP/hperiod and compactness. |
| ext-loc / ext-glue | `pgX_subset_closure_pgG` (ExtensionTubeData.lean:62) | PASS | Packed open/closed source domains and finite shifts; tube witness constructed from hP/hperiod and compactness. |
| ext-loc / ext-glue | `pgShiftSet` (ExtensionTubeData.lean:75) | PASS | Packed open/closed source domains and finite shifts; tube witness constructed from hP/hperiod and compactness. |
| ext-loc / ext-glue | `pgShift_mem` (ExtensionTubeData.lean:78) | PASS | Packed open/closed source domains and finite shifts; tube witness constructed from hP/hperiod and compactness. |
| ext-loc / ext-glue | `packVec_sub_pgShift` (ExtensionTubeData.lean:84) | PASS | Packed open/closed source domains and finite shifts; tube witness constructed from hP/hperiod and compactness. |
| ext-loc / ext-glue | `exists_pg_delta` (ExtensionTubeData.lean:88) | PASS | Packed open/closed source domains and finite shifts; tube witness constructed from hP/hperiod and compactness. |
| ext-loc / ext-glue | `PGTube` (ExtensionTubeData.lean:114) | PASS | Packed open/closed source domains and finite shifts; tube witness constructed from hP/hperiod and compactness. |
| ext-loc / ext-glue | `pgTube_exists` (ExtensionTubeData.lean:129) | PASS | Packed open/closed source domains and finite shifts; tube witness constructed from hP/hperiod and compactness. |
| ext-per | `fastShift_add` (ExtensionTubeP.lean:30) | PASS | Periodized extension; valid cells differ by coordinate shifts at most one; hglue proves independence of choice. |
| ext-per | `fastShift_fst_castAdd` (ExtensionTubeP.lean:39) | PASS | Periodized extension; valid cells differ by coordinate shifts at most one; hglue proves independence of choice. |
| ext-per | `realInclusion_pgShift` (ExtensionTubeP.lean:43) | PASS | Periodized extension; valid cells differ by coordinate shifts at most one; hglue proves independence of choice. |
| ext-per | `PGTube.Valid` (ExtensionTubeP.lean:49) | PASS | Periodized extension; valid cells differ by coordinate shifts at most one; hglue proves independence of choice. |
| ext-per | `PGTube.P` (ExtensionTubeP.lean:56) | PASS | Periodized extension; valid cells differ by coordinate shifts at most one; hglue proves independence of choice. |
| ext-per | `PGTube.valid_angle` (ExtensionTubeP.lean:60) | PASS | Periodized extension; valid cells differ by coordinate shifts at most one; hglue proves independence of choice. |
| ext-per | `PGTube.valid_diff` (ExtensionTubeP.lean:78) | PASS | Periodized extension; valid cells differ by coordinate shifts at most one; hglue proves independence of choice. |
| ext-per | `PGTube.P_eq` (ExtensionTubeP.lean:93) | PASS | Periodized extension; valid cells differ by coordinate shifts at most one; hglue proves independence of choice. |

## Definition classification

All 20 new non-theorem declarations are classified here (structures counted once, including their fields).

- `PGComplexPhase`, `assembleComplex`: genuine finite complex coordinate carrier and assembly on their entire carriers, with the frozen position/momentum order.
- `extensionDomain`: the designed witness-distance complex tube around the real skeleton, with unrestricted real fast angles and the real oscillator box of radius r0/2. No empty-set infDist fallback.
- `PGExtension`: produced witness specification; all analytical fields are proved by pgExtension_exists, not additional source hypotheses.
- `packVec`, `unpackL`: genuine coordinate insertion and inverse continuous linear projection. Inverse identities are proved.
- `pgWbox`, `pgX`: actual fundamental real angle box and packed compact parameter/phase box.
- `pgF`: the literal total source pulled back by unpackL, not an auxiliary model.
- `pgShift`, `pgK`, `pgG`, `pgShiftSet`: literal packed lattice shifts, closed source locus, open source locus, and finite neighboring shifts. Their membership/topology premises are proved from PGData.
- `PGTube`: intermediate produced extension witness. Its hglue field is proved in pgTube_exists, not assumed at the P-G boundary.
- `PGTube.Valid`: actual membership of a translated packed point in the proved holomorphic tube.
- `PGTube.P`: chosen valid local value, otherwise zero. The zero fallback is outside the valid union; exists_valid proves it is unreachable on every constrained theorem domain. P_eq proves all valid choices agree. This is legitimate total extension, with no theorem relying on junk values.
- `pgExtension`: choice from proved Nonempty; `pgWidth`, `pgOscRadius`: literal positive designed radii, depending only on d.
- `complexAverage`: literal normalized angular Bochner integral. Its intended analytical uses and attachment have explicit constrained domains; no off-domain analytic or source-value guarantee is asserted.

## Source / blueprint notes and limits

1. **Previously identified blueprint defect, retained as a note.** `blueprint-P/parts/p5-pg-assembly.tex:30` says “$\tilde P=P$ at real points”; `docs/graph/P/packets/P-p5.nodes.md:36` repeats “P~ = P at real points”. Literally over all X_delta this is false: joint analyticity near the closed cylinder permits angle-dependent neighborhoods and arbitrary total values outside them, whereas periodic extension plus exterior agreement would force source periodicity on a uniform exterior collar. Revision 4 (design lines 1986–2002; design audit 4 R4-S1) expressly restricts agreement to closure(cylinder V r0). The implementation follows that correction. Line 35's phrase “agreement at real points” on translated overlaps needs analytic germ identity; ExtensionPeriodic supplies it. No frozen or pinned-paper erratum is inferred from this project-blueprint defect.
2. **Domain reading.** The blueprint's line 30 separates real-distance and imaginary-coordinate bounds; the design and Lean use a complex sup-norm witness-distance tube. These need not be the identical set for the same numeric delta (complex coordinate norm combines real and imaginary parts). This is an inherited design representation: a fixed shrink compares the neighborhoods; the independently checked interface here is the literal approved design tube. No equality of these two set presentations is claimed.
3. **Scope.** The facade exports the exact designed pointwise uniform weighted Fourier bound. It does not by itself certify all later Banach-valued coefficient norm interfaces, jets, reflection/reality, averaging, KAM assembly, frozen P-G, or any campaign closure. Those remain their own packages. No new source premise, erratum or deviation was introduced by this audit.

## Independent hygiene and validation

Validation receipts follow below. All Lean/Lake commands are serialized within this audit, with `LEAN_NUM_THREADS=1` and `nice -n 5`; the build uses the required campaign compile gate. Waiting for its slot is expected. No heartbeat, recursion or synthesis overrides, clean, update or cache retrieval were used.

1. Targeted build (exit **0**):

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5ex KAM.Planetary.PGAssembly.Extension
[inp-gate] slot 2 acquired 10:08:19 for KAM.Planetary.PGAssembly.Extension
Build completed successfully (9097 jobs).
```

2. Signature/type probe and axioms (exit **0**, 0 errors, 0 warnings):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/p5ex-audit.lean
```

The probe contained the three fresh typed signature applications described above and `#print axioms` for all 62 public theorems. Exact axiom output:

```text
'KAM.Planetary.ext' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.complexAverage_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.consts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.assembleComplex_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.strip_mem_extensionDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiable_assembleComplex_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.assembleComplex_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PGExtension.angle_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PGExtension.summable_torus' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tube_fderiv_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.exists_H0_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgExtension_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.packVec_zero' depends on axioms: [propext, Quot.sound]
'KAM.Planetary.packVec_fst' depends on axioms: [propext, Quot.sound]
'KAM.Planetary.packVec_snd' depends on axioms: [propext, Quot.sound]
'KAM.Planetary.unpackL_packVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.packVec_unpackL' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.packVec_sub' depends on axioms: [propext, Quot.sound]
'KAM.Planetary.realInclusion_packVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_packVec_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiable_packVec_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuous_packVec_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuous_packVec_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.eventually_eq_zero_of_analyticAt_closure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.exists_delta_shift_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mem_actionNbhd_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tube_glue' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PGTube.exists_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PGTube.P_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PGTube.P_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PGTube.P_holo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PGTube.P_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pg_period_closure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PGTube.P_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgF_packVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuous_blockFast_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuous_blockSlow_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isClosed_pgWbox' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isBounded_pgWbox' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isCompact_pgWbox' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isCompact_pgX' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mem_actionNbhd_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_actionNbhd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.cylinder_sub_fastShift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.closure_cylinder_sub_fastShift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_cylinder' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgWbox_subset_closure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.packVec_mem_pgK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgX_subset_pgK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.analyticOnNhd_pgF' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_pgG' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgX_subset_closure_pgG' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgShift_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.packVec_sub_pgShift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.exists_pg_delta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgTube_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fastShift_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fastShift_fst_castAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.realInclusion_pgShift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PGTube.valid_angle' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PGTube.valid_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PGTube.P_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay (one invocation, exit **0**):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.Extension KAM.Planetary.PGAssembly.ExtensionConsts KAM.Planetary.PGAssembly.ExtensionDefs KAM.Planetary.PGAssembly.ExtensionExists KAM.Planetary.PGAssembly.ExtensionPack KAM.Planetary.PGAssembly.ExtensionPeriodic KAM.Planetary.PGAssembly.ExtensionProps KAM.Planetary.PGAssembly.ExtensionTube KAM.Planetary.PGAssembly.ExtensionTubeData KAM.Planetary.PGAssembly.ExtensionTubeP
replaying KAM.Planetary.PGAssembly.ExtensionTubeP
replaying KAM.Planetary.PGAssembly.ExtensionTubeData
replaying KAM.Planetary.PGAssembly.ExtensionTube
replaying KAM.Planetary.PGAssembly.ExtensionProps
replaying KAM.Planetary.PGAssembly.ExtensionPeriodic
replaying KAM.Planetary.PGAssembly.ExtensionPack
replaying KAM.Planetary.PGAssembly.ExtensionExists
replaying KAM.Planetary.PGAssembly.ExtensionDefs
replaying KAM.Planetary.PGAssembly.ExtensionConsts
replaying KAM.Planetary.PGAssembly.Extension
```

4. Full source lint (exit **1**, exclusively the brief's permitted stale generated-root exception):

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (530 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No line over 100 characters in the ten audited files; counts are Extension 113, ExtensionConsts 158, ExtensionDefs 68, ExtensionExists 96, ExtensionPack 127, ExtensionPeriodic 121, ExtensionProps 148, ExtensionTube 182, ExtensionTubeData 150, ExtensionTubeP 112 (1275 total). Each has its copyright header, module command, public imports, module docstring and exposed public section. Forbidden-token and option scan finds no sorry/admit/axiom/unsafe/opaque/EuclideanSpace or set_option in scope.

5. Import and protected-path checks:

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
warning: inp...HEAD: multiple merge bases, using d59d3373956033408a4dc55abe782d89092254f3
```

Exit **0**, no diff. A recursive scan of the facade's 51 KAM import-closure modules finds **0 provider-import edges** and **0 frozen-theorem-import edges**. Imported frozen modules are definitions, not DRAFT_SORRY anchors; no SEALED-theorem exception is needed. In particular the frozen properlyDegenerateKAM theorem was read as source authority, never imported into the probes or production package.

6. Final integrity: `git diff --check` and `git diff --no-index --check /dev/null docs/tracks/P/audits/P5-EX-audit-1.md` exit **0**. Report has 82 declaration rows, balanced fenced blocks, no trailing whitespace, and a terminal newline. Audit-created probe, inventory and logs were removed from `.lake/abi-scratch/` after their receipts were incorporated here. Final status contains only this report and the pre-existing untracked handoff; tracked files remain unchanged.

Final disposition: **PASS WITH NOTES** for this infrastructure package under the expressly amended revision-4 design. There are no unresolved implementation blockers found in the audited files. The blueprint/graph agreement wording and inherited domain presentation note above remain reported source-model qualifications; this verdict does not seal a frozen theorem.
