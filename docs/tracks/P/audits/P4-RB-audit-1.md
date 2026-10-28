# P4-RB independent package audit 1

Overall verdict: **PASS WITH NOTES** for P4-RB's internal helper package. No mathematical or statement-fidelity defect was found in the six audited modules. This verdict does not seal an anchor or prove the full two-scale measure theorem.

Audited HEAD: `be13c58bac4fe1ed59d899c98f6c4c8cec175e95`; comparison ref `inp`: `5991245cabc06e69ec900cb6006b45f72cc85eb0`. `git diff inp...HEAD` adds exactly six Lean files, 1,013 lines. Scope is exclusively `KAM/Planetary/PGMeasure/ResonanceLarge.lean` and its five submodules, as required by AUDIT FOCUS. The report is in the explicitly requested package worktree, overriding the generic brief's main-worktree destination.

Read AGENTS.md, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the P4-RB handoff, P45 design rows P4-RB/P4-M and resonance proof plan, design audits 1–4 (audit 4 from the main inp worktree), shared `/root/code/KAM-inp/.drafts/design/P45Signatures.lean`, blueprint-P Part 4, track-P statement, frozen P-G anchor and relevant frozen definitions, and imported setting/lattice/Tonelli interfaces. The local design is revision 3; audit 4 concerns the later P5 extension agreement repair and does not change S4 or the P4-RB interface. Historical draft-status prose is superseded by DECISIONS D20; no new owner approval is inferred from it.

## Anchor disposition and scope

| Anchor / contract | Verdict | Meaning |
|---|---|---|
| P4-RB internal helpers | PASS WITH NOTES | Correct large-mode structure, measurable slow sections, per-mode estimate, and summed frequency-coordinate estimate; validation below. |
| `two_scale_diophantine_measure` (P4-M signed design declaration) | Not delivered by this package | No restatement or weakening. Coordinate transfer, identification of the resonance union, and assembly remain with P4-M. |
| Frozen P-G `KAM.Planetary.properlyDegenerateKAM` | Not seal-ready on P4-RB evidence | Existing `DRAFT_SORRY` anchor remains unchanged; this package has no provider export and makes no anchor closure claim. |

Provider/frozen-type equality and literal seal-body probes are **not applicable**: no provider or frozen theorem is delivered by the scoped diff. Importing the unrelated draft P-G theorem to manufacture such a test would not audit these helpers. Consumer probes instead check the exact large-mode split and the literal frequency sum after applying Phi.

## Mathematical and consumer review

All new theorem premises are source S4 data, typing data, ordinary memberships/positivity, or explicitly scoped hypotheses of a generic helper. In particular, the pairwise-diameter premise of the generic Tonelli helper is discharged by `largeSection_line_diam`; it is not assumed by the package's final estimate. No conclusion-shaped field, instance, hidden resonance estimate, convexity of the core, or injectivity of the full perturbed frequency is assumed.

1. `largeModes` is exactly the strict complement of K_A within modes with nonzero fast block: `mu*LN*Lg*l1 k > norm(kFast k)/2`. The Pi norm of the real cast is the integer block max norm. Integrality gives `1 ≤ norm(kFast k)`. The smallness bound is exactly S4 with `M=2*b*LN*LB`. The four structure conclusions prove the cutoff, slow-block dominance, `l1 k < 2*b*norm(kSlow k)`, and the cancellation bound. The separate `one_le_inv_two_mul` proves the cutoff is at least one.
2. `freqCore` uses the actual image `fastFrequency H0 '' core`. `freqCore_spec` derives both core membership of `g y` and the inverse identity from `hinv`, with `core ⊆ V ⊆ closure V ⊆ W`. Thus no theorem uses arbitrary off-image values of the total inverse. `pullFreq` retains the full literal `freq` and real offset, and `pullFreq_eq` is an algebraic block decomposition.
3. Borelness is proved rather than added: analytic H0 gives continuity of its derivative and compactness of the core image; N1 and N2 give joint continuity of the fast part on the bounded slow domain. Evaluating the affine slow frequency at zero and `lambda0*e_j` gives continuity of Omega and beta entries from N1. Slow affine dependence then gives continuity on all slow coordinates. No differentiability of the arbitrary total coefficients outside the stated carrier is required.
4. N3 supplies a coordinate covering of every resonant point. Holding fast coordinates and all but one slow coordinate fixed, the affine slow increment is `mu*s*(beta^T*kSlow)_j`. N2 bounds the fast increment by `mu*LN*sum(abs(kFast))*abs(s)`; structure makes this at most half the slow lower bound. Two resonant values differ by less than `2*alpha`, giving diameter at most `4*LB*alpha/(mu*norm(kSlow))`. This argument compares endpoints only and does not require connected or convex slices.
5. The coordinate Tonelli argument splits off `Fin.natAdd a j` by a volume-preserving measurable equivalence. The remaining box product is exactly `(2*Ry)^a*(2*lambda)^(b-1)`, including `b=1`. Summation over j yields coefficient `8*b^2*LB*alpha1/mu` multiplying the shifted lattice weight and that box product.
6. The real cutoff is `m=(2*mu*LN*Lg)^(-1)`, with `m≥1`. Summability over the tail is established before converting the real sum to ENNReal. The inherited `lattice_tail` is applied with exponent tau; the weight being summed has exponent `-(tau+1)`. Since `2/m=4*mu*LN*Lg`, the final powers and coefficient are exactly the blueprint's second entry of the max defining c1, before the image factor and core normalization.

For `n=a+b`, `CT=2*3^(n-1)/(tau+1-n)`, the exported bound is

```text
volume (union_{k in largeModes} resonanceSet d mu Q k (alpha1/l1(k)^tau))
  ≤ ofReal(4*b^2*LB*(2*Ry)^a*CT*(4*LN*Lg)^(tau+1-n)
             *alpha1*mu^(tau-n)/lambda*(2*lambda)^b).
```

P4-M receives exactly its signed hypotheses (`mu ∈ Ioc 0 mu1`, `0<lambda≤lambda0`, Q measurable in the open box, `alpha1>0`). An elaborated probe confirms that pulling the frequency sum forward by `Phi(J)=append(fastFrequency H0 (blockFast J),blockSlow J)` gives the literal original sum on core actions; another confirms the exact K_A complement. `l1 k` is definitionally the denominator sum in `resonanceBad`. P4-M still has to establish the relevant image/set inclusion, apply the product-inverse Lipschitz measure factor `Lg^(a+b)`, and incorporate `1/(volume core).toReal` into c1. Those are explicit assembly obligations, not hypotheses silently charged to P4-RB. Full P4-M application was not compiled because that consumer is outside this package.

## Declaration-by-declaration audit

All names below have prefix `KAM.Planetary.`. Paths are relative to `KAM/Planetary/PGMeasure/`. Auxiliary identities are support lemmas for the cited node; they do not claim to replace a signed source theorem.

| Node / role | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| stepP:p4:dm-B | `resonanceSet_subset_largeSection` (ResonanceLarge.lean:36) | PASS | N3 and a maximizing coordinate give the cover; even valid beyond large modes. |
| lattice-tail support | `latticeWeight_succ_eq` (ResonanceLarge.lean:54) | PASS | Positive l1 justifies rpow algebra and inversion. |
| stepP:p4:dm-B | `volume_resonanceSet_large_le` (ResonanceLarge.lean:62) | PASS | Sums b sections; exact 8*b^2 per-mode coefficient. |
| stepP:p4:dm-Bstruct (i) | `one_le_inv_two_mul` (ResonanceLarge.lean:109) | PASS | Derives cutoff ≥1 from S4 smallness. |
| bpP:p4:lattice-tail support | `summable_latticeWeight_tail` (ResonanceLarge.lean:129) | PASS | Valid stronger summability range tau+1>n; injective tail restriction. |
| stepP:p4:dm-B / lt-b | `large_modes_measure_le` (ResonanceLarge.lean:148) | PASS | Exact frequency-coordinate final display; no extra source premise. |
| stepP:p4:dm-y | `freqCore` (ResonanceLarge/Frequency.lean:31) | PASS | Actual compact-core frequency image. |
| stepP:p4:dm-y | `fastPart` (ResonanceLarge/Frequency.lean:34) | PASS | Literal fast projection of freq. |
| stepP:p4:dm-y | `pullFreq` (ResonanceLarge/Frequency.lean:38) | PASS | Literal full dot product after inverse substitution. |
| stepP:p4:dm-y | `resonanceSet` (ResonanceLarge/Frequency.lean:43) | PASS | Full threshold set on freqCore × Q. |
| dm-y coordinate support | `blockFast_append` (ResonanceLarge/Frequency.lean:47) | PASS | Exact fast projection identity. |
| dm-y coordinate support | `blockSlow_append` (ResonanceLarge/Frequency.lean:50) | PASS | Exact slow projection identity. |
| stepP:p4:dm-y | `pullFreq_eq` (ResonanceLarge/Frequency.lean:53) | PASS | Algebraic full fast/slow decomposition; no regularity premise. |
| stepP:p4:dm-y | `freqCore_spec` (ResonanceLarge/Frequency.lean:67) | PASS | Inverse identities derived only on the actual image. |
| stepP:p4:dm-y | `norm_le_Ry_of_mem_freqCore` (ResonanceLarge/Frequency.lean:74) | PASS | Inherited Ry bound applies by core inclusion. |
| dm-y coordinate support | `norm_blockFast_le` (ResonanceLarge/Frequency.lean:81) | PASS | Pi max-norm projection contraction. |
| dm-y coordinate support | `norm_blockSlow_le` (ResonanceLarge/Frequency.lean:84) | PASS | Pi max-norm projection contraction. |
| stepP:p4:dm-y | `dist_g_le` (ResonanceLarge/Frequency.lean:87) | PASS | Restricts the supplied inverse Lipschitz bound. |
| stepP:p4:dm-y | `continuousOn_g` (ResonanceLarge/Frequency.lean:93) | PASS | Continuity derived from the bound, not assumed. |
| stepP:p4:dm-y / N1 | `fast_lip_y` (ResonanceLarge/Frequency.lean:98) | PASS | Correct 1+mu*LN*Lg bound for the full fast part. |
| stepP:p4:dm-B / N2 | `fast_lip_xi` (ResonanceLarge/Frequency.lean:116) | PASS | Literal N2 specialization with mu retained. |
| stepP:p4:dm-y / N1 | `slow_lip_y` (ResonanceLarge/Frequency.lean:121) | PASS | Correct LN*Lg bound for the unscaled slow frequency. |
| Borelness support | `beta_entry` (ResonanceLarge/Frequency.lean:132) | PASS | Affine finite-difference identity, arbitrary coefficients. |
| Borelness / N1 | `beta_lip_y` (ResonanceLarge/Frequency.lean:139) | PASS | Two evaluations give 2*LN*Lg/lambda0; lambda0>0 supplied by S4. |
| bpP:p4:ext-tonelli | `volume_le_of_line_diam` (ResonanceLarge/LineSlice.lean:27) | PASS | Generic nonnegative box/diameter helper; proved by coordinate Tonelli. |
| Borelness / dm-y | `sliceDomain` (ResonanceLarge/Measurable.lean:30) | PASS | Exact image-core and Q carrier. |
| Borelness support | `continuous_blockFast` (ResonanceLarge/Measurable.lean:33) | PASS | Continuous coordinate projection. |
| Borelness support | `continuous_blockSlow` (ResonanceLarge/Measurable.lean:36) | PASS | Continuous coordinate projection. |
| Borelness / dm-y | `continuousOn_fastFrequency` (ResonanceLarge/Measurable.lean:39) | PASS | Analytic H0 and open W imply continuous derivative. |
| Borelness / dm-y | `isCompact_freqCore` (ResonanceLarge/Measurable.lean:45) | PASS | Continuous image of the actual compact core. |
| Borelness / dm-y | `measurableSet_sliceDomain` (ResonanceLarge/Measurable.lean:49) | PASS | Compact image and measurable Q; no missing domain measurability. |
| Borelness support | `measurableSet_inter_preimage` (ResonanceLarge/Measurable.lean:54) | PASS | Valid generic subtype proof for continuous-on preimages. |
| Borelness / N1 | `continuousOn_beta_entry` (ResonanceLarge/Measurable.lean:66) | PASS | Derived Lipschitz estimate gives continuity on freqCore. |
| Borelness / N1 | `continuousOn_slowFrequency` (ResonanceLarge/Measurable.lean:75) | PASS | Affine formula extends continuity to all slow coordinates. |
| Borelness / N1,N2 | `continuousOn_fastPart` (ResonanceLarge/Measurable.lean:101) | PASS | Joint continuity via separate Lipschitz estimates on bounded Q. |
| Borelness / dm-y | `continuousOn_pullFreq` (ResonanceLarge/Measurable.lean:134) | PASS | Finite sum of the proved continuous pieces. |
| stepP:p4:dm-B | `colCoeff` (ResonanceLarge/Measurable.lean:148) | PASS | Actual real transposed matrix coefficient. |
| stepP:p4:dm-B | `colCoeff_eq` (ResonanceLarge/Measurable.lean:151) | PASS | Exact transpose.mulVec identity. |
| Borelness / dm-B | `continuousOn_colCoeff` (ResonanceLarge/Measurable.lean:156) | PASS | Finite continuous coefficient sum. |
| stepP:p4:dm-B | `largeSection` (ResonanceLarge/Sections.lean:34) | PASS | Resonance set intersected with the precise N3 coordinate condition. |
| dm-B box support | `norm_le_of_mem_actionShell` (ResonanceLarge/Sections.lean:38) | PASS | Open-box membership implies the required weak norm bound. |
| Borelness / dm-B | `measurableSet_largeSection` (ResonanceLarge/Sections.lean:45) | PASS | Derives section measurability from continuous-on preimages. |
| stepP:p4:dm-B | `slow_diff_single` (ResonanceLarge/Sections.lean:63) | PASS | Exact affine slow increment; real offset cancels. |
| dm-B coordinate support | `castAdd_ne_natAdd` (ResonanceLarge/Sections.lean:71) | PASS | Disjoint fast and slow index blocks. |
| stepP:p4:dm-B | `largeSection_line_diam` (ResonanceLarge/Sections.lean:79) | PASS | N2 cancellation with N3 and dominance; alpha positivity follows from membership. |
| dm-B box support | `boxRadius` (ResonanceLarge/Sections.lean:204) | PASS | Literal fast/slow radii, no fallback. |
| stepP:p4:dm-B | `prod_erase_boxRadius` (ResonanceLarge/Sections.lean:207) | PASS | Exact product excluding one slow coordinate; b=1 covered. |
| stepP:p4:dm-B | `volume_largeSection_le` (ResonanceLarge/Sections.lean:224) | PASS | Exact diameter times complementary box volume. |
| stepP:p4:dm-Bstruct | `kFast` (ResonanceLarge/Structure.lean:30) | PASS | Real cast of the actual fast integer block. |
| stepP:p4:dm-Bstruct | `kSlow` (ResonanceLarge/Structure.lean:33) | PASS | Real cast of the actual slow integer block. |
| stepP:p4:dm-Bstruct | `l1` (ResonanceLarge/Structure.lean:36) | PASS | Actual sum of absolute real casts. |
| stepP:p4:dm-Bstruct | `largeModes` (ResonanceLarge/Structure.lean:39) | PASS | Exact strict K_B condition with nonzero fast block. |
| dm-Bstruct support | `l1_split` (ResonanceLarge/Structure.lean:42) | PASS | Exact block sum splitting. |
| dm-Bstruct support | `sum_abs_le_mul_norm` (ResonanceLarge/Structure.lean:47) | PASS | Correct finite-dimensional l1/max comparison, including n=0. |
| dm-Bstruct support | `l1_nonneg` (ResonanceLarge/Structure.lean:52) | PASS | Nonnegativity of the literal l1 sum. |
| stepP:p4:dm-Bstruct (i) | `one_le_norm_kFast` (ResonanceLarge/Structure.lean:54) | PASS | Integrality and nonzero fast block imply max norm ≥1. |
| stepP:p4:dm-Bstruct (i),(ii) | `large_mode_structure` (ResonanceLarge/Structure.lean:62) | PASS | All four required cutoff/dominance/cancellation outputs. |

## Definition classification

Exactly 12 new definitions, no new abbreviations, structures, instances, axioms, or chosen witness functions:

| Definition | Classification on its whole carrier |
|---|---|
| `kFast` | Coordinate projection followed by integer-to-real cast. |
| `kSlow` | Coordinate projection followed by integer-to-real cast. |
| `l1` | Nonnegative finite l1 sum, including zero. |
| `largeModes` | Set predicate with exactly the prescribed nonzero-fast and strict-size tests, for all scalar parameters. |
| `freqCore` | Actual set image, without a totalized-inverse carrier substitution. |
| `fastPart` | Literal block projection of the imported frequency function. |
| `pullFreq` | Dot product evaluated at `append(g y,xi)`; meaningful as the total supplied function everywhere, used on freqCore where the inverse properties are proved. |
| `resonanceSet` | Actual inverse-coordinate resonance set restricted to freqCore and Q. |
| `sliceDomain` | Exact flat-coordinate product membership predicate. |
| `colCoeff` | Literal real matrix-column contraction, including zero vectors. |
| `largeSection` | Exact intersection defining the coordinate covering; LB divisions are used with LB≥1. |
| `boxRadius` | Constant fast/slow coordinate radii for arbitrary Ry and lambda. |

No newly defined object substitutes a junk/fallback value on a carrier needed by a theorem. The imported derivative-based `freq` is unchanged and every estimate of it follows from S4. Section-wide `@[expose]` is present for all newly defined bodies.

## Hygiene and independent validation

All audit Lean/Lake commands run serially with `LEAN_NUM_THREADS=1` and `nice -n 5`; no resource-budget override, clean, update, cache retrieval, or root regeneration was used. No subagents were used. Ordinary source checks ran without a concurrent audit Lean invocation.

### Targeted build

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p4rb KAM.Planetary.PGMeasure.ResonanceLarge
```

Exit **0**, output:

```text
[inp-gate] slot 2 acquired 09:37:21 for KAM.Planetary.PGMeasure.ResonanceLarge
Build completed successfully (9071 jobs).
```

This is the prescribed targeted build against the existing overlay, not a clean full-library rebuild. There were no build warnings.

### Axioms and consumer probes

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P4RBAudit.lean > /tmp/P4-RB-audit-1-axioms.log 2>&1
```

Exit **0**. The probe imported the facade, issued `#print axioms` for every one of the 45 new public theorems, and elaborated the two consumer bridge examples described above. All 45 lists contain only permitted axioms. Exactly 44 lists are `[propext, Classical.choice, Quot.sound]`; `castAdd_ne_natAdd` has `[propext, Quot.sound]`. No `sorryAx` or other axiom appears. The probe itself produced one nonsemantic deprecation warning for `Set.mem_setOf_eq` (replacement `Set.mem_ofPred_eq`); this is not a production warning and did not affect either example. The temporary probe is removed after validation. Exact axiom output:

```text
'KAM.Planetary.resonanceSet_subset_largeSection' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.latticeWeight_succ_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.volume_resonanceSet_large_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.one_le_inv_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.summable_latticeWeight_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.large_modes_measure_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.blockFast_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.blockSlow_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pullFreq_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.freqCore_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_le_Ry_of_mem_freqCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_blockFast_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_blockSlow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.dist_g_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuousOn_g' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fast_lip_y' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fast_lip_xi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.slow_lip_y' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.beta_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.beta_lip_y' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.volume_le_of_line_diam' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuous_blockFast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuous_blockSlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuousOn_fastFrequency' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isCompact_freqCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.measurableSet_sliceDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.measurableSet_inter_preimage' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuousOn_beta_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuousOn_slowFrequency' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuousOn_fastPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuousOn_pullFreq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.colCoeff_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuousOn_colCoeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_le_of_mem_actionShell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.measurableSet_largeSection' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.slow_diff_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.castAdd_ne_natAdd' depends on axioms: [propext, Quot.sound]
'KAM.Planetary.largeSection_line_diam' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.prod_erase_boxRadius' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.volume_largeSection_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.l1_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sum_abs_le_mul_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.l1_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.one_le_norm_kFast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.large_mode_structure' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Independent kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGMeasure.ResonanceLarge KAM.Planetary.PGMeasure.ResonanceLarge.LineSlice KAM.Planetary.PGMeasure.ResonanceLarge.Structure KAM.Planetary.PGMeasure.ResonanceLarge.Frequency KAM.Planetary.PGMeasure.ResonanceLarge.Measurable KAM.Planetary.PGMeasure.ResonanceLarge.Sections > /tmp/P4-RB-audit-1-kernel.log 2>&1
```

Exit **0**, exact output:

```text
replaying KAM.Planetary.PGMeasure.ResonanceLarge.Measurable
replaying KAM.Planetary.PGMeasure.ResonanceLarge.Structure
replaying KAM.Planetary.PGMeasure.ResonanceLarge.LineSlice
replaying KAM.Planetary.PGMeasure.ResonanceLarge.Frequency
replaying KAM.Planetary.PGMeasure.ResonanceLarge.Sections
replaying KAM.Planetary.PGMeasure.ResonanceLarge
```

One invocation covered all six scoped modules. This is an independent replay receipt, not the prover's report.

### Static hygiene and import quarantine

| File | Lines | Lines over 100 characters |
|---|---:|---:|
| `ResonanceLarge.lean` | 218 | 0 |
| `ResonanceLarge/LineSlice.lean` | 76 | 0 |
| `ResonanceLarge/Structure.lean` | 111 | 0 |
| `ResonanceLarge/Frequency.lean` | 172 | 0 |
| `ResonanceLarge/Measurable.lean` | 164 | 0 |
| `ResonanceLarge/Sections.lean` | 272 | 0 |

Every file has the required copyright, `module`, public imports, module docstring, and public section. No forbidden token (`sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`) or `set_option` occurs in the six files. No heartbeat, recursion-depth, or synthesis-heartbeat override was used. The handoff's “all <270 lines” is a minor reporting error: Sections has 272; every file remains far below the binding 1,500-line cap.

A recursive KAM import scan from the facade found 25 KAM modules, no provider imports, and exactly 14 frozen modules, all **SEALED definitions** according to `manifest/frozen-anchors.json`: `HamiltonianVectorField`, `IsDiophantine`, `SymplecticForm`, and planetary `Assemble`, `Cylinder`, `Fast`, `FastFrequency`, `FastShift`, `HasFastDiffeomorphism`, `HasSecularBirkhoffForm`, `OscillatorAction`, `Phase`, `SecularAverage`, `Slow`. No frozen theorem, `DRAFT_SORRY` anchor, or provider is in the package's KAM import closure.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
git diff --check
```

All exit **0**, all produce no output. The first command confirms protected paths are unchanged relative to inp; the last two confirm tracked diff whitespace. The report is additionally checked directly because it is untracked.

### Repository lint

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh > /tmp/P4-RB-audit-1-lint.log 2>&1
```

Exit **1**, solely for the explicitly permitted stale generated root. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (504 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No forbidden-token, 100-character-line, file-size, errata-rendering, module-system, frozen-guard, or ABI error was reported. `KAM.lean` was not regenerated or edited. Under the audit brief's explicit exception this lint result is acceptable, with the generated-root integration note retained.

## Suspected errata, deviations, uncertainties, and handoff

- **New suspected pinned-source or blueprint defects:** none found in the audited P4-RB steps. The already recorded CP10 covering-number issue is background to the direct slicing route; this audit does not independently re-adjudicate that paper allegation or claim to close other blueprint SOURCE_GAPs.
- **Representation differences:** casting the integer block to real before taking its Pi norm gives exactly the prescribed max norm. Defining the carrier as the actual frequency image is equivalent to the blueprint's image carrier, with inverse membership proved by `freqCore_spec`. Neither changes the source statement. No signed declaration was replaced, weakened, or edited.
- **Integration notes:** generated-root regeneration belongs to the orchestrator. The Lipschitz product-image estimate and core-volume normalization remain explicit P4-M work. There is no audited final provider or anchor seal in this package.
- **Minor handoff correction:** the largest file is 272 lines, rather than the handoff's claimed “all <270”; this has no effect on the 1,500-line rule or proof verdict.
- **Audit mutations:** only this report persists. The pre-existing untracked `P4-RB-handoff.md` was preserved. The scratch probe was deleted; the ABI check removed its own temporary file. No production source, blueprint, design, frozen file, manifest, generated root, or README was changed, and no state-changing git command was issued.

Final report validation: 57/57 declaration rows, 45/45 axiom records, balanced code fences, no trailing whitespace, terminal newline; `git diff --check` passes. Scratch directory is empty. Final git status contains only the pre-existing untracked handoff and the new audit report. Audit logs are `/tmp/P4-RB-audit-1-axioms.log`, `/tmp/P4-RB-audit-1-kernel.log`, and `/tmp/P4-RB-audit-1-lint.log`.
