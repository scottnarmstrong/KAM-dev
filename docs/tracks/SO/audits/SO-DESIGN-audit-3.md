# SO-DESIGN independent design audit 3

**Verdict: FAIL — Revision 3 repairs F7/F8/F9 and the F3/F6 residual contracts, but the unrestricted scalar complex exponential contract must be replaced and its consumers reconciled (F10).**

This is a design audit. It does not accept a proof package, seal an anchor, or establish the lunar theorem. There is no new SO frozen anchor/provider in the change; anchor seal-readiness is not applicable. The existing I-G1 engine passes the targeted build, axiom probe and kernel replay. All 108 draft theorems still contain `sorryAx`.

## Scope and authorities

Audited `/root/code/KAM-inp-design-so`, HEAD `b442a9124c69caa9bc25e3a98cc5bc0af4f6a340`, against `inp` observed at `8aa7e422c350037616af06004f80f76bc5087771`, using `git diff inp...HEAD`, together with the targeted Revision 2→3 diff. The three-dot diff adds only four Markdown files: audit 1 (375 lines), audit 2 (396), committed handoff (85), design (1889); 2745 added lines. The working handoff already had an uncommitted Round 3 addition; it was read and preserved.

The user's exact report path overrides the generic brief's main-worktree destination and older filenames in the handoff. This report is the only repository-content write. Temporary auditor probes/logs were confined to this worktree's `.lake/abi-scratch/` and removed after recording results. No state-changing git, generated-root regeneration, frozen/manifest edit, dependency update, or clean build was performed. All auditor Lean/Lake invocations were serialized with `LEAN_NUM_THREADS=1`; direct Lean/Lake commands used `nice -n 5`, including through the supplied wrappers. Lint/ABI ran only after kernel replay finished.

Read: AGENTS.md, PLAN, DECISIONS, the exact package brief and Round 3 handoff, audits 1/2, full current design and signatures, `.drafts/handoff-SO-DESIGN.md`; the controlling SO plan with D30 and O1–O4, proposal and pilot under `/root/code/KAM`; I-G1's frozen statement and relevant frozen strip/Gram/normal-frame/invariance/torsion/average definitions; `IG1Body`, `g1_explicit`, constants, track I statement and blueprint nodes `bpI:p0:g1`, `bpI:p2:g1`. N/P contribute no new implementation or anchor here. The additional Round 3 input was the actual SO-AIF `Roots.lean` and its rational transcendental implementation, read in `/root/code/KAM-inp-soaif` without editing or building that sibling.

Appendix A is byte-identical to both `.drafts/design/SOSignatures.lean` and `/root/code/KAM-inp/.drafts/design/SOSignatures.lean`: 1360 lines, SHA-256 `4998870ab6e4f1d8dd8da16a7a01f71b733e7b842b80894e8beedf57d6304fb8`. The six controlling plan/proposal/pilot and engine/Inputs/Defs hashes match the design's pins. SO-AIF `Roots.lean` observed SHA-256: `93a799af570043c674886b8de1abc45678a6e4fb74e72d7e6433c4dd45058007`. Historical upstream status labels in the design are snapshots, not freshly established campaign status.

## Prior findings and repairs

| Finding | Round 3 assessment | Evidence / limit |
|---|---|---|
| F1 exact frequencies | CLOSED at design level | Exact real `ωstar` theorem binder, proved `FreqEncloses`, external `IsDiophantine`. No shared quadratic-field restriction for n≥3. The cubic toy remains an unproved proposed application. |
| F2 arithmetic reality | CLOSED at design level | Real Fourier and embedding denotations use mathematical conjugation and zero; computed correctness carries backend laws. |
| F3 torsion/sub-check contracts | CLOSED at design level | Literal frozen torsion producer exports exact shape, enclosure, continuity; averaging consumer uses the same n. All eight checker contracts and their acyclic assembly remain explicit. This is interface closure, not a proof of construction. |
| F4 toys | CLOSED at design level | T2/T2d/T3 have rational approximations and positive errors; TR is explicitly checker-only and resonant. Passing data remain unwritten. |
| F5 Fourier J | Soundness route valid; numerical attachment OPEN | Actual four-component checks and G-J are mandatory. No certified budgets or new pilot margins supplied. |
| F6 scheduling | CLOSED at design level | `Arith/Rat` and its lawful instance move to pre-gate SO-AIF; SO-BALL explicitly depends on it. Fixed backend/selection remain post-gate. This does not certify that the instance has already landed. |
| F7 torsion dimension | CLOSED at design level | `HasShape`, n argument, shape theorem, producer shape and certificate-level call agree; details below. |
| F8 n=0 norm contracts | CLOSED at design level | Both bounds now take `1 ≤ n`, obtainable from static `2 ≤ n`; details below. |
| F9 lunar residual | CLOSED as an identity/budget repair | Original residual is retained, and replacement errors paid; quantitative G-J still open. |

**F7.** Draft 714–715 defines exact list shape, not merely entry presence. Draft 772–786 (`torsionModels_sound`) returns `HasShape (n+1) T ∧ Encloses ∧ continuity`. Draft 790–807 passes n to `torsionAvgCheck` and its soundness theorem, and `torsionAvgCheck_shape` derives both exact input shapes from success without arithmetic laws. `torsionIdx` enumerates every row/column 0,…,n once. Thus the formerly checked larger matrix cannot stand in for a singular leading block. Draft 949/1118–1129 and design §4 use the certificate's n and `s • ωstar`; no dimension-changing premise is introduced. A fresh no-placeholder probe proves a three-row matrix cannot have shape 2. Test 9 is correctly specified but not implemented; the checker bodies and shape theorem remain placeholders.

**F8.** Draft 679–693 adds `(hn : 1 ≤ n)` to both standalone Hamiltonian-vector-field norm bridges. The old n=0, B=−1 counterexample is excluded. Choosing the row `inl 0` makes a sum of nonnegative partial norms ≤B and forces B≥0; a fresh no-placeholder Lean probe verifies that implication. Local C²/C³ hypotheses retain the needed derivative regularity. The checker derives the dimension premise from `StaticFacts.hn`; no new external hypothesis is added.

**F9.** Design 307–325 now says `E(K̃)_J = E(K₀)_J − D_(sωstar) ΔJ`, becoming `p r − D_(sωstar) ΔJ` only under the scalar pilot identities (pilot line 50). This follows because changing J alone leaves this affine-in-J Hamiltonian's vector field unchanged. The other coordinates must be held fixed in that comparison; when comparing to a different scalar candidate, B_c pays their replacement errors. `B_r + B₁ + B_c ≤ e/2`, the other-row budgets, energy B₀ and derivative B₂ are explicitly required. Full checks on K̃ remain authoritative. The former standalone B₁ allocation is explicitly superseded in the historical Revision 2 table. The identity is repaired; neither these target allocations nor the pilot establish actual Fourier-J feasibility.

**F3/F6 residuals.** Draft `CertPoly.add` is now concrete list concatenation and `eval_add` an equality, law-free. This avoids an impossible uniform all-complex-θ error estimate for rounded nonzero coefficients. Rounded merging stays in strip-weighted model operations. Denominator-validation slots must survive compiler folding/pruning, as stated in design §1.4; this is still an implementation obligation. Moving the exact rational instance into SO-AIF removes the specific SO-BALL→post-gate backend dependency. It does not resolve F10's distinct complex exponential consumer issue.

## F10 — HIGH: the small-ball scalar exponential replacement is not attached to all consumers

**Location:** draft 228–234 / design 756–762 (`certCExp`, `certCExp_sound`); design §1.4, §1.7, §5/§7; draft 420–438 (`expWitnessRadius`, `expWitness_sound`), 589–602 (`Slp.balls`, `Slp.val_mem_ball`), 644–653 (`Slp.compose_sound`). Replacement source: `/root/code/KAM-inp-soaif/KAM/Certificate/Arith/Roots.lean:303–333`, scalar complex exponential section (`certCExpSmall`, `certCExpSmall_sound`, `certCExp_sound_of_small`).

The draft still states unrestricted soundness for every centre z, radius and Taylor order N. The SO-AIF implementation evaluates N+1 Taylor terms in ball arithmetic and adds `eRem (N+1)`. Its soundness proof legitimately needs `‖z.toC‖ + val zRad ≤ 1`, proved by `certCExpSmall_sound` after a backend test. The old no-size theorem does not apply to that implementation.

For the exact rational backend, take z=2, radius 0, N=0. The implemented formula has Taylor sum 1 and remainder `eRem 1 = 2`, so unrestricted soundness would imply `|exp(2)−1| ≤ 2`. In fact exp(2)>3. A fresh no-placeholder Lean proof establishes `¬ |Real.exp 2−1| ≤ 2` using `Real.add_one_lt_exp`. This checks the scalar inequality; the draft's placeholder arithmetic instance was not used to claim an evaluated counterexample to a production checker. This is a defect of the stated Taylor interface/implementation pairing, not a proof that every conceivable exponential algorithm is impossible.

| Consumer | Smallness available now? | Required reconciliation |
|---|---|---|
| `Slp.balls` on the full domain D, including general `HamExpr.exp` and compiled sin/cos | **No.** For `.exp (.const 2)` the input centre already exceeds 1. Action balls may have arbitrary centre/radius. An exp of a cosine mode can receive a ball centred at zero with radius greater than 1. Analyticity on D does not imply unit size. | Guard each primitive call and perform certified argument reduction, or explicitly return `none`. To retain the intended general exp clients, implement a range-reduced wrapper. |
| Scalar pin in `expWitnessRadius` | **No.** The degree-zero polynomial's value at 0 and its rounding enclosure have no unit bound. For constant g₀=2 the pin needs exp(2). Real Fourier data or n≥2 does not help. | Guard/reduce the full pin ball. Include reduction, input rounding, pin evaluation and squaring errors in ε₀. |
| Character witnesses in `Slp.compose` | **No general guarantee.** `2π i k·U` has arbitrarily large size for general k and Fourier embeddings. Normalizing indices or syntactically zero coordinates does not give a magnitude bound. | They inherit the repaired pin path. If syntactically halving the whole witness exponent instead, supply and check all needed reduced witnesses and account for every squaring. |
| `exp(2B)`, `exp(B)`, `exp(η)−1` bounds and strip weights | Separate route | These are rational real upper bounds via `ratExpUp`, whose SO-AIF implementation already halves and has the proved coarse fallback `3^ceil(q)` when the chosen Taylor parameters are insufficient. They do not justify arbitrary complex balls or a tight complex centre enclosure. Preserve that separation. |
| Lunar client's concrete pins / D balls | **Unproved here.** No exact passing data or certified primitive-size checks are supplied. The lunar cosine-mode domain majorants can avoid scalar complex exp, but witness pins still need a check. | Report exact `certCExpSmall` receipts for every unreduced pin, or use the same reduced wrapper. Do not infer smallness from a tiny residual. |

**Required change before design acceptance:** replace the draft theorem by the actual `certCExp_sound_of_small` contract and expose `certCExpSmall`/its soundness theorem; add a general certified complex-ball exponential wrapper for consumers that need arbitrary bounded input. A suitable design scales the ball by 2^−s, verifies the *rounded enclosing* reduced ball passes `certCExpSmall`, applies the small theorem, then squares the output ball s times using proved ball multiplication and `exp(2z)=(exp z)^2`. Carry every radius/rounding contribution. Use an explicit finite halving count or a proved finite rational selection, with structural recursion and no resource override. Specify whether insufficient counts return `none`, propagate that through `Slp.balls`/composition, and give their successful-return soundness contracts. Add tests with reduced/rejected large balls, large pin centres, and s=0 boundary cases; include the cost at intended precision in SO-REPLAY.

A bare call to the small theorem with an unpaid hsmall is invalid. Adding unit-size assumptions to the public black box would narrow the owner's general scope and would move a checkable obligation onto the caller. Existing remarks about rewriting `exp a` to `(exp(a/2))²` are compatible with a repair, but concern the full model witness and do not yet provide a scalar range-reduction contract for every consumer. F10 is the only new blocking design issue found. The analytic witness and KAM-engine routes need no reversal.

## Engine fidelity, semantics and lunar reach

A fresh `SOAudit3.engine_bridge` applies `(g1_explicit …).2.2.2` to all fields in their exact order. It has no new placeholder and its axioms exclude `sorryAx`. This verifies the engine application and all output clauses, not that the finite checks produce the fields.

| Engine obligation | Producer/field | Assessment |
|---|---|---|
| n≥2, τ≥n−1; 0<ρ∞<ρ; positive M,σK,σB,σT,μ,γbar,ν; σω>1 | StaticFacts | Exact ordering and dependencies |
| ωstar≠0, both endpoint margins | `checkStatic_freq`, hω | Reference vector is exact; nuRay is the margin, not the lunar rotation |
| open D, integer translations | `certDomain`, `ham_structural` | Correct open strip × polydisc |
| H holomorphic/periodic/real | balls certify `NonvanishingOn`, structural theorem | Correct division guards; ball implementation needs F10 |
| five bounds in order DH, XH, DXH, D²XH, D²H | `checkHamBounds_sound`, norm bridges | Exact norms; positive-dimension premises now available |
| K holomorphic/primary/real | direct denotation, `emb_structural` | Law-free semantics; no backend zero/conjugation shortcut |
| μ-ball inclusion, DK≤σK−μ | `checkEmbedding_sound` | Exactly the frozen margins |
| bilinear Gram invertibility and inverse row sums | `gramCheck_sound`, `checkGram_sound` | No Hermitian replacement |
| averaged literal extended torsion invertibility and row sums | torsion producer→average→`checkTorsion_sound` | Exact dimensions, last row DH(K)N, border sωstar and DN[sωstar] |
| 1<s<σω; 0<γ≤γbar; e≥0 | StaticFacts | Exact |
| IsDiophantine γ τ ωstar | external hdio | Applies to ωstar, with ray scalar s separately |
| full residual and averaged energy error | `checkInvariance_sound`, `checkEnergy_sound` | Actual K̃ and exact enclosed ω; no scalar-pilot substitution |
| isoC1 smallness and isoC2 displacement | `checkSmallness_sound` | μ,ν,γbar parameter order preserved |
| every output clause, pointwise energy, half margins, both displacement bounds | CertifiedTorus, fresh bridge | Both use hdisp since C₂=C₃ |

The certificate contains finite numerical data/witnesses, not assumed residuals, inverse existence or tori. `G1Hyps` and `StaticFacts` are derived Props. Backend laws and the exact-frequency enclosure are legitimate proved inputs; literally “only external mathematical input” must retain those qualifications alongside hdio. Natural τ is explicit; a real-exponent client needs a proved conversion, not a silently changed exponent.

Other semantics remain sound at design level: the frozen strip is open; positive weights make the real cube available for averages; `(2π)^deg` is positive for all integer degrees; lower π bounds control negative-degree upper estimates; reciprocal witnesses pay δ/(1−δ); continuity permits averaging; Neumann bounds apply to complex bilinear Gram matrices without positivity. Sup-tail bounds are not differentiated: derivatives come from exact polynomial data or the inverse derivative identity. Total division off the certified domain does not spoil periodicity/reality, and certified nonvanishing supplies analyticity. Optimized list/jet code must preserve these whole-carrier denotations and validation slots. F10 concerns the scalar pin implementation, not the analytic path estimate for exp witnesses.

D30/O1/O4 are represented correctly by the lunar statements: continuous ordered invariant graphs, explicit eventual rational momentum window, all initial q/φ, all real times, global existence and uniqueness, and 33/1000. The global Lipschitz physical field supplies existence independently of the band. The clock plus positive q derivative supplies a graph; range bounds widen by disp. Generality is no longer restricted by the frequency carrier or by excluding division. Exact window endpoints, data/pass proofs, G-J margins and replay measurements remain unpaid. The Fourier-J deviation is conditionally sound but its fit within the pilot margins is not established.

## Validation receipts

All commands were run by this auditor, sequentially. The signature wrapper runs `LEAN_NUM_THREADS=1 nice -n 5 timeout 1800 lake env lean <absolute-path>` against the shared `/root/code/KAM-inp` snapshot; the compile wrapper runs targeted `nice -n 5 lake build` in this worktree. No provider/type/seal probe is applicable to a new SO provider, since there is none.

1. `git diff inp...HEAD`, `git diff d2352a2d..HEAD -- docs/tracks/SO/design/SO-LEAN-DESIGN.md`: design/history inspected. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: **empty**. `git diff --check inp...HEAD` and `git diff --check`: **exit 0, no output**.
2. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-so .drafts/design/SOSignatures.lean`: **exit 0**, **156** warnings, all `declaration uses 'sorry'`, **0** errors. The 1360-line file has copyright, module, public imports, docstring and exposed public noncomputable section. A comment-masked scan found no forbidden identifier/proof escape or resource override; 156 `sorry` tokens are deliberate transient draft placeholders, excluded from production lint. They cannot enter production outside frozen manifest bodies.
3. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-design-so KAM.Iso.Apost.G1`: **exit 0**:

   ```text
   [inp-gate] slot 1 acquired 12:12:15 for KAM.Iso.Apost.G1
   Build completed successfully (3224 jobs).
   ```

4. Same signature gate on `.lake/abi-scratch/SOAudit3Probe.lean`: **exit 0**, 156 expected warnings, zero errors. The probe contains the complete draft, fresh engine bridge, shape rejection, positive-row implication and scalar exp inequality refutation; no new proof placeholder in those four probe theorems. It prints axioms for every one of the 108 explicit draft theorems, the four probe theorems and the engine: 113 outputs. Exact principal outputs (private probe prefix abbreviated):

   ```text
   SOAudit3.engine_bridge: [propext, Classical.choice, Quot.sound]
   SOAudit3.wrong_shape: [propext, Quot.sound]
   SOAudit3.row_bound_nonneg: [propext, Classical.choice, Quot.sound]
   SOAudit3.exp_order_zero_failure: [propext, Classical.choice, Quot.sound]
   KAM.Iso.Apost.g1_explicit: [propext, Classical.choice, Quot.sound]
   KAM.Certificate.certCExp_sound: [propext, sorryAx, Classical.choice, Quot.sound]
   KAM.Certificate.torsionModels_sound: [propext, sorryAx, Classical.choice, Quot.sound]
   KAM.Certificate.torsionAvgCheck_shape: [propext, sorryAx, Classical.choice, Quot.sound]
   KAM.Certificate.torsionAvgCheck_sound: [propext, sorryAx, Classical.choice, Quot.sound]
   KAM.Certificate.checkTorusCertificate_sound: [propext, sorryAx, Classical.choice, Quot.sound]
   KAM.SpinOrbit.lunar_spin_confinement: [propext, sorryAx, Classical.choice, Quot.sound]
   ```

   Of the 108 draft results, 106 have `[propext, sorryAx, Classical.choice, Quot.sound]`; `toyCert3_err_pos` has `[propext, sorryAx, Quot.sound]`; `lunarPLo_lt_lunarPHi` has `[sorryAx]`. In the inventory below these are S, T and U respectively. This is expected draft status, never a proof pass.
5. `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Iso.Apost.G1`: **exit 0**. Exact output:

   ```text
   replaying KAM.Iso.Apost.G1
   ```

   This independently replays the existing engine, not the placeholder draft or SO-AIF sibling.
6. `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`: **exit 0**. Exact output:

   ```text
   check_lean_modules: PASS (1281 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No generated-root exception was needed. No production Lean file was added or changed. The draft is below 1500 lines. Final status contains only the pre-existing handoff modification and this new report.
7. Auditor execution deviation: the first temporary full-draft probe plus separate axiom commands was 1609 lines, exceeding the literal 1500-line cap. Before final validation it was reduced to **1430 lines** by placing multiple axiom-print commands on each line, and the same probe was rerun. No proof, budget, theorem type or repository source was changed by this correction. The final probe was then deleted. Its final receipt is recorded in the handoff below.

## Declaration inventory and definition classification

One row per explicit declaration in Appendix A (224 total, including all 108 theorems); source locations are draft line numbers. PWN means **PASS WITH NOTES at design level only**: the stated object/interface was reviewed, and a placeholder algorithm/proof remains unpaid. It never means seal-ready. F10-linked downstream contracts are PWN with the explicit dependency; only the incompatible scalar contract is FAIL. S/T/U refer to the exact axiom sets above, and — means no theorem axiom probe applicable. Data/syntax carriers, backend law classes, semantic predicates, exact denotations, derived facts, algorithms and data placeholders are distinguished explicitly. Generated projections/recursors are not separate source declarations.

| Section | Lean declaration (draft line) | Verdict | Classification / note; axioms |
|---|---|---|---|
| A | `KAM.Certificate.CertArith` (67) | PWN | Backend operation/data class; laws separate; — |
| A | `KAM.Certificate.LawfulCertArith` (86) | PWN | Backend soundness law class (Prop); — |
| A | `KAM.Certificate.CC` (106) | PWN | Finite numerical/data/syntax carrier; — |
| A | `KAM.Certificate.CC.toC` (111) | PWN | Concrete denotation or exact finite operation; — |
| A | `KAM.Certificate.CC.conj` (114) | PWN | Concrete denotation or exact finite operation; — |
| A | `KAM.Certificate.CC.toC_conj` (116) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.CC.toC_zero` (120) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.instCertArithRat` (131) | PWN | Backend instance/law proof placeholder; Rat pre-gate, Fixed post-gate; — |
| A | `KAM.Certificate.instLawfulCertArithRat` (133) | PWN | Backend instance/law proof placeholder; Rat pre-gate, Fixed post-gate; — |
| A | `KAM.Certificate.CertFixed` (136) | PWN | Finite numerical/data/syntax carrier; — |
| A | `KAM.Certificate.instCertArithFixed` (139) | PWN | Backend instance/law proof placeholder; Rat pre-gate, Fixed post-gate; — |
| A | `KAM.Certificate.instLawfulCertArithFixed` (141) | PWN | Backend instance/law proof placeholder; Rat pre-gate, Fixed post-gate; — |
| A | `KAM.Certificate.ratExpUp` (147) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| A | `KAM.Certificate.exp_le_ratExpUp` (149) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.piLoQ` (157) | PWN | Concrete denotation or exact finite operation; — |
| A | `KAM.Certificate.piUpQ` (159) | PWN | Concrete denotation or exact finite operation; — |
| A | `KAM.Certificate.piLoQ_lt_pi` (161) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.pi_lt_piUpQ` (163) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.atanS` (166) | PWN | Concrete denotation or exact finite operation; — |
| A | `KAM.Certificate.piLowRat` (169) | PWN | Concrete denotation or exact finite operation; — |
| A | `KAM.Certificate.piUpRat` (171) | PWN | Concrete denotation or exact finite operation; — |
| A | `KAM.Certificate.piLowRat_lt_pi` (173) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.pi_lt_piUpRat` (175) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.PiHighCert` (178) | PWN | Proved π-enclosure interface; outside numerical certificate; — |
| A | `KAM.Certificate.eSum` (184) | PWN | Concrete denotation or exact finite operation; — |
| A | `KAM.Certificate.eRem` (186) | PWN | Concrete denotation or exact finite operation; — |
| A | `KAM.Certificate.eLowRat` (188) | PWN | Concrete denotation or exact finite operation; — |
| A | `KAM.Certificate.eUpRat` (190) | PWN | Concrete denotation or exact finite operation; — |
| A | `KAM.Certificate.eLowRat_lt_exp_one` (192) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.exp_one_lt_eUpRat` (194) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.PiEnclosure` (201) | PWN | Finite numerical/data/syntax carrier; — |
| A | `KAM.Certificate.checkPiEnclosure` (209) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| A | `KAM.Certificate.checkPiEnclosure_sound` (211) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.checkRootEnclosure` (217) | PWN | Concrete denotation or exact finite operation; — |
| A | `KAM.Certificate.rpow_mem_of_checkRootEnclosure` (220) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.sqrt_mem_of_checkRootEnclosure` (224) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.certCExp` (230) | PWN | Algorithm placeholder; denotation/correctness not implemented; F10 consumer/API reconciliation; — |
| A | `KAM.Certificate.certCExp_sound` (232) | FAIL | Unrestricted size contract incompatible with SO-AIF implementation; F10; S |
| B | `KAM.Certificate.CertKey` (239) | PWN | Representation alias; — |
| B | `KAM.Certificate.certKeyFun` (242) | PWN | Concrete denotation or exact finite operation; — |
| B | `KAM.Certificate.CertPoly` (246) | PWN | Finite numerical/data/syntax carrier; — |
| B | `KAM.Certificate.CertPoly.eval` (250) | PWN | Concrete denotation or exact finite operation; — |
| B | `KAM.Certificate.CertPoly.coeff` (254) | PWN | Concrete denotation or exact finite operation; — |
| B | `KAM.Certificate.CertPoly.eval_eq_fourierSum` (258) | PWN | Reviewed statement; proof placeholder; S |
| B | `KAM.Certificate.CertPoly.differentiable_eval` (261) | PWN | Reviewed statement; proof placeholder; S |
| B | `KAM.Certificate.CertPoly.eval_add_int` (264) | PWN | Reviewed statement; proof placeholder; S |
| B | `KAM.Certificate.CertRealPoly` (268) | PWN | Finite numerical/data/syntax carrier; — |
| B | `KAM.Certificate.CertRealPoly.eval` (273) | PWN | Concrete denotation or exact finite operation; — |
| B | `KAM.Certificate.CertRealPoly.eval_real` (279) | PWN | Reviewed statement; proof placeholder; S |
| B | `KAM.Certificate.CertRealPoly.differentiable_eval` (282) | PWN | Reviewed statement; proof placeholder; S |
| B | `KAM.Certificate.CertRealPoly.eval_add_int` (285) | PWN | Reviewed statement; proof placeholder; S |
| B | `KAM.Certificate.CertRealPoly.toPoly` (290) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| B | `KAM.Certificate.CertRealPoly.eval_toPoly` (293) | PWN | Reviewed statement; proof placeholder; S |
| B | `KAM.Certificate.CertRealPoly.conjugateSymmetric` (296) | PWN | Reviewed statement; proof placeholder; S |
| B | `KAM.Certificate.CertPoly.add` (302) | PWN | Concrete denotation or exact finite operation; — |
| B | `KAM.Certificate.CertPoly.eval_add` (304) | PWN | Reviewed statement; proof placeholder; S |
| B | `KAM.Certificate.CertPoly.shift` (308) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| B | `KAM.Certificate.CertPoly.eval_shift` (310) | PWN | Reviewed statement; proof placeholder; S |
| B | `KAM.Certificate.CertPoly.conjReflect` (315) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| B | `KAM.Certificate.CertPoly.eval_conjReflect` (317) | PWN | Reviewed statement; proof placeholder; S |
| C | `KAM.Certificate.CertWeight` (324) | PWN | Finite numerical/data/syntax carrier; — |
| C | `KAM.Certificate.checkWeight` (330) | PWN | Concrete denotation or exact finite operation; — |
| C | `KAM.Certificate.norm_character_le_weight` (333) | PWN | Reviewed statement; proof placeholder; S |
| C | `KAM.Certificate.CertModel` (339) | PWN | Finite numerical/data/syntax carrier; — |
| C | `KAM.Certificate.CertModel.Encloses` (345) | PWN | Concrete semantic predicate / exact shape; — |
| C | `KAM.Certificate.CertModel.supBound` (352) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| C | `KAM.Certificate.CertModel.norm_le_supBound` (354) | PWN | Reviewed statement; proof placeholder; S |
| C | `KAM.Certificate.ModelConfig` (360) | PWN | Finite numerical/data/syntax carrier; — |
| C | `KAM.Certificate.CertModel.add` (367) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| C | `KAM.Certificate.CertModel.mul` (370) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| C | `KAM.Certificate.CertModel.trim` (374) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| C | `KAM.Certificate.CertModel.toDeg` (378) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| C | `KAM.Certificate.CertModel.ofDeriv` (383) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| C | `KAM.Certificate.CertModel.Encloses.ofDeriv` (386) | PWN | Reviewed statement; proof placeholder; S |
| C | `KAM.Certificate.CertModel.Encloses.add` (391) | PWN | Reviewed statement; proof placeholder; S |
| C | `KAM.Certificate.CertModel.Encloses.mul` (396) | PWN | Reviewed statement; proof placeholder; S |
| C | `KAM.Certificate.CertModel.Encloses.trim` (401) | PWN | Reviewed statement; proof placeholder; S |
| C | `KAM.Certificate.CertModel.Encloses.toDeg` (406) | PWN | Reviewed statement; proof placeholder; S |
| C | `KAM.Certificate.CertModel.Encloses.average` (412) | PWN | Reviewed statement; proof placeholder; S |
| C | `KAM.Certificate.expWitnessRadius` (430) | PWN | Algorithm placeholder; denotation/correctness not implemented; F10 consumer/API reconciliation; — |
| C | `KAM.Certificate.expWitness_sound` (433) | PWN | Reviewed statement; proof placeholder; F10 consumer/API reconciliation; S |
| C | `KAM.Certificate.invWitnessRadius` (441) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| C | `KAM.Certificate.invWitness_sound` (444) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.phaseBasis` (456) | PWN | Concrete denotation or exact finite operation; — |
| D | `KAM.Certificate.HamExpr` (464) | PWN | Finite expression/program syntax carrier; — |
| D | `KAM.Certificate.modePhase` (479) | PWN | Concrete denotation or exact finite operation; — |
| D | `KAM.Certificate.HamExpr.eval` (484) | PWN | Concrete denotation or exact finite operation; — |
| D | `KAM.Certificate.HamExpr.NonvanishingOn` (499) | PWN | Concrete semantic predicate / exact shape; — |
| D | `KAM.Certificate.HamExpr.contDiffOn_eval` (509) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.HamExpr.eval_add_int` (512) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.HamExpr.eval_real` (515) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.SlpOp` (520) | PWN | Finite expression/program syntax carrier; — |
| D | `KAM.Certificate.Slp` (529) | PWN | Finite numerical/data/syntax carrier; — |
| D | `KAM.Certificate.Slp.val` (533) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| D | `KAM.Certificate.HamJet` (539) | PWN | Finite numerical/data/syntax carrier; — |
| D | `KAM.Certificate.phaseNat` (547) | PWN | Concrete denotation or exact finite operation; — |
| D | `KAM.Certificate.HamExpr.jet` (551) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| D | `KAM.Certificate.HamExpr.jet_v0` (553) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.HamExpr.jet_d1` (556) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.HamExpr.jet_d2` (562) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.HamExpr.jet_d3` (568) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.certDomain` (576) | PWN | Concrete denotation or exact finite operation; — |
| D | `KAM.Certificate.isOpen_certDomain` (581) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.certDomain_add_int` (584) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.Slp.balls` (593) | PWN | Algorithm placeholder; denotation/correctness not implemented; F10 consumer/API reconciliation; — |
| D | `KAM.Certificate.Slp.val_mem_ball` (596) | PWN | Reviewed statement; proof placeholder; F10 consumer/API reconciliation; S |
| D | `KAM.Certificate.HamExpr.nonvanishingOn_of_balls` (604) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.CertEmbedding` (611) | PWN | Finite numerical/data/syntax carrier; — |
| D | `KAM.Certificate.CertEmbedding.eval` (617) | PWN | Concrete denotation or exact finite operation; — |
| D | `KAM.Certificate.CertEmbedding.differentiable_eval` (624) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.CertEmbedding.isPrimaryOnStrip` (627) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.CertEmbedding.isRealOnReals` (631) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.Witnesses` (637) | PWN | Finite numerical/data/syntax carrier; — |
| D | `KAM.Certificate.Slp.compose` (644) | PWN | Algorithm placeholder; denotation/correctness not implemented; F10 consumer/API reconciliation; — |
| D | `KAM.Certificate.Slp.compose_sound` (649) | PWN | Reviewed statement; proof placeholder; F10 consumer/API reconciliation; S |
| E | `KAM.Certificate.norm_fderiv_le_sum_partials` (659) | PWN | Reviewed statement; proof placeholder; S |
| E | `KAM.Certificate.norm_iteratedFDeriv_two_le_sum_partials` (663) | PWN | Reviewed statement; proof placeholder; S |
| E | `KAM.Certificate.hamiltonianVectorFieldℂ_sumVec` (670) | PWN | Reviewed statement; proof placeholder; S |
| E | `KAM.Certificate.norm_fderiv_hamiltonianVectorFieldℂ_le` (679) | PWN | Reviewed statement; proof placeholder; F8 repaired; S |
| E | `KAM.Certificate.norm_iteratedFDeriv_two_hamiltonianVectorFieldℂ_le` (687) | PWN | Reviewed statement; proof placeholder; F8 repaired; S |
| F | `KAM.Certificate.matrix_inv_of_approx_inverse` (697) | PWN | Reviewed statement; proof placeholder; S |
| F | `KAM.Certificate.ModelMatrix` (702) | PWN | Representation alias; — |
| F | `KAM.Certificate.ModelMatrix.Encloses` (706) | PWN | Concrete semantic predicate / exact shape; — |
| F | `KAM.Certificate.ModelMatrix.HasShape` (714) | PWN | Concrete semantic predicate / exact shape; F7 repaired; — |
| F | `KAM.Certificate.polyMatrix` (718) | PWN | Concrete denotation or exact finite operation; — |
| F | `KAM.Certificate.gramModels` (723) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| F | `KAM.Certificate.gramModels_sound` (726) | PWN | Reviewed statement; proof placeholder; S |
| F | `KAM.Certificate.gramCheck` (734) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| F | `KAM.Certificate.gramCheck_sound` (738) | PWN | Reviewed statement; proof placeholder; S |
| F | `KAM.Certificate.torsionIdx` (749) | PWN | Concrete denotation or exact finite operation; — |
| F | `KAM.Certificate.FreqBox` (753) | PWN | Representation alias; — |
| F | `KAM.Certificate.FreqEncloses` (755) | PWN | Concrete semantic predicate / exact shape; — |
| F | `KAM.Certificate.torsionModels` (763) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| F | `KAM.Certificate.torsionModels_sound` (772) | PWN | Reviewed statement; proof placeholder; F10 consumer/API reconciliation; F7 repaired; S |
| F | `KAM.Certificate.torsionAvgCheck` (790) | PWN | Algorithm placeholder; denotation/correctness not implemented; F7 repaired; — |
| F | `KAM.Certificate.torsionAvgCheck_shape` (794) | PWN | Reviewed statement; proof placeholder; F7 repaired; S |
| F | `KAM.Certificate.torsionAvgCheck_sound` (798) | PWN | Reviewed statement; proof placeholder; F7 repaired; S |
| F | `KAM.Certificate.cRUpQ` (809) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| F | `KAM.Certificate.cR_le_cRUpQ` (811) | PWN | Reviewed statement; proof placeholder; S |
| F | `KAM.Certificate.isoC1Q` (815) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| F | `KAM.Certificate.isoC2Q` (817) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| F | `KAM.Certificate.isoC1_le_isoC1Q` (819) | PWN | Reviewed statement; proof placeholder; S |
| F | `KAM.Certificate.isoC2_le_isoC2Q` (825) | PWN | Reviewed statement; proof placeholder; S |
| F | `KAM.Certificate.checkRealLowerBound` (833) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| F | `KAM.Certificate.checkRealLowerBound_sound` (836) | PWN | Reviewed statement; proof placeholder; S |
| G | `KAM.Certificate.algFreq` (853) | PWN | Concrete denotation or exact finite operation; — |
| G | `KAM.Certificate.checkAlgBox` (859) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| G | `KAM.Certificate.algFreq_encloses` (861) | PWN | Reviewed statement; proof placeholder; S |
| G | `KAM.Certificate.CertParams` (868) | PWN | Finite numerical/data/syntax carrier; — |
| G | `KAM.Certificate.TorusCertificate` (889) | PWN | Finite numerical/data/syntax carrier; — |
| G | `KAM.Certificate.TorusCertificate.D` (914) | PWN | Concrete denotation or exact finite operation; — |
| G | `KAM.Certificate.TorusCertificate.H` (917) | PWN | Concrete denotation or exact finite operation; — |
| G | `KAM.Certificate.TorusCertificate.K` (919) | PWN | Concrete denotation or exact finite operation; — |
| G | `KAM.Certificate.checkStatic` (929) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| G | `KAM.Certificate.checkHamBounds` (933) | PWN | Algorithm placeholder; denotation/correctness not implemented; F10 consumer/API reconciliation; — |
| G | `KAM.Certificate.checkEmbedding` (936) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| G | `KAM.Certificate.checkInvariance` (939) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| G | `KAM.Certificate.checkEnergy` (942) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| G | `KAM.Certificate.checkGram` (945) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| G | `KAM.Certificate.checkTorsion` (949) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| G | `KAM.Certificate.checkSmallness` (952) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| G | `KAM.Certificate.checkTorusCertificate` (956) | PWN | Concrete denotation or exact finite operation; — |
| G | `KAM.Certificate.G1Hyps` (966) | PWN | Derived engine/static facts (Prop), not certificate input; — |
| G | `KAM.Certificate.CertifiedTorus` (1019) | PWN | Concrete semantic predicate / exact shape; — |
| G | `KAM.Certificate.StaticFacts` (1038) | PWN | Derived engine/static facts (Prop), not certificate input; — |
| G | `KAM.Certificate.checkStatic_sound` (1063) | PWN | Reviewed statement; proof placeholder; S |
| G | `KAM.Certificate.checkStatic_freq` (1067) | PWN | Reviewed statement; proof placeholder; S |
| G | `KAM.Certificate.TorusCertificate.emb_structural` (1073) | PWN | Reviewed statement; proof placeholder; S |
| G | `KAM.Certificate.checkHamBounds_sound` (1077) | PWN | Reviewed statement; proof placeholder; F10 consumer/API reconciliation; S |
| G | `KAM.Certificate.TorusCertificate.ham_structural` (1086) | PWN | Reviewed statement; proof placeholder; S |
| G | `KAM.Certificate.checkEmbedding_sound` (1094) | PWN | Reviewed statement; proof placeholder; S |
| G | `KAM.Certificate.checkGram_sound` (1100) | PWN | Reviewed statement; proof placeholder; S |
| G | `KAM.Certificate.checkInvariance_sound` (1105) | PWN | Reviewed statement; proof placeholder; F10 consumer/API reconciliation; S |
| G | `KAM.Certificate.checkEnergy_sound` (1111) | PWN | Reviewed statement; proof placeholder; F10 consumer/API reconciliation; S |
| G | `KAM.Certificate.checkTorsion_sound` (1118) | PWN | Reviewed statement; proof placeholder; F10 consumer/API reconciliation; S |
| G | `KAM.Certificate.checkSmallness_sound` (1125) | PWN | Reviewed statement; proof placeholder; S |
| G | `KAM.Certificate.checkTorusCertificate_hyps` (1136) | PWN | Reviewed statement; proof placeholder; F10 consumer/API reconciliation; S |
| G | `KAM.Certificate.checkTorusCertificate_sound` (1146) | PWN | Reviewed statement; proof placeholder; F10 consumer/API reconciliation; S |
| H | `KAM.Certificate.clock_frequency` (1159) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.cbrtTwo` (1175) | PWN | Concrete denotation or exact finite operation; — |
| J | `KAM.Certificate.cubicFreq` (1178) | PWN | Concrete denotation or exact finite operation; — |
| J | `KAM.Certificate.cubicFreq_eq_algFreq` (1180) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.cubicFreq_isDiophantine` (1186) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.toyHam3` (1189) | PWN | Concrete denotation or exact finite operation; — |
| J | `KAM.Certificate.toyCert3` (1196) | PWN | Generated/example/endpoint data placeholder; — |
| J | `KAM.Certificate.toyCert3_ham` (1198) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.toyCert3_err_pos` (1200) | PWN | Reviewed statement; proof placeholder; T |
| J | `KAM.Certificate.toyCert3_passes` (1202) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.toyCert3_freq` (1204) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.toyCert3_torus` (1207) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.toyCert2` (1212) | PWN | Generated/example/endpoint data placeholder; — |
| J | `KAM.Certificate.toyCert2d` (1214) | PWN | Generated/example/endpoint data placeholder; — |
| J | `KAM.Certificate.toyCert2_passes` (1216) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.toyCert2d_passes` (1218) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.toyCert2_torus` (1220) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.toyCert2d_torus` (1222) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.toyRatCert` (1226) | PWN | Generated/example/endpoint data placeholder; — |
| J | `KAM.Certificate.toyRatCert_passes` (1228) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.soHamExpr` (1241) | PWN | Concrete denotation or exact finite operation; — |
| I | `KAM.SpinOrbit.soHamExpr_eval` (1247) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.soHamExpr_clock` (1249) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunarFreqMinus_eq` (1254) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunarFreqPlus_eq` (1258) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.SoBarrier` (1265) | PWN | Invariant-graph semantics, derived from certificates; — |
| I | `KAM.SpinOrbit.SoGraphCert` (1277) | PWN | Finite numerical/data/syntax carrier; — |
| I | `KAM.SpinOrbit.checkSoGraph` (1289) | PWN | Algorithm placeholder; denotation/correctness not implemented; — |
| I | `KAM.SpinOrbit.soBarrier_of_cert` (1292) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.so_confinement` (1302) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.SoBackend` (1311) | PWN | Representation alias; backend choice awaits replay; — |
| I | `KAM.SpinOrbit.lunarLowerCert` (1314) | PWN | Generated/example/endpoint data placeholder; — |
| I | `KAM.SpinOrbit.lunarUpperCert` (1316) | PWN | Generated/example/endpoint data placeholder; — |
| I | `KAM.SpinOrbit.lunarLowerCert_ham` (1318) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunarUpperCert_ham` (1320) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunarLowerCert_passes` (1322) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunarUpperCert_passes` (1324) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunarLowerGraph_passes` (1326) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunarUpperGraph_passes` (1328) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunarLowerCert_freq` (1331) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunarUpperCert_freq` (1334) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunarPLo` (1338) | PWN | Generated/example/endpoint data placeholder; — |
| I | `KAM.SpinOrbit.lunarPHi` (1340) | PWN | Generated/example/endpoint data placeholder; — |
| I | `KAM.SpinOrbit.lunarPLo_lt_lunarPHi` (1342) | PWN | Reviewed statement; proof placeholder; U |
| I | `KAM.SpinOrbit.lunar_barriers` (1345) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunar_spin_confinement` (1352) | PWN | Reviewed statement; proof placeholder; S |


## Feasibility, errata, uncertainties and handoff

The revised package sums are arithmetically consistent: 7650 pre-gate + 8600 post-gate = 16250 still-to-write lines. The move of 100 exact-rational-instance lines changes scheduling without changing the total. Including the stated 400 clock and approximately 1500 other wave-0 lines gives 18150; 30–40% overrun on the unwritten part gives 21125–22750 before those landed additions. These remain planning estimates. File splits must independently respect 1500 lines. F10's scalar range-reduction wrapper and tests add work not explicitly costed in the table; revisit SO-AIF/SO-BALL/SO-EXPW estimates and measure the complete pin path, not only model products.

Backend-independent constant/π work, frequency enclosures, direct Fourier and expression semantics, positive-dimension norm bridges, inverse-matrix mathematics, graph inversion and barrier/ODE mathematics may proceed pre-gate on the displayed DAG. SO-BALL can use exact rational arithmetic pre-gate once its actual dependencies and F10 repair are supplied. Production backend selection, performance-sensitive convolution/model/witness algorithms and data remain subject to SO-REPLAY; lunar data additionally wait for G-J. Signature/kernel success for the engine supplies no replay timings, ulp accumulation or new lunar slack. Both feasibility gates remain open in the reviewed design.

No new suspected defect in a pinned mathematical source or frozen statement was established. F10 is a proposed interface versus selected implementation defect: the quoted unrestricted `certCExp_sound` omits the unit-size condition required by its Taylor remainder. The SO-AIF prover correctly reports and replaces it; that replacement is a declared interface deviation needing consumer reconciliation, not source errata. F7/F8/F9 were design corrections. The pilot's old 3% discrepancy remains explicit; D30's 33/1000 controls. Existing approved deviations remain: constant-window initial region, independent Fourier J with unpaid G-J attachment, bounded J polydisc, exact frequency in a theorem binder with rational enclosure, and deferred analytic graph/conjugacy claims. The auditor's temporary probe-size deviation is recorded above.

Files written: this report only. Approach: whole-carrier refutation of scalar/shape/norm contracts; exact producer-to-consumer and IG1Body comparison; independent signature/bridge/axiom probes; serialized targeted build, kernel replay and source/frozen/ABI lint. The concrete next design revision is F10's small primitive plus checked range reduction and explicit successful-call consumer contracts. F7, F8, F9 and F3/F6 need no reversal. The lunar theorem and checker proofs remain unproved.

Final compact-probe rerun: same signature-gate command on `.lake/abi-scratch/SOAudit3Probe.lean` (1430 lines), **exit 0**, **156** expected warnings, **0** errors, **113** axiom outputs with the same sets as above. Scratch files were removed after this receipt and report validation.
