# SO-DESIGN independent design audit 4

**Verdict: PASS WITH NOTES (design only). F10 is closed for every identified consumer. No new blocking design issue found. No SO theorem is seal-ready.**

Reviewed 2026-10-29 at `HEAD = 133a76025d1690b627ea98a916ae75289c51d306` (Revision 4 implementation-design commit `5767956a`), against `inp = d628f39ee7320757e0345cb7af9b5c018af60c2c`, using `git diff inp...HEAD`. The diff comprises five Markdown files only: the design, handoff, and audits 1–3 (3340 added lines). There is no new provider, production Lean module, or SO frozen anchor. Track I's existing sealed engine is the consumer; tracks N/P acquire no declaration or seal in this change.

The user's exact absolute destination overrides the generic brief's main-worktree report destination and historical handoff filenames. This report is the only repository-content edit. Probes were confined to this worktree's `.lake/abi-scratch/`, stayed below 1500 lines, and were deleted after validation. Every auditor Lean/Lake command was serialized, used `LEAN_NUM_THREADS=1` and `nice -n 5` directly or through the prescribed gate. No dependency refresh, clean, state-changing git, generated-root update, frozen-file edit, or sibling-worktree build was performed.

Authorities checked: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, Round 4 AUDIT FOCUS, handoff and audits 1–3; the current design and both signature copies; `.drafts/handoff-SO-DESIGN.md`; the controlling `/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md` including D30/O1–O4, proposal and pilot; frozen I-G1 and relevant strip, Gram, extended torsion/average and energy definitions; `IG1Body`, `g1_explicit`, track I statement, blueprint `bpI:p0:g1` and `bpI:p2:g1`. The newly relevant implementation sources are the landed shared `KAM/Certificate/Arith/{Interface,Roots}.lean` and `/root/code/KAM-inp-socexp/KAM/Certificate/Arith/ComplexExp.lean`. The older SO-AIF sibling path in the Round 3 brief no longer exists; the actual landed source was available in `/root/code/KAM-inp` and was used instead.

## Numbered findings

### F10 — previous HIGH finding CLOSED at design level

Locations: design Revision 4 table (lines 39–60), §1.4/§1.7, §5 replay item 7, §6 pins, §7/§8; Appendix A, equivalently `.drafts/design/SOSignatures.lean:229–317`, `503–553`, `703–725`, `750–774`, `1350–1362`.

The unrestricted `certCExp_sound` is withdrawn. The retained small primitive has its necessary `hsmall`; only the checked wrapper calls it. The general `certCExpReduced_sound` assumes successful computation and membership of the original input ball. It has **no input-size hypothesis**. There is no caller-side unit-disc premise in ball evaluation, witness soundness, composition, sub-check soundness, the black box, or the lunar statements. Keeping `hsmall` inside the explicitly named small primitive is correct.

The wrapper first forms `red = CertBall.times ⟨z,zRad⟩ (CertBall.ofRat (1/2^s))`. `mem_ofRat` pays conversion/scaling error; `mem_times` pays input and multiplication errors. It tests the rounded reduced ball, applies `certCExp_sound_of_small`, and squares the output ball `s` times. The identity `2^s * (w * (1/2^s)) = w` restores the intended exponential. Each squaring uses the proved ball product, including the quadratic radius term and centre-rounding errors. Neither a small unrounded centre nor an unchecked Taylor remainder substitutes for the test. A failed test returns `none`.

The exact type headers of `certCExp`, `certCExpSmall`, `certCExpSmall_sound`, `certCExp_sound_of_small` match landed `Roots.lean`, after whitespace normalization; the two `certCExpReduced` headers match the actual SO-CEXP file. `CertArith` and `LawfulCertArith` now also match the landed interface, including `abs`, `upMul`, and their laws. The ball carrier, membership predicate, rational-ball/product interfaces and their theorem types agree, accounting for namespace section variables. Implementations are restated as placeholders in the signature draft; they must be imported in production, not redefined there.

| Round-3 consumer | Revision-4 producer-to-consumer path | Verdict / remaining obligation |
|---|---|---|
| `Slp.balls`: arbitrary `HamExpr.exp`, compiled `sin`/`cos`, general domain balls | Each exp operand ball uses `certCExpReduced c r (cexpHalvings c r) taylorN`; failed call propagates `none`. `Slp.val_mem_ball` and denominator certification require a successful ball pass. | F10 closed. No caller smallness. Actual Slp algorithms/proofs remain to implement. |
| Automatic count over exact ℚ | `cexpHalvings = Nat.log2 ⌈2(|re|+|im|+r)⌉₊ + 1`; the proposed completeness theorem assumes only nonnegative radius. | Sound design. For L≥0 and M=⌈2L⌉₊, `2^(log2 M+1)>M≥2L`, including M=0, gives a reduced L1-size <1/2. Exact ℚ has no rounding enlargement. Completeness is not claimed for arbitrary lawful rounded backends. |
| `expWitnessRadius`: scalar pin | `expPinBall_sound` encloses the exact polynomial value at zero. Per-witness `pinHalvings`/`pinOrder` feed the wrapper. `expWitnessRadius_pin` states successful-call provenance and the exp enclosure. | F10 closed. `none` rejects the witness. No assumption that residual smallness implies pin smallness. |
| Pin budget ε₀ | `upAdd(|E(0)−out.1|↑, out.2)`; §C explicitly includes evaluation/subtraction rounding in the outward difference norm. | Pays input summation, scaling, Taylor remainder, Taylor arithmetic, every squaring, E evaluation and final subtraction. The analytic radius then pays `exp(2B) ε₀`, alongside residual and tail terms. Implementation must realize this formula. |
| Characters in `Slp.compose` | Both `expWit` and keyed `charWit` contain `ExpWitness`, so every `exp(2πi k·U)` pin has its own controls and the same repaired path. `compose_sound` is on `some ms`. | F10 closed, including large imaginary pins. Failed pins propagate to failed composition and the relevant checker stage. |
| Downstream torsion, HamBounds, invariance, energy and global soundness | Domain balls and composed models supply the same successful-call enclosures consumed by existing contracts. | No new size premise, conclusion weakening or missing F10 attachment in these signatures. |
| Real exp bounds, weights and witness growth factors | `ratExpUp`; real-route order/halving controls remain separate from complex-pin controls. | Unaffected. No need to force these through the complex small primitive. |
| Lunar client | No exp opcode in the domain Hamiltonian. Character pins use per-witness reduction and G-J must report each ε₀. | Sound conditional route; actual numerical pin budgets are still unpaid. |

Required implementation follow-through: prove the displayed algorithms and propagation properties, use the existing checked primitive, and execute the complete pin/composition/replay tests before claiming checker or lunar closure. These are explicitly planned proof obligations, not a new missing design contract.

### F11 — LOW, documentation: stale status and interface warning

Locations: `.drafts/handoff-SO-DESIGN.md`, Revision 4 uncertainties (“the draft's own CertArith stand-in ... lacks abs/upMul”); design §3/§9 (PI/clock build status) and Revision 4 historical status of SO-CEXP.

The current draft and landed arithmetic interface both contain `abs`/`upMul` and corresponding laws; the quoted warning is stale. The actual SO-CEXP source is now present and its generic proof independently re-elaborates. SO-PI/clock status remarks refer to old snapshots, whereas the input source table is explicitly historical. These do not invalidate the mathematical signatures. **Required change at the next documentation refresh:** replace the obsolete interface warning and label historical build/package statuses with their snapshot, without treating draft placeholders as imports or proof receipts. No source repair was made by this auditor.

### Carried findings F1–F9

F1/F2/F4 remain resolved by the exact real-frequency binder with a proved rational box, law-free direct real denotations plus lawful computed-operation theorems, and positive-error nonresonant toys (including n=3). F3/F6 remain resolved at interface level by explicit acyclic sub-check/torsion contracts, exact concatenation for polynomial addition, preserved denominator-validation obligations, shared phase basis, and the pre-gate exact rational instance. F7's exact `(n+1)×(n+1)` shape checks remain in the producer and averaging consumer at the same n. F8 retains `1≤n` in both vector-field norm bounds, derived from checker `2≤n`. F9 retains the correct original-J residual plus derivative difference. None needs reversal for the F10 repair.

## Engine and semantic fidelity

The following table records every binder group, rather than inferring closure from the black-box theorem's placeholder. A fresh **proved** `SOAudit4.engine_bridge` used `G1Hyps c ω` and `hdio` to apply `g1_explicit` in literal order, then used `hdisp` for both closeness inequalities; its axiom set excludes `sorryAx`.

| Frozen / explicit-engine binder group | Exact supplier / review |
|---|---|
| n≥2; τ≥n−1; 0<ρ∞<ρ | StaticFacts, same carriers; certificate τ is explicitly natural, cast to ℝ |
| positive M, σK, σB, σT, μ, γbar, ν; σω>1 | StaticFacts; g1 parameter order uses μ,γbar,σω,ν, while isoC1 uses μ,ν,γbar |
| exact ωstar≠0 | `checkStatic_freq` with the proved enclosure; never a rational-box centre in place of ωstar |
| D,H,K,s,γ,e,E₀ | `c.D,c.H,c.K,c.params.s,c.params.γ,c.params.err,c.params.E0` |
| D open and invariant under integer angle translations | literal strip × bounded polydisc; structural contract |
| H holomorphic, periodic, real on real D | structural expression semantics with certified denominator nonvanishing |
| all five derivative/field bounds on D | `checkHamBounds_sound`; third-order jets and positive-dimension norm bridges |
| K holomorphic/primary/real | direct law-free Fourier denotation; structural contract |
| μ-ball inclusion; DK≤σK−μ | `checkEmbedding_sound`, exact frozen margins |
| bilinear Gram invertibility and inverse row sums | `checkGram_sound`; no Hermitian or positivity substitution |
| averaged extended torsion determinant and inverse rows | `torsionModels_sound` → same-n shape/continuous enclosure → `torsionAvgCheck_sound` → `checkTorsion_sound` |
| 1<s<σω, ν≤(s−1)‖ωstar‖, ν≤(σω−s)‖ωstar‖ | static/frequency contracts; s is distinct from exact reference vector |
| 0<γ≤γbar; IsDiophantine γ τ ωstar; e≥0 | StaticFacts and external hdio on ωstar, not sωstar |
| full residual≤e and averaged energy error≤e | invariance/energy contracts on the actual candidate, using balls/composition and the exact vector enclosure |
| isoC1 smallness | SO-CONST dominance and `checkSmallness_sound` |
| all output clauses | `CertifiedTorus`: holomorphic/primary/real, exact invariance, pointwise energy, μ/2-ball and DK half-margin, both displacements≤disp |

The successful checker, proved backend laws, frequency-box fact and Diophantine membership remain the input boundary. “Only external mathematical input” means hdio after the backend and input-enclosure obligations are discharged; it must not erase those obligations. `G1Hyps`/`StaticFacts` are derived Props, never certificate fields. The fresh bridge verifies assembly compatibility, not the unproved `checkTorusCertificate_hyps` algorithm proof.

There is no open/closed-strip mismatch: frozen `complexStrip` is open. Positive checked weight width places the real cube inside the strip and continuity supports averaging. Integer `(2π)^deg` is positive; negative degrees use lower π bounds for upper estimates. Sup-norm tails are never differentiated: derivatives use exact Fourier polynomials or the inverse identity. Bilinear Gram matrices use a Neumann inverse certificate on the complex strip, with no real-positive argument. Literal extended torsion retains `DN[sω]`, border `sω`, and last row `DH(K)N`. Exact list shapes prevent the earlier leading-block counterexample.

The witness path bound remains conservative: periodic fundamental representatives give coordinate path length ≤1/2+ρ, the polynomial integrating-factor argument pays `exp(2B)(ε₀+Σ(1/2+ρ)r_j)`, and arbitrary sup tails pay `exp(B)(exp η−1)`. Repaired scalar pin evaluation supplies precisely the ε₀ needed by that argument. Reciprocal witnesses pay δ/(1−δ) and certify their own nonvanishing. Source-expression denominator checks must survive compiler folding/pruning, including `0*(1/0)` and powers zero; the design explicitly requires that.

The generic theorem remains dimension-polymorphic for n≥2, with a general exact frequency, finite Hamiltonian syntax including certified division, and all Fourier embedding components. It does not promise acceptance for every analytic expression or every candidate; invertibility, domain guards and the KAM inequalities are legitimately checked. Natural τ and finite expression syntax are explicit representation restrictions. No new frequency restriction or caller-side exp-size premise is introduced.

## Lunar reach and feasibility

D30's `|p(t)−1|≤33/1000`, all real times, unique global solutions, and O1's momentum window for arbitrary initial q/φ are retained. The clock fixes the second angle and s∞=2; positive q derivative after the `disp/ρ∞` Cauchy loss permits graph inversion. SOS pays its residual, p ranges widen by disp, and the physical globally Lipschitz field supplies global existence independently of confinement. O4's analytic graph/conjugacy claims stay deferred. The literal rational window endpoints and actual passing data remain prerequisites to a freeze.

The Fourier-J deviation is conditionally sound, with exact identity `E(K̃)_J=E(K₀)_J−D_(sωstar)ΔJ`, not just the derivative term. G-J must still establish `B_r+B₁+B_c≤e/2`, the other rows plus B_c≤e/2, energy B₀≤e/4, derivative budget B₂≤10⁻⁹⁰, all affected Gram/torsion/domain margins, and now each reduced-pin ε₀. The actual checker recomputes the full candidate. Neither this audit nor signature success establishes these numerical inequalities or fit within the pilot's margins.

The package arithmetic checks out: pre 7,850 plus post 8,650 = 16,500; Revision 4 adds 250 lines relative to 16,250. Including landed clock 400 and about 1,500 other wave-0 lines gives 18,400. Overrun on 16,500 gives 21,450–23,100 before those additions. These are planning estimates, and the table still counts landed SO-AIF work for comparability rather than as wholly remaining work. SO-CEXP 150 lines is credible for its ~80-line generic implementation plus small tests; the complete ball/witness path may require more than the +50 estimates in each downstream package. Jets, graph inversion and torsion remain the largest proof-estimation risks. The 1,494-line signature monolith is acceptable as this transient check; production splits must independently remain below 1500.

Backend-neutral arithmetic/constants/frequency/expression/denotation work, exact-ℚ domain balls, norm/inverse lemmas, graph mathematics and confinement may proceed on the listed pre-gate DAG. Backend selection and performance-sensitive polynomial/model/witness/checker implementation and data remain behind SO-REPLAY; SO-DATA additionally waits for G-J. Item 7 correctly adds complete reduced-pin and domain-ball exponential timing/memory/rational-growth measurements. The five small acceptance tests below are not those performance measurements. Both feasibility attachments remain open.

## Independent validation receipts

All Lean operations below finished sequentially. Gate scripts supply `nice -n 5`; direct replay/lint also use it. Signature probes elaborate against the shared inp build, as prescribed. Build/replay/lint use this audit worktree.

1. `git diff inp...HEAD` and `git diff dc55c821..HEAD -- docs/tracks/SO/design/SO-LEAN-DESIGN.md`: full branch scope and Revision 4 changes reviewed. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: **empty**. `git diff --check inp...HEAD` and `git diff --check`: **exit 0, no output**. No new provider signature/seal check applies to this documentation-only design.
2. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-so .drafts/design/SOSignatures.lean`: **exit 0**, **174** warnings, all `declaration uses 'sorry'`, **zero** errors. Local/shared draft and Markdown Appendix A compare byte-identical. Draft SHA-256: `95a45623f1cd75be9e406f32f2da407035b6663a7a8e98658541fbe4ff38a887`.
3. Same signature command with `.lake/abi-scratch/SOAudit4Probe.lean`: **exit 0**, **174** expected warnings, zero errors. This 985-line probe contains the comment/blank-compacted whole draft, fresh engine bridge, and axiom prints for **all 120 explicit draft theorems**, the bridge and engine (**122 outputs**). No new placeholder in the bridge. Of draft results: **118** have S, one has T, one has U:

   ```text
   S = [propext, sorryAx, Classical.choice, Quot.sound]
   T = [propext, sorryAx, Quot.sound]        (toyCert3_err_pos)
   U = [sorryAx]                           (lunarPLo_lt_lunarPHi)
   SOAudit4.engine_bridge = [propext, Classical.choice, Quot.sound]
   KAM.Iso.Apost.g1_explicit = [propext, Classical.choice, Quot.sound]
   ```

   In particular the draft reduced-exp, completeness, pin, Slp, sub-check, black-box, toy and lunar proofs still use `sorryAx`. This is an expected transient design exception, never a production proof hygiene pass.
4. Same signature gate with `.lake/abi-scratch/SOAudit4Reduced.lean`: **exit 0**, **zero warnings/errors**. This 109-line probe copies the actual SO-CEXP implementation/proof verbatim, imports the landed Roots module, and supplies a local exact rational arithmetic data instance. It proves the five proposed Boolean tests using **`decide +kernel`**, with no placeholder or budget override:

   ```text
   (z,r,s,N) = (1/2,0,0,8): isSome=true
   (1,1/2,0,8): none
   (2,0,0,8): none
   (2,0,2,8): isSome=true
   (19i,1/1000,5,12): isSome=true
   ```

   Printed axioms of the copied `certCExpReduced_sound`, landed `certCExp_sound_of_small`, `certCExpSmall_sound`, `CertBall.mem_times`, `CertBall.mem_ofRat` and all five tests: **ten outputs, each `[propext, Classical.choice, Quot.sound]`**. The exact-rational data instance is local test infrastructure, not a claim that the draft's placeholder `instCertArithRat` has been proved. The wrapper proof is generic over lawful backends. These tests verify acceptance/rejection, while its generic soundness theorem supplies the exponential enclosure; they do not execute placeholder Slp/composition algorithms.
5. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-design-so KAM.Iso.Apost.G1`: **exit 0**:

   ```text
   [inp-gate] slot 1 acquired 12:35:42 for KAM.Iso.Apost.G1
   Build completed successfully (3224 jobs).
   ```

6. `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Iso.Apost.G1`: **exit 0**, exact output `replaying KAM.Iso.Apost.G1`. This is kernel replay of the existing engine, not the unimplemented checker or sibling package.
7. `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`: **exit 0**. Exact output:

   ```text
   check_lean_modules: PASS (1281 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No generated-root exception was needed. The manifest records I-G1 as `SEALED`.
8. Comment-masked draft scan: **174** deliberate `sorry` tokens; no `axiom`, `admit`, `unsafe`, `opaque`, `EuclideanSpace`, `native_decide`, `implemented_by`, `maxHeartbeats` or `maxRecDepth`. No `set_option` or synthesis-budget override. The draft has copyright, `module`, public imports, docstring and exposed public section. No new production imports or provider-quarantine exceptions exist. No draft or final probe exceeds 1500 lines.

Source hashes independently recorded: landed shared Roots `93a799af570043c674886b8de1abc45678a6e4fb74e72d7e6433c4dd45058007`; read SO-CEXP source `66a31cd0655dfd619a5b552bb4571798d274cd321165367a2206b57cdab07d91`; design `19a463bd3e5d1307a7a3da8db2ea053f3bbed9ee8574a3fefc239b1703288f17`.

## Per-declaration review and definition classification

One row per **246 explicit declarations** in Appendix A; locations refer to the original 1494-line draft (Appendix A starts after design line 585). Generated projections/recursors are not separate source declarations. **PWN** means PASS WITH NOTES at design level, never seal-ready. S/T/U are the measured axiom sets above. Concrete bodies were reviewed over their whole carrier; missing entries in direct denotations use mathematical zero, keys use zero padding, list matrices require present entries, and algorithm placeholders are explicitly unpaid. Backend law fields are arithmetic laws, not hidden KAM conclusions. `PiHighCert` is a proved constant-bound interface, while the actual torus certificate uses numerical `PiEnclosure` data.

| Node | Lean declaration (draft line) | Verdict | Classification / reason; axioms |
|---|---|---|---|
| A | `KAM.Certificate.CertArith` (69) | PWN | Backend data interface |
| A | `KAM.Certificate.LawfulCertArith` (88) | PWN | Arithmetic soundness laws, proved per backend |
| A | `KAM.Certificate.CC` (108) | PWN | Finite data carrier |
| A | `KAM.Certificate.CC.toC` (113) | PWN | Concrete denotation / exact finite operation |
| A | `KAM.Certificate.CC.conj` (116) | PWN | Concrete denotation / exact finite operation |
| A | `KAM.Certificate.CC.toC_conj` (118) | PWN | Reviewed statement; draft proof unpaid; S |
| A | `KAM.Certificate.CC.toC_zero` (122) | PWN | Reviewed statement; draft proof unpaid; S |
| A | `KAM.Certificate.instCertArithRat` (133) | PWN | Backend instance placeholder; implementation/laws unpaid |
| A | `KAM.Certificate.instLawfulCertArithRat` (135) | PWN | Backend instance placeholder; implementation/laws unpaid |
| A | `KAM.Certificate.CertFixed` (138) | PWN | Finite data carrier |
| A | `KAM.Certificate.instCertArithFixed` (141) | PWN | Backend instance placeholder; implementation/laws unpaid |
| A | `KAM.Certificate.instLawfulCertArithFixed` (143) | PWN | Backend instance placeholder; implementation/laws unpaid |
| A | `KAM.Certificate.ratExpUp` (149) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| A | `KAM.Certificate.exp_le_ratExpUp` (151) | PWN | Reviewed statement; draft proof unpaid; S |
| A | `KAM.Certificate.piLoQ` (159) | PWN | Concrete denotation / exact finite operation |
| A | `KAM.Certificate.piUpQ` (161) | PWN | Concrete denotation / exact finite operation |
| A | `KAM.Certificate.piLoQ_lt_pi` (163) | PWN | Reviewed statement; draft proof unpaid; S |
| A | `KAM.Certificate.pi_lt_piUpQ` (165) | PWN | Reviewed statement; draft proof unpaid; S |
| A | `KAM.Certificate.atanS` (168) | PWN | Concrete denotation / exact finite operation |
| A | `KAM.Certificate.piLowRat` (171) | PWN | Concrete denotation / exact finite operation |
| A | `KAM.Certificate.piUpRat` (173) | PWN | Concrete denotation / exact finite operation |
| A | `KAM.Certificate.piLowRat_lt_pi` (175) | PWN | Reviewed statement; draft proof unpaid; S |
| A | `KAM.Certificate.pi_lt_piUpRat` (177) | PWN | Reviewed statement; draft proof unpaid; S |
| A | `KAM.Certificate.PiHighCert` (180) | PWN | Certified π bounds interface, contains proofs |
| A | `KAM.Certificate.eSum` (186) | PWN | Concrete denotation / exact finite operation |
| A | `KAM.Certificate.eRem` (188) | PWN | Concrete denotation / exact finite operation |
| A | `KAM.Certificate.eLowRat` (190) | PWN | Concrete denotation / exact finite operation |
| A | `KAM.Certificate.eUpRat` (192) | PWN | Concrete denotation / exact finite operation |
| A | `KAM.Certificate.eLowRat_lt_exp_one` (194) | PWN | Reviewed statement; draft proof unpaid; S |
| A | `KAM.Certificate.exp_one_lt_eUpRat` (196) | PWN | Reviewed statement; draft proof unpaid; S |
| A | `KAM.Certificate.PiEnclosure` (203) | PWN | Finite data carrier |
| A | `KAM.Certificate.checkPiEnclosure` (211) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| A | `KAM.Certificate.checkPiEnclosure_sound` (213) | PWN | Reviewed statement; draft proof unpaid; S |
| A | `KAM.Certificate.checkRootEnclosure` (219) | PWN | Concrete denotation / exact finite operation |
| A | `KAM.Certificate.rpow_mem_of_checkRootEnclosure` (222) | PWN | Reviewed statement; draft proof unpaid; S |
| A | `KAM.Certificate.sqrt_mem_of_checkRootEnclosure` (226) | PWN | Reviewed statement; draft proof unpaid; S |
| A | `KAM.Certificate.CertBall` (233) | PWN | Finite data carrier |
| A | `KAM.Certificate.CertBall.Mem` (238) | PWN | Concrete semantic predicate / exact matrix shape |
| A | `KAM.Certificate.CC.normUp` (242) | PWN | Restated implemented arithmetic algorithm; replace stand-in by import |
| A | `KAM.Certificate.CertBall.ofRat` (245) | PWN | Restated implemented arithmetic algorithm; replace stand-in by import |
| A | `KAM.Certificate.CertBall.times` (248) | PWN | Restated implemented arithmetic algorithm; replace stand-in by import |
| A | `KAM.Certificate.CertBall.mem_ofRat` (250) | PWN | Matches actual proved implementation contract; draft S |
| A | `KAM.Certificate.CertBall.mem_times` (253) | PWN | Matches actual proved implementation contract; draft S |
| A | `KAM.Certificate.certCExp` (268) | PWN | Restated implemented arithmetic algorithm; replace stand-in by import |
| A | `KAM.Certificate.certCExpSmall` (271) | PWN | Restated implemented arithmetic algorithm; replace stand-in by import |
| A | `KAM.Certificate.certCExpSmall_sound` (273) | PWN | Matches actual proved implementation contract; draft S |
| A | `KAM.Certificate.certCExp_sound_of_small` (279) | PWN | Matches actual proved implementation contract; draft S |
| A | `KAM.Certificate.certCExpReduced` (299) | PWN | Restated implemented arithmetic algorithm; replace stand-in by import |
| A | `KAM.Certificate.certCExpReduced_sound` (302) | PWN | Matches actual proved implementation contract; draft S |
| A | `KAM.Certificate.cexpHalvings` (309) | PWN | Concrete denotation / exact finite operation |
| A | `KAM.Certificate.certCExpReduced_cexpHalvings_isSome` (314) | PWN | Exact-ℚ completeness, no size premise; proof unpaid; S |
| B | `KAM.Certificate.CertKey` (320) | PWN | Representation alias |
| B | `KAM.Certificate.certKeyFun` (323) | PWN | Concrete denotation / exact finite operation |
| B | `KAM.Certificate.CertPoly` (327) | PWN | Finite data carrier |
| B | `KAM.Certificate.CertPoly.eval` (331) | PWN | Concrete denotation / exact finite operation |
| B | `KAM.Certificate.CertPoly.coeff` (335) | PWN | Concrete denotation / exact finite operation |
| B | `KAM.Certificate.CertPoly.eval_eq_fourierSum` (339) | PWN | Reviewed statement; draft proof unpaid; S |
| B | `KAM.Certificate.CertPoly.differentiable_eval` (342) | PWN | Reviewed statement; draft proof unpaid; S |
| B | `KAM.Certificate.CertPoly.eval_add_int` (345) | PWN | Reviewed statement; draft proof unpaid; S |
| B | `KAM.Certificate.CertRealPoly` (349) | PWN | Finite data carrier |
| B | `KAM.Certificate.CertRealPoly.eval` (354) | PWN | Concrete denotation / exact finite operation |
| B | `KAM.Certificate.CertRealPoly.eval_real` (360) | PWN | Reviewed statement; draft proof unpaid; S |
| B | `KAM.Certificate.CertRealPoly.differentiable_eval` (363) | PWN | Reviewed statement; draft proof unpaid; S |
| B | `KAM.Certificate.CertRealPoly.eval_add_int` (366) | PWN | Reviewed statement; draft proof unpaid; S |
| B | `KAM.Certificate.CertRealPoly.toPoly` (371) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| B | `KAM.Certificate.CertRealPoly.eval_toPoly` (374) | PWN | Reviewed statement; draft proof unpaid; S |
| B | `KAM.Certificate.CertRealPoly.conjugateSymmetric` (377) | PWN | Reviewed statement; draft proof unpaid; S |
| B | `KAM.Certificate.CertPoly.add` (383) | PWN | Concrete denotation / exact finite operation |
| B | `KAM.Certificate.CertPoly.eval_add` (385) | PWN | Reviewed statement; draft proof unpaid; S |
| B | `KAM.Certificate.CertPoly.shift` (389) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| B | `KAM.Certificate.CertPoly.eval_shift` (391) | PWN | Reviewed statement; draft proof unpaid; S |
| B | `KAM.Certificate.CertPoly.conjReflect` (396) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| B | `KAM.Certificate.CertPoly.eval_conjReflect` (398) | PWN | Reviewed statement; draft proof unpaid; S |
| C | `KAM.Certificate.CertWeight` (405) | PWN | Finite data carrier |
| C | `KAM.Certificate.checkWeight` (411) | PWN | Concrete denotation / exact finite operation |
| C | `KAM.Certificate.norm_character_le_weight` (414) | PWN | Reviewed statement; draft proof unpaid; S |
| C | `KAM.Certificate.CertModel` (420) | PWN | Finite data carrier |
| C | `KAM.Certificate.CertModel.Encloses` (426) | PWN | Concrete semantic predicate / exact matrix shape |
| C | `KAM.Certificate.CertModel.supBound` (433) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| C | `KAM.Certificate.CertModel.norm_le_supBound` (435) | PWN | Reviewed statement; draft proof unpaid; S |
| C | `KAM.Certificate.ModelConfig` (441) | PWN | Finite data carrier |
| C | `KAM.Certificate.CertModel.add` (449) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| C | `KAM.Certificate.CertModel.mul` (452) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| C | `KAM.Certificate.CertModel.trim` (456) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| C | `KAM.Certificate.CertModel.toDeg` (460) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| C | `KAM.Certificate.CertModel.ofDeriv` (465) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| C | `KAM.Certificate.CertModel.Encloses.ofDeriv` (468) | PWN | Reviewed statement; draft proof unpaid; S |
| C | `KAM.Certificate.CertModel.Encloses.add` (473) | PWN | Reviewed statement; draft proof unpaid; S |
| C | `KAM.Certificate.CertModel.Encloses.mul` (478) | PWN | Reviewed statement; draft proof unpaid; S |
| C | `KAM.Certificate.CertModel.Encloses.trim` (483) | PWN | Reviewed statement; draft proof unpaid; S |
| C | `KAM.Certificate.CertModel.Encloses.toDeg` (488) | PWN | Reviewed statement; draft proof unpaid; S |
| C | `KAM.Certificate.CertModel.Encloses.average` (494) | PWN | Reviewed statement; draft proof unpaid; S |
| C | `KAM.Certificate.ExpWitness` (521) | PWN | Finite data carrier |
| C | `KAM.Certificate.expPinBall` (528) | PWN | F10 repaired pin algorithm specification; implementation unpaid |
| C | `KAM.Certificate.expPinBall_sound` (530) | PWN | F10 repaired pin enclosure/budget, on success; proof unpaid; S |
| C | `KAM.Certificate.expWitnessRadius` (536) | PWN | F10 repaired pin algorithm specification; implementation unpaid |
| C | `KAM.Certificate.expWitnessRadius_pin` (541) | PWN | F10 repaired pin enclosure/budget, on success; proof unpaid; S |
| C | `KAM.Certificate.expWitness_sound` (547) | PWN | F10 repaired pin enclosure/budget, on success; proof unpaid; S |
| C | `KAM.Certificate.invWitnessRadius` (555) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| C | `KAM.Certificate.invWitness_sound` (558) | PWN | Reviewed statement; draft proof unpaid; S |
| D | `KAM.Certificate.phaseBasis` (570) | PWN | Concrete denotation / exact finite operation |
| D | `KAM.Certificate.HamExpr` (578) | PWN | Finite expression/program syntax |
| D | `KAM.Certificate.modePhase` (593) | PWN | Concrete denotation / exact finite operation |
| D | `KAM.Certificate.HamExpr.eval` (598) | PWN | Concrete denotation / exact finite operation |
| D | `KAM.Certificate.HamExpr.NonvanishingOn` (613) | PWN | Concrete semantic predicate / exact matrix shape |
| D | `KAM.Certificate.HamExpr.contDiffOn_eval` (623) | PWN | Reviewed statement; draft proof unpaid; S |
| D | `KAM.Certificate.HamExpr.eval_add_int` (626) | PWN | Reviewed statement; draft proof unpaid; S |
| D | `KAM.Certificate.HamExpr.eval_real` (629) | PWN | Reviewed statement; draft proof unpaid; S |
| D | `KAM.Certificate.SlpOp` (634) | PWN | Finite expression/program syntax |
| D | `KAM.Certificate.Slp` (643) | PWN | Finite data carrier |
| D | `KAM.Certificate.Slp.val` (647) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| D | `KAM.Certificate.HamJet` (653) | PWN | Finite data carrier |
| D | `KAM.Certificate.phaseNat` (661) | PWN | Concrete denotation / exact finite operation |
| D | `KAM.Certificate.HamExpr.jet` (665) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| D | `KAM.Certificate.HamExpr.jet_v0` (667) | PWN | Reviewed statement; draft proof unpaid; S |
| D | `KAM.Certificate.HamExpr.jet_d1` (670) | PWN | Reviewed statement; draft proof unpaid; S |
| D | `KAM.Certificate.HamExpr.jet_d2` (676) | PWN | Reviewed statement; draft proof unpaid; S |
| D | `KAM.Certificate.HamExpr.jet_d3` (682) | PWN | Reviewed statement; draft proof unpaid; S |
| D | `KAM.Certificate.certDomain` (690) | PWN | Concrete denotation / exact finite operation |
| D | `KAM.Certificate.isOpen_certDomain` (695) | PWN | Reviewed statement; draft proof unpaid; S |
| D | `KAM.Certificate.certDomain_add_int` (698) | PWN | Reviewed statement; draft proof unpaid; S |
| D | `KAM.Certificate.Slp.balls` (710) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| D | `KAM.Certificate.Slp.val_mem_ball` (713) | PWN | Reviewed statement; draft proof unpaid; S |
| D | `KAM.Certificate.HamExpr.nonvanishingOn_of_balls` (721) | PWN | Reviewed statement; draft proof unpaid; S |
| D | `KAM.Certificate.CertEmbedding` (728) | PWN | Finite data carrier |
| D | `KAM.Certificate.CertEmbedding.eval` (734) | PWN | Concrete denotation / exact finite operation |
| D | `KAM.Certificate.CertEmbedding.differentiable_eval` (741) | PWN | Reviewed statement; draft proof unpaid; S |
| D | `KAM.Certificate.CertEmbedding.isPrimaryOnStrip` (744) | PWN | Reviewed statement; draft proof unpaid; S |
| D | `KAM.Certificate.CertEmbedding.isRealOnReals` (748) | PWN | Reviewed statement; draft proof unpaid; S |
| D | `KAM.Certificate.Witnesses` (756) | PWN | Finite data carrier |
| D | `KAM.Certificate.Slp.compose` (763) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| D | `KAM.Certificate.Slp.compose_sound` (768) | PWN | Reviewed statement; draft proof unpaid; S |
| E | `KAM.Certificate.norm_fderiv_le_sum_partials` (778) | PWN | Reviewed statement; draft proof unpaid; S |
| E | `KAM.Certificate.norm_iteratedFDeriv_two_le_sum_partials` (782) | PWN | Reviewed statement; draft proof unpaid; S |
| E | `KAM.Certificate.hamiltonianVectorFieldℂ_sumVec` (789) | PWN | Reviewed statement; draft proof unpaid; S |
| E | `KAM.Certificate.norm_fderiv_hamiltonianVectorFieldℂ_le` (798) | PWN | Reviewed statement; draft proof unpaid; S |
| E | `KAM.Certificate.norm_iteratedFDeriv_two_hamiltonianVectorFieldℂ_le` (806) | PWN | Reviewed statement; draft proof unpaid; S |
| F | `KAM.Certificate.matrix_inv_of_approx_inverse` (816) | PWN | Reviewed statement; draft proof unpaid; S |
| F | `KAM.Certificate.ModelMatrix` (821) | PWN | Representation alias |
| F | `KAM.Certificate.ModelMatrix.Encloses` (825) | PWN | Concrete semantic predicate / exact matrix shape |
| F | `KAM.Certificate.ModelMatrix.HasShape` (833) | PWN | Concrete semantic predicate / exact matrix shape |
| F | `KAM.Certificate.polyMatrix` (837) | PWN | Concrete denotation / exact finite operation |
| F | `KAM.Certificate.gramModels` (842) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| F | `KAM.Certificate.gramModels_sound` (845) | PWN | Reviewed statement; draft proof unpaid; S |
| F | `KAM.Certificate.gramCheck` (853) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| F | `KAM.Certificate.gramCheck_sound` (857) | PWN | Reviewed statement; draft proof unpaid; S |
| F | `KAM.Certificate.torsionIdx` (868) | PWN | Concrete denotation / exact finite operation |
| F | `KAM.Certificate.FreqBox` (872) | PWN | Representation alias |
| F | `KAM.Certificate.FreqEncloses` (874) | PWN | Concrete semantic predicate / exact matrix shape |
| F | `KAM.Certificate.torsionModels` (882) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| F | `KAM.Certificate.torsionModels_sound` (891) | PWN | Reviewed statement; draft proof unpaid; S |
| F | `KAM.Certificate.torsionAvgCheck` (909) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| F | `KAM.Certificate.torsionAvgCheck_shape` (913) | PWN | Reviewed statement; draft proof unpaid; S |
| F | `KAM.Certificate.torsionAvgCheck_sound` (917) | PWN | Reviewed statement; draft proof unpaid; S |
| F | `KAM.Certificate.cRUpQ` (928) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| F | `KAM.Certificate.cR_le_cRUpQ` (930) | PWN | Reviewed statement; draft proof unpaid; S |
| F | `KAM.Certificate.isoC1Q` (934) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| F | `KAM.Certificate.isoC2Q` (936) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| F | `KAM.Certificate.isoC1_le_isoC1Q` (938) | PWN | Reviewed statement; draft proof unpaid; S |
| F | `KAM.Certificate.isoC2_le_isoC2Q` (944) | PWN | Reviewed statement; draft proof unpaid; S |
| F | `KAM.Certificate.checkRealLowerBound` (952) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| F | `KAM.Certificate.checkRealLowerBound_sound` (955) | PWN | Reviewed statement; draft proof unpaid; S |
| G | `KAM.Certificate.algFreq` (972) | PWN | Concrete denotation / exact finite operation |
| G | `KAM.Certificate.checkAlgBox` (978) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| G | `KAM.Certificate.algFreq_encloses` (980) | PWN | Reviewed statement; draft proof unpaid; S |
| G | `KAM.Certificate.CertParams` (987) | PWN | Finite data carrier |
| G | `KAM.Certificate.TorusCertificate` (1008) | PWN | Finite data carrier |
| G | `KAM.Certificate.TorusCertificate.D` (1033) | PWN | Concrete denotation / exact finite operation |
| G | `KAM.Certificate.TorusCertificate.H` (1036) | PWN | Concrete denotation / exact finite operation |
| G | `KAM.Certificate.TorusCertificate.K` (1038) | PWN | Concrete denotation / exact finite operation |
| G | `KAM.Certificate.checkStatic` (1048) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| G | `KAM.Certificate.checkHamBounds` (1052) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| G | `KAM.Certificate.checkEmbedding` (1055) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| G | `KAM.Certificate.checkInvariance` (1058) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| G | `KAM.Certificate.checkEnergy` (1061) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| G | `KAM.Certificate.checkGram` (1064) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| G | `KAM.Certificate.checkTorsion` (1068) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| G | `KAM.Certificate.checkSmallness` (1071) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| G | `KAM.Certificate.checkTorusCertificate` (1075) | PWN | Concrete denotation / exact finite operation |
| G | `KAM.Certificate.G1Hyps` (1085) | PWN | Derived engine/static facts (Prop), never input certificate data |
| G | `KAM.Certificate.CertifiedTorus` (1138) | PWN | Concrete semantic predicate / exact matrix shape |
| G | `KAM.Certificate.StaticFacts` (1157) | PWN | Derived engine/static facts (Prop), never input certificate data |
| G | `KAM.Certificate.checkStatic_sound` (1182) | PWN | Reviewed statement; draft proof unpaid; S |
| G | `KAM.Certificate.checkStatic_freq` (1186) | PWN | Reviewed statement; draft proof unpaid; S |
| G | `KAM.Certificate.TorusCertificate.emb_structural` (1192) | PWN | Reviewed statement; draft proof unpaid; S |
| G | `KAM.Certificate.checkHamBounds_sound` (1196) | PWN | Reviewed statement; draft proof unpaid; S |
| G | `KAM.Certificate.TorusCertificate.ham_structural` (1205) | PWN | Reviewed statement; draft proof unpaid; S |
| G | `KAM.Certificate.checkEmbedding_sound` (1213) | PWN | Reviewed statement; draft proof unpaid; S |
| G | `KAM.Certificate.checkGram_sound` (1219) | PWN | Reviewed statement; draft proof unpaid; S |
| G | `KAM.Certificate.checkInvariance_sound` (1224) | PWN | Reviewed statement; draft proof unpaid; S |
| G | `KAM.Certificate.checkEnergy_sound` (1230) | PWN | Reviewed statement; draft proof unpaid; S |
| G | `KAM.Certificate.checkTorsion_sound` (1237) | PWN | Reviewed statement; draft proof unpaid; S |
| G | `KAM.Certificate.checkSmallness_sound` (1244) | PWN | Reviewed statement; draft proof unpaid; S |
| G | `KAM.Certificate.checkTorusCertificate_hyps` (1255) | PWN | Reviewed statement; draft proof unpaid; S |
| G | `KAM.Certificate.checkTorusCertificate_sound` (1265) | PWN | Reviewed statement; draft proof unpaid; S |
| H | `KAM.Certificate.clock_frequency` (1278) | PWN | Reviewed statement; draft proof unpaid; S |
| J | `KAM.Certificate.cbrtTwo` (1294) | PWN | Concrete denotation / exact finite operation |
| J | `KAM.Certificate.cubicFreq` (1297) | PWN | Concrete denotation / exact finite operation |
| J | `KAM.Certificate.cubicFreq_eq_algFreq` (1299) | PWN | Reviewed statement; draft proof unpaid; S |
| J | `KAM.Certificate.cubicFreq_isDiophantine` (1305) | PWN | Reviewed statement; draft proof unpaid; S |
| J | `KAM.Certificate.toyHam3` (1308) | PWN | Concrete denotation / exact finite operation |
| J | `KAM.Certificate.toyCert3` (1315) | PWN | Generated/example/endpoint data placeholder; unpaid |
| J | `KAM.Certificate.toyCert3_ham` (1317) | PWN | Reviewed statement; draft proof unpaid; S |
| J | `KAM.Certificate.toyCert3_err_pos` (1319) | PWN | Reviewed statement; draft proof unpaid; T |
| J | `KAM.Certificate.toyCert3_passes` (1321) | PWN | Reviewed statement; draft proof unpaid; S |
| J | `KAM.Certificate.toyCert3_freq` (1323) | PWN | Reviewed statement; draft proof unpaid; S |
| J | `KAM.Certificate.toyCert3_torus` (1326) | PWN | Reviewed statement; draft proof unpaid; S |
| J | `KAM.Certificate.toyCert2` (1331) | PWN | Generated/example/endpoint data placeholder; unpaid |
| J | `KAM.Certificate.toyCert2d` (1333) | PWN | Generated/example/endpoint data placeholder; unpaid |
| J | `KAM.Certificate.toyCert2_passes` (1335) | PWN | Reviewed statement; draft proof unpaid; S |
| J | `KAM.Certificate.toyCert2d_passes` (1337) | PWN | Reviewed statement; draft proof unpaid; S |
| J | `KAM.Certificate.toyCert2_torus` (1339) | PWN | Reviewed statement; draft proof unpaid; S |
| J | `KAM.Certificate.toyCert2d_torus` (1341) | PWN | Reviewed statement; draft proof unpaid; S |
| J | `KAM.Certificate.toyRatCert` (1345) | PWN | Generated/example/endpoint data placeholder; unpaid |
| J | `KAM.Certificate.toyRatCert_passes` (1347) | PWN | Reviewed statement; draft proof unpaid; S |
| J | `KAM.Certificate.cexpTest_zero_small` (1353) | PWN | Scalar accept/reject test; proved independently against real wrapper; draft S |
| J | `KAM.Certificate.cexpTest_zero_large` (1355) | PWN | Scalar accept/reject test; proved independently against real wrapper; draft S |
| J | `KAM.Certificate.cexpTest_two_rejected` (1357) | PWN | Scalar accept/reject test; proved independently against real wrapper; draft S |
| J | `KAM.Certificate.cexpTest_two_reduced` (1359) | PWN | Scalar accept/reject test; proved independently against real wrapper; draft S |
| J | `KAM.Certificate.cexpTest_large_pin` (1361) | PWN | Scalar accept/reject test; proved independently against real wrapper; draft S |
| I | `KAM.SpinOrbit.soHamExpr` (1375) | PWN | Concrete denotation / exact finite operation |
| I | `KAM.SpinOrbit.soHamExpr_eval` (1381) | PWN | Reviewed statement; draft proof unpaid; S |
| I | `KAM.SpinOrbit.soHamExpr_clock` (1383) | PWN | Reviewed statement; draft proof unpaid; S |
| I | `KAM.SpinOrbit.lunarFreqMinus_eq` (1388) | PWN | Reviewed statement; draft proof unpaid; S |
| I | `KAM.SpinOrbit.lunarFreqPlus_eq` (1392) | PWN | Reviewed statement; draft proof unpaid; S |
| I | `KAM.SpinOrbit.SoBarrier` (1399) | PWN | Invariant-graph semantics derived by the client |
| I | `KAM.SpinOrbit.SoGraphCert` (1411) | PWN | Finite data carrier |
| I | `KAM.SpinOrbit.checkSoGraph` (1423) | PWN | Algorithm placeholder; whole-carrier implementation and correctness unpaid |
| I | `KAM.SpinOrbit.soBarrier_of_cert` (1426) | PWN | Reviewed statement; draft proof unpaid; S |
| I | `KAM.SpinOrbit.so_confinement` (1436) | PWN | Reviewed statement; draft proof unpaid; S |
| I | `KAM.SpinOrbit.SoBackend` (1445) | PWN | Representation alias; backend choice pending replay |
| I | `KAM.SpinOrbit.lunarLowerCert` (1448) | PWN | Generated/example/endpoint data placeholder; unpaid |
| I | `KAM.SpinOrbit.lunarUpperCert` (1450) | PWN | Generated/example/endpoint data placeholder; unpaid |
| I | `KAM.SpinOrbit.lunarLowerCert_ham` (1452) | PWN | Reviewed statement; draft proof unpaid; S |
| I | `KAM.SpinOrbit.lunarUpperCert_ham` (1454) | PWN | Reviewed statement; draft proof unpaid; S |
| I | `KAM.SpinOrbit.lunarLowerCert_passes` (1456) | PWN | Reviewed statement; draft proof unpaid; S |
| I | `KAM.SpinOrbit.lunarUpperCert_passes` (1458) | PWN | Reviewed statement; draft proof unpaid; S |
| I | `KAM.SpinOrbit.lunarLowerGraph_passes` (1460) | PWN | Reviewed statement; draft proof unpaid; S |
| I | `KAM.SpinOrbit.lunarUpperGraph_passes` (1462) | PWN | Reviewed statement; draft proof unpaid; S |
| I | `KAM.SpinOrbit.lunarLowerCert_freq` (1465) | PWN | Reviewed statement; draft proof unpaid; S |
| I | `KAM.SpinOrbit.lunarUpperCert_freq` (1468) | PWN | Reviewed statement; draft proof unpaid; S |
| I | `KAM.SpinOrbit.lunarPLo` (1472) | PWN | Generated/example/endpoint data placeholder; unpaid |
| I | `KAM.SpinOrbit.lunarPHi` (1474) | PWN | Generated/example/endpoint data placeholder; unpaid |
| I | `KAM.SpinOrbit.lunarPLo_lt_lunarPHi` (1476) | PWN | Reviewed statement; draft proof unpaid; U |
| I | `KAM.SpinOrbit.lunar_barriers` (1479) | PWN | Reviewed statement; draft proof unpaid; S |
| I | `KAM.SpinOrbit.lunar_spin_confinement` (1486) | PWN | Reviewed statement; draft proof unpaid; S |

## Errata, deviations and handoff

No new suspected defect in a pinned mathematical source, frozen statement or blueprint was established. The original unrestricted-exp defect was an interface/implementation error and has been explicitly corrected, not attributed to HL19. The pilot's old 3% band remains a documented failed target; D30's 33/1000 controls. Declared deviations remain the approved constant-window initial region, Fourier J with fresh G-J attachment, bounded auxiliary-J domain, exact frequency in a theorem binder with a proved rational box, and deferred analytic graphs/conjugacy. Revision 4 adds per-witness pin order/halving fields, a necessary certificate-data format change. The reporter introduced no mathematical/source deviation.

Files written: this report only. Approach: refute-first whole-carrier and producer/consumer review; actual implementation signature comparison; fresh engine bridge and exhaustive theorem-axiom probe; actual wrapper proof replay through elaboration and five kernel-decided acceptance tests; serialized targeted build, kernel replay, lint and protected-path checks. The result approves the **design repair**, while the checker implementation, all placeholder proofs, literal endpoint data, complete performance gate, and actual lunar G-J invoices remain unpaid.
