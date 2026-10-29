# SO-DESIGN independent design audit 2

**Verdict: FAIL — repair the remaining exact contracts before approving Revision 2.**

This is a design audit, not proof-package acceptance or anchor sealing. Revision 2 closes the original higher-dimensional frequency obstruction and the arithmetic-reality defect. Its engine application is correct. The averaged-torsion interface still lacks a dimension/shape attachment (F7), two public norm contracts are literally false at dimension zero (F8), and the revised lunar residual identity is incorrect (F9). No accepting counterexample to an implemented checker is claimed: the checker bodies remain placeholders.

Audited `/root/code/KAM-inp-design-so`, HEAD `d2352a2db82726ce425ffc775a248f147dbc8a93`, against `inp` observed at `22a2bd62679248ea5072ac1f3f3d3531f288dbb6`, using the full `git diff inp...HEAD`. The three-dot diff adds only the design (1826 lines), audit 1 (375 lines), and the committed handoff (67 lines). The working handoff already had an uncommitted Round 2 addition; it was read and preserved. There is no changed production Lean module, provider, frozen anchor, manifest, generated root or README. No anchor verdict of PASS (seal-ready) is applicable.

The user's exact absolute destination overrides the generic brief's main-worktree destination and the older filename inside the handoff. The sole repository-content write by this auditor is this report. Temporary probes/logs were confined to this worktree's `.lake/abi-scratch/` and removed after their results were captured here. No state-changing git command was used. All auditor Lean/Lake invocations were serialized with `LEAN_NUM_THREADS=1`; Lean commands used `nice -n 5`, including through the prescribed gates.

Authorities: AGENTS.md, docs/PLAN.md and DECISIONS.md; `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`; the Round 2 handoff and audit 1; the full Revision 2 design and signatures; the controlling SO plan with O1–O4, proposal and pilot in `/root/code/KAM`; `IG1Body`, `g1_explicit`, the frozen I-G1 and its strip/Gram/normal-frame/torsion/average/Diophantine conventions; blueprint-I `bpI:p0:g1` and `bpI:p2:g1`; and the current SO-MODEL, SO-DIO, SO-CLOCK and PiHigh interfaces. Track N/P supply no SO implementation node or new anchor here. No SO blueprint or frozen SO theorem is introduced by this diff.

Appendix A is byte-identical to `.drafts/design/SOSignatures.lean`, and that file is byte-identical to `/root/code/KAM-inp/.drafts/design/SOSignatures.lean`: 1337 lines, SHA-256 `10f24738f9940db5edabdf59e3de81b3cf018b5943a6b2f6b6db7f45a57ba839`. The controlling plan/proposal/pilot and engine/Inputs hashes match the design's pins. PiHigh in current `inp` and `inp-sopi` both have the pinned SHA-256 `0ee583ddcb69816240e0a38376de2819c71688941cc990f97f1dd00a1e907880`. The design's description of PiHigh as still running is now historical; its stand-in surface matches the landed module.

## Original findings F1–F6

| Finding | Round 2 assessment | Reason / remaining obligation |
|---|---|---|
| F1 frequency carrier | CLOSED at design level | `ωstar : Fin n → ℝ` is an exact theorem binder; `freqBox` constrains only finite arithmetic. `FreqEncloses` is a legitimate input-denotation proof, not an assumed KAM conclusion. The same-field quadratic obstruction is gone. |
| F2 law-free reality | CLOSED | Direct `CertRealPoly.eval` uses mathematical conjugation and a real constant; missing embedding components denote mathematical zero. `toPoly`, backend conjugation and computed correctness theorems carry the laws. The prior Unit-carrier counterexample no longer applies. |
| F3 missing torsion/sub-check contracts | SUBSTANTIALLY REPAIRED, not fully closed | `torsionModels_sound` now produces the literal frozen extended torsion and continuity from a successful Gram certificate, nonvanishing, domain inclusion and an enclosed exact frequency. All eight contracts are listed. F7 prevents accepting the averaging consumer contract as complete. |
| F4 unrepresentable zero-error toy | CLOSED at design level | T2/T2d/T3 use rational approximations with positive residuals; TR is explicitly checker-only and resonant. No exact irrational constant is demanded from rational Fourier coefficients. Actual passing data/proofs remain future work. |
| F5 Fourier J / pilot margins | Soundness route repaired; quantitative attachment OPEN | Every actual four-component sub-check is rerun; gate G-J explicitly demands weighted error/derivative budgets and recomputed margins. These are requirements, not delivered numerical evidence. Correct F9's identity. |
| F6 scheduling/DAG | REPAIRED WITH NOTE | Backend interface and backend implementation are separated; PhaseBasis is shared; post-gate implementation waits for SO-REPLAY. SO-BALL's rational ball correctness still references the concrete `CertArith ℚ` instance listed in post-gate SO-ABK: move the trivial rational denotation/interface support earlier, or state its pre-gate work is specification only. |

For F1's n=3 example, let x=∛2. The norm of β=k₀+k₁x+k₂x² is the nonzero integer `k₀³+2k₁³+4k₂³−6k₀k₁k₂`; nonzero follows from irreducibility of X³−2. Its real adjugate has coefficients as displayed in the draft and absolute value at most `6 |k|₁²`. Thus `|β| ≥ 1/(6 |k|₁²)`; permutation and scaling by 1/2 give the advertised `(1/12,2)` bound for `(x/2,x²/2,1/2)`. This is a valid mathematical route, not a completed Lean proof. The toy Hamiltonian `I₂+(I₀²+I₁²)/2` has a nonzero bordered twist through its clock direction, and rational approximations with arbitrarily small positive error are available. Huge constants require larger precision; they do not restore the old algebraic obstruction. “Any rationally independent vector” still requires the stated Diophantine premise: rational independence alone is insufficient, for example for Liouville frequencies.

## New / remaining numbered findings

### F7 — HIGH: averaged-torsion acceptance is not attached to the matrix dimension

**Location:** draft 694–701 (`ModelMatrix.Encloses`), 774–785 (`torsionAvgCheck`, `torsionAvgCheck_sound`); design §1.9, §4, Appendix A §F.

`torsionAvgCheck T S σTμ` receives no n. Its intended inverse check operates on the matrix dimension inferred from T/S. But `T.Encloses n (torsionIdx n) ρ F` only requires entries at indices 0,…,n to be present; it does **not** require exactly n+1 rows/columns. Therefore a successful inverse check on a larger matrix does not certify the leading block denoted by the theorem's independently quantified n. Static checks in the top-level certificate do not repair this standalone theorem, which has no static premise.

For a finite concrete illustration, the constant matrix

```
A = [1 0 0; 0 0 1; 0 1 0]
```

is its own inverse, with row norm 1 and zero inverse defect. Its leading 2×2 block `diag(1,0)` is singular. Both determinant facts were checked by a scratch Lean proof (`norm_num [Matrix.det_fin_three, Matrix.det_fin_two]`). These are also compatible with the frozen matrix forms: for n=2, K(θ)=(θ,0), H=I₁+I₀²/2, ω=(0,1), the extended torsion is A; for n=1, H=I²/2, K(θ)=(θ,0), ω=0, the extended torsion is its leading block. The current entry-presence relation can describe both with the same list T. There is no Diophantine or dimension-lower-bound premise in the averaging theorem. This illustrates the missing attachment; no checker body or passing test for A currently exists.

**Required change:** pass n to `torsionAvgCheck` and check exact `(n+1)×(n+1)` shapes of T and S, with a soundness statement for that n; or strengthen the enclosure relation with exact shape evidence tying its index set to the checked list dimension. Propagate this through the producer, `checkTorsion_sound`, and negative tests. Rejecting every larger matrix having a singular principal block would be an unjustified restriction of the intended general inverse test. Adding only `2 ≤ n` does not fix the missing dimension equality.

### F8 — MEDIUM: two public norm bounds are false on their stated whole carrier

**Location:** draft 672–684, `norm_fderiv_hamiltonianVectorFieldℂ_le` and `norm_iteratedFDeriv_two_hamiltonianVectorFieldℂ_le`; Appendix A §E.

Take n=0, H=0, z=(0,0), B=−1. Local C³ (hence C²) holds. Every row-sum premise is vacuous because `Fin 0 ⊕ Fin 0` is empty. Each conclusion nevertheless asserts a nonnegative norm is ≤−1. A scratch theorem proved both complete hypotheses and both negated conclusions, without using either draft theorem or any `sorry`; its axioms are only `[propext, Classical.choice, Quot.sound]`.

**Required change:** add `0 ≤ B` or `1 ≤ n` to each standalone theorem (and derive that premise in the checker), or give a distinct positive-dimension wrapper. Top-level `hn : 2 ≤ n` makes this easy for the intended consumer, but does not make the existing public signatures true. This defect was not caught in audit 1 and remains after Revision 2's local-regularity adjustment.

### F9 — MEDIUM: the new lunar J-residual formula drops the original residual

**Location:** design §6, lines 281–284 (four-component candidate and budgets); compare pilot §1 and proposal §5.2.

The design says “the J row of the invariance error is `−D_{sω*}ΔJ`.” For the pilot's exact energy lift J₀, that row was **p r**, not zero. The exact generally valid formula is

```
E(K̃)_J = E(K₀)_J − D_{sω*}ΔJ,
```

and under the scalar pilot identities this becomes `p r − D_{sω*}ΔJ`. Independent Fourier p data may also lose the scalar identities; then use the general difference formula and the actual full residual.

**Required change:** correct the displayed identity and budget the sum of the original full residual and the ΔJ derivative contribution, plus any other candidate replacement errors. Keep the mandatory recomputation of the actual full residual. The energy identity `H(K̃)−E₀=ΔJ` remains correct. Since no soundness contract substitutes the incorrect formula for its full-vector residual, this is a design/feasibility defect, not an established logical inconsistency in the black-box theorem.

## Soundness and semantics

A fresh `engine_bridge` proof, appended to a scratch copy of Revision 2, applied `(g1_explicit …).2.2.2` to every field in order. It contained no new placeholder and elaborated. Its axiom output is only `[propext, Classical.choice, Quot.sound]` (the required denotations here are concrete). This checks the bridge from `G1Hyps`; it does not prove that finite checks construct those hypotheses.

| Engine obligation | Revision 2 producer / field | Assessment |
|---|---|---|
| n≥2, τ≥n−1; 0<ρinf<ρ; all positive constants, σω>1, ν>0 | StaticFacts and `checkStatic_sound` | Exact shape |
| nonzero exact ωstar and both ray margins | `checkStatic_freq`, hω | Correct reference vector; no assumption on all vectors in the box being Diophantine |
| open, integer-translation-invariant D | `certDomain`, `ham_structural` | Exact open-strip/polydisc domain |
| H holomorphic, periodic and real on real points in D | `checkHamBounds_sound` → NonvanishingOn → `ham_structural` | Division guards apply on the whole D |
| five bounds, in order: DH, XH, DXH, D²XH, D²H | `checkHamBounds_sound`, hbd | Exact shape; fix F8 in norm helper API |
| K holomorphic, primary, real | `emb_structural` | Direct law-free denotation is sound |
| μ-ball containment; DK≤σK−μ | `checkEmbedding_sound` | Exact norms and domain |
| bilinear Gram determinant unit; inverse row sums | `checkGram_sound` | Correct bilinear object, no Hermitian replacement |
| average extended torsion determinant unit; inverse row sums | `torsionModels_sound` → `checkTorsion_sound` | Producer now literal frozen formula, including DN[sω] and DH(K)N; fix F7 in averaging consumer |
| 1<s<σω; ν endpoint margins; 0<γ≤γbar | StaticFacts and `checkStatic_freq` | Correct nuRay/ray-scalar distinction |
| IsDiophantine γ τ ωstar | external hdio | On ωstar, not on its box centre or initial sωstar |
| e≥0, full invariance residual, averaged energy error | StaticFacts, `checkInvariance_sound`, `checkEnergy_sound` | Actual four-component K; F9 must not replace these |
| isoC1 smallness and isoC2 displacement | `checkSmallness_sound` | Exact parameter order μ,ν,γbar in isoC1 |
| all output clauses, half margins, pointwise energy and both displacements | CertifiedTorus and fresh bridge | Preserved; both bounds use hdisp since C₂=C₃ |

`TorusCertificate` has numerical data and witnesses, no assumed torus/invertibility/residual proof. `G1Hyps` is a derived Prop, never an input to the public checker-soundness theorem. The general theorem now takes both hω (exact input enclosure) and hdio (Diophantine membership), in addition to a proved backend-law instance. This is an honest revision of “only external mathematical input”: enclosure proofs must also be supplied, but do not assume the difficult analytic conclusion.

Division is mathematically sound as designed: Lean's total `/` gives the stated denotation everywhere; recursive `NonvanishingOn` makes it analytic on open D, and derivative jets are conditional on that premise. Periodicity and reality hold even at zero denominators. A ball with radius smaller than `max(|re c|,|im c|)` excludes zero. Reciprocal witnesses with defect δ<1 prove nonvanishing and error `sup|Q| δ/(1−δ)`; the degree changes from d to −d. For actual implementation, preserve denominator-validation obligations when compiling/pruning jets: folding `0*(1/0)` to zero must not allow successful ball evaluation to assert the syntactic expression's `NonvanishingOn`. Likewise `.pow a 0` must not discard denominator obligations required by that recursive predicate. Keeping those validation slots is a sound implementation, and remains to be implemented.

There is no open/closed-strip mismatch: frozen `complexStrip` is open, exactly as in `CertModel.Encloses`. Positive widths are now checked. The exp-witness radius is a conservative valid path bound on a periodic fundamental representative and straight segment in the convex strip, applied to the polynomial part; no derivative is inferred from an arbitrary sup-radius tail. The tail is paid by `exp(B)(exp η−1)`. Degree conversion uses validated π intervals; negative-degree upper bounds correctly use a positive lower π bound. PiHigh's coarse/Machin bounds, `PiHighCert`, and e interfaces agree with the current landed module; `(50,15)` has its landed kernel-checked 10⁻¹⁴⁰ width theorem. The draft's PiHigh proofs remain stand-ins and must be replaced by imports.

Neumann matrix bounds and the derivative-of-inverse formula are mathematically valid. Average bounds require continuity and positive strip width, now supplied by the contracts; F7 concerns shape, not the averaging inequality itself. SOS residual slack `m≤m₀−r` is paid. `CertPoly.eval_add` has a uniform bound for **all complex θ**, without a strip weight: implement it by exact list concatenation/zero error, or move any rounded coefficient-merging estimate into the weighted model API. Nonzero-mode rounding errors cannot have that global constant bound. This is an implementation restriction of its current signature, not a counterexample to a yet-unspecified addition body.

The lunar continuous graphs and momentum-window region match O1/O4 and D30's 33/1000 band. `mono > disp/rhoInf` leaves the Cauchy-transferred derivative positive; the clock gives an exact second angle, enabling inversion and a graph. `so_confinement` states global existence and uniqueness among global solutions; its proof route uses the globally Lipschitz physical field. The graph/barrier/window claims still need actual passing data, literal rational endpoints, and all range/monotonicity checks. The pilot does not certify Fourier J feasibility: G-J's B₀/B₁/B₂ targets and fresh Gram/torsion/etc. margins are unpaid. Thus deviation (b) is sound conditionally, but is not proved to fit the pilot's margins in this revision.

## Validation receipts

All commands below were run by this auditor. The signature gate runs `LEAN_NUM_THREADS=1 nice -n 5 timeout 1800 lake env lean <absolute-file>` against the shared `/root/code/KAM-inp` build. This is the prescribed design workflow; it is not a production build of the draft.

1. Signature command:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-so .drafts/design/SOSignatures.lean
   ```

   Exit **0**; **156** warnings, each `declaration uses 'sorry'`; **0** errors. This is elaboration only. No production module may import this file.

2. Targeted engine build:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-design-so KAM.Iso.Apost.G1
   ```

   Output: `[inp-gate] slot 1 acquired 11:39:05 for KAM.Iso.Apost.G1`; `Build completed successfully (3224 jobs).` Exit **0**. No clean or library-from-scratch build.

3. Scratch probe (same gate, `.lake/abi-scratch/SOAudit2Probe.lean`): exit **0**, zero errors. It includes the complete draft, a fresh no-placeholder engine bridge, the no-placeholder zero-dimension counterexample, the two determinant checks for F7, and `#print axioms` for **all 107 public draft theorems**. All probe runs exited 0, including a final rerun of the matrix illustration with the frozen bordered corner equal to zero.

   Exact main axiom output:

   ```text
   'SOAudit2.engine_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
   'SOAudit2.zero_dim_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Iso.Apost.g1_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Certificate.checkTorusCertificate_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
   'KAM.Certificate.torsionModels_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
   ```

   All 107 draft public theorems contain `sorryAx` in their dependency output; no axiom outside `sorryAx`, `propext`, `Classical.choice`, `Quot.sound` appeared. This is expected for transient design signatures, and categorically **not** proof hygiene acceptance. The row table below records the exact axiom class for each theorem.

4. Kernel replay:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Iso.Apost.G1 KAM.Iso.Charts.Inputs
   ```

   Final output `replaying KAM.Iso.Charts.Inputs`, `replaying KAM.Iso.Apost.G1`; exit **0**. This replays the existing engine, not the unproved proposed checker. There are no new provider/lemma modules to replay or seal.

5. Hygiene:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **0**, exact output:

   ```text
   check_lean_modules: PASS (1281 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No generated-root exception was needed. Draft code-mask scan: 156 `sorry` tokens, no `axiom`, `admit`, `unsafe`, `opaque`, `native_decide`, `EuclideanSpace`, heartbeat or recursion-depth override. The 1337-line draft has the copyright header, `module`, public imports, module docstring and public section, below the 1500-line cap. Production lint excludes `.drafts`; its success must not be described as proving the draft has no placeholders. The known intentional duplicate names are the PiHigh and PhaseBasis/Clock stand-ins; new central SO-checker names do not clash in current inp. Replace stand-ins by imports when implementing.

6. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty. `git diff --check`: exit **0**, no output. Read-only diff inspection and no state-changing git. The engine imports no proposed checker or new provider. Provider/type/seal probes are inapplicable because SO-DESIGN introduces no provider or frozen SO declaration.

## Declaration review and definition classification

One row per all **222** proposed public declarations, in source order. Locators are line numbers in `.drafts/design/SOSignatures.lean` (also Appendix A, with its Markdown offset). Nodes A–J are the design's own sections, not newly invented blueprint nodes. `PWN` means PASS WITH NOTES **for a design statement/body only**, never proof closure. `S` means exactly `[propext, sorryAx, Classical.choice, Quot.sound]`; `s` means `[sorryAx]`; `T` means `[propext, sorryAx, Quot.sound]`. A dash means not a theorem axiom check. Concrete definitions were reviewed on their whole carrier; placeholders are explicitly not accepted implementations. Data-class laws are backend obligations, and `G1Hyps`/StaticFacts are derived propositions. SoBarrier is a conditional semantic structure used as a helper, not an assumed premise of the lunar headline.

| Node | Declaration (line) | Verdict | Classification / reason; axioms |
|---|---|---|---|
| A | `KAM.Certificate.CertArith` (67) | PWN | Backend data interface; — |
| A | `KAM.Certificate.LawfulCertArith` (86) | PWN | Backend correctness laws (Prop); — |
| A | `KAM.Certificate.CC` (106) | PWN | Data / syntax carrier; — |
| A | `KAM.Certificate.CC.toC` (111) | PWN | Concrete denotation / semantic predicate; — |
| A | `KAM.Certificate.CC.conj` (114) | PWN | Concrete denotation / semantic predicate; — |
| A | `KAM.Certificate.CC.toC_conj` (116) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.CC.toC_zero` (120) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.instCertArithRat` (126) | PWN | Algorithm / instance / data placeholder; — |
| A | `KAM.Certificate.instLawfulCertArithRat` (128) | PWN | Algorithm / instance / data placeholder; — |
| A | `KAM.Certificate.CertFixed` (131) | PWN | Data / syntax carrier; — |
| A | `KAM.Certificate.instCertArithFixed` (134) | PWN | Algorithm / instance / data placeholder; — |
| A | `KAM.Certificate.instLawfulCertArithFixed` (136) | PWN | Algorithm / instance / data placeholder; — |
| A | `KAM.Certificate.ratExpUp` (142) | PWN | Algorithm / instance / data placeholder; — |
| A | `KAM.Certificate.exp_le_ratExpUp` (144) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.piLoQ` (152) | PWN | Concrete denotation / semantic predicate; — |
| A | `KAM.Certificate.piUpQ` (154) | PWN | Concrete denotation / semantic predicate; — |
| A | `KAM.Certificate.piLoQ_lt_pi` (156) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.pi_lt_piUpQ` (158) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.atanS` (161) | PWN | Concrete denotation / semantic predicate; — |
| A | `KAM.Certificate.piLowRat` (164) | PWN | Concrete denotation / semantic predicate; — |
| A | `KAM.Certificate.piUpRat` (166) | PWN | Concrete denotation / semantic predicate; — |
| A | `KAM.Certificate.piLowRat_lt_pi` (168) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.pi_lt_piUpRat` (170) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.PiHighCert` (173) | PWN | External proved π-enclosure bundle; not certificate payload; — |
| A | `KAM.Certificate.eSum` (179) | PWN | Concrete denotation / semantic predicate; — |
| A | `KAM.Certificate.eRem` (181) | PWN | Concrete denotation / semantic predicate; — |
| A | `KAM.Certificate.eLowRat` (183) | PWN | Concrete denotation / semantic predicate; — |
| A | `KAM.Certificate.eUpRat` (185) | PWN | Concrete denotation / semantic predicate; — |
| A | `KAM.Certificate.eLowRat_lt_exp_one` (187) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.exp_one_lt_eUpRat` (189) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.PiEnclosure` (196) | PWN | Data / syntax carrier; — |
| A | `KAM.Certificate.checkPiEnclosure` (204) | PWN | Algorithm / instance / data placeholder; — |
| A | `KAM.Certificate.checkPiEnclosure_sound` (206) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.checkRootEnclosure` (212) | PWN | Concrete denotation / semantic predicate; — |
| A | `KAM.Certificate.rpow_mem_of_checkRootEnclosure` (215) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.sqrt_mem_of_checkRootEnclosure` (219) | PWN | Reviewed statement; proof placeholder; S |
| A | `KAM.Certificate.certCExp` (225) | PWN | Algorithm / instance / data placeholder; — |
| A | `KAM.Certificate.certCExp_sound` (227) | PWN | Reviewed statement; proof placeholder; S |
| B | `KAM.Certificate.CertKey` (234) | PWN | Representation alias; — |
| B | `KAM.Certificate.certKeyFun` (237) | PWN | Concrete denotation / semantic predicate; — |
| B | `KAM.Certificate.CertPoly` (241) | PWN | Data / syntax carrier; — |
| B | `KAM.Certificate.CertPoly.eval` (245) | PWN | Concrete denotation / semantic predicate; — |
| B | `KAM.Certificate.CertPoly.coeff` (249) | PWN | Concrete denotation / semantic predicate; — |
| B | `KAM.Certificate.CertPoly.eval_eq_fourierSum` (253) | PWN | Reviewed statement; proof placeholder; S |
| B | `KAM.Certificate.CertPoly.differentiable_eval` (256) | PWN | Reviewed statement; proof placeholder; S |
| B | `KAM.Certificate.CertPoly.eval_add_int` (259) | PWN | Reviewed statement; proof placeholder; S |
| B | `KAM.Certificate.CertRealPoly` (263) | PWN | Data / syntax carrier; — |
| B | `KAM.Certificate.CertRealPoly.eval` (268) | PWN | Concrete denotation / semantic predicate; — |
| B | `KAM.Certificate.CertRealPoly.eval_real` (274) | PWN | Reviewed statement; proof placeholder; S |
| B | `KAM.Certificate.CertRealPoly.differentiable_eval` (277) | PWN | Reviewed statement; proof placeholder; S |
| B | `KAM.Certificate.CertRealPoly.eval_add_int` (280) | PWN | Reviewed statement; proof placeholder; S |
| B | `KAM.Certificate.CertRealPoly.toPoly` (285) | PWN | Algorithm / instance / data placeholder; — |
| B | `KAM.Certificate.CertRealPoly.eval_toPoly` (288) | PWN | Reviewed statement; proof placeholder; S |
| B | `KAM.Certificate.CertRealPoly.conjugateSymmetric` (291) | PWN | Reviewed statement; proof placeholder; S |
| B | `KAM.Certificate.CertPoly.add` (295) | PWN | Algorithm / instance / data placeholder; — |
| B | `KAM.Certificate.CertPoly.eval_add` (297) | PWN | Reviewed statement; proof placeholder; S; exact concatenation or weighted API required |
| B | `KAM.Certificate.CertPoly.shift` (303) | PWN | Algorithm / instance / data placeholder; — |
| B | `KAM.Certificate.CertPoly.eval_shift` (305) | PWN | Reviewed statement; proof placeholder; S |
| B | `KAM.Certificate.CertPoly.conjReflect` (310) | PWN | Algorithm / instance / data placeholder; — |
| B | `KAM.Certificate.CertPoly.eval_conjReflect` (312) | PWN | Reviewed statement; proof placeholder; S |
| C | `KAM.Certificate.CertWeight` (319) | PWN | Data / syntax carrier; — |
| C | `KAM.Certificate.checkWeight` (325) | PWN | Concrete denotation / semantic predicate; — |
| C | `KAM.Certificate.norm_character_le_weight` (328) | PWN | Reviewed statement; proof placeholder; S |
| C | `KAM.Certificate.CertModel` (334) | PWN | Data / syntax carrier; — |
| C | `KAM.Certificate.CertModel.Encloses` (340) | PWN | Concrete denotation / semantic predicate; — |
| C | `KAM.Certificate.CertModel.supBound` (347) | PWN | Algorithm / instance / data placeholder; — |
| C | `KAM.Certificate.CertModel.norm_le_supBound` (349) | PWN | Reviewed statement; proof placeholder; S |
| C | `KAM.Certificate.ModelConfig` (355) | PWN | Data / syntax carrier; — |
| C | `KAM.Certificate.CertModel.add` (362) | PWN | Algorithm / instance / data placeholder; — |
| C | `KAM.Certificate.CertModel.mul` (365) | PWN | Algorithm / instance / data placeholder; — |
| C | `KAM.Certificate.CertModel.trim` (369) | PWN | Algorithm / instance / data placeholder; — |
| C | `KAM.Certificate.CertModel.toDeg` (373) | PWN | Algorithm / instance / data placeholder; — |
| C | `KAM.Certificate.CertModel.ofDeriv` (378) | PWN | Algorithm / instance / data placeholder; — |
| C | `KAM.Certificate.CertModel.Encloses.ofDeriv` (381) | PWN | Reviewed statement; proof placeholder; S |
| C | `KAM.Certificate.CertModel.Encloses.add` (386) | PWN | Reviewed statement; proof placeholder; S |
| C | `KAM.Certificate.CertModel.Encloses.mul` (391) | PWN | Reviewed statement; proof placeholder; S |
| C | `KAM.Certificate.CertModel.Encloses.trim` (396) | PWN | Reviewed statement; proof placeholder; S |
| C | `KAM.Certificate.CertModel.Encloses.toDeg` (401) | PWN | Reviewed statement; proof placeholder; S |
| C | `KAM.Certificate.CertModel.Encloses.average` (407) | PWN | Reviewed statement; proof placeholder; S |
| C | `KAM.Certificate.expWitnessRadius` (425) | PWN | Algorithm / instance / data placeholder; — |
| C | `KAM.Certificate.expWitness_sound` (428) | PWN | Reviewed statement; proof placeholder; S |
| C | `KAM.Certificate.invWitnessRadius` (436) | PWN | Algorithm / instance / data placeholder; — |
| C | `KAM.Certificate.invWitness_sound` (439) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.phaseBasis` (451) | PWN | Concrete denotation / semantic predicate; — |
| D | `KAM.Certificate.HamExpr` (459) | PWN | Syntax carrier; — |
| D | `KAM.Certificate.modePhase` (474) | PWN | Concrete denotation / semantic predicate; — |
| D | `KAM.Certificate.HamExpr.eval` (479) | PWN | Concrete denotation / semantic predicate; — |
| D | `KAM.Certificate.HamExpr.NonvanishingOn` (494) | PWN | Concrete denotation / semantic predicate; — |
| D | `KAM.Certificate.HamExpr.contDiffOn_eval` (504) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.HamExpr.eval_add_int` (507) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.HamExpr.eval_real` (510) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.SlpOp` (515) | PWN | Syntax carrier; — |
| D | `KAM.Certificate.Slp` (524) | PWN | Data / syntax carrier; — |
| D | `KAM.Certificate.Slp.val` (528) | PWN | Algorithm / instance / data placeholder; — |
| D | `KAM.Certificate.HamJet` (534) | PWN | Data / syntax carrier; — |
| D | `KAM.Certificate.phaseNat` (542) | PWN | Concrete denotation / semantic predicate; — |
| D | `KAM.Certificate.HamExpr.jet` (546) | PWN | Algorithm / instance / data placeholder; — |
| D | `KAM.Certificate.HamExpr.jet_v0` (548) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.HamExpr.jet_d1` (551) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.HamExpr.jet_d2` (557) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.HamExpr.jet_d3` (563) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.certDomain` (571) | PWN | Concrete denotation / semantic predicate; — |
| D | `KAM.Certificate.isOpen_certDomain` (576) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.certDomain_add_int` (579) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.Slp.balls` (588) | PWN | Algorithm / instance / data placeholder; — |
| D | `KAM.Certificate.Slp.val_mem_ball` (591) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.HamExpr.nonvanishingOn_of_balls` (599) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.CertEmbedding` (606) | PWN | Data / syntax carrier; — |
| D | `KAM.Certificate.CertEmbedding.eval` (612) | PWN | Concrete denotation / semantic predicate; — |
| D | `KAM.Certificate.CertEmbedding.differentiable_eval` (619) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.CertEmbedding.isPrimaryOnStrip` (622) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.CertEmbedding.isRealOnReals` (626) | PWN | Reviewed statement; proof placeholder; S |
| D | `KAM.Certificate.Witnesses` (632) | PWN | Data / syntax carrier; — |
| D | `KAM.Certificate.Slp.compose` (639) | PWN | Algorithm / instance / data placeholder; — |
| D | `KAM.Certificate.Slp.compose_sound` (644) | PWN | Reviewed statement; proof placeholder; S |
| E | `KAM.Certificate.norm_fderiv_le_sum_partials` (654) | PWN | Reviewed statement; proof placeholder; S |
| E | `KAM.Certificate.norm_iteratedFDeriv_two_le_sum_partials` (658) | PWN | Reviewed statement; proof placeholder; S |
| E | `KAM.Certificate.hamiltonianVectorFieldℂ_sumVec` (665) | PWN | Reviewed statement; proof placeholder; S |
| E | `KAM.Certificate.norm_fderiv_hamiltonianVectorFieldℂ_le` (672) | FAIL | Reviewed statement; proof placeholder; S; F8 |
| E | `KAM.Certificate.norm_iteratedFDeriv_two_hamiltonianVectorFieldℂ_le` (679) | FAIL | Reviewed statement; proof placeholder; S; F8 |
| F | `KAM.Certificate.matrix_inv_of_approx_inverse` (689) | PWN | Reviewed statement; proof placeholder; S |
| F | `KAM.Certificate.ModelMatrix` (694) | PWN | Representation alias; — |
| F | `KAM.Certificate.ModelMatrix.Encloses` (698) | PWN | Concrete denotation / semantic predicate; —; F7: exact shape absent |
| F | `KAM.Certificate.polyMatrix` (704) | PWN | Concrete denotation / semantic predicate; — |
| F | `KAM.Certificate.gramModels` (709) | PWN | Algorithm / instance / data placeholder; — |
| F | `KAM.Certificate.gramModels_sound` (712) | PWN | Reviewed statement; proof placeholder; S |
| F | `KAM.Certificate.gramCheck` (720) | PWN | Algorithm / instance / data placeholder; — |
| F | `KAM.Certificate.gramCheck_sound` (724) | PWN | Reviewed statement; proof placeholder; S |
| F | `KAM.Certificate.torsionIdx` (735) | PWN | Concrete denotation / semantic predicate; — |
| F | `KAM.Certificate.FreqBox` (739) | PWN | Representation alias; — |
| F | `KAM.Certificate.FreqEncloses` (741) | PWN | Concrete denotation / semantic predicate; — |
| F | `KAM.Certificate.torsionModels` (749) | PWN | Algorithm / instance / data placeholder; — |
| F | `KAM.Certificate.torsionModels_sound` (758) | PWN | Reviewed statement; proof placeholder; S; F3 producer repaired; averaging F7 |
| F | `KAM.Certificate.torsionAvgCheck` (774) | FAIL | Algorithm / instance / data placeholder; —; F7 |
| F | `KAM.Certificate.torsionAvgCheck_sound` (777) | FAIL | Reviewed statement; proof placeholder; S; F7 |
| F | `KAM.Certificate.cRUpQ` (788) | PWN | Algorithm / instance / data placeholder; — |
| F | `KAM.Certificate.cR_le_cRUpQ` (790) | PWN | Reviewed statement; proof placeholder; S |
| F | `KAM.Certificate.isoC1Q` (794) | PWN | Algorithm / instance / data placeholder; — |
| F | `KAM.Certificate.isoC2Q` (796) | PWN | Algorithm / instance / data placeholder; — |
| F | `KAM.Certificate.isoC1_le_isoC1Q` (798) | PWN | Reviewed statement; proof placeholder; S |
| F | `KAM.Certificate.isoC2_le_isoC2Q` (804) | PWN | Reviewed statement; proof placeholder; S |
| F | `KAM.Certificate.checkRealLowerBound` (812) | PWN | Algorithm / instance / data placeholder; — |
| F | `KAM.Certificate.checkRealLowerBound_sound` (815) | PWN | Reviewed statement; proof placeholder; S |
| G | `KAM.Certificate.algFreq` (832) | PWN | Concrete denotation / semantic predicate; — |
| G | `KAM.Certificate.checkAlgBox` (838) | PWN | Algorithm / instance / data placeholder; — |
| G | `KAM.Certificate.algFreq_encloses` (840) | PWN | Reviewed statement; proof placeholder; S |
| G | `KAM.Certificate.CertParams` (847) | PWN | Data / syntax carrier; — |
| G | `KAM.Certificate.TorusCertificate` (868) | PWN | Data / syntax carrier; — |
| G | `KAM.Certificate.TorusCertificate.D` (893) | PWN | Concrete denotation / semantic predicate; — |
| G | `KAM.Certificate.TorusCertificate.H` (896) | PWN | Concrete denotation / semantic predicate; — |
| G | `KAM.Certificate.TorusCertificate.K` (898) | PWN | Concrete denotation / semantic predicate; — |
| G | `KAM.Certificate.checkStatic` (908) | PWN | Algorithm / instance / data placeholder; — |
| G | `KAM.Certificate.checkHamBounds` (912) | PWN | Algorithm / instance / data placeholder; — |
| G | `KAM.Certificate.checkEmbedding` (915) | PWN | Algorithm / instance / data placeholder; — |
| G | `KAM.Certificate.checkInvariance` (918) | PWN | Algorithm / instance / data placeholder; — |
| G | `KAM.Certificate.checkEnergy` (921) | PWN | Algorithm / instance / data placeholder; — |
| G | `KAM.Certificate.checkGram` (924) | PWN | Algorithm / instance / data placeholder; — |
| G | `KAM.Certificate.checkTorsion` (927) | PWN | Algorithm / instance / data placeholder; — |
| G | `KAM.Certificate.checkSmallness` (930) | PWN | Algorithm / instance / data placeholder; — |
| G | `KAM.Certificate.checkTorusCertificate` (934) | PWN | Concrete denotation / semantic predicate; — |
| G | `KAM.Certificate.G1Hyps` (944) | PWN | Derived engine facts (Prop); — |
| G | `KAM.Certificate.CertifiedTorus` (997) | PWN | Concrete denotation / semantic predicate; — |
| G | `KAM.Certificate.StaticFacts` (1016) | PWN | Derived engine facts (Prop); — |
| G | `KAM.Certificate.checkStatic_sound` (1041) | PWN | Reviewed statement; proof placeholder; S |
| G | `KAM.Certificate.checkStatic_freq` (1045) | PWN | Reviewed statement; proof placeholder; S |
| G | `KAM.Certificate.TorusCertificate.emb_structural` (1051) | PWN | Reviewed statement; proof placeholder; S |
| G | `KAM.Certificate.checkHamBounds_sound` (1055) | PWN | Reviewed statement; proof placeholder; S |
| G | `KAM.Certificate.TorusCertificate.ham_structural` (1064) | PWN | Reviewed statement; proof placeholder; S |
| G | `KAM.Certificate.checkEmbedding_sound` (1072) | PWN | Reviewed statement; proof placeholder; S |
| G | `KAM.Certificate.checkGram_sound` (1078) | PWN | Reviewed statement; proof placeholder; S |
| G | `KAM.Certificate.checkInvariance_sound` (1083) | PWN | Reviewed statement; proof placeholder; S |
| G | `KAM.Certificate.checkEnergy_sound` (1089) | PWN | Reviewed statement; proof placeholder; S |
| G | `KAM.Certificate.checkTorsion_sound` (1095) | PWN | Reviewed statement; proof placeholder; S; engine shape valid; upstream F7/F8 |
| G | `KAM.Certificate.checkSmallness_sound` (1102) | PWN | Reviewed statement; proof placeholder; S |
| G | `KAM.Certificate.checkTorusCertificate_hyps` (1113) | PWN | Reviewed statement; proof placeholder; S; engine shape valid; upstream F7/F8 |
| G | `KAM.Certificate.checkTorusCertificate_sound` (1123) | PWN | Reviewed statement; proof placeholder; S; engine shape valid; upstream F7/F8 |
| H | `KAM.Certificate.clock_frequency` (1136) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.cbrtTwo` (1152) | PWN | Concrete denotation / semantic predicate; — |
| J | `KAM.Certificate.cubicFreq` (1155) | PWN | Concrete denotation / semantic predicate; — |
| J | `KAM.Certificate.cubicFreq_eq_algFreq` (1157) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.cubicFreq_isDiophantine` (1163) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.toyHam3` (1166) | PWN | Concrete denotation / semantic predicate; — |
| J | `KAM.Certificate.toyCert3` (1173) | PWN | Algorithm / instance / data placeholder; — |
| J | `KAM.Certificate.toyCert3_ham` (1175) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.toyCert3_err_pos` (1177) | PWN | Reviewed statement; proof placeholder; T |
| J | `KAM.Certificate.toyCert3_passes` (1179) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.toyCert3_freq` (1181) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.toyCert3_torus` (1184) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.toyCert2` (1189) | PWN | Algorithm / instance / data placeholder; — |
| J | `KAM.Certificate.toyCert2d` (1191) | PWN | Algorithm / instance / data placeholder; — |
| J | `KAM.Certificate.toyCert2_passes` (1193) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.toyCert2d_passes` (1195) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.toyCert2_torus` (1197) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.toyCert2d_torus` (1199) | PWN | Reviewed statement; proof placeholder; S |
| J | `KAM.Certificate.toyRatCert` (1203) | PWN | Algorithm / instance / data placeholder; — |
| J | `KAM.Certificate.toyRatCert_passes` (1205) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.soHamExpr` (1218) | PWN | Concrete denotation / semantic predicate; — |
| I | `KAM.SpinOrbit.soHamExpr_eval` (1224) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.soHamExpr_clock` (1226) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunarFreqMinus_eq` (1231) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunarFreqPlus_eq` (1235) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.SoBarrier` (1242) | PWN | Conditional invariant-graph semantics; — |
| I | `KAM.SpinOrbit.SoGraphCert` (1254) | PWN | Data / syntax carrier; — |
| I | `KAM.SpinOrbit.checkSoGraph` (1266) | PWN | Algorithm / instance / data placeholder; — |
| I | `KAM.SpinOrbit.soBarrier_of_cert` (1269) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.so_confinement` (1279) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.SoBackend` (1288) | PWN | Replay-dependent placeholder backend choice; — |
| I | `KAM.SpinOrbit.lunarLowerCert` (1291) | PWN | Algorithm / instance / data placeholder; — |
| I | `KAM.SpinOrbit.lunarUpperCert` (1293) | PWN | Algorithm / instance / data placeholder; — |
| I | `KAM.SpinOrbit.lunarLowerCert_ham` (1295) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunarUpperCert_ham` (1297) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunarLowerCert_passes` (1299) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunarUpperCert_passes` (1301) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunarLowerGraph_passes` (1303) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunarUpperGraph_passes` (1305) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunarLowerCert_freq` (1308) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunarUpperCert_freq` (1311) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunarPLo` (1315) | PWN | Algorithm / instance / data placeholder; — |
| I | `KAM.SpinOrbit.lunarPHi` (1317) | PWN | Algorithm / instance / data placeholder; — |
| I | `KAM.SpinOrbit.lunarPLo_lt_lunarPHi` (1319) | PWN | Reviewed statement; proof placeholder; s |
| I | `KAM.SpinOrbit.lunar_barriers` (1322) | PWN | Reviewed statement; proof placeholder; S |
| I | `KAM.SpinOrbit.lunar_spin_confinement` (1329) | PWN | Reviewed statement; proof placeholder; S |

## Feasibility, uncertainties, errata and handoff

The pre/post-gate table sums correctly to 7550 + 8700 = 16250 unwritten lines; adding 400 landed clock lines and approximately 1500 other wave-0 lines gives 18150. A 30–40% overrun of the unwritten part gives 21125–22750 new lines. These are plausible planning ranges, not validated estimates. Third-order shared jets, complex exp witnesses, rational/fixed-point replay, matrix derivatives and graph inversion remain the large risks. Individual modules must split before 1500 lines, independently of a multi-module package's total.

SO-PI, constants, backend-neutral interfaces, direct Fourier semantics, expression semantics, norm/matrix mathematics and barrier/graph mathematics can proceed before SO-REPLAY. Preserve the dependency note for pre-gate rational balls. Concrete backend choices, convolution/model algorithms, witness checks, finite-check soundness and data wait for measured replay results; SO-DATA additionally waits for G-J. Signature success provides no timing, recursion-depth, ulp, or lunar slack evidence. The new division witness/product and high-precision π wrapper should be measured at the planned precision, not inferred from the existing PiHigh kernel proof alone.

No new suspected defect in the pinned mathematical sources or frozen declarations was established. F7/F8 are proposed Lean-interface defects, and F9 is an incorrect design identity; report them as design corrections rather than source errata. The source discrepancy concerning the old 3% band remains the pilot's explicitly unresolved discrepancy, with D30's 3.3% ruling controlling this project. Deviations retained: approved constant-window initial region, independent Fourier J with unpaid G-J attachment, bounded J polydisc, exact frequency carried by a theorem binder plus rational enclosure proof, and deferred analytic graphs/conjugacy per O4. Division and high-precision π now follow O2/O3.

Files written: this exact audit report only. Approach: refute whole-carrier public contracts, compare every engine binder, inspect all proposed declarations, rerun signature/bridge/refutation probes, serialize targeted engine build and kernel replay, and run source/frozen/ABI lint. The concrete next repair is F7's dimension/shape link and F8's positivity/nonempty premise, together with F9's full residual formula. The general frequency and division routes need no reversal. The lunar theorem and all proposed checker proofs remain unproved; the two computational feasibility gates remain open.
