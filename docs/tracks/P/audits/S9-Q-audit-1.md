# S9-Q independent audit 1

Date: 2026-10-28. **Overall verdict: FAIL for the requested complete graph-cut slice; PASS for the exact signed `SecularSpectrum.diagonalize` theorem.** No mathematical or kernel defect was found in the signed theorem. The failure is the bounded statement-coverage discrepancy F1 below. Generated-root staleness is an allowed hygiene note.

## Scope and authority

Only `KAM/Planetary/SecularSpectrum/Diagonalize.lean` is audited as new proof code: 254 lines, eight public theorems, no definitions or instances. HEAD is `b88af5e462211297d84078202ebc493fdf20a75b`; observed `inp` is `c5776d12e9876873026dae249ec6f7e3e2dc1d22`; merge base is `cbc738ce2a4017c3c06bf565c99f028ec013fcd2`. The requested `git diff inp...HEAD` contains 15 new files / 2287 insertions: the fourteen inherited S8-Q modules plus this file. The inherited modules are inputs, not newly audited proof packages.

Audited source SHA-256: `f55d0f59cbfb5fed4f553aa8866fc2edff93b3afb4e415702bd9ec2434090727`.
Signed draft `/root/code/KAM-inp/.drafts/design/P810Signatures.lean` SHA-256: `492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d`.

Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, S9-Q handoff and AUDIT FOCUS, P810 design revision 2 (ownership table, graph-record mapping, proof plan, risks and Appendix A), both P810 design audits, relevant Track P statement conventions, Part 8/9 blueprint statements and published graph packets, and `inp-s8q:docs/tracks/P/audits/S8-Q-audit-1.md`. The cited S8-Q round-2 report path does not exist on that branch; this audit does not assume its repairs have landed here. Read the actual upstream average, lift, norm, definiteness, quadratic and model-transfer interfaces, and the relevant frozen average, oscillator and Birkhoff definitions. No frozen theorem anchor is implemented by S9-Q; provider/frozen seal equality is therefore inapplicable. The signed draft is checked instead, without importing its unproved bodies.

The user's exact absolute report destination overrides the brief's generic main-worktree destination. Only this report and temporary worktree `.lake/abi-scratch/` files were written. No production edits, git mutations or delegation.

## Findings and graph coverage

**F1 — Assigned `stepP:p9:d-c` is not fully exported/proved in this file.** Design `P810-LEAN-DESIGN.md:173` assigns this proof cut to `diagonalize`. Blueprint `p9-secular-spectrum.tex:142,151` explicitly states the domain implication under the oscillator-disc guard: “as soon as `sqrt n delta_0 <= rho_*`” and the action-distance guard. The graph packet `docs/graph/P/packets/P-p9.nodes.md:859–868` retains that quantitative conclusion. Design lines 53 and 479 also prescribe shrinking with `sqrt(n)`.

The delivered norm helper (`Diagonalize.lean:61–80`) proves only `‖R x‖∞ ≤ n ‖x‖∞`. The average proof chooses `r1/n` (163), and the uniform estimate chooses `min(r1,r2,ρ0)/n` and `C2*n^4` (180–193). These are entirely valid witnesses for the signed existential theorem. They do not establish the source's larger explicitly guarded oscillator domain: an input allowed by `sqrt(n)*delta_0 ≤ rho_*` need not satisfy the stronger `n*delta_0 ≤ rho_*`. None of the eight theorem statements mentions an oscillator-disc domain implication or a `sqrt(n)` bound.

Adversarial recheck: `SecularSpectrum.norm_compare` and the length-preservation results imported through `Lift` provide ingredients for the sharper calculation, but this module neither applies them to discharge this guard nor exports a matching adapter. The accepted signed signature itself omits the explicit guard; its byte identity does not certify every literal conclusion of the graph cut. Consequently the **signed S9-Q row is complete**, but the requested **whole graph cut `d-c` is not**. Add a distinct domain adapter using the Euclidean length comparison, or explicitly narrow the graph ownership/claim; this report makes neither change. This is a design-to-graph coverage discrepancy, not a refutation of `diagonalize`.

**N1 — S8-Q `qf-diag2` remains a separate upstream coverage issue.** The prior S8-Q audit F1 identifies the missing SO symplecticity, sum-of-squares preservation and `2*sigma*Gamma` export. Design line 432 assigns that cut to S8-Q; its graph packet is `P-p8.nodes.md:1262–1283`. `Quadratic.lean:28–31` says the cut is “consumed by S9-Q”. That statement is inaccurate as a dependency description of this implementation: S9-Q imports `quadratic_form`, but does not consume a `qf-diag2` export.

S9-Q proves exactly the algebraic portion it needs locally: `rotDiag_quad_conj`, `rotDiag_quad_rot` and the oscillator identities at 155–159 and 225–232. It also proves a coarse norm inequality. Those helpers **do not prove symplecticity or exact sum-of-squares preservation**. The latter facts are unnecessary for this signed average/remainder proof. Full action-dependent symplecticity is a separate `Lift.lift` result; S9-Q does not invoke it. Do not count the rotDiag helpers as closing all of `qf-diag2`, or silently reassign the S8-Q cut to S9-Q. That upstream coverage gap does not invalidate the signed theorem.

**N2 — Transport is intentionally split, not missing S9-Q proof work.** The design graph map at 174 mentions `d-d`, but package row 442 expressly assigns `diagonalize_transport` / `diagonalize_period_one`, polar composition and Q1/Q2 to S9-T. The design-audit-1 F3 discussion also assigns the full Hamiltonian split to `pc_share` and action preservation to `lift`. S9-Q's theorem establishes the secular/algebraic portion only. It does not close the entire `bpP:p9:diagonalize` source node, certify a symplectic chart, or prove a frozen `HasSecularBirkhoffForm` predicate. This split is explicit and was accepted in the design; unlike F1, it has a named separate owner.

## Declaration and node inventory

All names in the table are prefixed `KAM.Planetary.SecularSpectrum.`. Helpers are public, despite the handoff's informal word “local”.

| Node / role | Declaration / location in Diagonalize.lean | Verdict | Reason |
|---|---|---|---|
| d-a, quadratic conjugation | `rotDiag_quad_conj`, 41 | PASS | Arbitrary real matrix/vector identity; stronger than SO-only formulation. Literal transpose, diagonal and double sum. |
| d-a, rotated-variable identity | `rotDiag_quad_rot`, 56 | PASS | Only `RᵀR=1`; matrix associativity cancels the rotations. |
| d-b, local-radius control | `rotDiag_norm_le`, 61 | PASS | Row sum of squares is one from `RRᵀ=1`; each entry has absolute value at most one; triangle inequality gives `n‖x‖∞`. Valid for all dimensions, including empty vectors. |
| d-b, real-domain adapter | `rotDiag_mem_realDisc`, 83 | PASS | Literal real inclusion into complex polydisc, with correct `(xi,I,eta)` order. |
| d-b, inverse formula | `rotDiag_liftInv_assemble`, 99 | PASS | Definitional equality, with fast shift independent of t and correct derivative/sign/order. No regularity premise needed. |
| d-b, angle translation | `rotDiag_avg_shift`, 107 | PASS | Exact frozen normalization times a translated 2π-periodic cell integral; whole slowDom statement is stronger than local analytic-disc version. |
| d-b, matched average | `rotDiag_avg_lift`, 116 | PASS | One Boolean selects the same model on both sides. Explicit rotated-point domain premise; no average identity assumed. |
| signed S9-Q row / p9 diagonalize(a–c) secular portion | `diagonalize`, 124–250 | PASS | Exact signed header, all four conjuncts proved, no extra premise or wider constant dependence. |
| stepP:p9:d-a | `diagonalize` first and third conjuncts | PASS | Quadratic identity and strict negative `2*sigma`. |
| stepP:p9:d-b, secular portion | `diagonalize` second and fourth conjuncts | PASS | Exact average and common local fourth-order bound. Full Hamiltonian composition uses separately owned `pc_share` / `lift`, not claimed here. |
| stepP:p9:d-c | `diagonalize` first/fourth conjuncts plus radius helpers | FAIL for full cut | Dictionary terms present; explicit sqrt(n) oscillator-domain implication absent (F1). |
| bpP:p9:dict, assigned oscillator identity | `diagonalize` first/third/fourth conjuncts | PASS | Frozen half retained, Omega=2*sigma, negative sign and constant plus matched modelDelta. The source remark's other cases/conventions are not new theorem exports here. |
| stepP:p9:d-d | no S9-Q export | Separate owner | S9-T owns the transport wrappers; do not mark whole graph node closed from this file. |
| stepP:p8:qf-diag2 | rotDiag algebra only | Partial, outside scope | Algebraic part re-proved; symplecticity/sum-of-squares export not supplied by these helpers (N1). |

## Proof and statement refutation checks

The complete `diagonalize` declaration header, from `theorem` to before `:= by`, is byte-identical to draft lines 364–386. In particular `hAn` is present in the signed draft. It is unused because a total `fderiv` value merely determines a constant fast-angle translation here; invertibility or symplecticity of the lift is not needed for that integral equality. There is no invented regularity premise or conclusion-shaped hypothesis. `hDiag` and `hR` are the source's given spectral data; upstream local-analytic construction remains separate. Omitting simple spectrum is the documented, accepted strengthening once a diagonalizer is given.

The conjugation calculation respects `quad Q x = xᵀQx`; rewriting with `RᵀR=1` is legitimate for the rotated coordinates. `oscillatorAction p q j=(p_j²+q_j²)/2` makes `2*sigma` exactly correct; no factor two is lost.

`hax` derives `axis D I ∈ axes n` and `action D (axis D I)=I` from the actual image-domain premise, rather than interpreting arbitrary negative actions as physical. With n≥2, division by n is strictly positive. The local r1/n bound puts both rotated slow coordinates strictly within r1, and the action coordinates are centered exactly at I. `realDisc_subset_slowDom` supplies the periodicity guard. Translation invariance is the actual 2π-cell result; no period-one conversion is used here. `cell_integral_add` supports even total nonintegrable Bochner integrals; the local expansion separately uses the real analytic-disc integrability output, so it does not obtain the physical model correction from a zero integral fallback.

Negativity comes from `definite D hn hIa`: positive coercivity and `sigma_j ≤ -coercivity` imply `2*sigma_j<0`. No spectral sign is assumed.

For the uniform remainder, `quadratic_form D ha0` is centered at `axis D I0` and already evaluates `constantTerm` and `coeffs` at the varying `axis D I`; it is not a fixed-coefficient Taylor polynomial at I0. The minimum radius keeps actions inside W and both needed polydiscs; the proof checks all three coordinates. `identification`'s implication is applied with the fixed-model integrability supplied by `perturbation_analytic` at the rotated point. Thus moving=fixed+modelDelta is justified before cancellation. The same r and C are selected before b and nearby I; neither depends on b, I, xi, eta or a coupling. The fourth power of the proved max-norm estimate yields C2*n⁴. This coarse estimate is a valid proof-plan variation for the existential bound, while F1 records its quantitative source-cut limitation.

## Definition classification and hygiene

No new `def`, `abbrev`, `structure` or instance occurs in the audited file. No new fallback object is introduced. The inherited total `fderiv` in the literal lift inverse is only used as an angle-shift parameter in these helpers, not as an unproved derivative/inverse certificate.

A recursive import inspection found 137 local KAM modules, including 56 frozen modules. All 56 are manifest `kind=definition`, `state=SEALED`; there are no provider imports and no frozen theorem imports, hence no DRAFT_SORRY anchor in the closure. The inspected frozen average, oscillator, coordinate and norm objects are the original objects, not surrogates.

A code-mask scan found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace` or `set_option`. The file has copyright, `module`, six public imports, module docstring and the public exposed section. Its 254 total lines are below the 1500-code-line cap. All eight new short names were searched against declaration commands throughout KAM; no outside occurrence was found. Namespace nesting is `KAM.Planetary.SecularSpectrum`; no `_root_` declaration or root shadow occurs.

## Independent verification receipts

Every auditor-controlled Lean/Lake/checker invocation was serialized and used `LEAN_NUM_THREADS=1` and `nice -n 5`; the compile wrapper supplies niceness for the build. The wrapper waited for its gate slot before building. No clean, update, dependency/cache operation or broad library rebuild was requested.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s9q KAM.Planetary.SecularSpectrum.Diagonalize
   [inp-gate] slot 2 acquired 16:40:43 for KAM.Planetary.SecularSpectrum.Diagonalize
   Build completed successfully (9183 jobs).
   exit 0
   ```

   Scoped warning: `Diagonalize.lean:126:5: Variable name hAn is not explicitly referenced.` Its presence is required by the signed interface. Replayed upstream warnings concern unused binders in Kepler/Poincare/Hamiltonian modules, deprecated condition-rewrite names in Coefficients/Definiteness and a haveI style suggestion in Definiteness. No default-heartbeat failure or override occurred.

2. Signed-statement and axiom probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S9QProbe.lean
   exit 0
   ```

   The probe imports only the production Diagonalize module; copies the signed header under fresh name `auditS9QSigned`; proves it by `exact diagonalize D hn hW hWI hAn hR hDiag`; and elaborates `example : type_of% @auditS9QSigned := @diagonalize`. A separate textual comparison prints `SIGNED HEADER EXACT: True`. No unproved draft body is imported. All eight new public theorem axiom queries produced:

   ```text
   'KAM.Planetary.SecularSpectrum.rotDiag_quad_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.rotDiag_quad_rot' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.rotDiag_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.rotDiag_mem_realDisc' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.rotDiag_liftInv_assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.rotDiag_avg_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.rotDiag_avg_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularSpectrum.diagonalize' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. One scoped kernel replay:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularSpectrum.Diagonalize
   replaying KAM.Planetary.SecularSpectrum.Diagonalize
   exit 0
   ```

   S9-Q has one scoped module and no provider module; inherited S8-Q internals were not independently replayed as a second package audit.

4. Required source lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (801 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The only failing message is the explicitly permitted generated-root staleness. Module-system checks, frozen-anchor guard and elaborated ABI checks pass. KAM.lean was not regenerated.

5. Read-only diff checks:

   ```text
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   # empty stdout; exit 0
   git diff --check inp...HEAD -- KAM/Planetary/SecularSpectrum/Diagonalize.lean
   # empty stdout; exit 0
   git diff --check inp...HEAD
   # empty stdout; exit 0
   git diff --check
   # empty stdout; exit 0
   ```

   The source hash was rechecked after verification and is unchanged. At closeout, the only audit-created repository file is this report. The pre-existing untracked handoff is retained unchanged. All audit-created probe, import-inventory and log files were removed from `.lake/abi-scratch/` after recording their results.

## Uncertainties, source defects and deviations

No new suspected defect in a pinned paper was found; this is a local Lean/blueprint audit, not a fresh pinned-PDF verification of the existing errata ledger. The factor-half convention and Omega=2*sigma are preserved. The p9 radian/period-one transport issue is expressly assigned to S9-T, not resolved here. No frozen anchor or campaign theorem is sealed by this report.

F1 records an actual design/graph-versus-export discrepancy with exact source quotations and locators. N1 records the inherited inaccurate claim that an S8-Q rotation cut is consumed here. The n versus sqrt(n) proof-plan substitution preserves the signed existential theorem but leaves the explicit domain cut unpaid. No source, theorem signature, graph record or ledger was repaired. No mathematical deviation was introduced by the auditor.

Closeout: eight of eight public theorem statements and axiom lists inspected; exact signed header and fresh polymorphic proof probe passed; targeted build and scoped kernel replay passed; required lint completed with only the allowed stale-root exception. Signed theorem PASS; requested complete graph-cut coverage FAIL at `stepP:p9:d-c` (F1).
