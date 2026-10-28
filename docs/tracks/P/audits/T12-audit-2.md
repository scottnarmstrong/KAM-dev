# T12 independent package audit 2 (delta)

Overall verdict: **PASS WITH NOTES for T12 infrastructure; Round 1 F1 closed.**
The signed physical quadratic bridge remains unchanged. The appended spectral results establish
`bpP:p11b:sec-beta#data` on the physical source domain. No frozen anchor is implemented or
sealed here; provider/frozen-type and seal-body checks are N/A. This is not T13–T19 or headline
closure. Notes below distinguish the additive import and inherited lint failure from mathematics.

## Scope and immutable inputs

Date: 2026-10-28. Worktree: `/root/code/KAM-inp-p11c-t12`.
Audited HEAD: `487cc668d2f3571c9416dded1ccb2de0cc2cd887`.
Round 1 baseline: `65a4002b`; original implementation: `70ff9781`.
Observed `inp`: `d343cead359c794f416340f529531719f7b449d2`.
Three-dot merge base: `e2088d57c609cc20f1033b70a41e064402222f53`.

Authority read: user instructions; AGENTS.md; docs/PLAN.md and DECISIONS.md; the package audit
brief; T12-handoff.md and T12-audit-1.md; `.drafts/handoff-T12.md` Round 2 fix;
P11C-LEAN-DESIGN.md (especially lines 54, 125, 213–219); its independent design audit;
the signed P11CSignatures.lean; track P statement; Part 11b source and graph packet;
Setting, Part-8 coefficient/quadratic definitions, and imported Part-9 spectral interfaces.
The lean-statement-audit skill supplied source/binder/body and consumption checks.
Only this report is a lasting edit; probes were confined to `.lake/abi-scratch/` and deleted.
The user's exact worktree destination overrides the brief's generic main-worktree destination.

| Input | SHA-256 |
|---|---|
| SpectralAdapter.lean | `f084841eb0d1dc65285900f02212d57ecdca965a26aa5236683482bc9ac6fd3f` |
| P11C-LEAN-DESIGN.md | `51533142c3d8aa6611dd280f64f7ee06b54513cf2578684547fd393b53abfd36` |
| /root/code/KAM-inp/.drafts/design/P11CSignatures.lean | `34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079` |

## Delta integrity and notes

`git diff inp...HEAD` adds SpectralAdapter.lean (471 lines), the Round 1 report (235),
and its handoff (37); no other tracked path changes. `git diff 65a4002b..HEAD` changes only
SpectralAdapter.lean: **190 insertions, zero deletions**. Strict “only appends” is **not literally
true**: one public import of `KAM.Planetary.SecularSpectrum.TwoPlanets` is inserted at line 12,
and 189 lines are inserted before the original namespace/section terminators. This is a necessary
additive dependency, not a change to a signed declaration. Removing that import and the new
attachment block recovers the original file byte-for-byte. The handoff's “470 lines” is off by one.

Byte comparisons separately confirm that `p11c_Q`, `p11c_sigma`, `p11c_projector`, and the
entire `quadratic_physical_bridge` command including proof are unchanged since `65a4002b`.
All pre-existing helpers are also unchanged. The signed definition bodies are exactly the
signature formulas (projector line wrapping only); the signed bridge retains its exact type.
The target now has 471 lines, maximum Unicode line width **100**, within both hard caps.

**N1, informational:** report the import insertion instead of claiming a literal suffix append.
**N2, inherited hygiene:** full source lint still has the frozen AmdConfinement line-width
failure in addition to the explicitly permitted stale generated root. It is not a T12 delta
finding and is not silently counted as a passing full lint run. No repair was authorized.

## F1 refutation and declaration inventory

Source: `blueprint-P/parts/p11b-planar-torsion.tex:180–182`; graph:
`docs/graph/P/packets/P-p11b.nodes.md:1166–1185`.
The source requires “the orthogonal projection onto the sigma_1-eigenspace”, the trace and
rank-one product identities, and its outer-product relation to an ordered diagonalizing frame.
These are the conclusions checked below, not merely a matching matrix codomain.
Line locators refer to the pinned HEAD. All declarations are in `KAM.Planetary`.

| Node / role | Declaration and line | Verdict | Literal conclusion / source attachment |
|---|---|---|---|
| sec-beta#data, signed matrix | p11c_Q, 37 | PASS retained | Physical two-planet matrix; original Part-8 equality unchanged. |
| sec-beta#data, signed eigenvalues | p11c_sigma, 44 | PASS | Exact sorted square-root formula, now attached by sigma_eq_sigma. |
| sec-beta#data, signed projector | p11c_projector, 49 | PASS | Exact quotient formula; now characterized below. |
| sec-beta#data, signed second jet | quadratic_physical_bridge, 224 | PASS retained | Actual physical jet, both quadratic blocks, exact factorial convention. |
| Symmetry helper | p11c_Q_symm, 286 | PASS stronger domain | Q10=Q01 for every p,a, without positivity assumptions. |
| sec-beta#data / U9 | p11c_sigma_eq_sigma, 291 | PASS | Equality with upstream sorted physical spectrum, not an assumed spectrum. |
| sec-beta#data / n2 | p11c_sigma_lt, 324 | PASS | sigma0<sigma1 on the whole positive ordered axis cone. |
| sec-beta#data / n2 | p11c_sigma_neg, 330 | PASS | Both indexed eigenvalues strictly negative. |
| Algebra helper | p11c_sigma_sum_prod, 336 | PASS | Trace and determinant identities of the actual Q. |
| sec-beta#data | p11c_projector_trace, 353 | PASS | P00+P11=1. |
| sec-beta#data | p11c_projector_det, 363 | PASS | P00 P11=P01^2. |
| sec-beta#data | p11c_projector_symm, 377 | PASS stronger domain | P transpose=P for every p,a. |
| sec-beta#data | p11c_Q_mul_projector, 386 | PASS | QP=sigma0 P. |
| sec-beta#data | p11c_projector_idem, 403 | PASS | P^2=P. |
| sec-beta#data | p11c_projector_mulVec_eq_self_iff, 420 | PASS | Px=x iff Qx=sigma0 x, every real vector x. |
| sec-beta#data | p11c_projector_eq_frame, 442 | PASS | Ordered SO frame has s=p11c_sigma and Pij=Ri0 Rj0. |
| Entire assigned spectral-data node | bpP:p11b:sec-beta#data | PASS | Formula, physical spectrum, orthogonal projection, rank-one and frame clauses established together. |

The new helper names describe algebraic pieces of the one assigned node. They do not purport
to establish bf-gram, bf-avg, bt-rot or as-ent themselves. Their conclusions are exact components
of that node or supporting identities, with no weakened substitute for an assigned graph result.
The retained original helpers remain accepted as in Round 1, with their byte identity checked.

Independent proof review: sigma identification uses upstream strict order, trace and determinant
to choose the positive square root of the squared eigenvalue gap. The gap is proved before any
inverse cancellation. Symmetry plus idempotence gives orthogonality in the ordinary finite real
inner product; the fixed-vector iff identifies its image with precisely the first eigenspace.
Trace/product give the rank-one identities explicitly. Frame identification uses SO orthogonality,
ordered spectral uniqueness and the literal matrix decomposition, not an arbitrary eigenvector.
None of these proofs changes the Pi max-norm ambient carrier or assumes a spectral conclusion
on physical data. Ordinary finite-dimensional orthogonality here does not require EuclideanSpace.

## Expanded binder audit of the delta

The following table is schematic over the ten physical-domain lemmas: sigma_eq_sigma, sigma_lt,
sigma_neg, sigma_sum_prod, projector_trace, projector_det, Q_mul_projector, projector_idem,
projector_mulVec_eq_self_iff, projector_eq_frame. Each row applies once to each named lemma;
all additional binders are listed individually. Q_symm/projector_symm use only p,a.

| Declaration(s) | Expanded binder | Bin | Source meaning |
|---|---|---|---|
| Each physical-domain lemma | p | TYPING | G,m0,m:Fin 2→R physical record. |
| Each physical-domain lemma | hp.1 | STANDING | G>0, Part 11b standing assumptions. |
| Each physical-domain lemma | hp.2.1 | STANDING | m0>0, same source. |
| Each physical-domain lemma | hp.2.2 | STANDING | Every planet mass positive, same source. |
| Each physical-domain lemma | implicit a | TYPING | Fin 2→R axes, source A2. |
| Each physical-domain lemma | ha.1 | SOURCE | 0<a0, A2. |
| Each physical-domain lemma | ha.2 | SOURCE | a0<a1, A2. |
| Q_symm | p | TYPING | Arbitrary physical record; stronger than on-domain source. |
| Q_symm | a | TYPING | Arbitrary real axes. |
| projector_symm | p | TYPING | Arbitrary physical record; stronger domain. |
| projector_symm | a | TYPING | Arbitrary real axes. |
| sigma_neg | j | TYPING | Fin 2 eigenvalue index. |
| projector_mulVec_eq_self_iff | x | TYPING | Arbitrary Fin 2→R vector. |
| projector_eq_frame | implicit R | TYPING | Real 2x2 frame matrix. |
| projector_eq_frame | implicit s | TYPING | Real two-entry spectrum. |
| projector_eq_frame | hR.1 | SOURCE | R transpose R=1, expansion of rho in SO(2), source L182. |
| projector_eq_frame | hR.2 | SOURCE | det R=1, same source. |
| projector_eq_frame | hs | SOURCE | Strictly ordered spectral labels, source L180. |
| projector_eq_frame | h | SOURCE | Q=R diag(s) R transpose, diagonalizing-frame source context. |

Totals after expanding hp, ha and hR: **82 inputs: TYPING 28, STANDING 30, SOURCE 24,
RULED 0, EXCESS 0** (51 syntactic binders before those expansions). In particular, no spectral
gap, eigenvalue formula, or projection identity is assumed to obtain the corresponding physical
result. The frame lemma is universally quantified over the source's diagonalizing frame; it does
not claim to construct one. Its frame premises are discharged by the already imported
`SecularSpectrum.n2_global_frame` in the consumer probe.

## Definition classification

No new def, abbrev, structure, choice or assumption bundle occurs in the delta.
The unchanged definitions retain the following classifications:

| Definition | BODY_MATCH | PUBLIC_CARRIER | WELL_DEFINEDNESS | CHARACTERIZATION | CHOICE_INDEPENDENCE | DEFINITION_VERDICT |
|---|---|---|---|---|---|---|
| p11c_Q (literal physical formula) | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| p11c_sigma (literal root formula) | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| p11c_projector (literal quotient formula) | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| p11cSecularData (physical record adapter) | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |

The spectral assertions are on the exact source domain, not invented off-domain claims about
the total real formulas. The former missing on-domain characterization is now proved; no
arbitrary object or fallback is introduced to stand in for the physical projector.

## Consumer suitability

| Consumer | Required T12 output | Disposition |
|---|---|---|
| bf-gram, packet L1274 | Pi entries agree with first column of the ordered SO frame | projector_eq_frame supplies every i,j; specializing the standard rotation gives gamma², gamma s, s². |
| bf-avg, packet L1307 | P00+P11=1 and P00 P11=P01² | Exact trace/det exports; no extra frame premise. |
| bt-rot, packet L1379 | Simple spectrum and analytic Pi on the physical open set | Exact gap export; analytic projector composition checked using the imported analytic global frame and projector_eq_frame. No analytic angle lift claimed. |
| as-ent, packet L1725 | Product and projection identities, including delta_pi²=1-4P01² | Trace/det exports give the latter polynomial identity; independently elaborated. |

The consumer probe constructs a physical ordered analytic SO frame from
`SecularSpectrum.n2_global_frame (p11cSecularData p hp)`, rewrites its diagonalization using
Q_eq_coeffs and sigma_eq_sigma, and applies projector_eq_frame. It then proves
`AnalyticOnNhd ℝ (fun a => p11c_projector p a i j) p11c_axes` for arbitrary i,j by local
congruence with the analytic product Ri0*Rj0 on the open axis cone. Thus bt-rot's analytic
input is available through an actual composition, even though no separately named production
projector-analytic theorem was added. The scratch composition is evidence of applicability,
not a new production export or a claim that T14's signed frame has been implemented.
T14 still owns its concrete frame and rotation lift; T13 owns averaging and Gram calculations;
T18/T19 own asymptotic estimates. Those unimplemented modules are outside this delta audit.

## Verification receipts

All audit Lean commands were serialized, with `LEAN_NUM_THREADS=1 nice -n 5`.
The targeted build used the prescribed shared gate; other workers were not modified or stopped.

1. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
   `git diff --check inp...HEAD`: empty, exit 0. Initial worktree status was clean.
2. `LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh
   /root/code/KAM-inp-p11c-t12 KAM.Planetary.PlanarTorsion.SpectralAdapter`: exit 0;
   final output `Build completed successfully (9187 jobs).` The gate acquired slot 1.
   Replayed dependency warnings concern unused variables/deprecated names; no target-file warning.
3. Static checks: exact recovery of the Round 1 file by removing only the new import/block;
   all four signed commands byte-unchanged; 471 lines, maximum width 100; no forbidden proof
   escapes, resource overrides or EuclideanSpace; copyright/module/public imports/docstring/exposed
   public section intact. All **22 public short names** occur once among KAM declaration commands.
   Recursive import inventory: **141 KAM modules, zero providers, 55 frozen modules**, all imported
   frozen anchors manifest state SEALED, none a frozen theorem or DRAFT_SORRY.
4. `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T12Audit2.lean`:
   **exit 0**. Exact signed copies of all three definitions equal the exports by `rfl`;
   the exact signed bridge command with `exact quadratic_physical_bridge p hp a ha z`
   elaborates, as does its `type_of%` comparison. The root-name environment probe found no
   root shadow for any of the 22 public names. The consumer witnesses described above and
   the exact as-ent delta_pi identity all elaborate without added premises.
   An initial scratch-only attempt lacked `open Real` and the scoped elementwise matrix norm;
   correcting those probe imports/scopes resolved it. No production edit or resource override.

Exact axiom output of the successful probe:

```text
'KAM.Planetary.p11c_Q' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_sigma' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_projector' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_laplace_eq_laplace_def' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cSecularData' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_axes_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_Q_eq_coeffs' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_iteratedFDeriv_two_of_isBigO' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_iteratedFDeriv_two_quad' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.quadratic_physical_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_Q_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_sigma_eq_sigma' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_sigma_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_sigma_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_sigma_sum_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_projector_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_projector_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_projector_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_Q_mul_projector' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_projector_idem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_projector_mulVec_eq_self_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_projector_eq_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'audit2_consume_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'audit2_consume_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

5. `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose
   KAM.Planetary.PlanarTorsion.SpectralAdapter`: **exit 0**; exact output:

```text
replaying KAM.Planetary.PlanarTorsion.SpectralAdapter
```

6. `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`: completed, **exit 1**.
   Exact output:

```text
Lean lines over 100 characters:
/root/code/KAM-inp-p11c-t12/KAM/Frozen/Planetary/Theorems/AmdConfinement.lean:77:101
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (885 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The stale root is the brief's explicit exception. The frozen 101-character line is a separate
pre-existing failure, present in Round 1 and outside both the package and delta diffs.
Full lint is therefore recorded as failing globally, with module-system, frozen guard and ABI
checks independently passing. There is no SpectralAdapter lint finding; no generated or frozen
file was edited to conceal either issue.

## Closeout, uncertainties and errata

Round 1 F1 is **CLOSED**: original physical spectrum and complete projector characterization
are attached with source hypotheses, and required consumer inputs have checked compositions.
The signed bridge retains its Round 1 mathematical acceptance and passes fresh exact-type,
axiom and kernel checks. All requested validations completed; none remains pending.

No suspected mathematical erratum in a pinned source or frozen declaration was found.
No new source deviation was introduced. The old handoff's spectral deferral to T14 is superseded
by this fix; T14 still owns its own frame/lift result. The only new handoff inaccuracies are the
literal append claim and 470-versus-471 line count, documented above. No heartbeat/design signal
occurred in the package. No claim is made about downstream proof completion, analytic angle
lifting, moving-Sun higher jets, a frozen seal, or any campaign headline.

Final checks: `git diff --check` and `git diff --check inp...HEAD` pass; audited source SHA-256
is unchanged; no T12Audit2 scratch artifacts remain. Final status contains only this new report.
No tracked file was edited, and no state-changing git command was used.
