# T6 independent package audit 1

**Overall package verdict: FAIL — one assigned graph obligation is missing.**

The signed `KAM.Planetary.quartic_explicit` theorem and the signed `p11c_coeffs` definition pass signature and proof checks. The package is not complete under the handoff's explicit slice-completeness rule: `stepP:p11b:qe-c12` is not established. This is a missing proof, not a refutation of the signed theorem.

## Scope and authority

Audited 2026-10-28 in `/root/code/KAM-inp-p11c-t6`, HEAD `7a8900201ecfbd3156240041d0952b88c1fe0fdd`; comparison `inp` resolved to `b8f993d23d231733c86a70ab03dc9b362a45f1ea`. Read AGENTS.md, PLAN, DECISIONS, the package brief, T6 handoff/AUDIT FOCUS, P11C design and its design audit, relevant Part-8/11b blueprint statements, track-P statement, frozen Phase/Assemble/secular-average interfaces and reused Setting/Part-8/T5 interfaces.

The exact report destination follows the user's explicit worktree-path instruction, overriding the generic brief's MAIN-worktree destination. No frozen anchor or provider is delivered by T6; frozen-provider equality and seal-body tests are therefore not applicable. No frozen theorem is declared seal-ready by this report.

`git diff inp...HEAD` warns `multiple merge bases, using b5e58ec5e766134ead4e306f3ed3c4dc0da81acd`. Its full inventory is 24 files / 6701 insertions (6845 diff lines): 17 inherited T5 PairJet files and the seven T6 files below. All seven T6 files were read in full; inherited T5 proof internals are outside the requested audit-only scope. T5 exports and their use were checked as dependencies. Protected-path diff is empty.

Authoritative live signatures: `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean`, SHA-256 `6a9b154b4d1d18dc40d41e41a914452c3efe6f8ebe8a9701f3d23b1c2c07c5b7`. Design SHA-256 `51533142c3d8aa6611dd280f64f7ee06b54513cf2578684547fd393b53abfd36`. Current signatures, not historical audit hashes, control this comparison.

## Finding F1: missing exact diagonal consistency proof

**FAIL, completeness.** Design `docs/tracks/P/design/P11C-LEAN-DESIGN.md:107` assigns `stepP:p11b:qe-c12` to T6 as a local fragment of `quartic_explicit`. Blueprint `blueprint-P/parts/p11b-planar-torsion.tex:115` requires comparison with Part 8's formula, specifically

`c_i = -G*m_1*m_2*(h⁽⁴⁾(0)/64 - h''(0)/16)/Lambda_i^2`,

with `h = radialH a_i a_j`, for each of the two eccentric-planet cases. The theorem statement at line 108 explicitly says “c₁,c₂ coincide with the diagonal formula”.

The handoff claims “c1, c2 are covered because the whole degree-four part is identified through pair_jet (T5), which already contains the diagonal case.” That identifies the diagonal **of the pair-average jet**, but does not compare it to the independent radial-derivative expression. `Quartic.lean:199–216` concludes only analyticity and the two homogeneous-part equalities. Its fixed-jet proof (`:118–137`) uses conversion, the order-six remainder and a polynomial derivative; its moving proof (`:141–146`) uses `same_jets`. Neither contains the radial comparison. `PairJet.lean:103` exports analyticity and `p11c_JetEq 5` only. `PairJet/Diag.lean` supplies generic diagonal calculus, not the Part-8 radial formula. Searches of T6 and T5 find no reference to `radialH` or `pairSlowSecular_diag_jet`.

The relevant upstream result exists: `KAM/Planetary/SecularForm/DiagonalJet.lean:45`, `SecularForm.pairSlowSecular_diag_jet`, gives the literal pair-average radial expansion with an order-six remainder. The missing work is to attach both physical single-planet restrictions to that result (including the swapped outer-eccentric case), compare their fourth coefficients, and conclude the displayed equality with `p11c_coeffs p a 0/1`. A proof in the main theorem or a distinctly named helper is sufficient; no signature or frozen-file change is needed. Having two independently available expansions does not itself constitute their formal comparison.

This is a deviation from the handoff's completeness claim. It does not require changing the six coefficients, and no counterexample to their values was found. Until F1 is discharged, the whole assigned graph slice cannot receive PASS.

## Graph-node verdicts

| Node | Lean declaration / fragment | Verdict | Evidence |
|---|---|---|---|
| `bpP:p11b:quartic-explicit` signed surface | `quartic_explicit`, `p11c_coeffs`; reused `p11c_homogeneousPart` | PASS for signed surface; incomplete literal node | Exact signatures and physical jets; diagonal comparison F1 remains. |
| `stepP:p11b:qe-conv` | `qeScale`, `qeV`, `qe_pairJet_qeV`, `qe_alg`, `qe_quartic_coeffs` | PASS | Exact eccentric conversion, corrections −A/4 and −B/8, six physical denominators. |
| `stepP:p11b:qe-an` | `qe_gap_bound`, `qe_remainder_bound`, `qe_fix_jet`, `qe_mov_jet`, `qe_coeffs_analyticAt` | PASS | Analyticity and order-six error proved; moving/fixed same_jets applied on proved physical action domain. |
| `stepP:p11b:qe-c12` | no radial-comparison proof or export | FAIL | F1. T5's full pair jet does not discharge comparison with Part 8's independent formula. |

## Public declaration inventory

All names below are in `KAM.Planetary`. Each unsigned helper has its own name, mathematical premises and proved conclusion. No unsigned export impersonates a graph node. Generic calculus assumptions (analyticity, a line-polynomial identity, or an explicit error bound) belong to distinct helpers and are discharged in the physical proof. There are 44 public theorems and 10 definitions; no new structures or abbreviations.

| Node / purpose | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| quartic-explicit | `qe_iteratedFDeriv_four` (`Quartic.lean:60`) | PASS | Reads 4th diagonal derivative from a line polynomial; explicit smoothness premise. |
| quartic-explicit | `qe_quartic_smul` (`Quartic.lean:78`) | PASS | Exact degree-four homogeneity, all coefficients and phases. |
| quartic-explicit | `qePoly_line` (`Quartic.lean:84`) | PASS | Constant/quadratic/quartic line decomposition. |
| quartic-explicit | `qePoly_contDiff` (`Quartic.lean:104`) | PASS | Polynomial smoothness on the whole phase carrier. |
| quartic-explicit | `qe_eventually_small` (`Quartic.lean:110`) | PASS | Positive actions imply a neighborhood in the physical chart. |
| quartic-explicit | `qe_fix_jet` (`Quartic.lean:118`) | PASS | Physical fixed average has the displayed fourth diagonal jet. |
| quartic-explicit | `qe_mov_jet` (`Quartic.lean:141`) | PASS | Actual moving/fixed fourth jets agree via Part 8 same_jets. |
| quartic-explicit | `qe_coeffs_analyticAt` (`Quartic.lean:151`) | PASS | Analyticity at every admissible axis, no additional premise. |
| quartic-explicit | `quartic_explicit` (`Quartic.lean:199`) | PASS | Exact signed theorem; both physical averages, all slow directions. |
| conversion | `qeJetExpr` (`Algebra.lean:25`) | PASS | Finite pair-jet polynomial in independent scalar variables; no fallback. |
| conversion | `qePolyExpr` (`Algebra.lean:32`) | PASS | Finite polynomial truncation in squared lengths and dot product; no fallback. |
| conversion | `qe_alg` (`Algebra.lean:37`) | PASS | Exact conversion error; geometric inequalities are explicit helper premises and discharged downstream. |
| analyticity / jet | `qeScale_analyticAt` (`Bounds.lean:36`) | PASS | Positive-action square root analytic near zero. |
| analyticity / jet | `qeV_analyticAt` (`Bounds.lean:48`) | PASS | Eccentricity conversion analytic near zero. |
| analyticity / jet | `qeV_zero` (`Bounds.lean:56`) | PASS | Conversion sends zero to zero for all actions. |
| analyticity / jet | `qe_sq_le` (`Bounds.lean:59`) | PASS | Pi max norm controls both coordinates with factor 2. |
| analyticity / jet | `qeA_le` (`Bounds.lean:68`) | PASS | Positive-action quadratic norm bound. |
| analyticity / jet | `qeA_nonneg` (`Bounds.lean:73`) | PASS | Nonnegativity from positive actions. |
| analyticity / jet | `qeV_norm_le` (`Bounds.lean:78`) | PASS | Local conversion Lipschitz bound; square-root domain conditions explicit. |
| analyticity / jet | `qe_pairJet_eq` (`Bounds.lean:113`) | PASS | Eliminates squared slow-length square root exactly. |
| analyticity / jet | `qe_quartic_analyticAt` (`Bounds.lean:128`) | PASS | Polynomial quartic analytic everywhere. |
| analyticity / jet | `qe_pairJet_analyticAt` (`Bounds.lean:138`) | PASS | Pair jet polynomial analytic everywhere in slow variables. |
| analyticity / jet | `qe_gap_bound` (`Bounds.lean:154`) | PASS | T5 fifth-jet equality plus analyticity gives order-six remainder. |
| analyticity / jet | `qeS` (`Bounds.lean:169`) | PASS | Scaled literal pair average composed with qeV, not a substitute assumed model; qe_secular_eq proves physical equality near zero. |
| analyticity / jet | `qePoly` (`Bounds.lean:173`) | PASS | Concrete constant/quadratic/quartic polynomial; no assumed jet or remainder field. |
| analyticity / jet | `qe_alpha_mem` (`Bounds.lean:178`) | PASS | Admissible axes imply ratio in (0,1). |
| analyticity / jet | `qeS_analyticAt` (`Bounds.lean:182`) | PASS | Analytic pair average composed with exact eccentricity conversion. |
| analyticity / jet | `qePoly_analyticAt` (`Bounds.lean:188`) | PASS | Polynomial analytic for all physical data/axes; coefficients fixed. |
| analyticity / jet | `qe_cauchy` (`Bounds.lean:202`) | PASS | Two-coordinate Cauchy inequality with exact action normalization. |
| analyticity / jet | `qe_sig_sq` (`Bounds.lean:214`) | PASS | Exact square-root product identity on its explicit domain. |
| analyticity / jet | `qe_remainder_bound` (`Bounds.lean:220`) | PASS | Proves, rather than assumes, local order-six error; constant may depend on fixed p,a. |
| conversion | `qeA` (`Compose.lean:27`) | PASS | Squared slow length divided by action; total division at zero is harmless because physical uses prove action positivity. |
| conversion | `qeD` (`Compose.lean:30`) | PASS | Dot product divided by square-root actions; same positive-action restriction at uses. |
| conversion | `qeSig` (`Compose.lean:33`) | PASS | Product of exact conversion square roots; domain inequalities proved when squared or estimated. |
| conversion | `qeScale_eq` (`Compose.lean:36`) | PASS | Exact sqrt quotient; positive actions only. |
| conversion | `qeScale_sq` (`Compose.lean:47`) | PASS | Exact squared conversion on the nonnegative-radicand domain. |
| conversion | `qeV_sq` (`Compose.lean:51`) | PASS | Exact quadratic-minus-quartic length identity. |
| conversion | `qeV_dot` (`Compose.lean:62`) | PASS | Exact scalar product conversion. |
| conversion | `qeV_slowLength_sq` (`Compose.lean:72`) | PASS | Exact sum of squared eccentricity lengths. |
| conversion | `qe_pairJet_qeV` (`Compose.lean:80`) | PASS | Exact substitution of conversion into pair jet. |
| conversion | `qe_quartic_coeffs` (`Compose.lean:96`) | PASS | Exact six coefficients; rpow-to-sqrt justified by positive actions. |
| quartic-explicit | `p11c_coeffs` (`Defs.lean:25`) | PASS | Six explicit signed formulas; intended coefficients on admissible axes. Total real division/rpow elsewhere is not used for physical claims. |
| analyticity / jet | `qeJet_diag_eq_zero` (`Jet.lean:43`) | PASS | Generic analytic-series coefficients vanish below order N under proved Big-O bound. |
| analyticity / jet | `qeJet_iteratedFDeriv_eq_zero` (`Jet.lean:92`) | PASS | Generic vanishing diagonal derivatives below N. |
| analyticity / jet | `qeJet_isBigO_of_jet_zero` (`Jet.lean:102`) | PASS | Generic converse analytic remainder estimate. |
| conversion | `qeScale` (`Reduce.lean:33`) | PASS | Exact eccentricity scale; Real.sqrt has its standard total extension. Analytic and physical uses establish positive actions and a local nonnegative radicand. |
| conversion | `qeV` (`Reduce.lean:37`) | PASS | Exact scaled slow coordinates on the whole carrier, including the standard total sqrt extension. |
| conversion | `qe_pairPotential_two` (`Reduce.lean:40`) | PASS | Literal two-body finite-sum potential reduction. |
| conversion | `qe_position` (`Reduce.lean:47`) | PASS | Proves scaling of actual Poincare position to unit-axis orbit. |
| conversion | `qe_poincareV` (`Reduce.lean:70`) | PASS | Exact coordinate adapter; all actions, phases, angles. |
| conversion | `qe_axis_sq` (`Reduce.lean:75`) | PASS | Physical action/axis dictionary under standing positivity. |
| conversion | `qe_actions_pos` (`Reduce.lean:87`) | PASS | Positive physical actions on admissible axes. |
| conversion | `qe_integrand` (`Reduce.lean:98`) | PASS | Actual fixed perturbation equals scaled orbit integrand. |
| conversion | `qe_secular_eq` (`Reduce.lean:140`) | PASS | Literal frozen radian average equals scaled pair average. |

## Definition classification and proof fidelity

All ten definitions are concrete formulas for the intended adapters, finite polynomials or actual averaged functions. The definition rows above classify every one. There are no choice-based fallback witnesses, invented norm instances, assumed remainders or assumed physical representations. Total real division, square root and real powers outside the positive physical cone retain standard Mathlib behavior; physical conclusions are restricted to valid data/admissible axes and the proofs establish needed local chart bounds.

The proof uses the frozen phase order and literal `(2*pi)^(-2)` angular average. `qe_integrand` proves the physical integrand identity before integration, using the actual Poincare chart and axis dictionary. `qe_secular_eq` uses constant multiplication of the Bochner integral, an unconditional identity; it does not infer a physical jet from a zero integral outside an integrable neighborhood. Local analyticity and T5's actual jet attach at zero. Pi max-norm estimates retain explicit factors (notably `qe_sq_le`'s 2); the helper remainder constant is allowed to depend on fixed physical data and axes and is not claimed uniform.

All SIGNED declarations in this slice match the supplied signature text modulo whitespace. The coefficient body is also verified by definitional equality in Lean. A fresh copy of the signed theorem type is proved with `by exact quartic_explicit p hp`, preserving exactly the explicit binders, and a `type_of%` example checks the full polymorphic type. The helpers add no premises to the signed result. Generic homogeneous-part placement in Setting follows design-audit N2. T6's dependency on T12 SpectralAdapter uses only the proved physical data adapter and axes-membership lemma; no cycle or assumed quadratic/quartic output is introduced. Planned Beta/Asymptotic consumers receive the exact six formulas and physical jet they need; the separate radial-comparison node still requires F1.

## Independent validation

All Lean-facing commands used `LEAN_NUM_THREADS=1` and `nice -n 5`, serially. No subsequent Lean/Lake invocation was started before the previous invocation completed. No source repair, git mutation, cache/package modification or root regeneration was performed.

Targeted build:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-t6 KAM.Planetary.PlanarTorsion.Quartic
```

Exit 0. Output began `[inp-gate] slot 3 acquired 22:25:40 for KAM.Planetary.PlanarTorsion.Quartic` and ended `Build completed successfully (9225 jobs).` Replayed upstream warnings concerned unused variables, deprecated lemmas and a style suggestion; no T6 warning or proof escape was reported.

Signature/body and all-public-theorem axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T6Probe.lean
```

Exit 0; no signature/body elaboration error. The probe copied the authoritative coefficient body and theorem type under fresh names, checked coefficient equality by `rfl`, and used:

```lean
-- exact copied signed type precedes this body
by exact quartic_explicit p hp
example : type_of% @auditT6_signed := @quartic_explicit
```

Its exact axiom output for all 44 public theorems was:

```text
'KAM.Planetary.qe_iteratedFDeriv_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_quartic_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qePoly_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qePoly_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_eventually_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_fix_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_mov_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_coeffs_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.quartic_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_alg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeScale_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeV_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeV_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeA_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeA_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeV_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_pairJet_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_quartic_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_pairJet_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_gap_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_alpha_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeS_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qePoly_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_sig_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_remainder_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeScale_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeScale_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeV_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeV_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeV_slowLength_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_pairJet_qeV' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_quartic_coeffs' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeJet_diag_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeJet_iteratedFDeriv_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qeJet_isBigO_of_jet_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_pairPotential_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_position' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_poincareV' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_axis_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_actions_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_integrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qe_secular_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
```


## Source hygiene and files

The source-masked scan of the seven T6 files returned `FORBIDDEN []` for proof escapes, forbidden ambient types and resource overrides. All seven contain copyright, `module`, public imports, module docstrings and `@[expose] public noncomputable section`. No root namespace declarations or global instances were introduced. A repository-wide declaration-name inventory found `PUBLIC DECLS 54 SHORT NAME COLLISIONS []` (the handoff's 62 names also count eight private declarations).

Transitive KAM import scan: 179 modules; no provider modules or frozen theorem modules. The 56 frozen definition files in that closure each have a manifest entry, and every entry has state `SEALED`; no missing manifest entries. Physical reused definitions and their relevant domains were read, including Phase, Assemble, secularAverage, oscillatorAction, the slow-coordinate adapters and actual moving/fixed perturbations.

| Audited file under `KAM/Planetary/PlanarTorsion/` | Lines | Length check |
|---|---:|---|
| `Quartic.lean` | 220 | PASS |
| `Quartic/Defs.lean` | 36 | PASS |
| `Quartic/Jet.lean` | 124 | PASS |
| `Quartic/Reduce.lean` | 152 | PASS |
| `Quartic/Algebra.lean` | 154 | PASS |
| `Quartic/Compose.lean` | 125 | PASS |
| `Quartic/Bounds.lean` | 299 | PASS |

Every line in these files has at most 100 Unicode characters. No file approaches 1500 lines.

```sh
git diff --check inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

Both exit 0, with no whitespace findings or protected-path diff. Both report the multiple-merge-base warning recorded above. The pre-existing untracked `T6-handoff.md` was left untouched.

Kernel replay (one invocation, all seven audited modules):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.Quartic KAM.Planetary.PlanarTorsion.Quartic.Defs KAM.Planetary.PlanarTorsion.Quartic.Jet KAM.Planetary.PlanarTorsion.Quartic.Reduce KAM.Planetary.PlanarTorsion.Quartic.Algebra KAM.Planetary.PlanarTorsion.Quartic.Compose KAM.Planetary.PlanarTorsion.Quartic.Bounds
```

Exit 0. Exact output:

```text
replaying KAM.Planetary.PlanarTorsion.Quartic.Defs
replaying KAM.Planetary.PlanarTorsion.Quartic.Reduce
replaying KAM.Planetary.PlanarTorsion.Quartic.Jet
replaying KAM.Planetary.PlanarTorsion.Quartic.Algebra
replaying KAM.Planetary.PlanarTorsion.Quartic.Compose
replaying KAM.Planetary.PlanarTorsion.Quartic.Bounds
replaying KAM.Planetary.PlanarTorsion.Quartic
```

## Errata, deviations, uncertainties and disposition

No new suspected defect in a pinned mathematical source or frozen declaration was found. The already documented CP11 quartic-coefficient issue is not re-adjudicated here: T6 derives its coefficients from the physical orbit average rather than assuming the printed CP11 coefficients. F1 concerns missing formal comparison and the handoff's closure claim, not a new source erratum.

The design's relocation of generic `p11c_homogeneousPart` to Setting is already covered by design-audit N2. The T12 adapter dependency is sound and acyclic on the inspected import closure; moving two simple adapter declarations to Setting would be an optional architecture change, outside this read-only audit. No theorem premise, carrier, normalization, quantitative uniformity or source restriction was silently repaired.

Required next action: prove the literal `qe-c12` equality for both diagonal coefficients, then rerun the package audit. The signed quartic result can be used at its exact stated type, but T6 must not be marked graph-complete on the present receipt. This report neither seals a frozen anchor nor closes a planetary headline.

Final repository lint (after kernel replay completed):

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, **only the explicitly permitted generated-root exception**. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (976 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Module hygiene, frozen-anchor guard and all 144 elaborated ABI hashes pass. The generated root was left unchanged as required. This exception does not affect or excuse F1.

The disposable signature/axiom probe and this audit's scratch inventory/log files were removed after copying their receipts into this report. Final worktree status contains only this new report and the pre-existing untracked T6 handoff; tracked source bytes remain unchanged. Report-only whitespace validation and the final protected-path diff pass.
