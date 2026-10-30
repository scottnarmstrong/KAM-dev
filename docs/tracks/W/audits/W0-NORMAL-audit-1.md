# W0-NORMAL independent audit 1

**Overall: FAIL as a completion of `bpW:w0n:AB`; PASS WITH NOTES as finite angle-average and nondegeneracy infrastructure.** No provider or frozen theorem is offered for sealing. The other principal results pass their stated local mathematical contracts. This report does not certify W0, W3, W5, W7, or the wave headline as proved.

## Scope and frozen-v1 inputs

Audit date: 2026-10-30. Worktree `/root/code/KAM-inp-wpc`, HEAD `836404bdcde3ae89b4e1c0a856bfdb74969f7f38`, comparison branch `inp` at `a5f010ebcb430f2c7a9b15726507db29321760eb`. Inspected the full `git diff inp...HEAD`, including generated roots and the handoff. Initial working tree clean. User authorization: report-only repository changes, temporary probes under `.lake/abi-scratch/`, narrow verification, no commits. The user's exact absolute destination overrides the generic brief's main-worktree destination.

Read AGENTS.md, PLAN.md, DECISIONS.md, the named audit brief and handoff, W-STATEMENTS.md, the two imported frozen definitions and their manifest entries, W0 normalization/conventions, W3 quartic identification and W7 frequency definitions. There is no `docs/tracks/W/statement.md`; the actual statement document is `W-STATEMENTS.md`. There is no W5 TeX part in this snapshot; `blueprint-W/PLAN.md:40` calls W5 “One KAM step”, planned. W5 assessment below concerns the documented normal-form interface, not nonexistent implementation.

Method: focused tier-2 source/definition/binder audit, separate adversarial re-examination of candidate findings, then serial mechanical verification. No repairs. The auditor did not author the package. Refutation was a separate reasoning/search pass, not a second human or agent review.

Frozen imported identities: `wave.lam.v1` and `wave.sineMode.v1`, both SEALED definitions, D41. Neither imports a provider or draft theorem. Their complete bodies are respectively `sqrt(j²+m)` with explicit `hm : 0 < m`, and `sqrt(2/π) sin(jx)`. No manifest-bound W0-NORMAL theorem exists; provider-type and seal-body probes are N/A by AUDIT FOCUS.

SHA256 snapshot (all locators below refer to frozen-v1 at HEAD):

| File | SHA256 |
|---|---|
| `KAM/Wave/Normal/ActionCoeff.lean` | `d67b408b22d15d964c8104bd90accb79b25f5d99376b64b5fefbb676624cdc4d` |
| `KAM/Wave/Normal/AngleAvg.lean` | `c2298c26ce8f115c5b237e8ceb610a49d79aa7caa46f28efd3b4fffc14ba0649` |
| `KAM/Wave/Normal/FinsuppAbs.lean` | `41d3bc3e2d67415db285a7c00d23f45d0630f34c3232a24c39e6bf699c043ba2` |
| `KAM/Wave/Normal/Nondegeneracy.lean` | `f94824d29e457afdde644440af65b28bf6ff0c611309934cdff07547cf567e42` |
| `KAM/Wave/Normal/NonresAux.lean` | `becf74ee25a17f72b90b86f10c64619fbd88cef9324c5b91fd59430a95678e89` |
| `KAM/Wave/Normal/Nonresonance.lean` | `c2972eceb65564af41cff982a918a8278c07e9ea01e0f338fe38e93d23c6fa44` |
| `KAM/Wave/Normal/QuarticCoeff.lean` | `920ec8e5bcfe0c984f8ac7d219fe910a60e781cec2dd02aa89dd8c7777bc75ab` |
| `blueprint-W/parts/w0-normalization.tex` | `83719844737c92a00fc571cea8395ddb4431c063daf3dbefaf8462d5f96ab21a` |
| `blueprint-W/parts/w0-conventions.tex` | `016d51ed338af4b0dd7192cf82bc2f29783bac56e1405d5bb8542f22b9d2330d` |
| `blueprint-W/parts/w3-birkhoff.tex` | `5c03ee5a24cbcd834938a0aefda8111d084add8b73cb0e2f6734d85cd07ceefb` |
| `blueprint-W/parts/w7-measure.tex` | `fd2c3cd9c6f7ddf68ed7a4684e9910b061ada74574439bd7c9140492a5bf3644` |

## Findings and adversarial disposition

### F1 — source-completion blocker: AB identifies a different left-hand side

Source `w0-normalization.tex:270–294`: “$\bar G$ is the sum of the resonant monomials of $G^{\rm tan}$ (with their coefficients)”; theorem AB concludes `bar G = ½⟨AI,I⟩ + ⟨BI,Z⟩`. Its proof first establishes “Resonant equals averaged”.

Implementation `ActionCoeff.lean:251–256` instead concludes

```text
avgG (Fin.append I Z) - avgG (Fin.append 0 Z)
  = ½ Σ A_ii' I_i I_i' + Σ B_ji I_i Z_j.
```

This is a correct finite real action-average identity. It is not a theorem about the source resonant projection. There is no `Gtan`, resonant coefficient projection or characterization of it in these seven modules. `ActionCoeff.lean:26` nevertheless calls `partial_avgG_eq` “Theorem bpW:w0n:AB”. The handoff honestly acknowledges the missing Qdef/resavg step.

Required missing bridge: expand the correctly weighted complex quartic (prefactor 1/16), split monomials by occurrence of a tangential mode, define/characterize the projection onto zero signed-frequency divisor, apply `quartic_nonresonance` to show precisely the supported paired monomials survive, identify the angle average of each complex monomial, and prove this projection equals the tangential part of the average. Prove the reverse paired-implies-resonant direction as part of the characterization. The already proved nonresonance theorem supplies the hard forward ingredient, but is not consumed in `ActionCoeff` (its import closure does not include `Nonresonance`). A mathematical ingredient or import path is not the composition theorem.

Adversarial re-examination: searched `KAM/Wave` for `partial_avgG_eq`, `avgG_eq`, `quartic_nonresonance`, resonant and paired declarations; checked whether subtraction at zero tangential actions was definitionally Qdef; checked the W3 alternate paired-term counting argument. Subtraction correctly selects tangential terms of the *average*, but Qdef is a different, absent object. W3's independent counting proof could supply the bridge later; it is a source argument, not a Lean theorem here. Finding survives.

Consumer impact: W3 `w3-birkhoff.tex:282–313` requires the actual `bar G(w)` on all complex two-sided sequences with `I_j = w_j w_{-j}`, and the supported divisor-zero iff paired characterization. `partial_avgG_eq` cannot directly rewrite that expression. W5 may use these numerical A/B coefficients in an assumed normal-form input, but cannot infer the Hamiltonian's normal form from this package. W7 `w7-measure.tex:118–127` can use the explicit A/B formulas and `omegaTan`/`omegaNor` for its abstract affine frequency maps; identifying these with the wave Hamiltonian's frequencies still depends on the missing normal-form attachment. Thus fail AB completion, not the computed coefficients.

### F2 — scope gap: finite averages do not establish the infinite/complex identity

`avgG_eq` has `{N : ℕ}` and `I : Fin N → ℝ`; `partial_avgG_eq` has `{n : ℕ}`, `I : Fin 2 → ℝ`, `Z : Fin n → ℝ`, with nonnegative actions. Source `w0-normalization.tex:293–294` explicitly says “computed on finitely supported q and extended by the absolutely convergent formula”. The extension is absent. W3 additionally needs arbitrary complex `w_j w_{-j}`, without nonnegativity. This requires an absolutely convergent sequence identity and a polynomial/coefficient or complexification argument; the real finite integral theorem alone does not state either.

Adversarial re-examination: arbitrary finite N covers every finite initial truncation, and zero-padding covers arbitrary finite supports. Neither quantifies over the infinite weighted sequence carrier or proves the limiting passage. Real nonnegative actions also do not definitionally cover independent complex coordinates. The source is mathematically compatible with the implemented finite theorem; the gap is missing formal scope, not a counterexample to its formula. Finding survives. `avgG` therefore passes its finite specialization but FAILS full source-node closure under the brief's rule against weakened conclusions.

### H1 — protected generated-root delta

`git diff inp...HEAD -- KAM/Frozen manifest README.md` is empty. However, the exact brief's larger protected-path check including `KAM.lean` is **nonempty**: one generated import of `KAM.Root.Wave`; new `KAM/Root/Wave.lean` imports the seven modules. This was disclosed in the handoff as generated. It violates the audit brief's literal empty-root-diff acceptance condition; generation is not an exception in that condition. No unsafe mathematics follows from these imports, but hygiene is not an unqualified PASS. The auditor did not regenerate, edit or restore roots.

## Principal source verdicts

| Node | Export(s), namespace `KAM.Wave` | Verdict | Reason |
|---|---|---|---|
| quartic-coeff | `sineQuarticCoeff_eq`, `_perm`, `_diag`, `_diag_pair`, selection exports | PASS | Positive mode carrier; actual integral of frozen sine modes; all coefficients/signs match W0. |
| g-signed | `sineQuarticCoeff_signed`, `abs_quarticCoeff_le` | PASS | Eight Bool patterns encode exactly ± signs and the prescribed parity. |
| nonres | `quartic_nonresonance` | PASS | All m>0 and positive indices; supported coefficient and exact frequency resonance imply equal signed multisets. |
| moments | `angleAvg_cos_four`, `sum_quartic_moment` | PASS | Genuine normalized product integral; correct 3/8 diagonal and 1/4 pair moments. |
| avgG | `avgG_eq` | FAIL for full source closure; local identity PASS | Correct finite-mode specialization; F2. |
| AB | `partial_avgG_eq` | FAIL for source completion | Correct finite average identity, absent Qdef/resavg and infinite/complex bridge; F1/F2. |
| nondeg (i) | `actionA_eq`, `det_actionA` | PASS | Correct matrix and both determinant formulas, including nonzero conclusion. |
| nondeg (ii) | `pairing_ne_zero` | PASS | All finitely supported l with 1≤sum |l|≤2; correct normal-mode shift. |
| nondeg (iii) | `A3_holds`, `nondegeneracy` | PASS for explicit A/B | Exact affine-function nonidentity; not a Hamiltonian identification claim. |
| kappa and other excluded W0 labels | none claimed | N/A | Not part of package; no closure inferred. |

## Normalizations and A3 binder audit

`angleMeasure = (2π)⁻¹ volume|[0,2π]`, with a proved probability instance. This is the independent radian angle average, not an unnormalized integral. The substitution φ=2πθ sends normalized dφ/(2π) to dθ on [0,1]; hence q=√(2I)cos φ is exactly the period-one convention, with no extra factor in A/B. Here I=|z|²=(q²+p²)/2. These are oscillator actions, not Y=2πI; `omegaTan`/`omegaNor` are radian frequencies. Campaign tangential frequency is ν=ω/(2π); the relevant divisor becomes 2π k·ν+l·Ω. Source conventions at `w0-conventions.tex:127–146` agree. A formal change-of-variables lemma is not claimed by this package.

A3 uses `l : ℕ →₀ ℤ`, normal ν denotes physical mode ν+3; `l1Norm` is the natural-valued sum of integer absolute values. This represents precisely finite integer normal combinations. `affineForm` expands to k·(λ_J+AI)+l·(λ_N+BI). Its conclusion `∃ I : Fin 2 → ℝ, affineForm ... I ≠ 0` is exactly nonidentity of an affine function on ℝ², as in `w0-normalization.tex:341–351`. It does not assert pointwise nonresonance at every action. Restricting nonidentity to a nonempty open action region would need an elementary affine-function lemma downstream; that is not an extra premise here. No bound on k is introduced.

Expanded binder rows for A3 (no bundled assumptions):

| Binder | Bin | Source |
|---|---|---|
| `m : ℝ` | TYPING | W0 mass parameter |
| `hm : 0 < m` | STANDING | w0n opening standing assumption |
| `k : Fin 2 → ℤ` | TYPING | w0n:344, arbitrary k∈ℤ² |
| `l : ℕ →₀ ℤ` | TYPING | w0n:344 finite integer normal combinations |
| `h1 : 1 ≤ l1Norm l` | SOURCE | w0n:344 |
| `h2 : l1Norm l ≤ 2` | SOURCE | w0n:344 |

Counts: SOURCE 2, STANDING 1, TYPING 3, RULED 0, EXCESS 0. Witness I is existential after all inputs. `pairing_ne_zero` deletes k: counts SOURCE 2, STANDING 1, TYPING 2. `nondegeneracy` takes only m and hm; the k/l bounds occur inside its conclusions, not as additional premises.

For the other main surfaces: all positive mode indices, permutations, finite dimensions, actions and signs are typing data; mass positivity is standing; `hg≠0` and `hres=0` in nonres are exactly source premises; nonnegative action bounds are the real action chart's source domain. No conclusion-shaped premise was found. The algebraic helpers (`core_c`, `core_alpha`, `core_beta`, etc.) are explicitly separate conditional lemmas, with their inputs proved at `A3_holds`' call sites. In particular `s≠0` and its bound are supplied by the l1-norm classification and `s_single_props`/`s_pair_props`, not postulated by the public A3 theorem. No uniform constants with hidden extra parameter dependence occur.

## Definition classification

All 27 new named definitions are literal formulas; no structures, choice-selected witnesses, or new assumption bundles occur. Common classifications: WELL_DEFINEDNESS=N/A_LITERAL; CHARACTERIZATION=N/A_LITERAL; CHOICE_INDEPENDENCE=N/A. No definition is accepted as an implementation of the missing Qdef resonant projection.

| Definition | Body / carrier classification |
|---|---|
| `modeIdx` | PASS: Fin N index j maps to physical positive mode j+1. |
| `gN` | PASS: frozen-mode quartic coefficient under that reindexing. |
| `lamMode` | PASS: λ at physical mode j+1. |
| `quarticG` | PASS as finite real-coordinate quartic; not a definition of the infinite frozen Hamiltonian. |
| `avgG` | PASS as literal finite integral on nonnegative action inputs; public ℝ carrier also evaluates negative inputs through total sqrt. It must not be treated as a global action polynomial there (e.g. negative one-mode action gives zero, whereas the displayed polynomial need not). No proof relies on off-domain values. This is not Qdef. |
| `lamTan` | PASS: physical modes 1 and 2. |
| `lamNor` | PASS: finite normal mode j+3. |
| `actionA` | PASS: diagonal 9/(8πλ²), off diagonal 3/(2πλλ); branch is the intended matrix formula. |
| `actionB` | PASS: corrected finite normal coupling 3/(2πλ_jλ_i). |
| `angleMeasure` | PASS: normalized restricted Lebesgue measure on [0,2π]. |
| `angleAvg` | PASS: product-measure integral on Fin N angles; used on integrable quartic trigonometric polynomials. |
| `cosMoment` | PASS as truncated moment table for powers ≤4; default 0 above 4 is not claimed as a true higher even moment and no theorem uses it as one. |
| `idxCount` | PASS: exact multiplicity among four finite indices. |
| `l1Norm` | PASS: sum of integer natAbs on finite support. |
| `lamN` | PASS: infinite normal index ν maps to physical mode ν+3. |
| `actionBN` | PASS: infinite-index version of actionB; definitional restriction checked in probe. |
| `actionAMat` | PASS: Matrix.of actionA, no alternate matrix. |
| `linF` | PASS: finite-support integer-real pairing. |
| `omegaTan` | PASS: λ_J+AI, radian units, on all real actions as an affine map. |
| `omegaNor` | PASS: λ_N+BI, radian units, correct normal shift. |
| `affineForm` | PASS: k·omegaTan+l·omegaNor with exact finite-support pairing. |
| `lamExt` | PASS: literal real square-root extension; analytic facts restrict m>0. |
| `signSide` | PASS: signed-side multiset with multiplicities, signs in ℤˣ={±1}. |
| `sineQuarticCoeff` | PASS: finite interval integral of four frozen sine modes, positive mode indices. |
| `signedSign` | PASS: prescribed parity of the three Bool-coded negative signs. |
| `boolSign` | PASS: true→1, false→−1. |
| `QuarticSel` | PASS on positive modes: seven signed integer relations; auxiliary Nat carrier includes zero, but all source-facing uses take positive modes. |

BODY_MATCH and PUBLIC_CARRIER are OK for the literal auxiliary constructions just classified. For the proposed identification `avgG = source normal form`, BODY_MATCH=FAIL, PUBLIC_CARRIER=FAIL, DEFINITION_VERDICT=FAIL: real finite averaging is not the globally complex resonant polynomial. Its nonnegative-domain evaluation is valid infrastructure; the declaration is not admitted as the missing source definition.

## Complete public theorem ledger

One row per new named public theorem (92). PASS for a helper means its explicit conditional mathematical statement and its actual call-site use are sound, not that the helper alone closes its associated source node. All names below are in `KAM.Wave`; all were included individually in the axiom probe.

| Source node / role | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| AB / finite averaging helper | `modeIdx_injective` (ActionCoeff.lean:40) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| AB / finite averaging helper | `sineQuarticCoeff_pair_val` (ActionCoeff.lean:47) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| AB / finite averaging helper | `sineQuarticCoeff_pair_val_b` (ActionCoeff.lean:58) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| AB / finite averaging helper | `sineQuarticCoeff_pair_val_c` (ActionCoeff.lean:65) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| AB / finite averaging helper | `gN_pair` (ActionCoeff.lean:76) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| AB / finite averaging helper | `gN_pair_b` (ActionCoeff.lean:82) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| AB / finite averaging helper | `gN_pair_c` (ActionCoeff.lean:88) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| AB / finite averaging helper | `gN_diag` (ActionCoeff.lean:94) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| AB / finite averaging helper | `sum_ite_pair_ij_kl` (ActionCoeff.lean:100) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| AB / finite averaging helper | `sum_ite_pair_ik_jl` (ActionCoeff.lean:104) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| AB / finite averaging helper | `sum_ite_pair_il_jk` (ActionCoeff.lean:108) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| AB / finite averaging helper | `sum_ite_all` (ActionCoeff.lean:112) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| AB / finite averaging helper | `sum_quartic_moment` (ActionCoeff.lean:120) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| AB / finite averaging helper | `lamMode_pos` (ActionCoeff.lean:161) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| AB / finite averaging helper | `avgG_eq` (ActionCoeff.lean:177) | FAIL for full source closure; local identity PASS | Finite nonnegative-action specialization; F2. |
| AB / finite averaging helper | `lamTan_pos` (ActionCoeff.lean:230) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| AB / finite averaging helper | `lamNor_pos` (ActionCoeff.lean:233) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| AB / finite averaging helper | `lamMode_castAdd` (ActionCoeff.lean:236) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| AB / finite averaging helper | `lamMode_natAdd` (ActionCoeff.lean:239) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| AB / finite averaging helper | `partial_avgG_eq` (ActionCoeff.lean:251) | FAIL for AB; local identity PASS | F1/F2: finite averaged object, missing resonant and sequence bridge. |
| moments / integral helper | `integral_angleMeasure` (AngleAvg.lean:45) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| moments / integral helper | `integral_angleMeasure_cos_pow` (AngleAvg.lean:59) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| moments / integral helper | `angleAvg_prod_cos_pow` (AngleAvg.lean:79) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| moments / integral helper | `cos_mul_four_eq_prod` (AngleAvg.lean:91) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| moments / integral helper | `idxCount_le` (AngleAvg.lean:98) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| moments / integral helper | `prod_cosMoment_all` (AngleAvg.lean:102) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| moments / integral helper | `prod_cosMoment_pair` (AngleAvg.lean:110) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| moments / integral helper | `prod_cosMoment_zero` (AngleAvg.lean:119) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| moments / integral helper | `prod_cosMoment_pair_a` (AngleAvg.lean:125) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| moments / integral helper | `prod_cosMoment_pair_b` (AngleAvg.lean:130) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| moments / integral helper | `prod_cosMoment_pair_c` (AngleAvg.lean:137) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| moments / integral helper | `prod_cosMoment_idxCount` (AngleAvg.lean:145) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| moments / integral helper | `angleAvg_cos_four` (AngleAvg.lean:192) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| moments / integral helper | `integrable_cos_four` (AngleAvg.lean:201) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| moments / integral helper | `angleAvg_sum_cos_four` (AngleAvg.lean:216) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg finite-support helper | `l1Norm_eq_sum` (FinsuppAbs.lean:29) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg finite-support helper | `card_support_le_l1Norm` (FinsuppAbs.lean:31) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg finite-support helper | `l1Norm_one` (FinsuppAbs.lean:36) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg finite-support helper | `l1Norm_two` (FinsuppAbs.lean:52) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg / algebraic helper | `lamN_sq` (Nondegeneracy.lean:36) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg / algebraic helper | `lamN_gt` (Nondegeneracy.lean:41) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg / algebraic helper | `lamN_injective` (Nondegeneracy.lean:47) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg / algebraic helper | `lamTan_zero_sq` (Nondegeneracy.lean:55) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg / algebraic helper | `lamTan_one_sq` (Nondegeneracy.lean:60) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg / algebraic helper | `actionA_eq` (Nondegeneracy.lean:74) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg / algebraic helper | `det_actionA` (Nondegeneracy.lean:87) | PASS | Exact explicit-coefficient nondegeneracy contract; source quantifiers retained. |
| nondeg / algebraic helper | `linF_single` (Nondegeneracy.lean:114) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg / algebraic helper | `linF_add_single` (Nondegeneracy.lean:119) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg / algebraic helper | `sign_pair_ne_zero` (Nondegeneracy.lean:126) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg / algebraic helper | `pairing_ne_zero` (Nondegeneracy.lean:139) | PASS | Exact explicit-coefficient nondegeneracy contract; source quantifiers retained. |
| nondeg / algebraic helper | `linF_add_mul` (Nondegeneracy.lean:154) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg / algebraic helper | `linF_add_mul_mul` (Nondegeneracy.lean:160) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg / algebraic helper | `s_single_props` (Nondegeneracy.lean:166) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg / algebraic helper | `s_pair_props` (Nondegeneracy.lean:180) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg / algebraic helper | `core_c` (Nondegeneracy.lean:204) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg / algebraic helper | `core_alpha` (Nondegeneracy.lean:214) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg / algebraic helper | `core_beta` (Nondegeneracy.lean:238) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg / algebraic helper | `affineForm_expand` (Nondegeneracy.lean:291) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg / algebraic helper | `lam_facts` (Nondegeneracy.lean:314) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nondeg / algebraic helper | `A3_holds` (Nondegeneracy.lean:325) | PASS | Exact explicit-coefficient nondegeneracy contract; source quantifiers retained. |
| nondeg / algebraic helper | `nondegeneracy` (Nondegeneracy.lean:381) | PASS | Exact explicit-coefficient nondegeneracy contract; source quantifiers retained. |
| nonres analytic helper | `lam_eq_lamExt` (NonresAux.lean:30) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nonres analytic helper | `lamExt_pos` (NonresAux.lean:32) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nonres analytic helper | `lamExt_sq` (NonresAux.lean:35) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nonres analytic helper | `lamExt_lt` (NonresAux.lean:38) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nonres analytic helper | `lamExt_le` (NonresAux.lean:43) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nonres analytic helper | `lamExt_mul_ge` (NonresAux.lean:50) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nonres analytic helper | `lamExt_add_lt` (NonresAux.lean:57) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nonres analytic helper | `lamExt_le_of_sq` (NonresAux.lean:68) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nonres analytic helper | `lamExt_convex` (NonresAux.lean:72) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nonres analytic helper | `lamExt_super` (NonresAux.lean:85) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nonres analytic helper | `lamExt_nat_lt` (NonresAux.lean:107) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nonres analytic helper | `lamExt_nat_le` (NonresAux.lean:111) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nonres analytic helper | `lamExt_pair_eq` (NonresAux.lean:116) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nonres analytic helper | `lamExt_cross_eq` (NonresAux.lean:162) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nonres analytic helper | `lamExt_big_lt` (NonresAux.lean:178) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nonres analytic helper | `lamExt_three_ne` (NonresAux.lean:190) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nonres | `lamExt_two_two` (Nonresonance.lean:35) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nonres | `lamExt_three_pnat` (Nonresonance.lean:60) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nonres | `lamExt_two_two_pnat` (Nonresonance.lean:71) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| nonres | `quartic_nonresonance` (Nonresonance.lean:79) | PASS | Exact positive-index signed resonance implication; multiset multiplicities retained. |
| quartic-coeff / g-signed | `integral_cos_int_mul_Ioc_zero_pi` (QuarticCoeff.lean:39) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| quartic-coeff / g-signed | `sin_mul_four` (QuarticCoeff.lean:48) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| quartic-coeff / g-signed | `sineMode_mul_four` (QuarticCoeff.lean:58) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| quartic-coeff / g-signed | `sineQuarticCoeff_eq` (QuarticCoeff.lean:82) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| quartic-coeff / g-signed | `sineQuarticCoeff_signed` (QuarticCoeff.lean:141) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| quartic-coeff / g-signed | `sineQuarticCoeff_eq_zero_of_not_sel` (QuarticCoeff.lean:173) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| quartic-coeff / g-signed | `quarticSel_of_quarticCoeff_ne_zero` (QuarticCoeff.lean:182) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| quartic-coeff / g-signed | `sineQuarticCoeff_perm` (QuarticCoeff.lean:188) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| quartic-coeff / g-signed | `sineQuarticCoeff_diag` (QuarticCoeff.lean:202) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| quartic-coeff / g-signed | `sineQuarticCoeff_diag_pair` (QuarticCoeff.lean:210) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |
| quartic-coeff / g-signed | `abs_quarticCoeff_le` (QuarticCoeff.lean:224) | PASS | Literal identity/conditional helper; no hidden premise or normalization change. |

## Verification evidence

All Lean/Lake commands owned by this audit are serial and use LEAN_NUM_THREADS=1 and nice priority 5. The mandated compile-gate wrapper supplies nice for builds. Other worktrees have unrelated running builds/checkers; this audit did not start, modify, or terminate them.

Exact build command (exit 0):

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wpc KAM.Wave.Normal.QuarticCoeff KAM.Wave.Normal.NonresAux KAM.Wave.Normal.Nonresonance KAM.Wave.Normal.AngleAvg KAM.Wave.Normal.ActionCoeff KAM.Wave.Normal.FinsuppAbs KAM.Wave.Normal.Nondegeneracy
```

Output: `[inp-gate] slot 2 acquired 17:31:20 ...`; `Build completed successfully (2843 jobs).` No warnings. Warm targeted build, not a clean library rebuild; no heartbeat design failure observed.

Exact kernel replay command (exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Wave.Normal.QuarticCoeff KAM.Wave.Normal.NonresAux KAM.Wave.Normal.Nonresonance KAM.Wave.Normal.AngleAvg KAM.Wave.Normal.ActionCoeff KAM.Wave.Normal.FinsuppAbs KAM.Wave.Normal.Nondegeneracy
```

Output:

```text
replaying KAM.Wave.Normal.Nondegeneracy
replaying KAM.Wave.Normal.FinsuppAbs
replaying KAM.Wave.Normal.ActionCoeff
replaying KAM.Wave.Normal.AngleAvg
replaying KAM.Wave.Normal.Nonresonance
replaying KAM.Wave.Normal.NonresAux
replaying KAM.Wave.Normal.QuarticCoeff
```

Axiom and exact-type probe: generated `.lake/abi-scratch/W0Audit.lean` by importing the seven modules and emitting `#print axioms KAM.Wave.<name>` for **every** name matched by `^theorem (\w+)` in the seven files. Count: 92, identical to the complete ledger. Command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/W0Audit.lean
```

Exit 0. Ninety theorem outputs list `[propext, Classical.choice, Quot.sound]`; two list `[propext, Quot.sound]`; zero unexpected axioms, zero sorryAx. In particular `quartic_nonresonance`, `avgG_eq`, `partial_avgG_eq`, `det_actionA`, `pairing_ne_zero`, `A3_holds`, `nondegeneracy` all list exactly `[propext, Classical.choice, Quot.sound]`.

The same probe includes these independently expanded applications (all elaborate):

```lean
open KAM.Wave
example (m : ℝ) (hm : 0 < m) (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ)
    (h1 : 1 ≤ l1Norm l) (h2 : l1Norm l ≤ 2) :
    ∃ I : Fin 2 → ℝ,
      (∑ i, (k i : ℝ) * (lamTan m hm i + ∑ j, actionA m hm i j * I j)) +
      l.sum (fun ν v => (v : ℝ) * (lamN m hm ν + ∑ i, actionBN m hm ν i * I i)) ≠ 0 :=
  A3_holds m hm k l h1 h2
example (m : ℝ) (hm : 0 < m) {n : ℕ} (j : Fin n) (i : Fin 2) :
    actionB m hm j i = actionBN m hm j.val i := rfl
example (m : ℝ) (hm : 0 < m) {n : ℕ} (I : Fin 2 → ℝ) (Z : Fin n → ℝ)
    (hI : ∀ i, 0 ≤ I i) (hZ : ∀ j, 0 ≤ Z j) :
    avgG m hm (Fin.append I Z) - avgG m hm (Fin.append (0 : Fin 2 → ℝ) Z) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, actionA m hm i j * I i * I j +
      ∑ j, ∑ i, actionB m hm j i * I i * Z j :=
  partial_avgG_eq m hm I Z hI hZ
```

This checks the valid finite theorem's actual contract; it deliberately does not claim a term-level consumer of the missing resonant/infinite theorem.

Public instance: `AngleAvg.lean:35`, `IsProbabilityMeasure angleMeasure`, PASS. Its proof computes the mass as `(ofReal (2π))⁻¹ * ofReal (2π) = 1`, using π>0; no hidden assumptions.

Additional static checks: `rg -n '\b(sorry|admit|axiom|unsafe|opaque|EuclideanSpace)\b|set_option' KAM/Wave/Normal` produced no matches. All seven files have copyright, `module`, public imports, module docstring, and `@[expose] public noncomputable section`. Line counts (including comments): ActionCoeff 285, AngleAvg 241, FinsuppAbs 91, Nondegeneracy 391, NonresAux 202, Nonresonance 162, QuarticCoeff 241. No file approaches 1500 lines. `git diff inp...HEAD --check` and working-tree `git diff --check` produce no output, exit 0. Imported frozen definition SHA256 values match their manifest hashes: Lam `097b70740bbedd0463d2e0ffb98e99bf508f81207b8370ac05ddc91aa3e05f81`, SineMode `708e6e5d2d878d13e87acb6f2e2b4a057be17a33f9999b417cbaf75bac555263`.

## Source errata, deviations and scope limits

No new suspected defect in the pinned source was established by this audit. Existing confirmed errata E-PDE-W-1/2 in `docs/errata/ledger.json:2635–2660` control the normalization. E-PDE-W-1 quotes the printed quartic expansion with prefactor `¼` in z and then no prefactor in w; W0:260–263 has the correct `1/16`, leading to A_ii=9/(8πλ_i²), A_ij=B_ji=3/(2πλ_iλ_j). E-PDE-W-2 quotes `I=½|z|²` and `q=Re z, p=Im z`; the adopted convention is I=|z|² and q=√2 Re z, p=√2 Im z. The package's integrals, actions and numerical coefficients follow the corrected convention. This audit checked the local blueprint and adopted ledger, not fresh images of the original P96-W PDF.

Implementation deviations: Bool coding of signs, positive modes via ℕ+, finite mode indices shifted by one and normal indices shifted by three, multiset resonance conclusions, finite-support integer normal combinations, and algebraic/convexity proofs replacing some source calculus arguments are faithful for the local results. Finite averaging replacing the source resonant projection is a substantive missing realization (F1), not an approved definitional identification. No source or frozen declaration was changed to resolve it.

Uncertified scope: absolute convergence/infinite extension, complexification, analytic Birkhoff transformation, smoothing/vector-field attachment, W5 integration and wave-headline closure. No body in this package establishes them. These gaps are retained explicitly; the clean kernel and axiom results only verify the implemented contracts.

Exact slim lint command (exit 0):

```sh
LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpc
```

Complete output:

```text
check_lean_modules: PASS (1635 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
```

No stale-root warning or forbidden-token warning. This lint PASS does not erase H1: the generated root is current but still changed relative to inp. The two axiom outputs omitting Classical.choice are `modeIdx_injective` and `idxCount_le`.

## Closeout

All 92 named public theorem contracts and 27 named definitions are classified; the probability instance is checked separately. Serial targeted build, seven-module kernel replay, all-theorem axiom census, expanded A3 and finite-average probes, and mandated slim lint passed. Frozen/manifest/README byte deltas are empty; all recorded snapshot hashes remain unchanged. Generated-root delta remains H1. Full AB and full infinite avgG source closure fail for F1/F2. The local coefficient, resonance and explicit-frequency nondegeneracy results are usable within their stated scopes.

The only repository file created/edited by this audit is `/root/code/KAM-inp-wpc/docs/tracks/W/audits/W0-NORMAL-audit-1.md`. Temporary W0Audit probe and audit-owned verification logs under `.lake/abi-scratch/` were removed after recording their commands/results here. No git state changes, source repair or root regeneration were performed. Remaining work is the explicit resonant-object bridge and infinite/complex extension, plus orchestrator disposition of the protected generated-root diff. Audit complete; implementation completion is not claimed.
