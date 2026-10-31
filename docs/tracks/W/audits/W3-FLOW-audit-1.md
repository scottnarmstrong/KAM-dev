# W3-FLOW independent package audit 1

Date: 2026-10-31. **Overall verdict: FAIL for the claimed complete package.**
The proved flow equations, quantitative bounds, inverse and symplecticity pass within their stated domains.
Three source-facing obligations remain: the multilinear slot-recursion identification, multilinear reality,
and joint C¹ regularity. This is a completeness/fidelity rejection, not a claim that a checked Lean theorem is false.
No frozen anchor is sealed by this package; “seal-ready” is inapplicable.

## Snapshot and authority

- Worktree `/root/code/KAM-inp-wpfa` (the environment's `/mnt/HC_Volume_106379410/kam-w/KAM-inp-wpfa` resolves here).
- HEAD `686a1f84b425379844afce778f574c7fa29e335f`; comparison `inp` =
  `ba270772d4dfe54965e03af2033bd21182545318`.
- Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`,
  `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the live
  `docs/tracks/W/audits/W3-FLOW-handoff.md`, including its AUDIT FOCUS.
- Source: current inp `blueprint-W/parts/w3-birkhoff.tex`, SHA256
  `1e09a1eb1b06815116809f1f45e996b1ba79962ebfb755e3c75b797e5a19b161`;
  identical to the worktree copy. Source ranges: standing assumptions 22–26,
  lie-coeff 461–466, leibniz 470–480, flow 504–527, symplectic 579–586.
  The brief's generic `docs/tracks/W/statement.md` does not exist; read the applicable
  `docs/tracks/W/W-STATEMENTS.md` and D41 for headline conventions instead.
- `git diff inp...HEAD`: 25 new `KAM/Wave/Birkhoff/Lie*.lean` modules (3544 lines),
  25 generated root imports, and the handoff. The initial working tree already had an unstaged
  handoff change containing the audit focus; it was preserved. Live handoff SHA256:
  `cfcab7e254f4a5447991a3aab7c4fbd6a1d0e8beafba2fcb0b5707a47e3168ab`.
- No provider or seal: brief item 1 skipped as directed. Generated root changes are explicitly authorized.
  No implementation, frozen, manifest, root or handoff edits were made by this audit.

## Findings and exact unpaid statements

### F1 — Missing full multilinear identification (major)

Source `w3-birkhoff.tex:463–465` defines Φₖ on **arbitrary ordered inputs** by
“`sum_{i=1}^{2k+1} Phi_k(..., S(w^i,w^{i+1},w^{i+2}), ...) / (k+1)`”.
`LieMulti.lean:98–113` instead defines `lieMulti` by block Cauchy recursion
`(k+1) lieMulti_{k+1} = sum_{a+b+c=k} T(lieMulti_a,lieMulti_b,lieMulti_c)`.
`lieMulti_const` (117–132) only identifies its diagonal with `lieSeq`.
`lieDer_apply_field` (`LieLeibniz.lean:170`) proves the correct diagonal Lie recurrence,
and `hasFDerivAt_lieSeq` identifies its derivative. Neither states the source's full multilinear recursion.

The handoff acknowledges the changed recursion, but diagonal equality does not by itself identify
unsymmetrized multilinear maps. There is no theorem in these 25 modules connecting `lieMulti` to the
literal slot-insertion family on all inputs. This audit does **not** assert those two recursions are
mathematically inequivalent; the missing result is their general identification (or the literal slot
recurrence for `lieMulti`). A replacement coefficient construction is valid infrastructure for the flow,
but it cannot certify the exact source definition without that bridge. Consequently the power-series
coefficient identification in flow (i) also remains conditional on this bridge. No source change is authorized here.

### F2 — Multilinear reality is not exported (major)

Source `w3-birkhoff.tex:477` requires
`Phi_k(rho w^1, ..., rho w^{2k+1}) = rho(Phi_k(w^1,...,w^{2k+1}))`.
`LieReal.lean:30–55` proves only `lieSeq_rho`, with the **same** `w` in every input.
`LieReal.lean:60–75` and `LieBirk.lean:114–117` correctly prove reality of the flow.
No public theorem proves the all-input statement for `lieMulti` (or the literal source Φₖ).
The trilinear supplier `birkT_rho` is present (`LieApp.lean:64`), so the missing induction has an available input;
it is still an unpaid source clause. Flow reality itself passes.

### F3 — Joint differentiability is weaker than joint C¹ (major)

Source `w3-birkhoff.tex:514` states “`(t,w) mapsto Gamma_t(w) is C^1 on (-2,2) times B_rho0`”.
`LieFlow2.lean:104–109` concludes `HasFDerivAt ... (tsum lieTermD) (t,w)` and pointwise
summability of the derivative series. It does not conclude continuity of that derivative on the domain.
The proof has a local uniform majorant, but uses `hasFDerivAt_tsum_of_isPreconnected` to export only
pointwise differentiability. Searches of every new module found no `ContDiffOn`, `ContDiffAt`,
`ContinuousOn`/`ContinuousAt` derivative result or other joint C¹ theorem.
`birkGamma_analyticOnNhd` fixes `t`; it is spatial analyticity, not joint regularity.

Required completion: a theorem giving `ContDiffOn ℝ 1 (fun z : ℝ × E => lieGamma T z.1 z.2)`
on `{z | |z.1| < 2 ∧ 40*C*‖z.2‖^2 < 1}`, or an equivalent continuous-derivative statement,
with the concrete specialization. No extra continuity premise may replace this proof.

## Node verdicts and preserved mathematics

| Node/clause | Lean exports (namespace `KAM.Wave`) | Verdict | Reason |
|---|---|---|---|
| lie-coeff | `lieSeq`, `lieMulti`, `lieMulti_const` | FAIL | F1: diagonal construction identified, full slot recurrence not certified. |
| leibniz (i) | `hasFDerivAt_lieSeq`, `lieDer_apply_field` | PASS | Exact diagonal Lie recurrence; symmetric `T` supplied by `birkT_perm`. |
| leibniz (ii) | `norm_lieMulti_le`, `norm_lieMultiF_le`, `birkLieM_le_pow` | PASS WITH NOTES | Bounds for constructed block coefficients; literal Φ identification pending F1. |
| leibniz (iii) | `lieSeq_rho`, `birkT_rho` | FAIL | F2: only diagonal coefficient reality proved. |
| leibniz (iv) | `lieSeq_succ`, `lieDer_succ_sym` | PASS | Cauchy recursion and differentiated identity with exact factor 3. |
| flow (i), absolute convergence | `summable_norm_lieTerm`, `summable_norm_lieDTerm` | PASS | Norm summability, including the origin and t=0. |
| flow (i), spatial analyticity | `lieGamma_hasFPowerSeriesOnBall`, `birkGamma_analyticOnNhd`, `birkGamma_sub_analytic` | PASS WITH NOTES | Both W and W⁺ analyticity proved. Coefficients are constructed `lieMulti`; F1 remains. |
| flow (i), joint C¹ | `hasFDerivAt_lieGamma` | FAIL | F3: joint derivative exists, continuous derivative not exported. |
| flow (ii) | `lieGamma_zero`, `birkGamma_flow`, `birkGamma_transport` | PASS | Actual trilinear field, no ODE solution assumed. |
| flow (iii) | `norm_birkGamma_le`, `birkGamma_sub_plus`, `birkGammaD_sub_plus`, `birkGammaD_inverse_plus` | PASS | W⁺ lifts and compatible inverses proved; constants 10/9, 3, 10, 2, 20 retained. |
| flow (iv) | `birkGamma_rho` | PASS | Correct conjugate-linear reality and real time. |
| flow (v) | `birkGammaD_var` | PASS | T=ι∘S and symmetry put derivative in required order. |
| flow (vi) | `birkGamma_neg_birkGamma`, `birkGamma_injOn`, `birkGamma_image_subset`, `birkGamma_image_superset` | PASS | ρ₁²=1/(160 C_F); inverse valid on larger time interval |t|<2. |
| symplectic | `birkT_omega_symm`, `birkGammaD_symplectic`, `birk_gradient_transport` | PASS WITH NOTES | Correct pairing, chain rule, uniqueness; inverse premise supplied by proved producer (probe below). |

Here PASS for a clause is scoped to the named, constructed coefficients/flow; it is not closure of the four
whole blueprint nodes. `leibniz` and `flow` as compound nodes FAIL because of the findings above.

The concrete space is the existing weighted-coordinate `BirkSpace = lp ... 2`.
W⁺ is represented by a separate point/operator at weight p+1 with the **nonidentity** embedding
`birkEmbed a (p+1) p`. The smoothing conclusions explicitly factor through this embedding;
they do not merely put the W norm on an alleged W⁺ value. `birkS`, `birkCF`, the pairing and reality
supplier are from the already landed FForm/Space modules; `birkT` composes S with the embedding.

`40*C_F*‖w‖² < 1` is exactly `‖w‖ < (40 C_F)^(-1/2)` since `birkCF_pos` is proved.
`160*C_F*‖w‖² < 1` is exactly the ρ₁ domain.
The numeric `hq : 2*|t|*C_F*‖w‖² ≤ 1/10` on bound theorems is supplied by `birk_q_le`
on the source domain, rather than an additional analytic assumption. The image lemmas allow any
ρ with `160 C_F ρ² ≤ 1`; setting ρ=ρ₁ gives the exact stated balls.

## Premise audit

The following table expands the source-facing logical inputs rather than treating abstract proof premises
as standing assumptions. Data binders are listed individually; there is no hidden project-owned assumption bundle.

| Binder | Bin | Source/role |
|---|---|---|
| `m : ℝ` | TYPING | Fixed mass parameter. |
| `hm : 0 < m` | STANDING | W3 standing convention, lines 22–26. |
| `a : ℝ` | TYPING | Weight parameter. |
| `ha : 0 ≤ a` | STANDING | W3 line 24. |
| `p : ℝ` | TYPING | Weight exponent. |
| `hp : 1/2 ≤ p` | STANDING | W3 line 24. |
| `t : ℝ` | TYPING | Real flow time. |
| `w : BirkSpace` | TYPING | Weighted phase-space point. |
| `ht : |t| < 2` | SOURCE | flow/symplectic time window; inverse version is stronger. |
| `hw : 40*C_F*‖w‖² < 1` | SOURCE | Exact Bρ₀ membership. |
| inverse `hw : 160*C_F*‖w‖² < 1` | SOURCE | Exact Bρ₁ membership. |
| `v : BirkSpace` | TYPING | Variational test vector. |
| `ξ : BirkSpace` | TYPING | Symplectic test vector. |
| `η : BirkSpace` | TYPING | Symplectic test vector. |
| `ρ : ℝ` | TYPING | Ball radius. |
| `hρ : 160*C_F*ρ² ≤ 1` | SOURCE | Radius-generalized image helper; exact ρ₁ satisfies equality. |
| image `hw : ‖w‖ < ρ` | SOURCE | Ball membership. |
| `y : BirkSpace` | TYPING | Target image point. |
| `hy : ‖y‖ < 9/10*ρ` | SOURCE | Inner-ball membership. |
| `P : BirkSpace → ℂ` | TYPING | Hamiltonian being pulled back. |
| `dP : BirkSpace →L[ℂ] ℂ` | TYPING | Chosen derivative data. |
| `hP : HasFDerivAt P dP (Γ_t w)` | SOURCE | Pointwise weakening of differentiability-near premise. |
| `X : BirkSpace` | TYPING | Hamiltonian vector at image point. |
| `hX : ∀ u, dP u = Ω X u` | SOURCE | Meaning of Hamiltonian field; no gradient existence smuggled in. |
| `hq` in numeric helpers | EXCESS if promoted as independent source premise | Discharged by `birk_q_le`; internal numeric helper only. |
| `B : BirkSpace →L[ℂ] BirkSpace` | TYPING | Named inverse witness for conditional transport helper. |
| `hAB : DΓ*B=1` | EXCESS in standalone source result | Proved by `birkGammaD_invertible`, consumed in probe; retain helper status. |

Table counts (distinct binder roles, not a sum over repeated theorem signatures): SOURCE 8,
STANDING 3, TYPING 14, RULED 0, EXCESS 2 before discharge. The unconditional source conclusions
have no remaining EXCESS input in the checked gradient composition or numeric-bound specialization.

The abstract helpers take Banach-space typing, a continuous trilinear map, a norm bound, symmetry,
real involution compatibility, and (for symplecticity) a continuous skew form and `hΩT`.
These are explicitly **conditional helpers**, not independently closed W3 statements. `LieApp` supplies
`norm_birkT_le`, `birkT_perm`, `birkT_rho`, `birkT_omega_symm`, and positivity from the concrete FForm.
The abstract uniqueness lemma `lie_gradient_transport` takes `hY` as a candidate characterization;
it proves uniqueness of that candidate, not existence of a field from `hY`. The concrete transport
export also proves the actual pairing and chain rule, so its use is not circular.
For smoothing of the transported field, the equality `ι.comp BF = B.comp ι` in
`birkGammaD_inverse_plus` supplies the W⁺ lift. The inverse B agrees with any inverse selected in
transport, by two-sided inverse uniqueness. No new estimate or symplecticity premise is left at that consumer.

## Definition classification

There are 25 new definitions, no new structures or abbrevs. No classical choice is used to define
source objects. `tsum` totality is separated from the local source domain: outside a convergence domain,
no value or flow property is certified. This is not a globally defined source flow.

| Definition | Classification and whole-carrier behavior | Verdict |
| `lieSeries` (LieAnalytic:29) | Literal odd-degree series packaging; zero even degrees are source-required. Coefficient identity subject to F1. | FAIL source identification (F1) |
| `lieMultiF` (LieAnalyticPlus:33) | Constructed F-valued Cauchy block coefficient; full source identification subject to F1. | FAIL source identification (F1) |
| `lieSeriesF` (LieAnalyticPlus:88) | Literal positive odd-degree tail series; zeros in absent degrees are intentional. | PASS (local for tsum) |
| `liePsiSum` (LieAnalyticPlus:125) | Totalized tsum of F-valued tail; summability and embedding equality proved on hq domain. | PASS (local for tsum) |
| `birkT` (LieApp:45) | Literal ι∘S on entire triple carrier; symmetry, reality and pairing supplied. | PASS (local for tsum) |
| `birkGamma` (LieBirk:34) | Alias of totalized lieGamma for concrete T; only local source flow is claimed. | PASS (local for tsum) |
| `birkGammaD` (LieBirk:37) | Alias of totalized lieGammaD; derivative identification proved on source domain. | PASS (local for tsum) |
| `lieDer` (LieDeriv:35) | Finite recursive derivative of lieSeq; hasFDerivAt_lieSeq proves all-input characterization. | PASS (local for tsum) |
| `lieGamma` (LieFlow1:33) | Literal totalized tsum; absolute convergence on hq, no off-domain value used. | PASS (local for tsum) |
| `lieGammaD` (LieFlow1:36) | Literal totalized operator tsum; absolute convergence and derivative identification on domain. | PASS (local for tsum) |
| `powD` (LieFlow2:33) | Literal derivative of first-coordinate power; k=0 factor removes truncated exponent artifact. | PASS (local for tsum) |
| `lieTermD` (LieFlow2:38) | Literal product/chain-rule derivative, globally characterized by hasFDerivAt_lieTerm. | PASS (local for tsum) |
| `lieTupleEquiv` (LieFlow4:30) | Finite tuple/product reindexing equivalence, inverse laws proved. | PASS (local for tsum) |
| `tupleBump` (LieLeibniz:66) | Literal update of the zeroth tuple coordinate; injectivity and reindexing checked. | PASS (local for tsum) |
| `lieBlockEquiv` (LieMulti:33) | Dependent finite block indexing equivalence, equality proof is typing data. | PASS (local for tsum) |
| `lieBlock` (LieMulti:38) | Literal continuous block composition on all well-typed inputs. | PASS (local for tsum) |
| `lieBlockT` (LieMulti:83) | Internal arity-totalized composition, zero on wrong arity; every recursive use supplies sum_blocks. | PASS (local for tsum) |
| `lieMulti` (LieMulti:98) | Alternative recursive multilinear coefficient; diagonal and bound proved, full source recurrence missing (F1). | FAIL source identification (F1) |
| `birkLieM` (LieNumeric:32) | Finite recursive scalar majorant, denominator k+1 is always nonzero. | PASS (local for tsum) |
| `birkLieY` (LieNumeric:74) | Literal formal power series with coefficients birkLieM; formal identities proved. | PASS (local for tsum) |
| `lieT` (LiePlus:33) | Literal composition ι∘S. | PASS (local for tsum) |
| `liePsi` (LiePlus:38) | Finite F-valued tail lift; index zero is omitted source tail, never claimed as lift of φ₀. | PASS (local for tsum) |
| `lieXi` (LiePlus:135) | Finite F-valued derivative-tail lift; index zero intentionally zero; comp_lieXi is for k+1. | PASS (local for tsum) |
| `lieSeq` (LieSeq:35) | Finite Cauchy recursion on all w,k; exact diagonal Lie recurrence independently proved. | PASS (local for tsum) |
| `bilinReal` (LieSympl:25) | Scalar restriction of the complex bilinear form, evaluation equality rfl. | PASS (local for tsum) |

For `lieMulti` as the literal source Φ: BODY_MATCH: FAIL (F1 missing equivalence);
PUBLIC_CARRIER: OK (finite multilinear inputs); WELL_DEFINEDNESS: N/A_LITERAL;
CHARACTERIZATION: FAIL (source slot recurrence missing); CHOICE_INDEPENDENCE: N/A;
DEFINITION_VERDICT: FAIL for promotion to the source definition.
The tail lifts and zero wrong-arity branch are auxiliary constructions, not source-defined global maps.
For each tsum, BODY_MATCH is OK as a formula; PUBLIC_CARRIER is broader than the source's local carrier.
Convergence/characterization are OK only under the displayed guards. No theorem depends on divergent-tsum
fallback values; no off-domain semantic promotion is accepted by this audit.

## Verification

D53 governs all invocations in this audit. The following prefix enclosed each entire command,
including Lean children of the prescribed lint/gate scripts:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1
```

Commands were serialized (lint completed before probe; probe before targeted build). No cache fetch,
clean build, application build, heartbeat override or replay was run.

1. Prescribed lint only:
   `/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpfa` (under prefix).
   Exit **0**, output:

   ```text
   check_lean_modules: PASS (3608 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
   ```

2. Axiom and composition probe:
   `lake env lean .lake/abi-scratch/W3FlowAudit1.lean` (under prefix).
   The generated scratch file imports all 25 modules and prints axioms of **all 137** new public theorems.
   Each output is exactly `[propext, Classical.choice, Quot.sound]`. Final exit **0**, no warnings/errors.
   An initial probe run exited 1 because the auditor supplied a nonexistent named `ha` argument to
   `birk_q_le` (the numeric lemma does not depend on a). Removing that argument fixed the probe;
   this was an audit-probe error, not a package defect.
   The probe also constructs B with `birkGammaD_invertible` using `birk_q_le`, then applies
   `birk_gradient_transport`; the source premise set does not assume invertibility.
   Probe removed after recording results. Full axiom result coverage is enumerated below.

3. Targeted build (under prefix):
   `/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wpfa KAM.Wave.Birkhoff.LieBirkAnalytic`.
   Exit **0**. Output begins `[inp-gate] slot 2 acquired 21:56:27 for KAM.Wave.Birkhoff.LieBirkAnalytic`
   and ends `Build completed successfully (3384 jobs).` This target transitively imports all 25 modules.
   Lake replayed cached compiler warnings (unused tactics/simp arguments/section variables, and deprecated
   tactic syntax); there were no build errors. These are style notes, not ignored source-lint failures.
   Lake's “Replayed” messages here are cached build diagnostics, not a leanchecker kernel replay.

4. Kernel replay and short-name checks: **launcher-run, not independently rerun**.
   The user's instruction states they were run, and authorizes skipping replay. The launcher's output and
   exit code are not visible in this session; no exact exit code is fabricated or inferred from the handoff.
   Independent axiom checking above supplements, but does not substitute for, that replay evidence.

5. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty.
   `git diff --check inp...HEAD`: exit 0, no output.
   All new modules have module headers, public imports, module documentation and exposed public definitions.
   Largest file: `LieAnalyticPlus.lean`, **245 lines** (well below 1500).
   `rg -n 'set_option|\bsorry\b|\badmit\b|\baxiom\b|\bunsafe\b|\bopaque\b' KAM/Wave/Birkhoff/Lie*.lean`:
   exit 1, no matches. Lint independently checked forbidden escapes/import boundaries and line lengths.

## Public theorem inventory

One row per new public theorem. PASS here means the stated helper/conclusion passes within its explicit
scope; it does not upgrade it to a missing source statement. Every row's axiom set was checked as above.
All names have prefix `KAM.Wave.`; file names below are relative to `KAM/Wave/Birkhoff/`.

| Node/role | Declaration | Location | Verdict / scope |
|---|---|---|---|
| flow | `lieSeries_const` | LieAnalytic.lean:35 | PASS, conditional helper or literal identity |
| flow | `norm_lieSeries_le` | LieAnalytic.lean:43 | PASS, conditional helper or literal identity |
| flow | `lieGamma_hasFPowerSeriesOnBall` | LieAnalytic.lean:59 | PASS constructed coefficients; source identification pending F1 |
| flow | `analyticAt_lieGamma` | LieAnalytic.lean:114 | PASS, conditional helper or literal identity |
| flow | `lieMultiF_const` | LieAnalyticPlus.lean:37 | PASS constructed coefficients; source identification pending F1 |
| flow | `norm_lieMultiF_le` | LieAnalyticPlus.lean:53 | PASS constructed coefficients; source identification pending F1 |
| flow | `lieSeriesF_const` | LieAnalyticPlus.lean:94 | PASS, conditional helper or literal identity |
| flow | `norm_lieSeriesF_le` | LieAnalyticPlus.lean:105 | PASS, conditional helper or literal identity |
| flow | `summable_liePsi` | LieAnalyticPlus.lean:128 | PASS, conditional helper or literal identity |
| flow | `liePsiSum_hasFPowerSeriesOnBall` | LieAnalyticPlus.lean:142 | PASS, conditional helper or literal identity |
| flow | `exists_lie_rho` | LieAnalyticPlus.lean:196 | PASS, conditional helper or literal identity |
| flow | `map_liePsiSum` | LieAnalyticPlus.lean:212 | PASS, conditional helper or literal identity |
| flow | `analyticAt_liePsiSum` | LieAnalyticPlus.lean:236 | PASS, conditional helper or literal identity |
| concrete suppliers | `waveCubicConst_pos` | LieApp.lean:29 | PASS, conditional helper or literal identity |
| concrete suppliers | `birkCF_pos` | LieApp.lean:40 | PASS, conditional helper or literal identity |
| concrete suppliers | `birkT_apply` | LieApp.lean:48 | PASS, conditional helper or literal identity |
| concrete suppliers | `norm_birkT_le` | LieApp.lean:51 | PASS, conditional helper or literal identity |
| concrete suppliers | `birkT_perm` | LieApp.lean:60 | PASS, conditional helper or literal identity |
| concrete suppliers | `birkT_rho` | LieApp.lean:64 | PASS, conditional helper or literal identity |
| concrete suppliers | `birkT_omega_symm` | LieApp.lean:68 | PASS, conditional helper or literal identity |
| flow | `birkGamma_flow` | LieBirk.lean:47 | PASS stated concrete conclusion |
| flow | `birkGamma_transport` | LieBirk.lean:56 | PASS stated concrete conclusion |
| flow | `birkGamma_hasFDerivAt` | LieBirk.lean:64 | PASS stated concrete conclusion |
| flow | `birkGammaD_var` | LieBirk.lean:73 | PASS stated concrete conclusion |
| flow | `norm_birkGamma_le` | LieBirk.lean:87 | PASS stated concrete conclusion |
| flow | `norm_birkGamma_sub_le` | LieBirk.lean:92 | PASS stated concrete conclusion |
| flow | `norm_birkGammaD_sub_le` | LieBirk.lean:97 | PASS stated concrete conclusion |
| flow | `birkGammaD_invertible` | LieBirk.lean:105 | PASS stated concrete conclusion |
| flow | `birkGamma_rho` | LieBirk.lean:114 | PASS stated concrete conclusion |
| flow | `birkGamma_neg_birkGamma` | LieBirk.lean:121 | PASS stated concrete conclusion |
| symplectic | `birkGammaD_symplectic` | LieBirk.lean:129 | PASS stated concrete conclusion |
| flow | `norm_birkT_le_cf` | LieBirkAnalytic.lean:29 | PASS, conditional helper or literal identity |
| flow | `birkGamma_analyticOnNhd` | LieBirkAnalytic.lean:34 | PASS stated concrete conclusion |
| flow | `birkGamma_sub_analytic` | LieBirkAnalytic.lean:42 | PASS stated concrete conclusion |
| flow | `lieT_birk` | LieBirkPlus.lean:32 | PASS, conditional helper or literal identity |
| flow | `birk_q_le` | LieBirkPlus.lean:39 | PASS, conditional helper or literal identity |
| flow | `birkGamma_sub_plus` | LieBirkPlus.lean:48 | PASS stated concrete conclusion |
| flow | `birkGammaD_sub_plus` | LieBirkPlus.lean:56 | PASS stated concrete conclusion |
| flow | `birkGammaD_inverse_plus` | LieBirkPlus.lean:68 | PASS stated concrete conclusion |
| flow | `birkGamma_image_subset` | LieBirkPlus.lean:92 | PASS stated concrete conclusion |
| flow | `birkGamma_injOn` | LieBirkPlus.lean:104 | PASS stated concrete conclusion |
| flow | `birkGamma_image_superset` | LieBirkPlus.lean:116 | PASS stated concrete conclusion |
| symplectic | `birk_gradient_transport` | LieBirkPlus.lean:146 | PASS conditional helper; inverse discharged in probe |
| flow | `hasSum_tri_cauchy` | LieCauchy.lean:26 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `lieVec_eq` | LieDeriv.lean:30 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `lieDer_succ` | LieDeriv.lean:45 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `lieDer_zero` | LieDeriv.lean:55 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `hasFDerivAt_lieSeq` | LieDeriv.lean:58 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `norm_toCLM_le` | LieDeriv.lean:87 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `opNorm_toCLM_le` | LieDeriv.lean:104 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `norm_lieDer_le` | LieDeriv.lean:118 | PASS, conditional helper or literal identity |
| flow | `norm_lieTerm_le` | LieFlow1.lean:43 | PASS, conditional helper or literal identity |
| flow | `norm_lieDTerm_le` | LieFlow1.lean:55 | PASS, conditional helper or literal identity |
| flow | `geom_sums` | LieFlow1.lean:66 | PASS, conditional helper or literal identity |
| flow | `summable_norm_lieTerm` | LieFlow1.lean:105 | PASS, conditional helper or literal identity |
| flow | `summable_norm_lieDTerm` | LieFlow1.lean:112 | PASS, conditional helper or literal identity |
| flow | `summable_lieTerm` | LieFlow1.lean:126 | PASS, conditional helper or literal identity |
| flow | `summable_lieDTerm` | LieFlow1.lean:130 | PASS, conditional helper or literal identity |
| flow | `norm_lieGamma_le` | LieFlow1.lean:135 | PASS, conditional helper or literal identity |
| flow | `norm_lieGamma_sub_le` | LieFlow1.lean:148 | PASS, conditional helper or literal identity |
| flow | `norm_lieGammaD_sub_le` | LieFlow1.lean:176 | PASS, conditional helper or literal identity |
| flow | `hasFDerivAt_pow_fst` | LieFlow2.lean:42 | PASS, conditional helper or literal identity |
| flow | `hasFDerivAt_lieTerm` | LieFlow2.lean:46 | PASS, conditional helper or literal identity |
| flow | `norm_lieTermD_le` | LieFlow2.lean:59 | PASS, conditional helper or literal identity |
| flow | `hasFDerivAt_lieGamma` | LieFlow2.lean:104 | PASS derivative; FAIL as joint C¹ (F3) |
| flow | `q_le_of_dom` | LieFlow3.lean:29 | PASS, conditional helper or literal identity |
| flow | `shifted_term_eq` | LieFlow3.lean:34 | PASS, conditional helper or literal identity |
| flow | `hasDerivAt_lieGamma_t` | LieFlow3.lean:47 | PASS, conditional helper or literal identity |
| flow | `hasFDerivAt_lieGamma_w` | LieFlow3.lean:64 | PASS, conditional helper or literal identity |
| flow | `hasDerivAt_lieGamma_transport` | LieFlow3.lean:87 | PASS, conditional helper or literal identity |
| flow | `lie_tri_smul` | LieFlow4.lean:36 | PASS, conditional helper or literal identity |
| flow | `lie_clm_apply2` | LieFlow4.lean:48 | PASS, conditional helper or literal identity |
| flow | `lie_clm_apply1` | LieFlow4.lean:52 | PASS, conditional helper or literal identity |
| flow | `lie_clm_apply0` | LieFlow4.lean:56 | PASS, conditional helper or literal identity |
| flow | `hasSum_lieCauchy` | LieFlow4.lean:63 | PASS, conditional helper or literal identity |
| flow | `hasDerivAt_lieGamma_flow` | LieFlow4.lean:124 | PASS, conditional helper or literal identity |
| flow | `lieGamma_zero` | LieInv.lean:27 | PASS, conditional helper or literal identity |
| flow | `hasDerivAt_lieGamma_inv` | LieInv.lean:35 | PASS, conditional helper or literal identity |
| flow | `lieGamma_neg_lieGamma` | LieInv.lean:79 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `sum_tuple_perm` | LieLeibniz.lean:27 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `sum_tuple_weight` | LieLeibniz.lean:39 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `tupleBump_injective` | LieLeibniz.lean:68 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `sum_tuple_shift` | LieLeibniz.lean:74 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `toCLM_swap` | LieLeibniz.lean:107 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `sum_toCLM_eq` | LieLeibniz.lean:126 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `toCLM_zero_apply` | LieLeibniz.lean:138 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `lieDer_succ_sym` | LieLeibniz.lean:146 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `lieDer_apply_field` | LieLeibniz.lean:170 | PASS, conditional helper or literal identity |
| symplectic / inverse | `lieGammaD_invertible` | LieMain.lean:30 | PASS, conditional helper or literal identity |
| symplectic / inverse | `lie_gradient_transport` | LieMain.lean:44 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `lieBlock_apply` | LieMulti.lean:50 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `lieBlock_const` | LieMulti.lean:56 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `norm_lieBlock_le` | LieMulti.lean:61 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `sum_blocks` | LieMulti.lean:88 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `lieMulti_succ` | LieMulti.lean:108 | PASS constructed coefficients; source identification pending F1 |
| lie-coeff / leibniz | `lieMulti_const` | LieMulti.lean:117 | PASS constructed coefficients; source identification pending F1 |
| lie-coeff / leibniz | `norm_lieMulti_le` | LieMulti.lean:134 | PASS constructed coefficients; source identification pending F1 |
| flow | `neumann_inv` | LieNeumann.lean:23 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `birkLieM_succ` | LieNumeric.lean:41 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `sum_nested_antidiag` | LieNumeric.lean:51 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `birkLieY_deriv` | LieNumeric.lean:76 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `birkLieM_succ` | LieNumeric.lean:85 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `birkLieM_nonneg` | LieNumeric.lean:95 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `two_eq_C` | LieNumeric.lean:107 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `ode_sq_unique` | LieNumeric.lean:110 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `birkLieY_sq` | LieNumeric.lean:134 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `birkLieM_le_pow` | LieNumeric.lean:150 | PASS, conditional helper or literal identity |
| flow | `lieT_apply` | LiePlus.lean:35 | PASS, conditional helper or literal identity |
| flow | `map_liePsi` | LiePlus.lean:43 | PASS, conditional helper or literal identity |
| flow | `lieT_bound` | LiePlus.lean:50 | PASS, conditional helper or literal identity |
| flow | `norm_liePsi_le` | LiePlus.lean:57 | PASS, conditional helper or literal identity |
| flow | `exists_lieGamma_sub` | LiePlus.lean:85 | PASS, conditional helper or literal identity |
| flow | `lieF_opNorm_toCLM_le` | LiePlus.lean:112 | PASS, conditional helper or literal identity |
| flow | `comp_lieXi` | LiePlus.lean:141 | PASS, conditional helper or literal identity |
| flow | `norm_lieXi_le` | LiePlus.lean:149 | PASS, conditional helper or literal identity |
| flow | `exists_lieGammaD_sub` | LiePlus.lean:186 | PASS, conditional helper or literal identity |
| flow | `lie_plus_inverse` | LiePlusInv.lean:31 | PASS, conditional helper or literal identity |
| flow | `lie_geom_bound` | LiePlusNum.lean:32 | PASS, conditional helper or literal identity |
| flow | `lie_geom_bound_D` | LiePlusNum.lean:41 | PASS, conditional helper or literal identity |
| flow | `lie_tail_one` | LiePlusNum.lean:53 | PASS, conditional helper or literal identity |
| flow | `lie_tail_two` | LiePlusNum.lean:74 | PASS, conditional helper or literal identity |
| flow | `norm_one_div_succ` | LiePlusNum.lean:105 | PASS, conditional helper or literal identity |
| flow | `lie_step_A` | LiePlusNum.lean:111 | PASS, conditional helper or literal identity |
| flow | `lie_step_B` | LiePlusNum.lean:123 | PASS, conditional helper or literal identity |
| flow | `lie_perx_D` | LiePlusNum.lean:139 | PASS, conditional helper or literal identity |
| flow | `lieSeq_rho` | LieReal.lean:30 | PASS diagonal; insufficient for multilinear reality (F2) |
| flow | `lieGamma_rho` | LieReal.lean:60 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `lieSeq_succ` | LieSeq.lean:46 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `lieSeq_zero` | LieSeq.lean:55 | PASS, conditional helper or literal identity |
| lie-coeff / leibniz | `norm_lieSeq_le` | LieSeq.lean:58 | PASS, conditional helper or literal identity |
| symplectic / inverse | `bilinReal_apply` | LieSympl.lean:28 | PASS, conditional helper or literal identity |
| symplectic / inverse | `hasDerivAt_omega_pair` | LieSympl.lean:30 | PASS, conditional helper or literal identity |
| symplectic / inverse | `lieGammaD_zero` | LieSympl.lean:40 | PASS, conditional helper or literal identity |
| symplectic / inverse | `lie_symplectic` | LieSympl.lean:50 | PASS, conditional helper or literal identity |
| flow | `hasDerivAt_powSeries` | LieVar.lean:24 | PASS, conditional helper or literal identity |
| flow | `summable_lieDer_deriv` | LieVar.lean:50 | PASS, conditional helper or literal identity |
| flow | `hasDerivAt_lieGammaD_var` | LieVar.lean:96 | PASS, conditional helper or literal identity |

## Closeout, uncertainties, errata and deviations

- **Do not mark all four blueprint nodes closed from this package.** Close F1 by proving the full
  multilinear source recurrence/identification; close F2 with the all-input reality theorem; close F3
  with joint C¹. Keep the current flow, smoothing, inverse and symplectic receipts at their proved scope.
- No suspected false formula in the pinned blueprint or external source was established.
  F1–F3 are Lean coverage gaps relative to quoted source clauses; they are not proposed source errata.
- Prover deviation: Cauchy block coefficients in place of the literal slot construction, acknowledged in
  the handoff but not accompanied by an all-input source-identification theorem.
- Audit limitation: launcher replay/name-check logs are unavailable; no fresh replay exit code is claimed.
  Earlier W3 groups/FForm are baseline dependencies, not re-audited as an independent package here.
- Audit artifacts: only this report is a repository edit. Scratch Lean probe is removed; logs were kept
  outside the repository at `/tmp/W3FlowAudit1-axioms.log` and `/tmp/W3FlowAudit1-build.log`.
