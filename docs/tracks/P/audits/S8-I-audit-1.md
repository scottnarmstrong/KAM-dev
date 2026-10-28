# S8-I independent package audit 1

Overall verdict: **PASS WITH NOTES** for S8-I at `9dd80da67c4c33a7a56238e4d854cd3437376238` (2026-10-28). `identities`, `radialPhi` and `radialH` match the approved design exactly. The proof has no added premise or unpaid differentiation step. The substantive note is a source-domain coverage boundary: the blueprint includes zero, whereas the approved design and this export cover strictly positive axis ratios. This is an infrastructure-package verdict, not a frozen-anchor seal or track/root closure.

## Scope, authority and frozen inputs

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package audit brief at `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the S8-I handoff and its AUDIT FOCUS, revision-2 P810 design and both design audits, original signatures, Part 8 statements/proofs and relevant track-P statement conventions/proof-route repairs. Applied `lean-statement-audit` and `manuscript-audit` as a focused tier-2 audit: signature/body comparison, full proof reading, separate adversarial checks, and mechanical verification. Permission envelope comes from the user/brief: only this report may change; probes/logs are temporary under `.lake/abi-scratch/`; no state-changing git. The user's exact worktree report path overrides the generic brief's main-worktree destination. No subagents were used.

Audited only `KAM/Planetary/SecularForm/LaplaceIdentities.lean` (308 lines), as the handoff requests. All locators below refer to this frozen-v1 snapshot unless another file is named.

| Input | Revision or SHA-256 |
|---|---|
| HEAD | `9dd80da67c4c33a7a56238e4d854cd3437376238` |
| `inp` at comparison | `05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2` |
| `inp-s8l` at comparison | `63d355613cb892d2ad76be5f33af4184982f39af` |
| `LaplaceIdentities.lean` | `6a5a566fb300ef75ff16208d0c4fbfa4f78f88b90c0eca02357750ae8c2c70b8` |
| `docs/tracks/P/design/P810-LEAN-DESIGN.md` | `f555e21a468123ce906f6818359cb8faaffc5d0435ea0f70c65967cec38722c4` |
| `blueprint-P/parts/p8-secular-form.tex` | `413806b9fcc86156e0b241da85668677b44bf142897c7039940504a50ae1febc` |
| `/root/code/KAM-inp/.drafts/design/P810Signatures.lean` | `492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d` |
| `docs/tracks/P/design/DESIGN-P810-design-audit-1.md` | `60d5ecd0fd3bf6f655b980f1ca4a9884a5f6506ca022cb741477ba75b679e15a` |
| `docs/tracks/P/design/DESIGN-P810-design-audit-2.md` | `9b23c970815181dd0e7ba42c7b263572dae925773b6aa3c7a166e7dec8727afa` |
| `docs/tracks/P/audits/S8-I-handoff.md` (pre-existing untracked input) | `a871eedc36ef5e47b7fa5002dc91124823a84811d72079f3d2991de8491cbe0f` |

The signature file is absent from this worktree's `.drafts/design`; its authoritative main-worktree copy was read, never imported as a proof dependency. Design audit 1 passed these three declarations; revision-2 audit preserves them unchanged. Independent extraction confirms exact text equality for the theorem signature and both complete definition bodies against both original signatures and design Appendix A (design :708–713, :789–791; signatures :151–156, :232–234). Package ownership is design row :427, S8-I, input S8-L.

Both requested comparisons were run: `git diff inp...HEAD` and `git diff inp-s8l...HEAD`. The first contains the four inherited S8-L modules and its two audit/handoff documents, plus this single new module (seven files, 1312 insertions). The second also contains unrelated inherited branch divergence, outside the AUDIT FOCUS. Restricting either comparison to `LaplaceIdentities.lean` gives byte-identical 314-line diffs. `git diff --stat 6b3bf59..HEAD` isolates the two S8-I implementation commits and shows only this file, 308 insertions. No inherited S8-L proof is re-certified by this report.

There is no S8-I provider, manifest entry or frozen theorem to seal. Provider=frozen-type and copied frozen seal-body probes are **N/A**. An exact approved-design-type application and literal-definition `rfl` probes were compiled instead. Frozen physical headlines remain outside this audit.

## Declaration ledger

All names have prefix `KAM.Planetary.SecularForm`. All 22 declarations were read; every theorem and definition was axiom-checked. Generic helper premises below belong to their separately named conditional lemmas and are discharged in `identities`; none is added to its public source contract.

| Node / role | Declaration and line | Verdict | Evidence |
|---|---|---|---|
| id-1/id-2 analytic infrastructure | `hasDerivAt_tsum_pow` :32 | PASS | Explicit polynomial coefficient bound and upper/lower exponent growth imply a locally summable derivative majorant; no summability assumption is hidden. |
| id-1/id-2 coefficient | `halfCoef` :102 | PASS | Literal product of the two half-integer binomial coefficients. |
| coefficient recurrence | `pcoef_succ` :104 | PASS | Pochhammer/factorial recurrence, all real s and natural q. |
| coefficient bound | `pcoef_half_le_one` :110 | PASS | Induction uses nonnegativity and `(q+1/2)/(q+1) ≤ 1`. |
| coefficient bound | `halfCoef_abs_le` :122 | PASS | Product bounded by one for all k,q. |
| series conversion | `laplaceTerm_half` :130 | PASS | Literal coefficient algebra, all real alpha. |
| local series identification | `laplace_def_half_eventually` :135 | PASS | S8-L integral/series equality on an open neighbourhood inside (0,1). |
| first differentiation | `half_deriv1` :143 | PASS | k≤2 supplies the exponent bound; eventual equality transfers the actual derivative. |
| second differentiation | `half_deriv2` :153 | PASS | Coefficients grow at most linearly; derivative equality holds on a neighbourhood before differentiating again. |
| id-1/id-2 recurrence | `poch_succ'` :184 | PASS | First-factor extraction in the literal finite product. |
| id-1/id-2 recurrence | `poch_three_halves` :192 | PASS | Exact `(3/2)_q = 2*(1/2)_(q+1)`. |
| monomial derivative | `pow_aux1` :197 | PASS | Includes exponent zero by an explicit case split. |
| monomial derivative | `pow_aux2` :202 | PASS | Includes exponents zero and one; natural subtraction causes no endpoint error. |
| shifted HasSum | `hasSum_shift_unique` :209 | PASS | Generic conditional reindexing lemma; zero initial term and successor equality are both proved at uses. |
| recurrence alias | `poch_half_two` :215 | PASS | Direct application of upstream `poch_succ`. |
| id-1 monomial algebra | `term_comb1` :218 | PASS | Linear combination of the two proved monomial identities. |
| id-2 monomial algebra | `term_comb2` :224 | PASS | Same algebra with the half-factor and subtraction retained. |
| id-1 coefficient equality | `coef1` :230 | PASS | Pochhammer recurrences and nonzero factorial denominators; no estimate is assumed. |
| id-2 coefficient equality | `coef2` :242 | PASS | Correct shifted q+2 factorial and factor 1/2. |
| `bpP:p8:identities`, `stepP:p8:id-1`, `stepP:p8:id-2` | `identities` :254 | PASS WITH NOTES | Both approved identities, exactly two source domain guards; see N1 for the blueprint endpoint. |
| `stepP:p8:qf-scale`, quartic data | `radialPhi` :303 | PASS | Exact normalized radial integral, all real arguments as in the design. |
| `bpP:p8:quartic`(b) | `radialH` :305 | PASS | Exact `Phi(a*(1-epsilon),b)*(1-epsilon)`, including its Jacobian factor. |

## Main theorem binders and normalization

The complete expanded binder table for `identities` is:

| Binder | Classification | Authority |
|---|---|---|
| `{α : ℝ}` | TYPING | Design :708; blueprint :130 scalar ratio |
| `(hα : 0 < α)` | SOURCE (approved interior-domain specialization) | Design :708, original signatures :151; blueprint :130 includes this interior |
| `(hα1 : α < 1)` | SOURCE | Same locators |

Counts `(SOURCE, STANDING, TYPING, RULED, EXCESS) = (2,0,1,0,0)`. There are no instance binders, bundled assumptions, hidden Data records, free dimension variables or constant witnesses. Both conclusions are equalities in ℝ and remain a conjunction in the approved order. The first uses mode 0 and then mode 1; the second uses mode 1 and then mode 2, with s=1/2 and 3/2 exactly. Upstream `laplace_def` is the literal `(2*pi)^(-1)` cosine integral with integer mode; `poch` and `pcoef` have their literal product/factorial meanings. There is no period conversion or norm change.

On `0<α<1`, Lean's first identity is α times blueprint (I1), and the second is one half of blueprint (I2). Multiplication by α is reversible under the existing source positivity guard; scaling by 2 is unconditional. A compiled probe recovers both literal blueprint forms on this interval from `identities`, so this normalization does not weaken either interior conclusion.

Helper-input review: `hasDerivAt_tsum_pow` takes scalar/index data plus `hb` (polynomial coefficient bound), `he` (upper exponent growth), `hj` (lower exponent growth) and `hy` (interior-disc guard). These are its advertised generic analytic hypotheses, not a renamed source theorem. At :148–149 and :160–172 each bound is supplied by `halfCoef_abs_le`, elementary arithmetic and the explicit proved linear bound. `half_deriv1/2` require only their mode range and interval membership; `identities` instantiates them at k=0,1. `hasSum_shift_unique` takes `hf,hg,h0,hfg`; :279–300 produce both HasSum facts from the differentiated/source series and prove the two algebraic conditions. Every other algebraic helper has only real/natural typing data. No hard source step survives as a premise of `identities`.

## Definition classification

All three new definitions are **literal formulas**, not characterization-defined selections. No classical witness is chosen and there are no if/dite/default branches.

| Definition | Body and carrier assessment |
|---|---|
| `halfCoef : ℕ → ℕ → ℝ` | Exact auxiliary coefficient `pcoef (1/2) (q+k) * pcoef (1/2) q`, meaningful for every natural k,q; nonzero factorial denominators. |
| `radialPhi : ℝ → ℝ → ℝ` | Exact approved normalized interval integral with real exponent -1/2; no radius-ratio substitution, sign change or missing normalization. |
| `radialH : ℝ → ℝ → ℝ → ℝ` | Exact approved composition and multiplicative `(1-epsilon)` factor. |

For each: `BODY_MATCH: OK`; `PUBLIC_CARRIER: OK`; `WELL_DEFINEDNESS: N/A_LITERAL`; `CHARACTERIZATION: N/A_LITERAL`; `CHOICE_INDEPENDENCE: N/A`; `DEFINITION_VERDICT: PASS`.

`radialPhi` retains the design's total real-power/interval-integral semantics on all real inputs. At singular or nonintegrable arguments it is not asserted to be the finite Newtonian average, analytic, or differentiable. This package proves no such theorem and uses neither radial definition in `identities`. Physical consumers must supply the separated positive-axis neighbourhoods required by the blueprint; this report does not certify those later regularity or quartic computations. Both definition equations were checked by `rfl` on their entire declared carriers.

## Proof and adversarial checks

The analytic argument :37–97 chooses `r=(|y|+1)/2`, proves `0<r<1`, and obtains the summable majorant

```text
u(q) = (2*C / r^(j+1)) * (q+1)^(m+1) * r^q.
```

The coefficient hypothesis itself forces C≥0. The exponent lower bound controls negative shifts by `r^(-(j+1))`; the upper bound supplies the factor `2*(q+1)`. At the basepoint 0, only finitely many powers can have exponent zero, so the series is summable there. These are precisely the open-set, preconnectedness, derivative-bound and basepoint-convergence premises of Mathlib `hasDerivAt_tsum_of_isPreconnected` (`Mathlib/Analysis/Calculus/SmoothSeries.lean`:89). They are proved, not assumed from formal tsum notation.

For the second derivative :174–180, the first derivative equals its series throughout a neighbourhood, not merely at a single point. Thus differentiating that equality is valid and `iteratedDeriv 2` is the actual iterated derivative. Finally each identity is a linear combination of convergent HasSum series. The q=0 term vanishes, a one-step shift aligns exponents, `coef1/coef2` supply the rational coefficient identities, and `HasSum.unique` closes both branches.

Separate refutation attempts checked: zero and unit exponents with natural subtraction; possibly negative C; factorial zero denominators; differentiating a pointwise equality; missing first-series convergence; incorrect q=0 or shifted indices; loss of an alpha or half-factor; hidden assumptions through imports. All were discharged by the cited proof steps and compiled interior-source-form probe. The endpoint mismatch survives as N1, a coverage note rather than a false identity. No other mathematical blocker was found. This is one independent auditor's separate refutation pass, not a claim of an additional reviewer.

Import closure inspection found 68 project modules, including 47 frozen definition modules. All 47 exact manifest path matches are `SEALED` definitions. No provider or frozen theorem module is transitively imported, so there is no `DRAFT_SORRY` import. Mathlib supplies general calculus/algebra; S8-L supplies the integral/series equality, positivity and Pochhammer recurrence; Basic is pre-existing carrier infrastructure. S8-L was already audited, and its unchanged proof bodies are outside the present focus.

## Notes, source defects and boundaries

**N1 — approved design covers the open interval only.** Blueprint `p8-secular-form.tex`:130 says “For α∈[0,1)” and :132 states the unmultiplied first identity. The design :708 and implementation :254 instead say `(hα : 0 < α)`. Cancellation recovers the blueprint formula only for α>0. Adversarial check: upstream `laplace_def_zero` supplies values at zero, but the public identity theorem cannot be applied there, and the differentiated half-series helpers also require `Ioo 0 1`. Thus this export does not certify the literal blueprint endpoint. The exact approved signature is respected; no package premise was added. Any full-blueprint closure claim needs a separate endpoint argument/export or an explicit scope disposition. Intended distinct positive-axis ratios lie in (0,1), so this does not obstruct those uses. No statement was repaired during audit.

No newly suspected pinned-paper defect was found. The existing Fej04r global-meromorphy allegation and CP11 quartic-coefficient erratum are inherited context, not re-audited or proved here. S8-I uses the series route and literal radial formula, not those printed assertions. No introduced mathematical deviation was found beyond the already designed scaling of the two identities and open-interval boundary recorded above. Downstream secular jets, spectra, torsion, physical headlines and seals are not audited.

## Verification evidence

All auditor-controlled Lean/Lake/checker invocations ran sequentially with `LEAN_NUM_THREADS=1` and `nice -n 5`. No clean/update/cache request, heartbeat/recursion/synthesis override, frozen edit, generated-root edit or package edit was performed.

1. Targeted compile gate:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s8i KAM.Planetary.SecularForm.LaplaceIdentities
   [inp-gate] slot 2 acquired 10:49:33 for KAM.Planetary.SecularForm.LaplaceIdentities
   Build completed successfully (9114 jobs).
   exit 0
   ```

   The output replayed inherited unused-variable warnings in Kepler/Energy (:106), Poincare/Chart (:212,:247) and Kepler/Mass (:147,:157,:500,:524). No S8-I diagnostic appeared. This was a targeted cached build, not a clean library rebuild.

2. Exact design-type, both literal definition equations, interior blueprint-form applications and exhaustive axiom probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S8IAudit1.lean
   exit 0
   ```

   The first example copies the original `identities` signature and uses exactly `identities hα hα1`; the next two check the full definition bodies by `rfl`; the fourth cancels α and scales by 2 to recover the blueprint formulas. No resource override was used. `#print axioms` output, with the common namespace omitted here, was exactly the same permitted list for each declaration:

   ```text
   hasDerivAt_tsum_pow        [propext, Classical.choice, Quot.sound]
   pcoef_succ                [propext, Classical.choice, Quot.sound]
   pcoef_half_le_one         [propext, Classical.choice, Quot.sound]
   halfCoef_abs_le           [propext, Classical.choice, Quot.sound]
   laplaceTerm_half          [propext, Classical.choice, Quot.sound]
   laplace_def_half_eventually [propext, Classical.choice, Quot.sound]
   half_deriv1               [propext, Classical.choice, Quot.sound]
   half_deriv2               [propext, Classical.choice, Quot.sound]
   poch_succ'                [propext, Classical.choice, Quot.sound]
   poch_three_halves         [propext, Classical.choice, Quot.sound]
   pow_aux1                  [propext, Classical.choice, Quot.sound]
   pow_aux2                  [propext, Classical.choice, Quot.sound]
   hasSum_shift_unique       [propext, Classical.choice, Quot.sound]
   poch_half_two             [propext, Classical.choice, Quot.sound]
   term_comb1                [propext, Classical.choice, Quot.sound]
   term_comb2                [propext, Classical.choice, Quot.sound]
   coef1                     [propext, Classical.choice, Quot.sound]
   coef2                     [propext, Classical.choice, Quot.sound]
   identities                [propext, Classical.choice, Quot.sound]
   halfCoef                  [propext, Classical.choice, Quot.sound]
   radialPhi                 [propext, Classical.choice, Quot.sound]
   radialH                   [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay, after the probe finished:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.LaplaceIdentities
   replaying KAM.Planetary.SecularForm.LaplaceIdentities
   exit 0
   ```

   One invocation, naming the only audited module; no checker error.
4. Repository lint, run after kernel replay:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (556 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The only failure is the stale generated root, explicitly allowed by the package brief. All module, frozen-source and elaborated-ABI checks pass. `KAM.lean` was left untouched as required. This permitted lint exception is a second package note; it is not an unreported clean-lint claim.
5. Static checks: 308 lines, maximum line width 97; copyright, `module`, public imports, module docstring and exposed public noncomputable section present. Forbidden-token/resource-option scan found no matches. `git diff --check inp...HEAD` exits 0, no output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty (`git diff --quiet` exit 0). Broad protected-path integrity therefore passes literally in this snapshot.

Final snapshot/cleanup check: HEAD and both compared refs retained the recorded revisions; source SHA-256 retained the frozen-v1 value. All four auditor-created scratch files (`S8IAudit1.lean`, `S8IAudit1-kernel.log`, `S8IAudit1-lint.log`, `S8IAudit1-diff.txt`) were deleted after recording their evidence. `git diff --check` and `git diff --check inp...HEAD` exit 0. Final `git status --short` contains only the pre-existing untracked S8-I handoff and this new report. No production or protected file was edited.

Closeout: all 22 declarations classified; all 19 public theorems and three definitions have permitted axiom closure; exact signature/definition probes, targeted build and kernel replay pass; lint has only its explicitly permitted generated-root exception. N1 remains a visible blueprint endpoint coverage boundary. No unresolved implementation blocker or newly alleged pinned-source erratum remains. No seal/root closure is claimed.
