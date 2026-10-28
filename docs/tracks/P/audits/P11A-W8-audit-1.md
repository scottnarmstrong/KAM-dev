# P11A-W8 independent package audit 1

Overall verdict: **PASS WITH NOTES** for the W8 infrastructure package. No frozen theorem is implemented or sealed by this package; provider/frozen-type equality and a frozen seal-body probe are **not applicable**. This verdict concerns only the three assigned modules, not P-FIXED or the later iteration/preparation consumers.

## Scope and authority

Audited HEAD `db1a1590b1cd8fa7d883f8b7f93a823ed92eed04` in `/root/code/KAM-inp-p11aw8`. Read AGENTS.md, PLAN.md, DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the local handoff/AUDIT FOCUS, track P statement, design and its R1–R3 audits, the R3 signatures, relevant blueprint statements and imported definition/dependency interfaces. The user's exact report destination overrides the generic brief's main-worktree destination.

`git diff inp...HEAD` and `git diff inp-p11aw7...HEAD` both contain exactly:

| File | Lines / delta |
|---|---:|
| `KAM/Planetary/WeakMeasure/Bridge.lean` | 72 / +72 |
| `KAM/Planetary/WeakMeasure/PowerLaw.lean` | 247 / +247 |
| `KAM/Planetary/WeakMeasure/ChartScaling.lean` | 257 / +257 |

Comparison refs at inspection: `inp=31f0bfbf70c07b1eefd006237f331c00e003a0e5`, `inp-p11aw7=a6a046414754694ff5c8469d6a8e145f5a7410b9`; merge base with inp `526146e4975bd0d49e583c25e7bf1086619f0a22`. No inherited W0–W7 module is re-audited here.

The signature file and design audits are outside this worktree, so they were read from `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean` and `/root/code/KAM-inp/docs/tracks/P/design/DESIGN-P11A-design-audit-{1,2,3}.md`. The handoff's `audits/` location for the design audits is stale; the actual directory is `design/`.

| Authority | SHA-256 |
|---|---|
| R3 signatures | `c31fda0b479f2dd0488b12e7f2daeda18f965eb316610df1c65f14012dfcb092` |
| Local design | `8619ea896c856347a9a5c5efac5080f0c830ea19245320b5f03a2b4267a300b9` |
| Local `blueprint-P/parts/p11a1-weak-measure.tex` | `66b5ce26db59b57dbf934938a7bae2fead6b6ff4c7c9d420d33b9582e272bab5` |

These match the R3 audit's pinned hashes. All nine assigned theorem headers and both new definition bodies match the delivered signatures after whitespace normalization. The scratch probe independently checks each complete expected theorem type, including implicit arguments, by assigning the corresponding `@KAM.Planetary` export to the literal signature-derived universally quantified type.

## Declaration ledger

Names below are in `KAM.Planetary`; line locators refer to the assigned files. PASS means the local declaration/interface passes, with package-level notes below.

| Node / responsibility | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| limit-bridge, per mode | `limit_bridge` (Bridge:26) | PASS | Exact doubled margin, lattice l1 / Pi max-norm tail, arbitrary real tau; no extra premise. |
| limit-bridge, frozen predicate | `limit_bridge_diophantine` (Bridge:59) | PASS | Mode-dependent maps and all nonzero modes retained; conclusion is the literal frozen `KAM.IsDiophantine`. |
| power-law constant | `p11CDio` (PowerLaw:26) | PASS | Exact prescribed sublevel, beta, dimension and lattice factors. |
| power-law threshold | `p11GammaStar` (PowerLaw:30) | PASS | Exact minimum and exponents; no dependence on the maps beyond the declared constants. |
| nonzero lattice length | `p11_modeSize_pos` (PowerLaw:38) | PASS | Elementary fact on all nonzero integer modes; zero-dimensional case cannot supply hk. |
| integer lattice lower bound | `p11_modeSize_ge_one` (PowerLaw:45) | PASS | Uses a nonzero integer coordinate; no hidden analytic premise. |
| pl-profile | `p11_pl_profile` (PowerLaw:54) | PASS | Correct l1-to-Euclidean comparison and exponent; its `0 ≤ tau+1` is derived from the main theorem's source assumptions. |
| pl-sum, lattice component | `p11_pl_sum` (PowerLaw:83) | PASS | Summability and exact `2*3^(m-1)*(1+1/s)` bound, with source exponent condition. Weighted profile comparison is completed in power_law. |
| constant sign | `p11_C_nonneg` (PowerLaw:116) | PASS | Positivity follows from source geometry and exponent gap, not an assumed estimate. |
| power-law / pl-conc | `power_law` (PowerLaw:135) | PASS | Exact R3 signature: compact good set, excluded measure and epsilon concentration, correct quantifier order and rho/mu exponent. |
| Euclidean homogeneity | `p11_euclid_smul` (ChartScaling:31) | PASS | All real scalars, absolute value retained; no ambient norm replacement. |
| affine derivative identity | `p11_iteratedFDeriv_affine` (ChartScaling:37) | PASS | Local open-domain regularity, all j≤k, including j=0; scalar factor lambda^j. |
| power upper envelope | `p11_pow_le_max` (ChartScaling:65) | PASS | Both positive-lambda regimes covered. |
| power lower envelope | `p11_min_le_pow` (ChartScaling:71) | PASS | Both positive-lambda regimes covered. |
| chart-scaling, tensor identities | `chart_scaling_jets` (ChartScaling:77) | PASS | Both diagonal and full tensor gauges with exact scaling, no polarization factor. |
| chart-scaling (b) | `chart_scaling_upper` (ChartScaling:111) | PASS | Full tensor orders 1..k, intended max factor and local carrier. |
| chart-scaling (c) | `chart_scaling_closeness` (ChartScaling:124) | PASS | Input/output both diagonal `true`, order zero included; numerical recheck retained. R3 F5-R2 repair is implemented. |
| affine Lebesgue scaling | `p11_volume_affine` (ChartScaling:146) | PASS | Arbitrary sets, positive dilation, dimension n and ENNReal inverse; no illicit measurability premise. |
| chart-scaling, geometry | `chart_scaling_geometry` (ChartScaling:156) | PASS | Inverse dilation for diameter and explicit Euclidean thickening; correct volume transport. |
| chart-scaling (d) | `chart_scaling_good` (ChartScaling:199) | PASS | Exact preimage good-set identity and excluded measure scaling. |
| chart-scaling (a) | `chart_scaling` (ChartScaling:224) | PASS | Scalar-family amount, unchanged rho, infimum direction and min factor; positive dimensions/nonempty source patch retained. |

## Definition classification and hypotheses

The only new definitions are `p11CDio` and `p11GammaStar`. Both are explicit real formulas, with no choice, arbitrary map, branch, bundled conclusion, or surrogate frozen object. Their bodies are the intended total Lean formulas on the entire declared carrier. The analytic interpretation uses the positive dimensions/orders/beta and exponent gap supplied by `P11DioHyp` and `ht`; outside that regime inverse/rpow operations retain Lean's ordinary total meanings, and no theorem exploits an invalid fallback. The proof explicitly handles C=0 when deriving concentration rather than dividing by it without justification.

All remaining new declarations are theorems. No new structures, abbreviations, instances, choice selectors or global norm changes occur. `P11DioHyp` is inherited source data D1–D3, with regularity, amount, size and diagonal closeness; the measure estimate is proved from it, not stored as a field. Chart recheck `hrecheck` is the source's numerical scaling obligation, not a disguised Diophantine/measure conclusion.

The recursive project-import closure has 15 KAM modules, no provider and no frozen theorem anchor. Its sole frozen module is `KAM.Frozen.Defs.IsDiophantine`, manifest state **SEALED**. Thus no DRAFT_SORRY theorem is imported. The frozen predicate was inspected directly: its lattice l1 denominator and dot product match Bridge's final rpow conversion.

## Refutation checks and proof assessment

Bridge: inspected the coordinatewise Pi max-norm bound and the l1 sum, the identity `s*(gamma*s^(-tau-1))=gamma*s^(-tau)` for s>0, and the triangle inequality. The consequence tests the correct doubled per-mode good set; it does not identify that set itself with a single-vector Diophantine predicate before applying the tail estimate.

PowerLaw: `modeSize_euclid_compare` is consumed in the correct direction, `|k|_1 ≤ sqrt(m)*|k|_2`. Integer `|k|_1≥1` and tau+1>0 give the profile bound. W7 supplies compactness and the excluded-measure series. `lattice_sum` is applied at tau'=(tau+1)*rho/mu-1; the source exponent gap gives tau'>m-1 and s>0. The proof obtains Summable before converting the nonnegative real series to ENNReal; it does not rely on a divergent real tsum's default. Algebra retains exactly the prescribed C_Dio factor. Concentration uses the threshold's second branch and compact measurability for the measure decomposition.

The R3 `power_law` interface retains explicit `hsmall : (sqrt(m)*gamma)^rho < beta/4` for its first two conclusions and the nested concentration clause. This is exactly the source corollary's opening hypothesis, not an added implementation premise. Its proof does not separately export the elementary implication from the threshold's first branch to hsmall. Callers must instantiate that source hypothesis; no stronger threshold-only export is claimed here.

ChartScaling: the chain rule is applied on open preimage domains; conversion from within derivatives is justified by openness. Attainment and boundedness lemmas of W0 justify both suprema and the amount infimum, with the stated positive dimensions/nonempty set. Check j=0 and both lambda≤1 / lambda≥1 regimes: the min/max factors have the correct direction. Translation/dilation geometry uses the explicit Euclidean distance in p11thick, and scalar dilation of the existing Pi metric for diameter. Haar scaling is stated for arbitrary sets, preserving the outer-measure carrier. Positive lambda makes ENNReal inversion/cancellation legitimate, including for infinite-measure sets. No finite-measure or measurable-set assumption is silently inserted.

## Notes, errata and limits

1. **Documented dependency deviation:** ChartScaling:9 imports W1 `Stability`, while design L881–882 says “W8's ChartScaling imports only W0 and Mathlib affine calculus/measure facts”. Its amount proof uses `contDiffOn_p11scalar` (Stability:273). Stability imports Basic/W0 only, so there is no cycle, provider leak or added theorem premise. Record the actual W1 edge in scheduling documentation; no proof repair is required.
2. **Nonblocking build warnings:** ChartScaling has unused `hM`, `ht`, and `hK` binders (retained to preserve exact signatures), plus deprecations for `if_true`, `Set.mem_setOf_eq`, legacy `rwa ... at *`, and `Set.preimage_diff`. Replayed Stability/DividedDifference also report inherited unused-binder warnings. These are not proof escapes or heartbeat failures.
3. **Expected generated-root lint exception:** KAM.lean is stale and was not regenerated, as the audit brief expressly allows.
4. No suspected new pinned-paper erratum, false frozen declaration, weakened assigned conclusion, changed normalizer or undeclared source premise was found in scope. The stale audit path in the handoff and W0/W1 design dependency sentence are documentation discrepancies, not mathematical source errata. No implementation deviation was introduced by this audit.
5. This package does not prove convergence/tails of an actual iteration, construct prepared physical frequencies, or close any planetary frozen anchor. Those remain downstream obligations.

## Independent check receipts

All audit-owned Lean checks use `LEAN_NUM_THREADS=1` and `nice -n 5`, sequentially. No resource-budget override, clean, update, cache fetch, provider edit, frozen edit or root regeneration was used.

### Targeted build

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11aw8 KAM.Planetary.WeakMeasure.Bridge KAM.Planetary.WeakMeasure.PowerLaw KAM.Planetary.WeakMeasure.ChartScaling
```

Exit **0**. Output includes:

```text
[inp-gate] slot 1 acquired 12:38:07 for KAM.Planetary.WeakMeasure.Bridge KAM.Planetary.WeakMeasure.PowerLaw KAM.Planetary.WeakMeasure.ChartScaling
Build completed successfully (9061 jobs).
```

The gate used the existing build overlay. W8 warnings: ChartScaling:114 unused hM; :127 unused ht; :158 and :225 unused hK; :133/:180/:196/:214 deprecations. Inherited replay warnings: Stability:302/:304/:403 and DividedDifference:96. No sorry, elaboration error or heartbeat failure.

### Exact expected types and axioms

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AW8Audit.lean
```

Final exit **0**, nine signature-derived full-type assignments, **19 axiom prints**, **0 errors**. Scratch-only warnings concern unused proposition binder names. Two earlier scratch attempts exited 1 because generated formatting lost the line-break/semicolon delimiters of `let` expressions; no production declaration failed. Restoring those delimiters made the unchanged expected types pass. Neither failed attempt is treated as a successful receipt.

Exact axiom output for every new public theorem:

```text
'KAM.Planetary.limit_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.limit_bridge_diophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_modeSize_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_modeSize_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pl_profile' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pl_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_C_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.power_law' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_euclid_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_iteratedFDeriv_affine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pow_le_max' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_min_le_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chart_scaling_jets' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chart_scaling_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chart_scaling_closeness' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_volume_affine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chart_scaling_geometry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chart_scaling_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chart_scaling' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` or other unapproved axiom occurs. Both definition bodies also matched R3 after whitespace normalization. No frozen provider/type or seal-body test is applicable because this is a helper-only package.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakMeasure.Bridge KAM.Planetary.WeakMeasure.PowerLaw KAM.Planetary.WeakMeasure.ChartScaling
```

Exit **0**, one invocation for all three modules. Exact output:

```text
replaying KAM.Planetary.WeakMeasure.ChartScaling
replaying KAM.Planetary.WeakMeasure.PowerLaw
replaying KAM.Planetary.WeakMeasure.Bridge
```

### Lint and integrity

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1 solely for the explicitly permitted stale generated root**. All other checks pass. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (558 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

An early lint launch was stopped during the Python source guard, before its ABI elaboration, so the complete final lint invocation could run after kernel replay. It is not counted as a completed check.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no output. `git diff --check` and `git diff inp...HEAD --check` exited **0**. Forbidden-token/resource-override scans of the three owned modules returned no matches. Module formatting and the 1500-line cap pass; line counts are 72, 247 and 257. Both new definitions are in the exposed public section.

The exact-type probe `.lake/abi-scratch/P11AW8Audit.lean` was deleted after successful elaboration. Only this report was written persistently by the audit; final status retains the pre-existing untracked `P11A-W8-handoff.md` alongside this untracked report. No state-changing git command was run. Report whitespace, code-fence balance and final path were checked.



