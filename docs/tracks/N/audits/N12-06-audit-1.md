# N12-06 independent package audit 1

Overall verdict: **PASS WITH NOTES** for the scoped infrastructure package. Both new public results pass statement fidelity and proof checks. No frozen anchor is proved by this package, so no frozen theorem is declared seal-ready. In particular this is not closure of N-AVERAGING-MEAN or N-AVERAGING-MOST.

## Scope and authority

Audited HEAD `77f0e5a4934ad4c181e96fca624edd2b4b73a388` in `/root/code/KAM-inp-n1206`, on 2026-10-28. Read AGENTS.md, PLAN, DECISIONS, the package brief, N12-06 handoff/AUDIT FOCUS, N12 design and both design audits, the delivered signatures, relevant Part 12 blueprint, Track N statement, frozen averaging targets and their analytic/rank/domain definitions, and the implementation and its coefficient/corrector inputs. Only this report is a repository edit; temporary probes were confined to `.lake/abi-scratch/`. No delegation or state-changing git.

The user's exact report destination overrides the generic brief's main-worktree destination. The handoff narrows substantive review to `KAM/Nekhoroshev/Averaging/CorrectorRegular.lean`, comparing with `inp-n1205`. Both requested comparisons were inspected:

- `git diff inp...HEAD`: two new modules, Corrector (119 lines) and CorrectorRegular (760 lines). Git warns of multiple merge bases and selects `6e36995edb8c5fb4ee4ec0ed914f4a0c55a9b7f1`. Corrector is inherited N12-05 infrastructure, outside this audit's proof verdict.
- `git diff inp-n1205...HEAD`: also contains unrelated landed modules/reports and generated-root additions because the reference branches have moved/diverged. Restricting it to CorrectorRegular gives precisely the new 760-line module; no previous version exists in that base. These unrelated changes are not attributed to this prover.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty (apart from the merge-base warning). The two-tip comparison with inp-n1205 does contain inherited root additions; it is not an empty protected-path delta and is not used to claim one.

Current reference tips: inp `408ea7a6f026a1ecf1d0cf0e988bdc54494497f9`; inp-n1205 `9967aeded43210bf8896cd6903b059f9c1815ea6`.

SHA-256:

| Input | Hash |
|---|---|
| CorrectorRegular.lean | `4b6c54cc73d6b88cc5ffa5ab7bad39b0f5871cfc23ea291b38c197eb2a587079` |
| N12-LEAN-DESIGN.md | `d66059fe35c7b3f76307ae60df90aa3da66ea089cd3ec073b39cbe2ffd1b6370` |
| `/root/code/KAM-inp/.drafts/design/N12Signatures.lean` | `0ad9cf0f84ffc435f1d85360516ad94f5ec100ff4a53c76d410f9e7d3b028369` |

## Declaration and node ledger

All Lean names below are in `KAM.Nekhoroshev`; helper names are private.

| Node / declaration | Lean implementation and locator | Verdict | Reason |
|---|---|---|---|
| `bpN:p12:wreg` / public `wreg` | CorrectorRegular:638–756 | PASS | Exact delivered signature: C¹, full-domain directional HasSum, periodicity, all four bounds, exact residual HasSum and individual-mode action-derivative bound. No added premise or changed carrier/constants. |
| `stepN:p12:wr-smooth` | `hasFDerivAt_gk`:251; `contDiffOn_gk`:428; `contDiffOn_avgW`:458 | PASS | Product/chain derivatives of actual summands, analytic coefficient regularity, C² frequency and smooth rational divisor; continuous derivative series establishes C¹. |
| `bpN:p12:ext-tsum` | `hasFDerivAt_avgW`:407–426 | PASS | Concrete use of `hasFDerivAt_tsum_of_isPreconnected`; every hypothesis discharged on the open convex full domain. |
| `stepN:p12:wr-ac` | `norm_avgU_le`:195; `hfst`:680; final bounds:712–756 | PASS | Sup norm on Pi spaces, exact 2π and l1 mode factor; actual convergence proved before estimating the sum. |
| `stepN:p12:wr-b` | `hres`:695–711; residual norm:714–736 | PASS | Subtracts actual angle-derivative HasSum from coefficient field HasSum. Rational identity gives κ²/(q²+κ²), with correct minus sign, 2πi, mode vector and character. |
| `stepN:p12:wr-d` | `abs_dQ_le`:81; `hasFDerivAt_aScal`:139; `norm_dU_le`:494; `hasFDerivAt_avgU`:506 | PASS | Row sums give modeSize*M₂*norm v; coefficient derivative contributes 2n/s. The individual and summed action-derivative bounds have the intended strength. |
| public `envelope_regular` / envelope measurability and finiteness | CorrectorRegular:594–636 | PASS | Exact signature: measurable zero extensions of all five envelopes, arbitrary real ε in the Phi clause, four finite envelopes at every valid action. |

Only `wreg` and `envelope_regular` are new public theorems. Normalizing whitespace in their complete declarations through the colon/conclusion gives equality with the delivered signatures for both (`True`, `True`). Fresh-name copies of those delivered statements elaborate with bodies `KAM.Nekhoroshev.wreg d hκ hM` and `KAM.Nekhoroshev.envelope_regular d hκ hM0`. This checks actual theorem application, not just textual resemblance. Provider-versus-frozen and seal-body probes are **not applicable**: this module has no provider export and implements no entire frozen theorem.

## Proof and definition review

The full-domain identity is the second top-level conjunct, outside the avgG guard. At :668–671 the CLM-valued HasSum is evaluated at an arbitrary real phase direction; choosing (v,0) or (0,v) gives both partial derivative series. The explicit private `hfst` and `hsnd` formulas at :680–686 expand those derivatives. The zero mode has zero mode vector, hence identically zero summand and derivative; summing over all integer vectors rather than excluding zero is faithful.

The design :348–354 proposes small preconnected product neighborhoods. The proof legitimately strengthens this to the whole domain: `avgDomain = univ × ball 0 R` is open and convex; the coefficient bounds hold uniformly on the real action ball, and hM holds on its closure. The constant

`domC = n/(s*κ) + M₂/κ² + π/κ + 1/(2κ)`

multiplies the same summable `(1+modeSize k)^3 * avgBeta s k` for values and derivative operator norms (:318–405). hM implies M₂≥0 using the action 0 and an existing coordinate (d.hn). No off-domain differentiability is invoked. At :424–426, Mathlib SmoothSeries:72 receives summability, openness, preconnectedness, each HasFDerivAt, a uniform derivative bound, an in-domain base point with convergent values, and the target point. The additional continuity proof :466–475 uses the C¹ summands and the same majorant; it does not infer C¹ solely from pointwise differentiability.

Envelope convergence (:526–575) follows from global rational bounds and coefficient polynomial summability, independently of regularity of an arbitrary extension of h. Measurability uses the actual measurable total fderiv API (:577), rational operations and ENNReal sums, followed by measurable indicators. This justifies a stronger private global Borel claim without asserting global continuity of the arbitrary extension. ENNReal.ofReal truncation does not erase any needed estimate: the summands used for finiteness and norm bounds are proved nonnegative.

Every new definition is private, with no structure, abbrev, instance, choice-based fallback or surrogate corrector introduced:

| Definition | Locator | Classification |
|---|---|---|
| `kvec` | :41 | Exact coordinatewise complex integer vector, valid on the whole carrier. |
| `aScal` | :53 | Exact real-slice Fourier coefficient times rational divisor, on the whole carrier. Total division inherited from avgPsi is only differentiated with κ>0. |
| `gk` | :205 | Actual negative-character-weighted avgU summand; `avgW_eq` :390 proves its tsum is avgW. |
| `linK` | :210 | Finite sum of continuous real-linear coordinate maps representing 2πi k·v everywhere. |
| `domC` | :318 | Explicit numerical majorant; required positivity is proved under source s>0, κ>0 and derived M₂≥0. No fallback. |

`AveragingData` supplies dimension/positivity, analytic h/f and rank premises only. hM is the design's uniform row-sum bound, not an assumed corrector conclusion. A recursive import scan found 51 KAM modules, **zero frozen theorem modules and zero provider modules**. Frozen definitions are allowed; no DRAFT_SORRY theorem or provider enters the proof closure. The public axiom checks below independently exclude sorryAx.

## Independent checks

Targeted build, one invocation:

```text
env LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1206 KAM.Nekhoroshev.Averaging.CorrectorRegular
[inp-gate] slot 1 acquired 09:15:40 for KAM.Nekhoroshev.Averaging.CorrectorRegular
⚠ [3181/3181] Replayed KAM.Nekhoroshev.Averaging.CorrectorRegular
Build completed successfully (3181 jobs).
exit 0
```

Four replayed warnings at :605:11, :609:11, :614:11, :619:11:

```text
`Measurable.ennreal_tsum` has been deprecated: Use `Measurable.tsum` from `Mathlib.MeasureTheory.Constructions.Polish.Basic` instead
```

Fresh delivered-statement probe and axioms:

```text
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N1206Audit.lean
'KAM.Nekhoroshev.wreg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.envelope_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

Kernel replay (completed serialized rerun):

```text
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Averaging.CorrectorRegular
replaying KAM.Nekhoroshev.Averaging.CorrectorRegular
exit 0
```

The sole scoped lemma module is passed by module name, not by source path. No provider module exists to add.

Source hygiene: 760 lines; no lines over 100 characters; module header, copyright, public imports, module docstring and exposed public section present. Comment-masked scan: no forbidden proof escapes, resource overrides, EuclideanSpace or other set_option. `git diff --check inp...HEAD`: exit 0 (only multiple-merge-base warning).

Final lint (serialized after the completed kernel replay):

```text
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (500 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The only failure is the generated-root mismatch explicitly allowed by the audit brief. No regeneration was attempted. The initial plain lint invocation produced the same diagnostics and exit code.

## Notes, suspected defects and deviations

No new blueprint or frozen-statement defect found. Part 12 :113's “with termwise derivatives” obligation, omitted in design revision 1 and restored in revision 2, is fully paid here. Design :243–245 quotes p12:109 “all Borel; the pointwise sums of nonnegative continuous functions” and limits continuity to the analytic domain. This proof respects that qualification; the global measurable-fderiv route is valid and does not assert global continuity.

Inherited source issue E-NAVG-NEI-17 is already declared in the design/statement: Neishtadt (1976), p.1298 equation (17), interchanges a supremum and integral without justification. This audit checks the present Fourier-corrector package against its local contracts; it does not independently re-audit that PDF or certify the later integral-of-maximum repair. No new pinned-source erratum is alleged.

Implementation variation: global rather than local domination is justified above; private `contDiffOn_freq'` duplicates the private Setting lemma. Neither changes the source statement. The public results also retain the approved strengthening κ>0 without κ≤1 and include the harmless zero mode.

Audit execution deviation: the first lint invocation was plain `sh scripts/lint_sources.sh`, so explicit LEAN_NUM_THREADS=1/nice were not applied to its internal ABI subprocess. A kernel replay was briefly started before that lint's ABI phase finished, then immediately interrupted (exit 130, no result relied on). The successful replay above ran after the first lint finished. Final lint was rerun separately with explicit LEAN_NUM_THREADS=1 and nice -n 5; no claim is made that the initial execution perfectly obeyed serialization. No production content was changed to obtain a passing check.

Cleanup and integrity: the audit probe `.lake/abi-scratch/N1206Audit.lean` was deleted. Final status contains only the pre-existing untracked handoff and this new untracked report; no tracked file changed. Report whitespace check and recheck of the audited module hash passed.
