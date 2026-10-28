# B04 independent package audit 1

Overall package verdict: **FAIL (incomplete design obligation F1)**. The six named signature declarations, including `KAM.Planetary.smooth_cutoff`, pass source/signature inspection, elaboration, axiom checks and kernel replay; the theorem itself has no identified mathematical defect. The per-result verdict for `KAM.Planetary.smooth_cutoff` is **PASS WITH NOTES** (only the allowed lint exception); no frozen anchor is in this package. This package has no provider and does not seal a track headline. The required B04 completeness check fails because its binding proof plan requires positivity of c-prime, while the delivery defines that constant and defers its use without supplying positivity.

Scope: ONLY `KAM/Planetary/WeakKAM/Cutoff{Bump,Tensor,Scale,Conv,}.lean`; 648 lines, 49 public declarations (8 definitions, 41 theorems). Compared using `git diff inp...HEAD`: exactly these five new Lean files. HEAD `c9b021e5ace56873f1f2ee8cbaf8a01e578c430d`; comparison ref `cbc738ce2a4017c3c06bf565c99f028ec013fcd2`. Existing B01 data are inputs, not reaudited. Read AGENTS, PLAN, DECISIONS, the audit brief, B04 handoff and offload brief, P11B design and both design audits, track-P statement conventions, and blueprint p11a3 smooth-cutoff, sc-constr, sc-deriv and y-conv. No relevant frozen theorem is claimed or imported; frozen provider-type and seal-body probes therefore do not apply.

The main-worktree signature `/root/code/KAM-inp/.drafts/design/P11BSignatures.lean` has SHA256 `6800132b3e98b3badc215d5cb1cccc6b016e2f14ec976b661519e436cbf39596`. It is absent locally, so the live main-worktree copy was read as requested. All five definition texts and the entire `smooth_cutoff` statement are byte-identical to its B04 slice; that slice also occurs exactly in local design Appendix A (lines 565–584). The external design-audit reports are under `docs/tracks/P/design/`, not the handoff's `audits/` shorthand.

## Finding F1: B04 does not prove c-prime positive

**Location and quote:** `docs/tracks/P/design/P11B-LEAN-DESIGN.md:278`: “Prove the bump L1 constants finite and c-prime positive”. The binding offload B04 brief requires every obligation assigned by the design. Blueprint `p11a3-iteration-selection.tex:147` defines c-prime, implemented as `selectionExtensionC` at `CutoffBump.lean:31–35`. There is no lemma establishing `0 < selectionExtensionC n μ` under `1 ≤ n` anywhere in the five audited files. Searching the entire local WeakKAM subtree finds only its definition and a docstring mention. The handoff explicitly says its boundedness/use belongs to B05; that does not discharge the design's B04 positivity requirement.

This is an omitted proof/export, not a false definition or a refutation of smooth_cutoff. Required repair: prove positivity for the intended positive dimension (and the prescribed μ range), including the finite-supremum justification used for the exact constants; alternatively obtain and record an explicit controlling reassignment from the orchestrator. Positivity must not be added as a premise to a consumer or inferred merely from `ℝ` being the codomain of a Bochner integral. The bump derivative integrability for j≤μ is already supplied, and its absolute integrability follows by `Integrable.norm`; no numerical quadrature is used.

## Mathematical review

`SelectionR n` unfolds to `Fin n → ℝ` with its Pi max norm. The bump is the stated positive-part polynomial of degree exponent μ+1; its normalizing integral is strictly positive for every μ, from continuity, nonnegative compact support and value 1 at zero. Its μ-times continuous differentiability is proved by positive-part-power induction, including the derivative at zero via little-o. Higher derivative compact support is obtained from Mathlib's total iterated derivative; no unsupported smoothness is assumed.

The tensor coordinate formula counts coordinate occurrences in each tuple and differentiates a product. Positive scaling δ=t/4 yields unit integral and the exact coordinate L1 value δ^(-k) times the product of one-dimensional derivative norms. The multiindex set is bounded above by a finite image before `le_csSup` is used. Expanding arbitrary multilinear arguments into coordinates gives exactly n^k summands and the declared constant. The nonempty multiindex instances used in this bound are supplied by actual coordinate tuples; no empty-supremum fallback is used to prove the bound.

For the cutoff, A={z:infDist z E≤t/4} is closed, so its indicator is locally integrable. The right factor is compactly supported C^μ. The convolution derivative induction uses `HasCompactSupport.hasFDerivAt_convolution_right`, checks compact support and differentiability of the evaluated derivative, and supplies integrability before moving a continuous linear evaluation through the integral. Normalization gives 0≤χ≤1, the support radius yields χ=1 on E, and closure gives the stated topological support inclusion. Integrating the absolute derivative bounds gives the exact `(4/t)^k` estimate, including k=0. No hard conclusion is assumed as a premise. Some source hypotheses are unused (`hn`, `hμ`, compactness, nonemptiness, t≤1), but they are preserved verbatim; stronger auxiliary generality is harmless.

## Declaration inventory

Every name below is in namespace `KAM.Planetary`. Helper rows implement the construction or derivative proof steps, rather than claiming independent frozen results. PASS here concerns declaration fidelity and proof review; it does not discharge F1 or the checks recorded below.

| Node / step | Declaration and source locator | Verdict | Reason |
|---|---|---|---|
| `sc-deriv` | `selectionCutoffSet_bddAbove` (Cutoff:24) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-deriv` | `selectionMultilinear_expand` (Cutoff:37) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-deriv` | `selectionKernel_integrable_deriv` (Cutoff:50) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-deriv` | `selectionKernel_deriv_bound` (Cutoff:61) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `bpP:p11a:smooth-cutoff` | `smooth_cutoff` (Cutoff:97) | PASS | Verbatim source contract; all range, equality, support and derivative clauses proved. |
| `sc-constr` | `selectionBumpRaw` (CutoffBump:25) | PASS | Literal object; classified below. |
| `sc-constr` | `selectionBump` (CutoffBump:26) | PASS | Literal object; classified below. |
| `sc-constr` | `selectionBumpL1` (CutoffBump:28) | PASS | Literal object; classified below. |
| `sc-constr` | `selectionCutoffC` (CutoffBump:29) | PASS | Literal object; classified below. |
| `sc-constr` | `selectionExtensionC` (CutoffBump:31) | PASS WITH NOTE | Exact signature body; positivity required by design is not exported (F1). |
| `sc-constr` | `selectionPosPow_hasDerivAt` (CutoffBump:36) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-constr` | `selectionPosPow_contDiff` (CutoffBump:67) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-constr` | `selectionBumpRaw_contDiff` (CutoffBump:82) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-constr` | `selectionBumpRaw_nonneg` (CutoffBump:85) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-constr` | `selectionBumpRaw_eq_zero` (CutoffBump:88) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-constr` | `selectionBumpRaw_zero` (CutoffBump:94) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-constr` | `selectionBumpRaw_support` (CutoffBump:97) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-constr` | `selectionBumpRaw_hasCompactSupport` (CutoffBump:106) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-constr` | `selectionBumpRaw_continuous` (CutoffBump:109) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-constr` | `selectionBumpInt_pos` (CutoffBump:112) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-constr` | `selectionBump_contDiff` (CutoffBump:117) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-constr` | `selectionBump_nonneg` (CutoffBump:120) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-constr` | `selectionBump_support` (CutoffBump:123) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-constr` | `selectionBump_hasCompactSupport` (CutoffBump:129) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-constr` | `selectionBump_integral` (CutoffBump:132) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-constr` | `selectionBump_iteratedDeriv_continuous` (CutoffBump:136) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-constr` | `selectionBump_iteratedDeriv_hasCompactSupport` (CutoffBump:140) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-constr` | `selectionBump_iteratedDeriv_integrable` (CutoffBump:149) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-constr` | `selectionBumpL1_nonneg` (CutoffBump:154) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `bpP:p11a:y-conv` / `sc-deriv` | `selectionConv_iteratedFDeriv` (CutoffConv:24) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-deriv` | `selectionBumpScaled` (CutoffScale:25) | PASS | Literal object; classified below. |
| `sc-deriv` | `selectionKernel` (CutoffScale:28) | PASS | Literal object; classified below. |
| `sc-deriv` | `selectionMult_sum` (CutoffScale:30) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-deriv` | `selectionBumpScaled_contDiff` (CutoffScale:35) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-deriv` | `selectionBumpScaled_iteratedDeriv` (CutoffScale:39) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-deriv` | `selectionBumpScaled_nonneg` (CutoffScale:48) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-deriv` | `selectionBumpScaled_eq_zero` (CutoffScale:52) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-deriv` | `selectionBumpScaled_integral` (CutoffScale:61) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-deriv` | `selectionBumpScaled_L1` (CutoffScale:68) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-deriv` | `selectionKernel_contDiff` (CutoffScale:88) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-deriv` | `selectionKernel_nonneg` (CutoffScale:91) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-deriv` | `selectionKernel_ne_zero` (CutoffScale:95) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-deriv` | `selectionKernel_hasCompactSupport` (CutoffScale:102) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-deriv` | `selectionKernel_integral` (CutoffScale:108) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-deriv` | `selectionKernel_coord_L1` (CutoffScale:115) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-deriv` | `selectionMult` (CutoffTensor:25) | PASS | Literal object; classified below. |
| `sc-deriv` | `selectionMult_succ` (CutoffTensor:28) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-deriv` | `selectionTensor_fderiv_single` (CutoffTensor:34) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |
| `sc-deriv` | `selectionTensor_iteratedFDeriv` (CutoffTensor:51) | PASS | Auxiliary lemma; only typing, regularity, positivity or integrability premises used. |

## Definition classification

| Definition | Classification on its whole carrier |
|---|---|
| `selectionBumpRaw` | Exact nonnegative positive-part polynomial for every μ,x. |
| `selectionBump` | Exact integral normalization; denominator proved positive for every μ. No division-by-zero fallback used. |
| `selectionBumpL1` | Exact Bochner integral of absolute total iterated derivative for every μ,j; genuine derivative L1 norm justified when j≤μ. No higher-order regularity claim. |
| `selectionCutoffC` | Exact n^k times supremum over multiindices. Finite bounded set proved; nonempty in the positive-dimensional intended range. Zero-dimensional empty cases use Lean's total sSup and are not substituted for the positive-dimensional source constants. |
| `selectionExtensionC` | Exact sqrt(n) times finite maximum formula, including Nat power convention 0^0=1. Intended body, but required positivity proof missing (F1). |
| `selectionMult` | Exact finite count of occurrences, for every coordinate tuple. |
| `selectionBumpScaled` | Literal inverse-scale formula for all δ; δ=0 has Lean's total inverse value, and normalization/support claims require δ>0. No zero-scale fallback relied upon. |
| `selectionKernel` | Exact tensor product for every n,μ,δ,w; normalization and support use δ>0. Empty product at n=0 is standard. |

## Validation receipts

All Lean/Lake checks were serialized with `LEAN_NUM_THREADS=1` and nice priority 5. The build wrapper itself supplies `nice -n 5`; no heartbeat, recursion or synthesis override was used.

1. Targeted build (exit **0**):

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11b-b04 KAM.Planetary.WeakKAM.Cutoff
```

Output began `[inp-gate] slot 1 acquired 15:59:05 for KAM.Planetary.WeakKAM.Cutoff` and ended `Build completed successfully (9084 jobs).` Warnings concerned deprecated CLM names and unused source hypotheses. Waiting for a slot was substantial; no build was bypassed or run concurrently by this audit.

2. Literal-contract and axiom probe (exit **0**, no errors):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B04-probe.lean
```

The probe imports only `KAM.Planetary.WeakKAM.Cutoff`, copies the literal signature statement under the fresh name `b04_contract` and proves it with `exact KAM.Planetary.smooth_cutoff hn hμ E hE hne ht ht1`. It copies each of the five signature definition bodies to a fresh name and checks pointwise equality by `rfl`. Source text comparison separately confirms exact binders, type and definition bodies. This is the relevant contract check for an infrastructure theorem; there is no frozen-provider ABI to compare. The 41 `#print axioms` commands, one for every public theorem in the inventory, produced exactly:

```text
'KAM.Planetary.selectionCutoffSet_bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionMultilinear_expand' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionKernel_integrable_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionKernel_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.smooth_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionPosPow_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionPosPow_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBumpRaw_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBumpRaw_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBumpRaw_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBumpRaw_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBumpRaw_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBumpRaw_hasCompactSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBumpRaw_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBumpInt_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBump_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBump_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBump_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBump_hasCompactSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBump_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBump_iteratedDeriv_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBump_iteratedDeriv_hasCompactSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBump_iteratedDeriv_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBumpL1_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionConv_iteratedFDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionMult_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBumpScaled_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBumpScaled_iteratedDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBumpScaled_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBumpScaled_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBumpScaled_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionBumpScaled_L1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionKernel_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionKernel_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionKernel_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionKernel_hasCompactSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionKernel_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionKernel_coord_L1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionMult_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionTensor_fderiv_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionTensor_iteratedFDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay, one invocation (exit **0**):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.Cutoff KAM.Planetary.WeakKAM.CutoffBump KAM.Planetary.WeakKAM.CutoffTensor KAM.Planetary.WeakKAM.CutoffScale KAM.Planetary.WeakKAM.CutoffConv
```

Complete output:

```text
replaying KAM.Planetary.WeakKAM.CutoffConv
replaying KAM.Planetary.WeakKAM.CutoffScale
replaying KAM.Planetary.WeakKAM.CutoffTensor
replaying KAM.Planetary.WeakKAM.CutoffBump
replaying KAM.Planetary.WeakKAM.Cutoff
```

4. Lint (exit **1**, solely the brief-permitted generated-root exception):

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (777 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The generated root was not regenerated. Hygiene is **PASS WITH NOTES** for this permitted exception. Module checks, frozen-anchor guard and all 144 frozen declaration ABI hashes pass. This exception is independent of the package FAIL for F1.


Source checks completed: `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` has empty output; `git diff --check inp...HEAD` exits 0. Forbidden-token/resource-override search of all five files has no matches. All five have copyright, module, public import, module docstring, exposed public noncomputable section. File lengths: Cutoff 183; CutoffBump 157; CutoffConv 72; CutoffScale 138; CutoffTensor 98. Exact declaration-name scan across all other local KAM Lean files finds zero collisions, including no reuse of the P11C family. Recursive KAM import scan visits 38 modules and 12 frozen definition modules; no provider or frozen theorem imports occur. No DRAFT_SORRY theorem or other package's proof is assumed.

## Source defects, deviations and limits

No suspected defect in a pinned mathematical source, blueprint contradiction, or mathematical statement change was found. F1 is a package/design completeness failure. Splitting the module into a public-import facade and four focused modules preserves the interface and stays below the file cap. All temporary B04 probes and logs were removed after their receipts were included above. The audit changes only this report and temporary `.lake/abi-scratch/` material; no Lean repair, generated-root change, frozen edit, git state change, or reassignment is performed. This audit supplies no conclusion about B05, downstream applicability, or frozen-anchor closure.
