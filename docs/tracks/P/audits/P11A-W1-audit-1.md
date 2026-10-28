# P11A-W1 independent package audit 1

Overall verdict: **PASS WITH NOTES** for the scoped infrastructure package. `KAM.Planetary.stability`
and `KAM.Planetary.M_bound` pass mathematical, exact-signature, axiom and elaboration checks.
Kernel replay passed for both the target and its Basic dependency. There is **no frozen anchor or provider in this package**;
this verdict does not seal P-G, P-PLANAR, P-FIXED, or establish downstream KAM/measure closure.

## Scope and authority

Audited worktree `/root/code/KAM-inp-p11aw1`, HEAD
`67715359f047f24dc463d00310077cb52130ad3b`.
Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the specified package brief, the untracked
P11A-W1 handoff, design Revision 3 (W1 row, registry, proof instructions and Appendix A),
track P statement context, p11a1 blueprint L18–78 and the relevant dispositions in design audits 1–3.
The latter reports actually reside in `docs/tracks/P/design/`, not `audits/`; the signature scratch
exists at `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`, not in this package checkout.
Those external inputs were read only. The user's exact output-path instruction overrides the
brief's generic instruction to place the report in the main inp checkout.

Required comparison `git diff inp...HEAD` was inspected. `inp` resolved to
`408ea7a6f026a1ecf1d0cf0e988bdc54494497f9`; its three-dot diff contains Basic.lean (465 lines),
Stability.lean (453 lines), and the three W0 audit/handoff documents. W0 is inherited context,
not re-audited here. Also inspected the scoped Stability.lean diff against `inp-p11aw0`
(`51ab502cfc33f7d9a5427f0f0ac6cc5399b71e82`), where it is a new 453-line file.
The full three-dot diff against that older branch includes unrelated inherited work; no verdict
is assigned to those changes. Audit implementation scope is only
`KAM/Planetary/WeakMeasure/Stability.lean`.

Pins (SHA-256):

- Stability.lean: `d5f934d0392804a8ca442337c6e4e5b12860441d7a79c39563d992bb2576d406`.
- Design Revision 3: `8619ea896c856347a9a5c5efac5080f0c830ea19245320b5f03a2b4267a300b9`.
- Signature draft: `c31fda0b479f2dd0488b12e7f2daeda18f965eb316610df1c65f14012dfcb092`.
- p11a1 blueprint: `66b5ce26db59b57dbf934938a7bae2fead6b6ff4c7c9d420d33b9582e272bab5`.

## Fidelity, proof review and applicability

Both main signatures, from `theorem` through the type before `:=`, are byte-identical to the
corresponding signature-draft declarations (L99 and L109), also reproduced in design L1042–1059.
An independent scratch probe copied each signature under a fresh name, proved it using the
production theorem applied to exactly its explicit binders in order, and checked
`example : type_of% @audit_stability := @stability` and its `M_bound` counterpart.
Both elaborated. Frozen-provider equality/seal probes are inapplicable: there is no frozen
export mapped to W1 and no provider to seal. No frozen statement was copied or changed.

The stability proof first contracts vector jets by a unit coefficient vector using
Cauchy–Schwarz. For rho=2 it factors the difference as s(s+2t), restricts to a line to use the
iterated Leibniz formula, and sums binomial coefficients. The reverse triangle inequality at
an attaining order gives the maximum-jet estimate; the nonempty coefficient-sphere/patch and
greatest-lower-bound property then give the amount estimate. `hm` and `hne` explicitly guard
that infimum. No analyticity or nondegeneracy of the perturbed map is assumed.

Although the aggregate signature bounds the error by eta_mu, the source's sharper
`2^j*theta*(2*M+theta)` bound at each j≤mu is available by applying `stability_jet` with its
order parameter set to j and restricting the C^mu and jet bounds to that order. This exact
specialization was independently elaborated in the scratch probe, including j=0. Thus the
source's step st-2 is not lost. The beta/2 consequence follows from the two exported
inequalities by transitivity and subtraction, under the source's numerical smallness premise.
It requires no new analytic theorem. Compactness and the positive ambient dimension are
retained in the design signature even though this proof does not need them.

`M_bound` uses the full operator gauge, not the diagonal one. It transports the input vectors
through an explicit continuous linear equivalence to an L2 wrapper, uses Mathlib's full
operator-norm product derivative inequality there, and transports back. It handles all
factor orders including zero. Each product summand is bounded by M² and their binomial sum
is 2^j. The final source bound 2^(mu+1)M² follows from j≤mu+1 and M²≥0. There is no uncharged
polarization factor and no identification of the Pi max-norm operator gauge with `p11op`.
The equal-argument Leibniz identity is the exported W1 helper; the general product estimate
needed by M_bound is supplied directly by Mathlib, not assumed as a hypothesis.

No public hypothesis conceals a hard step. Jet bounds in these estimates are the source's
finite-derivative size/closeness inputs. Hypotheses of generic scalar-gauge and operator
helpers are explicitly conditional helper inputs, not replacements for stability or M_bound.

## Declaration / node ledger

All names below are in `KAM.Planetary`; every new definition and theorem is included.
Generic helper rows identify their role instead of claiming a separate blueprint node.

| Declaration and source line | Verdict | Node / reason |
|---|---|---|
| `p11toE` (L30) | PASS WITH NOTES | Concrete continuous linear equivalence to the L2 wrapper; see public-bridge note. |
| `p11euclid_eq_norm` (L33) | PASS | Explicit Euclidean gauge equals norm after transport; does not identify the Pi max norm. |
| `p11euclid_add_le` (L36) | PASS | Triangle inequality via exact transport. |
| `p11euclid_sub_le` (L40) | PASS | Subtraction triangle inequality via exact transport. |
| `p11euclid_one` (L44) | PASS | One-dimensional Euclidean length is absolute value. |
| `abs_p11dot_le` (L47) | PASS | Cauchy–Schwarz for the explicit Euclidean length. |
| `p11lin` (L60) | PASS | Finite linear combination of coordinate projections; intended dot functional. |
| `p11lin_apply` (L63) | PASS | Exact evaluation of the dot functional. |
| `p11const` (L67) | PASS | Continuous linear scalar embedding into Fin 1 → ℝ. |
| `p11const_apply` (L70) | PASS | Exact evaluation of the scalar embedding. |
| `iteratedFDeriv_dot` (L72) | PASS | Linear commutation under C^j regularity at the evaluation point. |
| `abs_iteratedFDeriv_dot_le` (L81) | PASS | Linear commutation followed by Cauchy–Schwarz. |
| `p11euclid_iteratedFDeriv_scalar` (L88) | PASS | Scalar jet transport into the one-dimensional carrier. |
| `p11dg_scalar_le` (L100) | PASS | Upper bound from every diagonal unit direction; nonnegative bound handles empty sphere. |
| `abs_jet_dot_le_of_p11dg` (L110) | PASS | Unit coefficient contraction and the bounded-supremum lower membership lemma. |
| `p11line_isOpen` (L124) | PASS | Private preimage-openness helper for the line restriction. |
| `p11line_iteratedDeriv` (L129) | PASS | bpP:p11a:f-mvt; restriction to y+t•a with all domain checks explicit. |
| `p11line_contDiffAt` (L150) | PASS | Source regularity restricts to the line near zero. |
| `p11leibniz_diag` (L158) | PASS | bpP:p11a:f-leib, equal-argument formula, including order zero; not a standalone full-tensor identity. |
| `p11eta_nonneg` (L180) | PASS | Nonnegativity of the explicit error bound for all rho; no restriction needed. |
| `contDiffOn_p11dot` (L187) | PASS | Dot contraction preserves the supplied regularity. |
| `p11scalar_sub_eq` (L193) | PASS | Exact identity for rho=1,2; squared case is s(s+2t). |
| `stability_jet` (L207) | PASS | stepP:p11a:st-1/st-2; bounds each order by eta_mu. Specialization mu=j recovers the sharper source 2^j bound (probe passed). |
| `contDiffOn_p11scalar` (L273) | PASS | Polynomial scalar family is C^mu for every natural rho. |
| `p11dg_le_add` (L279) | PASS | Reverse triangle estimate via iterated derivative subtraction. |
| `p11maxJet_le_add` (L293) | PASS | stepP:p11a:st-amount; use an attaining order before comparison. |
| `stability` (L302) | PASS | bpP:p11a:stability; exact design signature and source amount/error bounds, no extra premise. |
| `p11euclid_symm` (L333) | PASS WITH NOTES | Exact inverse-transport norm; public L2-wrapper statement (note). |
| `opNorm_le_of_unit` (L336) | PASS | General multilinear unit-ball estimate; explicit zero-coordinate branch, empty tuple included. |
| `iteratedFDeriv_comp_fromE` (L358) | PASS WITH NOTES | Exact transport of the tensor through the continuous linear equivalence; public bridge (note). |
| `norm_comp_dot_le` (L367) | PASS WITH NOTES | Transports the actual Euclidean input-ball bound, without a dimension-dependent loss. |
| `p11op_scalar_le` (L379) | PASS WITH NOTES | Transfers the transported operator-norm bound back to the declared Euclidean gauge. |
| `M_bound` (L403) | PASS | bpP:p11a:M-bound; exact design signature; contraction plus full operator Leibniz estimate and sum choose=2^j. |

## Definition classification and public-bridge note

There are exactly three new definitions and no abbreviations or structures:

- `p11toE` (L30): the inverse of `PiLp.continuousLinearEquiv 2 ℝ ...`. This is an actual
  continuous linear equivalence on the whole finite Pi carrier, including dimension zero.
  No choice fallback, special branch or junk value occurs.
- `p11lin` (L60): the finite sum of scalar multiples of coordinate projections, exactly
  `v ↦ ∑ i, c i*v i` on the whole carrier; the empty-dimensional case is the zero functional.
- `p11const` (L67): the continuous linear map r↦(fun _ : Fin 1 => r), exactly on all scalars.

**N1 — Public bridge, rather than private implementation.** The handoff calls `p11toE` a
“private-use helper” and says “no statement mentions it”. It is actually public under the
file's public section, and L33, L333, L358–381 expose it and/or `PiLp 2` in helper statements.
`PiLp 2 (fun _ : Fin n => ℝ)` is the same L2 model underlying Mathlib's `EuclideanSpace` alias.
Thus the lint's absence of the forbidden token alone does not settle a broader owner policy
against that mathematical carrier.

The main exported source estimates still use only `Fin n → ℝ`; their Euclidean gauges are
unchanged. No norm instance is installed on that carrier. I found no mathematical or
meaning-changing norm error in the bridge, and the design expressly forbids changing the
ambient Pi norm, which this implementation respects. The note is therefore not a proof
failure. The handoff should describe the bridge as public; making these bridge-only helpers
private would match its stated intent. If the owner interprets rule 7 to forbid even auxiliary
L2 transport wrappers, this implementation needs a direct tensor-product proof instead.
This audit does not invent permission to waive that broader interpretation.

## Hygiene and independently rerun checks

The build, scratch probe, kernel replay and final lint rerun explicitly used
`LEAN_NUM_THREADS=1`. No heartbeat, recursion-depth or
synthesis override was supplied. No clean, cache update, root regeneration, git mutation,
provider edit or frozen edit occurred.

**Operational deviation:** I initially started `sh scripts/lint_sources.sh` while the targeted
build was waiting on the compile gate. The lint script invokes `lake env lean` internally
through `abi_hashes.py`; its execution could therefore overlap the subsequently admitted
build invocation. That first lint command also lacked an explicit `LEAN_NUM_THREADS=1` and
`nice` prefix. This did not follow the requested process controls.
I waited for both to finish before starting the signature/axiom probe, then waited for that
probe before kernel replay. No additional simultaneous audit Lean jobs were launched. This
scheduling mistake is reported explicitly; the mathematical check receipts below are not
claims of perfect process serialization. After kernel replay, lint was rerun alone with both
`LEAN_NUM_THREADS=1` and `nice -n 5`; the final lint receipt below is from that rerun.

Targeted build:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11aw1 KAM.Planetary.WeakMeasure.Stability
[inp-gate] slot 2 acquired 09:21:02 for KAM.Planetary.WeakMeasure.Stability
⚠ [9050/9050] Replayed KAM.Planetary.WeakMeasure.Stability
Build completed successfully (9050 jobs).
exit 0
```

Warnings only: unused `hn` at L302, `hK` at L304 and `hn` at L403, all retained from the
verbatim design signatures. The reported job count is Lake's dependency/replay count,
not evidence of a clean library rebuild; no clean or full-library build was requested.

Scratch probe:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AW1Audit.lean
exit 0
```

This passed both fresh-name signature/application checks, both `type_of%` checks, and the
sharper order-j stability specialization described above. It also ran `#print axioms` on
**all 29 new public theorems**. For every theorem in the ledger (except the private
`p11line_isOpen`, which is covered by replay), the output was exactly of the form:

```text
'KAM.Planetary.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

In particular:

```text
'KAM.Planetary.stability' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.M_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakMeasure.Stability KAM.Planetary.WeakMeasure.Basic
replaying KAM.Planetary.WeakMeasure.Basic
replaying KAM.Planetary.WeakMeasure.Stability
exit 0
```

Lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (509 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The stale generated-root line is the sole lint failure and is explicitly permitted by this
audit brief. The root was left untouched. A separate Python Unicode-character check found
453 source lines, zero lines exceeding 100 characters, and no forbidden token or `set_option`.
Module header, copyright, public imports, docstring, exposed public noncomputable section
all satisfy the module conventions. All three definition bodies are exposed by that section.

Import closure over project modules is exactly `Stability`, `Basic`,
`KAM.Nekhoroshev.Interfaces.Norms`, `KAM.Fourier.Derivative`; there are no frozen or provider
imports. Consequently no DRAFT_SORRY module or unsealed dependency enters these results,
and there is no imported frozen manifest state requiring a SEALED ruling.

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(no output; exit 0)
git diff --check inp...HEAD
(no output; exit 0)
```

## Defects, uncertainty and handoff boundaries

No new suspected pinned-source or blueprint mathematical defect was found in this scope.
The public/private discrepancy and auxiliary-carrier policy question are N1 above; no source
hypothesis, constant dependence, carrier of a source estimate, or conclusion was silently
changed. The design-audit history's unrelated preparation/chart findings are not reopened by
this W1 audit. The proof of rank_compact and later weak-measure/KAM consumers remain outside
this package verdict.

Only this report is a persistent audit edit. The audit probe is deleted after its checks.
The pre-existing untracked P11A-W1-handoff.md is retained unchanged.
