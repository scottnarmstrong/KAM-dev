# SO-PI independent audit 1

**Verdict: PASS WITH NOTES.** The backend-independent SO-PI slice is complete and sound at the audited revision. All four signed declarations match exactly; the strict π and e enclosures and the advertised rational width bounds pass independent elaboration and kernel replay. Notes: the allowed stale generated-root lint exception, one unused-simp warning, and the documented downstream arithmetic wrapper. No frozen anchor is proved or sealed by this package.

## Scope and authority

- Worktree: `/root/code/KAM-inp-sopi`; branch `inp-sopi`.
- Audited HEAD: `dddf8f7b71315b70258c26ec0dfeb3a9db9343cc`.
- `inp` at initial comparison: `2dcaff9daa985bb46795fcefbf19a4c8cc773143`; merge base `836e8efe03c1f2e23422a12dd35058c9bc7101a6`.
- Full `git diff inp...HEAD` inspected: exactly one new file, `KAM/Certificate/Arith/PiHigh.lean`, 238 added lines.
- Source SHA-256: `0ee583ddcb69816240e0a38376de2819c71688941cc990f97f1dd00a1e907880`.
- Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, this worktree's `SO-PI-handoff.md`, and `/root/code/KAM-inp/.drafts/briefs/offload-main/SO-PI.md`.
- Controlling SO sources: `/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md` (O3), `/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md` (especially lines 63–68, 291, 488–509), and `/root/code/KAM-inp/.drafts/design/SOSignatures.lean:122–131`.
- The explicit user instruction controls the report destination: this report is inside the package worktree, overriding the generic audit brief's MAIN-inp destination.
- The requested audit is only PiHigh. There are no SO frozen anchors or I/N/P blueprint nodes implemented here, so provider-to-frozen-type and frozen seal-body tests are inapplicable. The four signed declarations instead receive exact source comparison plus fresh typed probes. The draft signature file is read as authority, never imported.

## Signed surface and declaration audit

All names below are in `KAM.Certificate`; line numbers refer to `KAM/Certificate/Arith/PiHigh.lean`. Each public declaration is covered. Private supporting declarations are included for proof review.

| Node / line | Declaration | Verdict | Reason |
|---|---|---|---|
| Signed coarse lower, 39 | `piLoQ` | PASS | Definition text exactly `def piLoQ : ℚ := 3141592 / 1000000`. |
| Signed coarse upper, 41 | `piUpQ` | PASS | Definition text exactly `def piUpQ : ℚ := 3141593 / 1000000`. |
| Signed lower proof, 43 | `piLoQ_lt_pi` | PASS | Exact signed type `(piLoQ : ℝ) < Real.pi`, no binders or extra premises. |
| Signed upper proof, 50 | `pi_lt_piUpQ` | PASS | Exact signed type `Real.pi < piUpQ`, including the inferred real coercion. |
| Arctan data, 60 | `atanS` | PASS | Exact rational sum over `range m`, including zero-length sums. |
| Arctan terms, 63 | `atanT` (private) | PASS | Unsigned real terms, positive denominator for every natural index. |
| Cast bridge, 65 | `atanS_cast` (private) | PASS | Rational-to-real sum identity. |
| Term decay, 69 | `atanT_strict` (private) | PASS | Strict decay under precisely `0 < x < 1`. |
| Term monotonicity, 81 | `atan_term_anti` (private) | PASS | Includes the valid `x = 0` boundary. |
| Series identity, 88 | `atan_tendsto` (private) | PASS | `Real.hasSum_arctan`, with its norm premise discharged from `0 ≤ x < 1`. |
| Even bound, 98 | `atanS_le` (private) | PASS | Even number of terms gives a lower bound. |
| Odd bound, 105 | `le_atanS` (private) | PASS | Odd number of terms gives an upper bound. |
| Strict even bound, 113 | `atanS_even_lt_arctan` | PASS | Next even partial sum is strictly larger, still below the limit. |
| Strict odd bound, 127 | `arctan_lt_atanS_odd` | PASS | Next odd partial sum is strictly smaller, still above the limit. |
| Machin lower, 144 | `piLowRat` | PASS | `16` times even sum minus `4` times odd sum. |
| Machin upper, 147 | `piUpRat` | PASS | `16` times odd sum minus `4` times even sum. |
| Machin lower proof, 149 | `piLowRat_lt_pi` | PASS | Universal in `k,j : ℕ`, including zero; strictness from the `1/5` term. |
| Machin upper proof, 160 | `pi_lt_piUpRat` | PASS | Same parameter domain and correct reversal for the negative `1/239` coefficient. |
| Certificate hook, 172 | `PiHighCert` | PASS | Rational endpoints and strict real containment proofs; no accuracy field claimed. |
| Width predicate, 179 | `piWidthOk` | PASS | Decides exactly the rational inequality, with `N : ℕ`. |
| Constructed witness, 183 | `PiHighCert.ofParams` | PASS | Fills both proof fields using proved universal bounds; no assumed enclosure. |
| 50-digit width, 191 | `piHigh_50` | PASS | Parameters `(18,5)`, rational width `≤ 1 / 10^50`, `decide +kernel`. |
| 100-digit width, 193 | `piHigh_100` | PASS | Parameters `(36,11)`, rational width `≤ 1 / 10^100`, `decide +kernel`. |
| 140-digit width, 195 | `piHigh_140` | PASS | Parameters `(50,15)`, rational width `≤ 1 / 10^140`, `decide +kernel`. |
| Exp partial sum, 200 | `eSum` | PASS | Exact rational Taylor sum through degree `n-1`. |
| Exp remainder, 203 | `eRem` | PASS | Exact `(n+1)/(n! n)` for positive `n`; see zero-input classification below. |
| Exp lower data, 205 | `eLowRat` | PASS | `eSum n - 2 * eRem n`. |
| Exp upper data, 207 | `eUpRat` | PASS | `eSum n + 2 * eRem n`. |
| Exp error estimate, 209 | `exp_one_sub_eSum` (private) | PASS WITH NOTE | Correct use of `Real.exp_bound`; one redundant simp argument at line 218. |
| Positive remainder, 220 | `eRem_pos` (private) | PASS | Requires `0 < n`; denominator is strictly positive. |
| Strict exp lower, 225 | `eLowRat_lt_exp_one` | PASS | Twice a positive error allowance makes the non-strict estimate strict. |
| Strict exp upper, 230 | `exp_one_lt_eUpRat` | PASS | Same strictness argument, correct upper side. |
| 30-digit exp width, 236 | `eHigh_30` | PASS | `n = 40`, rational width `≤ 1 / 10^30`, `decide +kernel`. |

The four signed source comparisons returned `True` individually. For definitions, comparison includes the entire body. For theorems, comparison includes the full declaration before `:=`; only proof bodies differ from the draft. The surrounding namespace matches. No signed `PiEnclosure` or `checkPiEnclosure` declaration is part of this explicitly scoped backend-independent slice; their later SO-ARITH implementation remains necessary.

## Definition classification and proof reasoning

`piLoQ` and `piUpQ` are exact rational constants. `atanS` is the intended finite sum for every rational input and every natural length; the convergence/bound theorems correctly restrict to `0 < x < 1`. Private `atanT` is the intended real unsigned term on its whole carrier, with denominator `2i+1` never zero. `piLowRat` and `piUpRat` are total finite rational expressions for all natural parameters; their strict enclosure proofs hold even at `(0,0)`.

`PiHighCert` is a proof-carrying enclosure object. Its fields `lo_lt` and `lt_hi` specify what a certificate is; no exported arithmetic theorem assumes an arbitrary certificate to bypass a proof. `ofParams` constructs both fields from proved lemmas. Neither the structure nor its constructor promises a particular width. `piWidthOk` is a computable Boolean predicate for the exact rational width inequality, not an added assumption in any theorem; a fresh probe proved its `= true` equivalence to that inequality.

`eSum`, `eRem`, `eLowRat`, and `eUpRat` are the stated rational expressions on their whole carriers. At `n = 0`, totalized rational division gives `eRem 0 = 0`, and both endpoints are zero. Fresh probes checked these facts. Such endpoints are not an enclosure of e, but both endpoint soundness theorems explicitly require `0 < n`, and the width instance uses `40`. No proof relies on an invalid fallback or an enclosure at zero.

For the arctan proof, Mathlib's local source `Analysis/SpecialFunctions/Complex/Arctan.lean:144–146` identifies the series with `Real.arctan`. The antitone-series theorems in `Analysis/SpecificLimits/Normed.lean:1007–1033` give even lower and odd upper partial sums. Strict decrease of unsigned terms makes consecutive even sums strictly increase and consecutive odd sums strictly decrease; the package compares with the next partial sum to obtain strict inequalities, including `k=0`.

Machin's identity in `Analysis/SpecialFunctions/Trigonometric/Arctan.lean:336` is `4 * arctan 5⁻¹ - arctan 239⁻¹ = π / 4`. Multiplication by four yields exactly the package's `16` and `-4` coefficients. Its negative coefficient correctly exchanges the upper/lower arctan choices. Only one strict component is needed for each strict π bound.

`Real.exp_bound`, in `Analysis/Complex/Exponential.lean:517–521`, bounds the absolute error of the `range n` Taylor sum by `|x|^n * (n.succ / (n.factorial * n))`. At `x=1` this is precisely `eRem n`. For `n>0`, `eRem n>0`; subtracting/adding twice that quantity gives strict containment. The 30-digit width is `4 * eRem 40`. There are no hidden instances, extra conclusions assumed as premises, norm changes, or parameter-dependent analytic constants.

The width theorems themselves state rational width inequalities only. Their analytic containment comes from the separate endpoint theorems. A fresh probe assembled the complete strict enclosure plus advertised width for both the 140-digit π instance and the 30-digit e instance. The module docstring's enclosure claims are justified by this combination.

## Independent checks

All commands ran from `/root/code/KAM-inp-sopi`, with at most one audit Lean/Lake/checker invocation active at a time. `LEAN_NUM_THREADS=1` and `nice -n 5` applied to every such invocation, including lint's ABI subprocess by inheritance. No provider or lemma module other than the single in-scope module needs building/replaying.

### Targeted compile gate

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sopi KAM.Certificate.Arith.PiHigh
```

Exit **0**. Output:

```text
[inp-gate] slot 1 acquired 11:26:30 for KAM.Certificate.Arith.PiHigh
⚠ [2839/2839] Replayed KAM.Certificate.Arith.PiHigh
warning: KAM/Certificate/Arith/PiHigh.lean:218:8: This simp argument is unused:
  Nat.succ_eq_add_one

Hint: Omit it from the simp argument list.
  [apply] simp [div_eq_mul_inv]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (2839 jobs).
```

This is the required targeted build on the existing overlay, not a clean library rebuild. No warning-suppression option was set. The warning differs from the handoff's “no warnings” receipt but does not affect the proof.

### Fresh signature, enclosure, axiom, and timing probe

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOPIAudit1.lean
```

Final exit **0**. The scratch probe imported only `KAM.Certificate.Arith.PiHigh`, checked the signed rational bodies with `rfl`, checked both exact signed proposition types, and independently assembled strict enclosure/width conjunctions. It also checked the Boolean width meaning and zero-input exponential definitions. No frozen anchor or draft signature file was imported. The probe was deleted after validation.

An initial probe run exited 1 because the auditor used `rfl` to prove the three zero-input rational equalities. Replacing those probe-only proofs with `norm_num` over the explicit definitions made the final run pass. This was a probe elaboration error, not a package failure; no package source changed.

For **each** of the following 24 explicit public source declarations, the command `#print axioms KAM.Certificate.<name>` produced exactly `depends on axioms: [propext, Classical.choice, Quot.sound]`:

```text
piLoQ                    piUpQ
piLoQ_lt_pi              pi_lt_piUpQ
atanS                    atanS_even_lt_arctan
arctan_lt_atanS_odd       piLowRat
piUpRat                  piLowRat_lt_pi
pi_lt_piUpRat            PiHighCert
piWidthOk                PiHighCert.ofParams
piHigh_50                piHigh_100
piHigh_140               eSum
eRem                     eLowRat
eUpRat                   eLowRat_lt_exp_one
exp_one_lt_eUpRat        eHigh_30
```

This includes every public theorem and all explicitly declared public definitions/structures. No `sorryAx`, `Lean.ofReduceBool`, or nonstandard axiom appears.

The probe re-proved all four width statements using `by decide +kernel`, with only `set_option profiler true in` (no resource overrides). Final successful run, in declaration order:

| Fresh width proof | Profiler output |
|---|---|
| `audit_pi50` | `type checking took 856ms` |
| `audit_pi100` | `type checking took 1.16s` |
| `audit_pi140` | `type checking took 1.78s` |
| `audit_e30` | `type checking took 1.84s` |

Cumulative `type checking 5.63s`. These are fresh kernel type-checking measurements, not numerical evaluation or native-code timing. The initial probe run also completed the four width evaluations, at 389ms, 905ms, 1.48s, and 1.54s respectively; timing variation is expected.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Arith.PiHigh
```

Exit **0**. Complete output:

```text
replaying KAM.Certificate.Arith.PiHigh
```

### Source hygiene and integrity

- Every import is a `public import Mathlib...`; there are no project imports, provider imports, or frozen theorem imports, hence no quarantined/DRAFT_SORRY dependency.
- The new file has copyright, `module`, a module docstring, `@[expose] public section`, and the intended namespace. Its definitions are exposed for downstream unfolding.
- 238 physical lines; maximum line length **95 Unicode characters**; both size limits pass.
- A scan of the full in-scope source found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `native_decide`, `EuclideanSpace`, `Lean.ofReduceBool`, or `set_option` of any kind.
- All 24 explicit public declaration short names were searched as complete tokens through every other `KAM/**/*.lean`; **no occurrences** were found. A corresponding Mathlib declaration-name search found no matching unqualified declaration. All package declarations are inside `KAM.Certificate`; no root declaration or open-scope alteration is introduced. Generated structure projections/recursors remain qualified under their structure.
- `git diff --check inp...HEAD`: exit **0**, no output.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit **0**, empty output.

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the expressly permitted stale generated-root diagnostic. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1283 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No other lint failure occurred. The generated root was left untouched.

## Notes, uncertainties, and source defects

1. **Permitted generated-root exception.** The audit brief expressly permits only the stale `KAM.lean` lint diagnostic. The generated file was not edited or regenerated.
2. **Minor proof warning.** `PiHigh.lean:218` contains the unused simp argument `Nat.succ_eq_add_one`. This is a style/maintenance note; no audit source edit was made.
3. **Downstream interface remains open by scope.** `PiHighCert.ofParams` supplies exact rational endpoints and proofs. Conversion to the backend `PiEnclosure`, its width/radius validation, and connection to the general certificate checker belong to SO-ARITH. This package supplies the stated hook and does not establish checker soundness, lunar confinement, any frozen I/N/P theorem, or consumer integration.
4. **Design scheduling is superseded explicitly.** SO-LEAN-DESIGN revision 1 line 291 says `SO-PI | W1 (optional) ... | SO-ARITH`, and line 505 calls the Machin package optional. Owner ruling O3 and the package-specific offload brief explicitly authorize the backend-independent core now. This is a documented scheduling/interface split, not a silent deviation or mathematical source defect.

No suspected mathematical erratum was found in the pinned/local source statements used by this module. No introduced deviation, changed hypothesis, or unproved analytic attachment was found within the requested SO-PI slice. Timing measurements depend on host load; no universal performance guarantee is inferred.

Only this report was written in the repository; the pre-existing untracked handoff was preserved. Temporary audit probes were confined to `.lake/abi-scratch/` and removed. No state-changing git operation, frozen/manifest edit, generated-root edit, dependency update, or cache operation was performed.
