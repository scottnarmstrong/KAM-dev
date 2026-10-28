# Independent audit: P11A-C2

Audit date: 2026-10-28. Auditor did not author the package.

Overall verdict: **PASS WITH NOTES** for the C2 helper package. Both public exports pass all required semantic and kernel checks; the notes are inherited C1 deprecations and the explicitly allowed generated-root staleness.
No anchor is claimed seal-ready: this package contains no provider or frozen theorem.

## Scope and pinned evidence

Target: `/root/code/KAM-inp-p11ac2`, HEAD `50589b77ac0c129e2e609a4e946d41b351763b16`.
Comparison `inp` = `722ad4a37de68b025a0c690051afff665dcb1176`; C1 = `001688bedc2fb21dc7e9585d5ccd9c601895f489`.
Both `git diff inp...HEAD` and `git diff inp-p11ac1...HEAD` add only
`KAM/Planetary/MaximalStep/Loss.lean` (201 lines). The supplied handoff is pre-existing untracked input.
The user's exact report-path instruction overrides the common brief's default main-worktree destination.

Read AGENTS.md, PLAN, DECISIONS, the package audit brief, handoff AUDIT FOCUS,
track-P statement, P11A design row C2 and appendix, all three design-audit reports,
and blueprint `blueprint-P/parts/p11a2-cutoff-step.tex` L42–92.
The local `.drafts/design/P11ASignatures.lean` is absent; the actual delivered file is
`/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`.
Both public theorem signatures are byte-identical, through the text before `:=`, to that
file L239–256 and the design appendix L1182–1199. The latest design audit's hash matches.

| Input | SHA-256 |
|---|---|
| Loss.lean | `c4f4bd157835999d3be9e7dfda21f026c19b67ed3ebcb6ddeee1def1f5ac66ef` |
| P11A-LEAN-DESIGN.md | `8619ea896c856347a9a5c5efac5080f0c830ea19245320b5f03a2b4267a300b9` |
| Delivered signatures | `c31fda0b479f2dd0488b12e7f2daeda18f965eb316610df1c65f14012dfcb092` |
| p11a2-cutoff-step.tex | `990694a832aa02dca0138c5cbb3bab842984583f4ca92576479eff04786ed3ec` |

No frozen theorem/provider is supplied by C2. Provider=frozen-type and frozen seal-body
checks are therefore N/A. Exact design-type application probes cover both exports instead.
No frozen anchor, planetary headline, or full Fourier-cutoff theorem is certified by this package.

## Declaration and node review

Names below are in `KAM.Planetary`; line numbers refer to Loss.lean.

| Node / responsibility | Declaration | Semantic verdict | Reason |
|---|---|---|---|
| Auxiliary logarithm lower bound | private `one_lt_log_piT`, L27 | PASS | Derives `1 < log(πT)` from `T ≥ 1`, `π > 3 > e`. |
| Auxiliary constant logarithm | private `log_two_c_pos`, L35 | PASS | Uses the proved C1 `p11C_ge_one`, positive alpha and alpha ≤ 1. |
| `stepP:p11a:lc-mono` | private `loss_anti_aux`, L43; public `loss_choice`, L113–124 | PASS | Finite-difference proof via log(v/u) ≤ v/u−1, followed by alpha log monotonicity. Its auxiliary inequality is proved at the call site, never assumed by the public theorem. |
| `stepP:p11a:lc-exponent` | inline in `loss_choice`, L69–91 | PASS | Establishes positivity and πTd = log(2c/alpha)+n log(πT), with the exponent > 1. |
| `stepP:p11a:lc-estimate` | inline in `loss_choice`, L85–112 | PASS | Exact exponential identity and reciprocal-power bounds give error ≤ alpha. |
| `bpP:p11a:loss-choice` | `loss_choice`, L62 | PASS | Exact signature: positivity, conditional error bound, both AntitoneOn conclusions. |
| `bpP:p11a:loss-sum` | `loss_sum`, L126 | PASS | Exact pointwise and infinite-sum bounds, with explicit Summable conclusion; constants have exactly the designed dependence. |

All new public declarations are the two listed theorems. There is no new public or private
`def`, `abbrev`, `structure`, instance, premise bundle or choice-defined object.

### Expanded public binder classification

SOURCE references: choice = blueprint L70–75; sum = L84–89, with the standing dimension N ≥ 1
from L43/70. TYPING references: natural dimension and real scalar/sequence carriers in those same statements.
No project-owned hypothesis alias or typeclass hides additional inputs.

| Theorem | Binder | Bin | Exact meaning / source |
|---|---|---|---|
| loss_choice | `{n : ℕ}` | TYPING | Dimension, choice L71. |
| loss_choice | `hn : 1 ≤ n` | SOURCE | N ≥ 1, L71. |
| loss_choice | `{alpha : ℝ}` | TYPING | Real alpha, L71. |
| loss_choice | `{T : ℝ}` | TYPING | Real cutoff, L71. |
| loss_choice | `ha : 0 < alpha` | SOURCE | L71. |
| loss_choice | `ha1 : alpha ≤ 1` | SOURCE | L71. |
| loss_choice | `hT : 1 ≤ T` | SOURCE | L71. |
| loss_sum | `{n : ℕ}` | TYPING | Same dimension as choice. |
| loss_sum | `hn : 1 ≤ n` | SOURCE | Standing N ≥ 1, L43/70. |
| loss_sum | `{theta : ℝ}` | TYPING | Geometric factor, L85. |
| loss_sum | `{T0 : ℝ}` | TYPING | Initial cutoff, L85. |
| loss_sum | `{a : ℝ}` | TYPING | Log envelope constant, L85. |
| loss_sum | `{b : ℝ}` | TYPING | Log envelope slope, L85. |
| loss_sum | `ht : 1 < theta` | SOURCE | L85. |
| loss_sum | `hT : 1 ≤ T0` | SOURCE | L85. |
| loss_sum | `ha : 0 ≤ a` | SOURCE | L85. |
| loss_sum | `hb : 0 ≤ b` | SOURCE | L85. |
| loss_sum | `alpha : ℕ → ℝ` | TYPING | Sequence indexed from zero, L85–86. |
| loss_sum | `hap : ∀ j, 0 < alpha j ∧ alpha j ≤ 1` | SOURCE | Both source inequalities, at every natural j, L85. |
| loss_sum | `hlog : ∀ j, log(2*p11C n/alpha j) ≤ a+b*j` | SOURCE | Source envelope at every natural j, L85. |

Counts: choice SOURCE 4, STANDING 0, TYPING 3, RULED 0, EXCESS 0;
sum SOURCE 7, STANDING 0, TYPING 6, RULED 0, EXCESS 0.
The `d_T ≤ 1` guard is inside the conclusion, not an input assumed for positivity or monotonicity.
All remaining binders inside conclusions are the intended universal comparison points/indices.

### Definition classification and totality

No new definitions require classification. The three existing meaning-carrying definitions
in `Constants.lean` L26–32 were checked directly against blueprint L44 and L72:

| Existing definition | Classification | Body/carrier/use assessment |
|---|---|---|
| p11C | Literal dimension constant | Exact `2(1+1/π)(3n/(eπ))^(n−1)`; n−1 is natural subtraction. C2 uses n ≥ 1 and C1's proved bound. |
| p11Error | Literal error formula | Exact `c_n(1+(d^n)⁻¹)exp(−πTd)`; C2 supplies strictly positive d. |
| p11Loss | Literal logarithmic formula | Exact `[log(2c_n/alpha)+n log(πT)]/(πT)`; alpha > 0, T ≥ 1 and c_n ≥ 1 protect every used logarithm and denominator. |

For each: BODY_MATCH OK; PUBLIC_CARRIER OK for this inherited literal real formula;
WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A;
DEFINITION_VERDICT PASS for its use here. Standard total real log/inverse values outside the
source-positive locus are never used to discharge a theorem. No invented fallback or chosen witness occurs.

### Independent proof review

Let u = πT and A = log(2c_n/alpha). The proof has u > 3, log u > 1 and A > 0.
Thus d = (A+n log u)/u > 0 and ud > 1. It rewrites
`exp(−ud) = alpha/(2c_n) * (u^n)⁻¹`, then bounds each of `(u^n)⁻¹` and
`(d^n)⁻¹*(u^n)⁻¹ = ((ud)^n)⁻¹` by 1. Consequently the error is at most
`alpha/2*(1+1)`. This route actually does not need the introduced `hd : d ≤ 1`;
that is a sound strengthening of the proof, with the designed interface preserved.

For T-antitonicity the private helper derives the finite-difference inequality from
`log(v/u) ≤ v/u−1` and `n ≤ A+n log u`; the call proves this last condition from
A > 0 and log u > 1. Alpha-antitonicity follows from decreasing `2c_n/alpha` and log monotonicity.
The blueprint says “decreasing”; the audited design explicitly chooses non-strict AntitoneOn,
which is exactly what the implementation exports. No strict-antitone export is claimed.

For the schedule, logarithm splitting gives the displayed numerator. Set
A0 = a+n log(πT0), B0 = b+n log theta, r = theta⁻¹ ∈ (0,1).
The majorant is `(A0+B0*j)*r^j/(πT0)`. The proof establishes its summability using both
geometric and arithmetico-geometric series, bounds the positive losses by it, and invokes
`tsum_le_tsum` only with both summability proofs. The exact sums are
`theta/(theta−1)` and `theta/(theta−1)^2`. No nonsummable-tsum-zero artifact occurs.

## Verification receipts

All audit-owned Lean/Lake invocations were serial and used `LEAN_NUM_THREADS=1` and `nice -n 5`.
No clean, update, cache fetch, dependency mutation or state-changing git command was used.

1. Targeted gated build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ac2 KAM.Planetary.MaximalStep.Loss
   [inp-gate] slot 2 acquired 12:10:54 for KAM.Planetary.MaximalStep.Loss
   Build completed successfully (9088 jobs).
   exit 0
   ```

   The gate executes `nice -n 5 lake build`. This was an incremental targeted build;
   the reported job count is Lake's dependency traversal, not a clean rebuild.
   It replayed five inherited deprecation warnings in FourierCutoffTail.lean:
   `if_pos` at 71:8, 177:24, 179:70; `if_neg` at 206:24, 207:33.
   No Loss.lean warning or default-heartbeat failure occurred.

2. Exact-type application and axiom probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AC2Audit.lean
   'KAM.Planetary.loss_choice' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.audit_loss_choice' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.loss_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.audit_loss_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
   exit 0
   ```

   The probe imported Loss, copied each exact signature from the delivered R3 file,
   renamed it `audit_loss_choice` / `audit_loss_sum`, and replaced its draft body by
   `by exact loss_choice hn ha ha1 hT` /
   `by exact loss_sum hn ht hT ha hb alpha hap hlog`, respectively.
   Thus it checks the intended full application with every explicit binder in order,
   rather than checking only declaration existence. No signature draft was imported.

3. Kernel replay, a single invocation covering the sole new module:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.MaximalStep.Loss
   replaying KAM.Planetary.MaximalStep.Loss
   exit 0
   ```

4. Source lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (555 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The sole failure is exactly the generated-root exception authorized by the common
   audit brief. All other checks pass. KAM.lean was not regenerated or edited.

5. Static/integrity checks:

   - `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
   - `git diff --check inp...HEAD` and `git diff --check`: empty, exit 0.
   - Loss.lean: 201 lines; copyright, `module`, public imports, module docstring and
     `@[expose] public noncomputable section` all present. No forbidden declaration,
     sorry/admit, resource override, unsafe/opaque or EuclideanSpace use.
   - Recursively checked all 42 project modules in its import closure: no provider,
     no frozen theorem, and ten frozen definition modules, each manifest state SEALED.
     Therefore no DRAFT_SORRY import is hidden transitively.
   - The only project definitions in the public types are the three literal constants
     reviewed above. No conclusion-shaped premise, bundled result or hidden instance.


## Source defects, deviations and limitations

No suspected blueprint/source defect was found in the audited loss nodes. No production change
or source correction was introduced. The alternate elementary error proof and finite-difference
monotonicity proof are equivalent/stronger proof routes, not statement deviations.
The special exponentially decaying alpha example in blueprint L87 is a consumer specialization;
the theorem supplies its general envelope form, as designed. No downstream composition or
frozen-root closure is claimed.

## Final disposition and workspace integrity

- `loss_choice`: **PASS** against the accepted exact design signature and blueprint loss-choice node.
- `loss_sum`: **PASS** against the accepted exact design signature and blueprint loss-sum node.
- Package: **PASS WITH NOTES**, ready for integration as helper infrastructure; frozen-anchor sealing N/A.
- No unresolved mathematical uncertainty, suspected erratum or introduced statement deviation was found.
- Only this report was written outside the permitted ABI scratch directory. The temporary exact-type/axiom
  probe was deleted. The pre-existing untracked handoff remains untouched; production and protected paths
  are unchanged. Final whitespace checks pass.

No test receipt here is borrowed from the prover: build, probes, axioms, kernel replay and lint were
independently rerun in this worktree. The earlier audit memory was used only as a workflow reminder;
all package facts and verdicts were checked against current files and fresh command output.
