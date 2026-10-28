# Independent package audit N10-1, round 1

Overall verdict: **PASS WITH NOTES** for N10-1. No material findings.
The only hygiene note is the expected generated-root mismatch. This package is ready
for downstream assembly; it does not prove or make any frozen anchor seal-ready.

Per-anchor status: **N-HEAD-C is not proved by this package**. No provider theorem is
included in the scoped diff, so a seal-readiness verdict for that anchor is inapplicable.

## Scope and authority

Audited only `KAM/Nekhoroshev/Assembly/Choice.lean` at HEAD
`3929ba23e1f85b4e5454f1a5f259c2c9188ea01c`, comparing `git diff inp...HEAD`
(`inp` initially observed at `fc9999550e1af9ee704bf1c7032361475a2bc0de`, subsequently
at `d030f8799fbc9a4c5e23582162b9bd844fa49574`; shared branch advanced during this audit).
The three-dot comparison was rechecked; merge base is
`64bb192e84b482a5b32b3233897a21a993f42e99`. The diff is exactly one
new file, 161 insertions. Read AGENTS.md, PLAN, DECISIONS, the package audit brief,
N10-1 handoff and AUDIT FOCUS, N10-LEAN-DESIGN (especially row N10-1 and Appendix A),
and DESIGN-N10-design-audit-1. Compared against blueprint-N Part 10, the track-N
statement and the frozen N-HEAD-C theorem and its predicates.

The user's exact report destination inside this worktree overrides the generic brief's
main-worktree destination. No source, frozen file, manifest, generated root, README,
or git state is modified by this audit. Pre-existing untracked N10-1-handoff.md is preserved.

This is an arithmetic infrastructure package. It contains no provider export and proves
no frozen anchor. Provider/frozen-type equality and seal-body probes are consequently
not applicable; N-HEAD-C remains outside the package's proof-closure claim.

## Declaration and blueprint fidelity

All names below are in `KAM.Nekhoroshev`; line numbers refer to Choice.lean.
The eight definition bodies and five public theorem signatures are byte-identical to
Appendix A. Appendix A is byte-identical to the canonical
`/root/code/KAM-inp/.drafts/design/N10Signatures.lean`, SHA-256
`22021dd133e9ee9b787f52fae98bed1f544f960de5a83ec3ba891c62fb413bfe`.

| Node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| bpN:p10:choice | HeadParams.s1 (28) | PASS | Geometric strip width s/2. |
| bpN:p10:choice | HeadParams.F1 (29) | PASS | Existing coth(pi*s/4)^n; no 2*pi factor. |
| bpN:p10:choice | HeadParams.eps1 (30) | PASS | Exactly mu*r0^2/(2^10*A^(2*n)). |
| bpN:p10:choice | HeadParams.R0 (31) | PASS | Exactly r0/A. |
| bpN:p10:choice | HeadParams.epsPrime (32) | PASS | Exactly F1*epsilon. |
| bpN:p10:choice; confinement time | HeadParams.tau (33) | PASS | Exactly T*exp(c*epsilon^(-a)), a=1/(2n). |
| bpN:p10:choice; confinement radius | HeadParams.rho (35) | PASS | Exactly C*epsilon^a in the existing real scalar carrier. |
| bpN:p10:choice; hd-order, hd-dep | choice (38) | PASS | Four existing constants depend only on p and its dimension index. |
| bpN:p10:choice-props(a,b); cp-ab; hd-const | choice_props (41) | PASS | Positivity, headline margin, mu<=B, A>=22 and all four radius bounds. A=11*B/mu and R0=r0/A are definitions. |
| Private positivity support | eps1_pos (55) | PASS | Positive numerator and denominator under hp and n>=1. |
| Private positivity support | F1_pos (63) | PASS | Positive coth power from s>0. |
| Private dictionary support | epsStar_eq (68) | PASS | Exact algebraic identity, no added premises. |
| Private dictionary support | F_eq (72) | PASS | Exact algebraic identity, no added premises. |
| bpN:p10:choice-props(c); cp-dict | cp_dict (77) | PASS | Both 2*pi identities, unrestricted-epsilon equivalence, and positive-smallness implication. |
| bpN:p10:choice-props(c); cp-rad | cp_rad (95) | PASS | Exact half-radius and exponent identities; epsilon positivity retained. |
| bpN:p10:choice-props(d); cp-size; ex-rho | cp_size (124) | PASS | Radius bound with additional valid radius/time positivity. |
| stepN:p10:hc-time, arithmetic component | head_time_prefactor (139) | PASS | Positive scalar Omega<=sqrt(n)*M implies the required 2T bound. It does not assume a dynamical conclusion or define a maximum. |

The signatures preserve binder order, source premises, norms and numerical factors.
No constant depends on h, f, epsilon, initial data, or the existential holomorphic-value
bound in IsAnalyticIntegrable. HeadParams has six real fields plus the dimension index;
Pos contains only their positivity. No hard analytic step is hidden in a hypothesis.

For cp_rad, cancelling positive 2*pi gives F*epsilon/epsStar=epsPrime/eps1
and its inverse ratio. The reused const_conclusion then gives exactly rho/2 and the
claimed exponent; s0=pi*s=2*pi*s1. The time helper applies const_time_arith to
2*pi*Omega, proves sqrt(n)<=n, and cancels 2*pi. Equivalently,
2T=A^2*s/(2*n*M)<=A^2*s1/Omega. This is a numerical estimate, not a
claim that an actual Part-9 maximum has already been bounded or attained.

## Definition classification

All eight new definitions are exposed numerical definitions, not predicates, bundled
assumptions, structures or instances. s1, F1, eps1 and R0 are precisely the Theorem-1
data; epsPrime is its perturbation-size majorant; tau and rho are the proposed
headline time and radius; choice packs the four existing constants.

Their bodies implement the stated formulas on the whole carrier. Lean division and
real powers are total outside the positive parameter region, but no theorem relies on
such values: n>=3 and p.Pos supply the positive denominators, and cp_rad/cp_size
require positive epsilon. cp_dict's unrestricted-epsilon equivalence uses positive F1
and remains valid even for negative epsilon. No zero-size dynamical conclusion is
inferred from tau at epsilon=0. No fallback, divergent sum, inverse matrix or supremum
is introduced.

## Hygiene and independent validation

All commands below were run from `/root/code/KAM-inp-n101`. Lean invocations were
sequential, at niceness 5, with `LEAN_NUM_THREADS=1`. No heartbeat, recursion or
synthesis budget override, cache fetch, library-wide rebuild or cleanup was used.

1. Targeted build through the required compile gate:

   ```sh
   env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n101 KAM.Nekhoroshev.Assembly.Choice
   ```

   Exit 0, output:

   ```text
   [inp-gate] slot 1 acquired 05:55:25 for KAM.Nekhoroshev.Assembly.Choice
   Build completed successfully (2896 jobs).
   ```

   The wrapper invokes `nice -n 5 lake build`. Waiting for the compile gate was
   respected. No Lean warning was printed.

2. Independent signature/body/axiom probe:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/n101-audit/Probe.lean
   ```

   Exit 0. The probe imports only Choice, copies each of the five exact design
   signatures into an `example` with an explicit application of the implemented
   theorem, and checks all eight definition bodies by `rfl`. Its complete output:

   ```text
   'KAM.Nekhoroshev.choice_props' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.cp_dict' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.cp_rad' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.cp_size' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.head_time_prefactor' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay, one invocation for the sole scoped implementation module:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Assembly.Choice
   ```

   Exit 0, complete output:

   ```text
   replaying KAM.Nekhoroshev.Assembly.Choice
   ```

4. Full source lint:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1 solely for the generated-root mismatch explicitly allowed by the brief.
   Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (416 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No over-100-character line or other source violation was reported. KAM.lean
   was left untouched, as required. The ABI subprocess was slow under shared-host
   memory pressure but completed successfully; it was not retried or run alongside
   another auditor-started Lean process.

5. Mechanical/source checks: `git diff --check inp...HEAD` and `git diff --check`
   exit 0 without output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`
   is empty. Choice.lean has 161 lines, maximum width 99 Unicode characters,
   and the required copyright, module command, public import, module docstring,
   exposed public section and namespace endings. A comment-masked token scan found
   no prohibited proof escape, resource override or EuclideanSpace.

   The local KAM import closure contains 31 modules and no frozen theorem module
   or provider module. Thus there is no DRAFT_SORRY or provider dependency, directly
   or transitively; all frozen modules in this closure are definitions. There is
   no new provider whose imported theorem manifest state needs checking.

Temporary probe files were deleted after the checks. The only persistent auditor-authored
repository file is this report; the pre-existing handoff remains untouched.

## Findings, uncertainties, errata and deviations

No mathematical defect, additional source premise, weakened conclusion, widened
constant dependence, blueprint contradiction, or suspected frozen-statement defect
was found in this module. No new pinned-source erratum is asserted; this audit checks
the package against the supplied blueprint and design, and does not independently
re-audit the Pos93 scan or certify upstream analytic/Part-9 arguments.

The design audit's pending Part-9 reconciliation and later ODE/provider obligations
remain outside N10-1. Passing this numerical module does not discharge them or seal
N-HEAD-C. No implementation deviation or default-heartbeat design signal was found.
