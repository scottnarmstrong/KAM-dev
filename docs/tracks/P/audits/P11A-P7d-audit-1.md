# P11A-P7d independent package audit 1

Audit date: 2026-10-29 UTC. Auditor: Codex. Scope: the five files specified by
`P11A-P7d-handoff.md`, read against `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`,
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the track-P statement,
`docs/tracks/P/design/P11A-LEAN-DESIGN.md`, the external signed
`/root/code/KAM-inp/.drafts/design/P11ASignatures.lean:979-1044`, and
`blueprint-P/parts/p11-cp09-preparation.tex:170-185`.

## Verdict and revision boundary

**PASS WITH NOTES for the signed slow-averaging package**. See the independent
validation receipts below. No frozen theorem anchor is proved or sealed by this
package: provider/frozen-type equality and a frozen seal-body probe are inapplicable.
The signed `avg_slow` result is infrastructure for P-FIXED, not closure of that headline.

The task started at `01c51946`; another actor merged P7cb during the audit, advancing
HEAD to `7cd373f3f8f5e7de6ade7d8d7cf1bb3d63651dc6`. The author then adapted
`SlowAssembly.lean` to P7cb and committed it as final audited HEAD
`11a05936187b0e9191a65fbbab67b3ba7ea89048`. The auditor did not make that edit
or any git state change. The exact source hashes below, including the 207-line
assembly, were verified unchanged across the independent final build, probes,
kernel replay and the author commit. The initial build is not used as the final
receipt for the updated assembly.

`git diff inp...HEAD` was inspected with Git's warning:
`multiple merge bases, using 3fcfb654e1e10a82cc4ab57401156fc446225ce1`.
The final comparison was repeated with `inp` at
`a2464f937a8b578ae414ec08331359284ec94a78`; it contains 26 files and 5147 added lines, including inherited
P7/P7b/P7c implementation and audit files. The five-file focus and the author
adaptation diff were inspected separately. The protected-path comparison is empty.
The initially untracked handoff was left untouched.

## Node and declaration review

All names below are in `KAM.Planetary`; file locators omit
`KAM/Planetary/Preparation/`.

| Node / role | Declaration or export | Verdict | Reason |
|---|---|---|---|
| as-concl, torus integration | `p11_torusAverage_natAdd` (`SlowCoeff:31`) | PASS | Measure-preserving append equivalence, product restriction and unit-cube volume establish the identity for arbitrary `g`; no integrability premise added. |
| as-concl, zero mode | `p11_slow_coeff_zero` (`SlowCoeff:53`) | PASS | Exact cancellation of the polar `G` mean; residual zero mode bounded by `(eps * MF)^3` using the fast identity and native domains. |
| as-nr, scalar bracket | `p11_C_norm_le` (`SlowMW:29`) | PASS | Fast mean at zero, working-domain bound and coth factor at least one give `norm C(J) ≤ MF`. |
| as-nr, uniform constant | `p11SlowMW` (`SlowMW:53`) | PASS | Explicit bound depending only on secular data and dimension. |
| as-nr, positivity | `p11SlowMW_nonneg` (`SlowMW:56`) | PASS | Derived from secular standing constants. |
| as-nr, bracket bound | `p11_slow_MW` (`SlowMW:61`) | PASS | Bounds constant, linear and Z terms on the full Z domain; uses `eta1 ≤ 1`. Its smallness/domain premises are discharged in assembly. |
| as-b2 and smallness | `p11_slow_eventually` (`SlowAssembly:35`) | PASS | Derives all eventual inequalities, including P7cb's stronger `/4` Cauchy smallness, from secular data and `1 ≤ nu`; no assumed limiting estimate. |
| avg-slow constants | `p11SlowAsmC` (`SlowAssembly:75`) | PASS | Maximum of `c0` and the three exact conclusion constants; no epsilon dependence. |
| avg-slow assembly helper | `p11_slow_at` (`SlowAssembly:83`) | PASS | Explicit conditional helper; its oscillation and smallness inputs are supplied by proved lemmas in the final core. |
| avg-slow parametric core | `avg_slow_of_spec` (`SlowAssembly:182`) | PASS | Only secular specification, `1 ≤ nu`, positive fast threshold and fast specifications below it. Existential output has the full parametric spec. |
| signed spec | `P11SlowSpec` (`SlowSigned:26`) | PASS | Exact signed definition, whitespace aside; kernel-checked definitional equality to the parametric spec. |
| bpP:p11:avg-slow | `avg_slow` (`SlowSigned:90`) | PASS | Exact signed type, same binder order and no added premise; uses `holo_chart`, `avg_fast` and the core. |
| signed constant | `p11SlowConstant` (`SlowSigned:102`) | PASS | Exact signed choice and fallback, including the dependence on `D, nu` only. |
| signed selected datum | `p11SlowData` (`SlowSigned:105`) | PASS | Exact signed choice/default body; the successful branch is proved available on a common positive epsilon interval. |
| stepP:p11:as-osc | `p11_slow_osc`, assembled `o1`–`o12` | PASS | Imported P7b output supplies the identities, Z holomorphy and jets, reality, periodicity and weighted perturbation bound. Underlying pointwise oscillation estimate is exported by the facade's dependency closure. |
| stepP:p11:as-nr | `p11_slow_divisor`, local `hdiv0`, `hdiv` (`SlowAssembly:136-152`) | PASS | Merged P7cb gives pure-slow `3 eps delta0/4` and mixed `delta0/2`. Assembly derives the stronger smallness, retains that result as `hdiv0`, then weakens it to the signed quarter bound. |
| stepP:p11:as-b2 | `p11_slow_eventually`, local `hb2'` | PASS | Actual final `c2` enters the eventual estimate; the definition of K2 rewrites the literal B2 bound. The averaging application checks its kappa threshold. |
| stepP:p11:as-concl | `p11_slow_coeff_zero`, `p11_slow_conclude`, local `hU` | PASS | Mean coefficient bound, averaging output, correction and displacement bounds all supplied; no mean estimate assumed in the final core. |
| public facade | `Slow.lean` | PASS | Re-exports the proved modules, including signed wrappers; no duplicate declarations. |

The design node table at `P11A-LEAN-DESIGN.md:171-175` maps exactly the avg-slow
node and the four steps above to `Preparation/Slow`. All five are accounted for.
The P7cb correction is necessary for this completeness verdict. The old quarter-only
unsigned divisor statement would not have established the literal mixed-bound step.

## Clause trace and premise audit

The actual signed spec has 26 outer conjuncts (the last contains three displacement
bounds). Informal clause numbers in inherited comments/handoffs are not the contract.

- Conjuncts 1–3: `o1`, `o2`, `o3` restricted using `p11SlowBox_subset_avg`.
- Conjunct 4: `o4`, with the full Z domain unchanged.
- Conjunct 5: `o6` and monotonicity from `c0 ≤ c2`, including nonnegative jet factors.
- Conjunct 6: `hdiv0` from P7cb, weakened to `hdiv` for the exact signed conclusion.
- Conjuncts 7–26: the full `hU` returned by `p11_slow_conclude`, including all
  differentiability, reality, periodicity, symplecticity, lattice equivariance,
  injectivity, maps-to, weighted bounds, B2, Hamiltonian identity and displacements.

`avg_slow_of_spec` obtains `c0` and an oscillation threshold from `p11_slow_osc`;
chooses one `c2 = p11SlowAsmC C nu c0`; obtains eventual smallness with that constant;
and takes the minimum of the resulting positive radius, the oscillation threshold,
the fast threshold, and `1/2`. Thus every input to `p11_slow_at` is derived.
Neither the final core nor its signed wrapper assumes an oscillation output,
a divisor bound, an averaging transformation or a conclusion-shaped bundle.
The conditional helper has a distinct name and is not substituted for the final result.

The omission of `P11SecularHReal` is valid. `p11_slow_osc` takes only `hC`; the
reality inputs used by the assembly come from its proved outputs. Moreover
`FastSigned.lean:26-31` derives `P11SecularHReal` from `P11SecularSpec` for the fast
stage, so it is not an extra unavailable premise hidden in the signed wrapper.

The signature deliberately stores quarter-sized divisor bounds. The literal
half-sized mixed bound is nonetheless proved before weakening. Current consumers
in this package (`p11_slow_conclude`, the signed wrapper and the choice definitions)
need only the signed bound. No claim is made that unimplemented later consumers or
the frozen P-FIXED theorem are closed. The core's chosen threshold is below `eps1`;
the signed type, exactly as approved, does not expose a separate `eps2 ≤ eps1` field.

## Definition classification

| Definition | Classification on its whole carrier |
|---|---|
| `p11SlowMW` | Intended total arithmetic bound `MF + n*(L*(pi*rz^2/16)) + 2^(2*n)*(MF/16+1)`. No epsilon argument, choice or fallback. |
| `p11SlowAsmC` | Intended total maximum of explicit constants. Standard total real powers/division are used; positivity hypotheses hold wherever the analytic bound is invoked. No fallback. |
| `P11SlowSpec` | Intended signed proposition with literal domains, norms, constants and carrier; no weakened or vacuous replacement of an analytic field. |
| `p11SlowConstant` | Signed classical choice when `1 ≤ nu`, else exactly `1`. The fallback outside the theorem range is intentional and unused in the proof. |
| `p11SlowData` | Signed classical choice when a witness exists, else exactly `default`. The successful branch is kernel-proved available throughout the theorem's certified interval; no theorem relies on the default being analytic data. |

No new abbrev or structure occurs in the five-file focus. The inherited
`P11SlowData` structure and `P11SlowSpecOf` are used unchanged. In particular
`P11SlowSpec D nu eps c A = P11SlowSpecOf (p11SecularData D)
(p11FastData D eps) nu eps c A` elaborates by `rfl`.

`MW = p11SlowMW C` is independent of epsilon after `eta1 ≤ 1` is eventually derived.
`cf0 = C.MF^3` is also independent of epsilon: `p11_slow_coeff_zero` gives
`(eps*MF)^3 = MF^3*eps^3`, and the assembly passes that exact coefficient.
The constant `c0` is selected before epsilon and all terms in `c2` depend only on
fixed secular data, `nu` and `c0`.

## Validation receipts

Final commands were run serially, with `LEAN_NUM_THREADS=1`; all Lean invocations
used `nice -n 5` (the prescribed build gate applies it internally). No clean,
cache fetch, toolchain change or repository repair was performed.

1. Targeted independent gate build:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap7d KAM.Planetary.Preparation.Slow
   ```

   Exit **0**. Exact gate/final lines:

   ```text
   [inp-gate] slot 3 acquired 00:54:57 for KAM.Planetary.Preparation.Slow
   Build completed successfully (9418 jobs).
   ```

   Replayed inherited warnings occurred; the only focused-module warning was the
   deprecated `dif_pos` in `SlowSigned.lean:98:10`. The author's concurrent build
   was allowed to finish before this independent final gate invocation.

2. Signed and choice/axiom probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AP7dAudit.lean
   ```

   Final exit **0**. The probe copied all three signed definition bodies under
   fresh names and proved equality to production definitions by `rfl`; copied
   the signed `avg_slow` declaration with body `by exact KAM.Planetary.avg_slow D hnu`;
   checked the spec/core equality by `rfl`; and proved a common positive epsilon
   interval on which the chosen `p11SlowData` satisfies the exact spec and the
   chosen constant is at least one. Independent whitespace-normalized comparisons
   of signed bodies/types all returned `True`.

   Earlier discarded scratch attempts omitted a local `open Classical` and then
   encountered a temporarily absent object during the author's rebuild. These
   were probe/race issues, not accepted validation receipts or production defects.
   The corrected final probe ran after the independent build and succeeded.

   Every new public theorem and both signed choice exports were checked:

   ```text
'KAM.Planetary.p11_torusAverage_natAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_coeff_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_C_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowMW_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_MW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.avg_slow_of_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.avg_slow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowConstant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowData' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. One kernel replay invocation:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.Slow KAM.Planetary.Preparation.SlowAssembly KAM.Planetary.Preparation.SlowCoeff KAM.Planetary.Preparation.SlowMW KAM.Planetary.Preparation.SlowSigned
   ```

   Exit **0**. Complete output:

   ```text
replaying KAM.Planetary.Preparation.SlowSigned
replaying KAM.Planetary.Preparation.SlowMW
replaying KAM.Planetary.Preparation.SlowCoeff
replaying KAM.Planetary.Preparation.SlowAssembly
replaying KAM.Planetary.Preparation.Slow
   ```

4. Repository lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, solely for the generated-root exception expressly allowed by the
   brief. Complete output:

   ```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1181 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
   ```

   Module-system, frozen-anchor guard and elaborated ABI checks all pass. No
   substantive lint failure was found; the permitted stale root accounts for
   the overall PASS WITH NOTES rather than an unqualified hygiene pass.

5. Protected paths / whitespace:

   ```sh
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   git diff --check
   ```

   Both exit **0**; protected-path diff empty (apart from Git's multiple-merge-base
   warning on stderr), whitespace check silent. No generated root was rewritten.


## Source, hygiene and revision details

Static scans of the five files found no forbidden proof escape, resource override
or `EuclideanSpace`. A comment-masked declaration search across `KAM/**/*.lean`
found no repeated focused declaration short name, and no root declaration/shadow
was introduced: the declarations live in `KAM.Planetary`.

The transitive project import scan reaches 64 frozen definition anchors, all
manifest `SEALED`, no frozen theorem, and no provider module. Thus there is no
`DRAFT_SORRY` theorem or provider dependency hidden behind the facade. Relevant
frozen P-G/P-PLANAR/P-FIXED anchors were read as context; they are not imported by
this package. Protected files remain unchanged.

| File | Lines | Maximum columns | SHA256 of audited source |
|---|---:|---:|---|
| `SlowAssembly.lean` | 207 | 96 | `fd82f8a5fb604bbdc83a5d37d03f8f6a7a2599ce592300619a5ea68c095e54f5` |
| `SlowCoeff.lean` | 136 | 97 | `93c4b2fffa497b8d16ec2ca58fdb17342c66b80046d51fd2c3ee5d871f360672` |
| `Slow.lean` | 26 | 92 | `db07c52da6015539d636e3404437a6d444696a7ad30a15be24ec05b2de3187cd` |
| `SlowMW.lean` | 102 | 94 | `3cfdc56ffeaf60b487572a717b019770572e3ce26d2f6b00b6aed0b62df41093` |
| `SlowSigned.lean` | 110 | 99 | `f5e0b08c92310d01cda3b778d54625a93ea0611997b391519a19370b3b8dc24a` |

## Errata, deviations and limits

No new suspected pinned-source defect or blueprint contradiction was found in
this scope. P7cb resolves the earlier literal mixed-divisor mismatch; this report
does not supersede unrelated findings in inherited audits. The dropped redundant
`P11SecularHReal` premise and the signed quarter bound are justified above.
The deprecated `dif_pos` at `SlowSigned.lean:98` is cosmetic.

The report is written in this package worktree, following the user's explicit
absolute-path instruction over the generic brief's main-worktree destination.
Only this report and temporary `.lake/abi-scratch/` probes were authored by the
auditor. The probes are removed after validation. The author's assembly commit and
the untracked handoff are preserved.
