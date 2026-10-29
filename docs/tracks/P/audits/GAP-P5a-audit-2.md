# GAP-P5a independent audit 2

Date: 2026-10-29. Auditor: maud-gp5a-2.

**Overall verdict: PASS WITH NOTES. Audit-1 finding F1 is closed.** All six new public
exports state and prove their assigned literal conclusions. The four extension steps may
be skipped under their current PROVED records. The only hygiene exception is the expressly
permitted stale generated root. This is an unsigned graph-gap package audit; it does not
certify a new frozen-anchor seal or close source-graph bookkeeping.

## Scope and authority

Report destination: `/root/code/KAM-inp-gp5a/docs/tracks/P/audits/GAP-P5a-audit-2.md`.
The user's exact absolute destination overrides the generic brief's main-worktree wording.

Audited HEAD: `7978f25eb2713da4a2462eeb2fdbf85af793c794`.
Observed comparison branch `inp`: `9208f71fad9c557fdee5db7c9a1b7bd222094650`.
Merge base: `c1839fee225146e0c60e389ca73433801f3a9c52`.
The complete `git diff inp...HEAD` has four additions, 541 lines:

| File | Lines | Scope |
|---|---:|---|
| `KAM/Planetary/PGAssembly/ScaleNodes.lean` | 214 | Six private helpers and four public theorems |
| `KAM/Planetary/PGAssembly/ExtensionNodes.lean` | 65 | Two public theorems |
| `docs/tracks/P/audits/GAP-P5a-audit-1.md` | 206 | Prior independent finding and receipts |
| `docs/tracks/P/audits/GAP-P5a-handoff.md` | 56 | Handoff including round-2 repair |

Read AGENTS.md, PLAN, DECISIONS, the package audit brief, handoff and audit 1; the explicit
GAP-P5a scope and rulings in `.drafts/briefs/offload-main/GAP-P5a.md` and GAP-PLAN-P section
GAP-P5a; P45 design context and relevant P45 signatures; track P statement and frozen P-G
statement and pertinent definitions; every assigned graph record, its cited blueprint passage,
and AMENDMENTS. The handoff has no literal `AUDIT FOCUS` heading; its node table, self-check
and Round 2 section supply the focus. The package brief's generic P11B template references
have no GAP-P5a signature; its explicit graph-gap ruling supplies this package's UNSIGNED
literal-node contract. Existing P45 signatures govern the underlying objects.

No new provider or frozen theorem is introduced. Provider/frozen type-equality and seal-body
probes are therefore not applicable. The already sealed P-G anchor was inspected for the
standing telescope; its existing provider was not re-audited. Full-history comparison and
`git diff 0fd00801..HEAD -- KAM/Planetary` confirm that the round-2 Lean repair changes only
`kam_cond_node` and its docstring. Other audited exports remain byte-identical to round 1.

## Node and declaration verdicts

Short names below are in `KAM.Planetary`. S = ScaleNodes.lean, E = ExtensionNodes.lean.
Graph locators refer to `docs/graph/P/DEPGRAPH.md`; blueprint locators refer to
`blueprint-P/parts/p5-pg-assembly.tex`.

| Node / declaration | Export and locator | Verdict | Reason |
|---|---|---|---|
| `stepP:p5:kc-eval` (graph 9570; blueprint 224) | `kc_eval`, S:117 | PASS | Exact actual P3 x equality and bound, L, K0, radius min, both P3/params bridges, error quotient and max identity, internally derived for positive r and 0<mu≤1. |
| `stepP:p5:kc-small` (9599; 225) | `kc_small`, S:143 | PASS | Product smallness and gamma2 = mu*gamma1 ≤ gamma1. |
| `bpP:p5:kam-cond` (9536; 212–226) | `kam_cond_node`, S:159 | PASS | Data-only scale specification precedes universally quantified parameters; actual x equality, bound, exact cutoff, both bridges, min/quotient/max, smallness, gamma order and tau>n all retained. F1 closed. |
| `stepP:p5:rk-dir` (9660; 233) | `rk_dir`, S:185 | PASS | All seven conjuncts, including error bound and both links of radius chain, min, half-rhoBar, relative-width and power bounds. Source admissibility only. |
| `bpP:p5:rK` (9629; 228–234), additional completion | `rk_dir`, S:185 | PASS | Final six conjuncts supply all literal displayed bounds, including those missing from historical r_k reference. |
| `stepP:p5:be-an` (8375; 59) | `be_an`, E:29 | PASS | Holomorphy of each jet entry, symmetry, joint continuity on parameter interval times full complex half tube. Joint continuity is stronger than parameter-only continuity. |
| `stepP:p5:be-jet` (8403; 60) | `be_jet`, E:50 | PASS | Every k≤4 and every multilinear input; holomorphy on full half tube, whole derivative-map vanishing on V and tube. Stronger than coordinate multi-index vanishing. |
| `stepP:p5:ext-loc` (8168; 33), skipped | existing `ext`, Extension.lean:36 | PASS, status check | Explicit PROVED, local to proved parent; P5-CL audit cited in record. |
| `stepP:p5:ext-glue` (8195; 34), skipped | existing `ext` | PASS, status check | Explicit PROVED, local to parent; P5-CG audit cited. |
| `stepP:p5:ext-per` (8222; 35), skipped | existing `ext` | PASS, status check | Explicit PROVED, local to parent; P5-EX audit cited. |
| `stepP:p5:ext-H0` (8250; 36), skipped | existing `ext` | PASS, status check | Explicit PROVED, local to parent; P5-EX audit cited. |
| Private helper | `kcnode_L`, S:27 | PASS | Computes actual maximum using C1≥1 and positive mu≤1. |
| Private helper | `kcnode_x`, S:37 | PASS | Positive-radius real-power identity and cancellation in actual P3 expression. |
| Private helper | `kcnode_cutoff`, S:50 | PASS | Substitutes x into actual cutoff; K0 depends on data alone. |
| Private helper | `kcnode_rhoHat`, S:60 | PASS | Cancels positive mu in small-divisor radius; exact actual radius bridge. |
| Private helper | `kcnode_eHat`, S:78 | PASS | Actual EL/rhoHat² attaches to params error. |
| Private helper | `kcnode_Ehat_max`, S:85 | PASS | Positive min branches, square/rpow identities, reciprocal order give exact max. |

The four skip rows verify the authorized skip rather than repeat the earlier extension audits.
The sole AMENDMENTS entry targets parent `bpP:p5:ext`, not these ten assigned nodes; its
closure-agreement restriction remains binding on their extension supplier.

## F1 closure, constants and hypotheses

At S:160, the named export now concludes `PGScaleSpec d (pgScales d)` before the `∀ {r mu}`
at S:161. Unfolding the specification yields κ0≥C1², κ1>0, both strict numerical smallness
inequalities and the full three-term lower bound on G. All choices are functions of d alone.
The underlying Scales.lean:95–130 construction chooses κ0 first, κ1 second, G third;
no parameter-dependent constant or circular choice is introduced.

S:163–164 retains the actual expression `E*M^2*L/gamma1^2 = C1^4/k0^2`.
S:167–168 retains both `rhoHat (pgKamScale ...) = params.rhoHat` and
`eHat (pgKamScale ...) = params.Ehat`. S:169–178 retains the remaining literal clauses.
The proof at S:179–181 uses the previously discarded kc_eval components as conclusions,
with `pgScales_spec d` proved internally. A fresh probe independently expanded the scale
specification and extracted the x equality and both bridges from this export; it elaborated.
Thus none of the repair is an added premise or a handoff-only citation.

`PGData` (Setting.lean:46) is the frozen P-G standing telescope, not a bundle of analytic
outputs. P45 design:439 explicitly permits specializing these helpers to that context.
`admissible` (Parameters.lean:71) consists of positive r, r<R, positive mu, mu<mu0 and the
source logarithmic upper bound. Threshold existence supplies pgRstar before r and mu.
No public theorem takes an extension, jet-vanishing assertion, KAM bound, or dependency's
output as a premise. Scale evaluations hold for all positive r and 0<mu≤1, stronger than
the blueprint's small-r regime. No assertion is claimed at zero denominators.

The product smallness `chat*Ehat<1` is equivalent to the displayed `Ehat<1/chat` by
`pgChat_pos`; the error bridge makes it the actual P3 KAM condition. `pgChat` and `pgTau`
agree with the constants in Part 3. All ambient carriers are ordinary Fin-function spaces
and products with their stated Pi/Prod norms. There is no changed metric or dimension.

## Definition classification and domain attachment

No new def, abbrev or structure occurs in either file. Local A and B in kcnode_Ehat_max
are the two positive radius expressions, not public fallback objects.

Inspected existing `PGScales`, `PGScaleSpec`, `pgScales`, `params`, `pgKamScale`, and Part 3
`constants`/`initialL`: these are the intended data-only witness and explicit scale formulas.
Positivity guards used by the new proofs prevent reliance on totalized division or powers.

Inspected JetsDefs.lean:30–47: jets are actual derivatives of the normalized complex average;
jetBeta's diagonal factor is 1/3, its off-diagonal entries are fourth derivatives with two
inputs in each coordinate, and pgRemainder is the average minus the oscillator polynomial.
Extension.lean:44–47 defines the actual (2π)^(-a) angular integral, attached on its constrained
real domain by complexAverage_real. No surrogate zero function is substituted.

For be_jet, mu lies in [0,mu0], then k≤4 and arbitrary v; the domain is the entire complex
`actionNbhd (closure V) (delta/2)`, not just its real slice. Zero lies in the oscillator
domain. Equality of the whole continuous multilinear map implies every coordinate derivative,
including order zero. JetsRegular.lean:146–165 proves tube vanishing using the proved
`connected_complex_tube` and `real_slice_identity`; its real vanishing input is proved by
JetsVanish.lean:66 onward from the actual Birkhoff remainder. JetsRegular's regularity and
symmetry route uses actual parameter integration and derivative-permutation results.

## Independent validation

All Lean/Lake invocations were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`, including
lint's ABI phase. No heartbeat/depth override, clean, cache fetch, package modification,
generated-root rewrite or state-changing git command was used.

1. `git diff inp...HEAD`, `git diff --stat inp...HEAD`, `git diff --numstat inp...HEAD`:
   four additions as above, 541 insertions. `git diff --check inp...HEAD` and
   `git diff --check`: exit 0, no output.
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, no output.
2. Targeted build:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp5a KAM.Planetary.PGAssembly.ScaleNodes KAM.Planetary.PGAssembly.ExtensionNodes
   ```

   Exit 0. Output included:

   ```text
   [inp-gate] slot 2 acquired 02:09:42 for KAM.Planetary.PGAssembly.ScaleNodes KAM.Planetary.PGAssembly.ExtensionNodes
   Build completed successfully (9231 jobs).
   ```

   Only existing dependency warnings replayed; none from ScaleNodes or ExtensionNodes.
3. Fresh `.lake/abi-scratch/GAPP5aAudit2.lean`: imported both modules; checked all six
   full signatures and printed their axioms; additionally elaborated the expanded scale
   specification and independent extraction of the three repaired x/radius/error clauses.
   Command: `env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPP5aAudit2.lean`.
   Exit 0; no warnings or errors. Exact axiom output:

   ```text
   'KAM.Planetary.kc_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kc_small' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kam_cond_node' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.rk_dir' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.be_an' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.be_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

4. Kernel replay:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.ScaleNodes KAM.Planetary.PGAssembly.ExtensionNodes
   ```

   Exit 0. Complete output:

   ```text
   replaying KAM.Planetary.PGAssembly.ExtensionNodes
   replaying KAM.Planetary.PGAssembly.ScaleNodes
   ```

5. Static scan and recursive import traversal: 185 KAM modules, zero providers and zero
   frozen theorem modules, hence no DRAFT_SORRY import in the closure. The audited files
   have all module/header/public-section components, no forbidden proof/resource tokens,
   no EuclideanSpace, no new definitions, and maximum line width 98 characters each.
   Their 214 and 65 lines are below the 1500-line cap. Each public short name occurs as
   a declaration exactly once in KAM, within namespace KAM.Planetary.

6. Lint: `env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`.
   Exit 1; complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1198 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   PASS WITH NOTES under the explicit audit-brief exception. No other lint failure;
   the generated file was left untouched.

## Source/blueprint issues, uncertainties and deviations

No new suspected pinned-source mathematical defect or frozen-statement defect was found.
F1 was a literal Lean-export omission and is now repaired, without a source amendment.

Retain the existing extension erratum, rather than silently restoring the printed stronger
clause. Blueprint p5:30 says “P̃ = P at real points” throughout X_delta. As documented in
P45 design:1993–2010, total P is unconstrained off the closed cylinder and need not be
uniformly periodic on a whole surrounding real tube; an angle-dependent exterior bump
refutes that stronger claim. `docs/graph/P/packets/AMENDMENTS.md:1–19` (P-A001) explicitly
replaces it by agreement on the closed cylinder. ExtensionDefs.lean:54–56 carries this
restriction and complexAverage_real uses it only on the allowed cylinder. This is an
inherited, already recorded blueprint issue, not a new deviation in these wrappers.

Historical SOURCE_GAP notes remain at graph be-an:8401 (parameter integration, continuity,
mixed derivatives), be-jet:8430 (real-slice identity theorem and connected tube), and the
skipped extension records. The corresponding proved Lean suppliers were inspected and are
used without extra premises. This audit establishes the scoped Lean conclusions, not the
addition of approved external-input nodes or supplying graph edges. No graph status or
amendment was changed. The older handoff table and uncertainty paragraph omit facts now
present in kam_cond_node; its later Round 2 section and the actual code govern this audit.

Only this report was added. All audit-created scratch probes and logs were removed after
recording results. Initial tracked/untracked status was clean; final status contains only
this report. No production, frozen, manifest, generated or other audit file was edited.
