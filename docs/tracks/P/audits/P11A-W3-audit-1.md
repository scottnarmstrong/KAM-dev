# P11A-W3 independent package audit 1

Overall verdict: **PASS WITH NOTES** for `KAM.Planetary.divided_difference` and the P11A-W3 infrastructure package. No implementation defect or unpaid proof obligation was found in the assigned module. Notes concern one minor blueprint boundary-case omission and the explicitly permitted stale generated root. **No frozen anchor is supplied or sealed by this package; seal readiness is not applicable.**

## Scope and authority

Audited only `KAM/Planetary/WeakMeasure/DividedDifference*.lean`; the sole matching file is `KAM/Planetary/WeakMeasure/DividedDifference.lean` (125 lines). Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the package handoff, the Track P statement, design Revision 3 including row P11A-W3 and its proof contracts, all three design audits, the supplied signatures and the relevant blueprint text. The user's exact report destination overrides the generic brief's main-worktree destination.

Snapshot: HEAD `1ebcceecf2cf39e8aec2ad128659da4d7bee82d7`; comparison ref `inp` resolved to `aa359d8fcbe90f6489dc2c4a3ccaf7b5a8e7f8ec`. `git diff inp...HEAD` contains exactly the new 125-line module. The handoff was already untracked before this audit.

SHA-256 pins checked during the audit:

| Input | SHA-256 |
|---|---|
| Audited Lean module | `a273748b0af51cce68bc77441ea9c28d9f9cb3cbded11a98e3afff7c2b1168d4` |
| `docs/tracks/P/design/P11A-LEAN-DESIGN.md` | `8619ea896c856347a9a5c5efac5080f0c830ea19245320b5f03a2b4267a300b9` |
| `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean` | `c31fda0b479f2dd0488b12e7f2daeda18f965eb316610df1c65f14012dfcb092` |

The latter two agree with design audit 3's R3 pins. The main theorem's complete declaration header is byte-identical to the supplied signature at L116–121 and the design's Appendix A at L1059–1064. There is no provider or imported frozen declaration: all five imports are Mathlib modules. Provider/frozen type equality and frozen seal-body probes therefore do not apply. Instead I elaborated a fresh copy of the exact main declaration with body `by exact KAM.Planetary.divided_difference hq hab hf t ht ha hb`, and a separately stated interpolation-coefficient example.

## Declaration and node ledger

All names below are in `KAM.Planetary`; line numbers refer to the audited Lean module.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| Iterated-Rolle induction predicate / `bpP:p11a:f-rolle` | `P11RolleIcc` (L34) | PASS | Literal finite-order Rolle property on increasing nodes; closed hull permits the legitimate order-zero base case. |
| One positive-order Rolle step / `bpP:p11a:f-rolle` | `p11Rolle_step` (L40) | PASS | Explicitly conditional induction helper, separately named; returns a zero strictly inside the outer nodes. The IH is discharged by the next theorem, never added to the main source statement. |
| Iterated Rolle / `bpP:p11a:f-rolle` | `p11Rolle_Icc` (L68) | PASS | Unconditional proof for every natural order by structural recursion; base case evaluates at the sole node. Positive-order open-hull conclusion is available through `p11Rolle_step (p11Rolle_Icc k)`. |
| Polynomial evaluation bridge | `p11_iteratedDeriv_eval` (L77) | PASS | All real polynomials and all natural orders; identifies analytic iterated derivatives with evaluated polynomial derivatives. No regularity premise is needed for polynomials. |
| `stepP:p11a:dd-interp` | `p11_iterate_derivative_interpolate` (L88) | PASS | Exactly the required constant polynomial `q!` times the divided difference; arbitrary node values. Uses Mathlib's interpolation derivative formula with cardinality `q+1` and injectivity from strict monotonicity. Also valid at `q=0`. |
| `bpP:p11a:divided-difference` | `divided_difference` (L96) | PASS | Exact design signature, source order `q≥1`, `C^q` on `[a,b]`, increasing contained nodes, exact sum/product formula and interior witness. No extra premise or weakened conclusion. |
| `stepP:p11a:dd-rolle` | Proof at L112–119 using `p11Rolle_step` and `p11Rolle_Icc` | PASS | Applies iterated Rolle to the actual function `f−P`, then uses interior regularity to subtract genuine iterated derivatives. |

Design mapping names `dd_interp` and `dd_rolle` describe proof-local obligations; the design explicitly permits splitting them into separately named helpers. The delivered interpolation helper and the final theorem's Rolle application retain both mathematical obligations. The package does not separately reprove interpolation uniqueness: it uses Mathlib's literal interpolant and node-evaluation theorem, as the design prescribes.

## Definition classification and adversarial proof checks

The only new definition is `P11RolleIcc : ℕ → Prop`. It is an exposed proposition abbreviation expressed as a `def`, not an assumed instance or output structure. Its body is the intended universal implication for every order, interval, function and node family. At order zero its closed singleton hull and `iteratedDeriv 0` give the expected evaluation assertion. Inconsistent interval/node inputs merely make the implication vacuous; there is no junk numerical value, fallback or choice-based object. No new `abbrev` or `structure` occurs. Local `P` is exactly `Lagrange.interpolate Finset.univ t (fun i => f (t i))`.

The conditional `IH : P11RolleIcc k` is a legitimate lower-order induction hypothesis in a distinctly named helper, not a missing theorem assumed by the package: `p11Rolle_Icc` proves it recursively without external premises, and the main theorem supplies it explicitly. All remaining hypotheses are source regularity, node ordering and interval typing data.

At L45–60, adjacent Rolle points lie strictly between adjacent nodes, hence form an increasing family. Their entire closed hull lies in `Ioo a b`; differentiating `g` there is justified by `ContDiffOn` on the original closed interval and restriction to the open interval. This prevents a totalized `deriv` value at a nondifferentiability point from serving as the proof. At L117–119 the final witness is again proved interior to `[a,b]` before `iteratedDeriv_fun_sub` is used. Thus arbitrary values of `f` outside `[a,b]` cannot supply a spurious derivative identity.

Strict monotonicity makes every difference `t i − t j` with `j≠i` nonzero, so the interpolant and divided-difference denominators have their intended mathematical meaning. The cardinality inequality in `Lagrange.iterate_derivative_interpolate` is `q < q+1`. The final factorial is positive and explicitly shown nonzero before division. Signs, factorial normalization, real carrier and derivative order match the blueprint at `p11a1-weak-measure.tex:84–90`. There is no dependence on a frozen theorem, a provider, an analytic extension outside the interval, or a source result assumed as a field.

## Independent verification

All audit-owned Lean/Lake commands ran serially with `LEAN_NUM_THREADS=1` and `nice -n 5`; no heartbeat, recursion-depth or synthesis override was used. No clean, update, cache fetch, generated-root regeneration or library-wide build was run. The gate waited normally before acquiring slot 1 at `08:58:25` UTC.

Targeted build:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11aw3 KAM.Planetary.WeakMeasure.DividedDifference
```

Exit **0**. Output:

```text
[inp-gate] slot 1 acquired 08:58:25 for KAM.Planetary.WeakMeasure.DividedDifference
⚠ [2381/2381] Replayed KAM.Planetary.WeakMeasure.DividedDifference
warning: KAM/Planetary/WeakMeasure/DividedDifference.lean:96:59: Variable name `hab` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hab

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (2381 jobs).
```

This is a replayed targeted build, not a claim of forced recompilation. The existing checked artifact was independently kernel-replayed below. The unused `hab` is harmless: the required strict endpoint ordering already follows from the positive-order increasing node family. It is retained to match the signature exactly; no suggested linter override was applied.

Exact statement/interpolation probes and axiom inspection:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AW3Audit.lean
```

Exit **0**, no errors or warnings; complete output:

```text
'KAM.Planetary.P11RolleIcc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rolle_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rolle_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_iteratedDeriv_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_iterate_derivative_interpolate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.divided_difference' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay, one invocation covering the sole implementation/helper module:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakMeasure.DividedDifference
```

Exit **0**; complete output:

```text
replaying KAM.Planetary.WeakMeasure.DividedDifference
```

Source hygiene inspection: **125 lines**, maximum Unicode line length **99**, no forbidden proof escapes or resource overrides, copyright header, `module`, five `public import`s, module docstring and `@[expose] public noncomputable section` present. No ambient-space violation, provider import or frozen import exists.

## Suspected blueprint defects, deviations and limitations

**N1 — Minor omitted positive-order guard in prose.** At `blueprint-P/parts/p11a1-weak-measure.tex:31`, the external fact says: “If $u\in C^q([a,b])$ has $q+1$ distinct zeros, then $u^{(q)}$ has a zero in $(a,b)$”. Read literally for natural `q`, this needs `q≥1`: at `q=0`, take `a=0`, `b=1` and `u(x)=x`, whose sole zero in `[0,1]` is the endpoint. The design repeats the interior-zero wording at `docs/tracks/P/design/P11A-LEAN-DESIGN.md:440`. The correct mathematical main lemma explicitly has `q≥1` at blueprint L85 and Lean L96, so this omission does not affect the package proof or its consumers. The Lean helpers correctly distinguish the order-zero closed hull from the positive-order open hull. Recommend making the prose guard explicit; no source or design edit was made.

The module docstring at `DividedDifference.lean:17–18` also omits `q≥1` when describing its open-hull conclusion. At `q=0` that displayed open interval is empty, even though the coefficient identity remains valid. Recommend adding “for `q ≥ 1`” to that sentence when the prover next edits documentation. This is a prose correction, not a type or proof failure.

**N2 — Expected generated-root lint exception.** The added module is absent from the generated `KAM.lean`; the audit brief explicitly allows the resulting stale-root diagnostic. Root regeneration belongs to the orchestrator. No protected file was changed.

No suspected pinned-paper erratum was found in the assigned elementary interpolation/Rolle argument; the proof uses Mathlib directly. No mathematical deviation or unresolved implementation design signal was found. This package proves infrastructure only, not scalar sublevel estimates, the measure layer, P-FIXED, or any frozen headline. No frozen anchor or downstream theorem was audited for sealing.

## Final lint and integrity receipts

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the brief's permitted stale-root exception; complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (508 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no output and exited **0**. Both `git diff --check inp...HEAD` and `git diff --check` exited **0** with no output. The only tracked branch difference remains the audited Lean module; the working-tree tracked diff is empty. The temporary `.lake/abi-scratch/P11AW3Audit.lean` probe was deleted. Final status contains only the pre-existing untracked handoff and this new report. An explicit scan of this untracked report found no trailing whitespace and balanced Markdown fences. No state-changing git command was used.

Only this report persists as an audit-created repository file. Required package checks are complete; the permitted lint exception and minor documentation guard omissions are the only notes.
